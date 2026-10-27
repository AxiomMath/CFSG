module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCocycles

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem complement_quotient_restriction_bijective {G : Type u} [Group G]
    (kernel complement : Subgroup G) [kernel.Normal] (hcomplement : kernel.IsComplement' complement) :
    Function.Bijective ((QuotientGroup.mk' kernel).comp complement.subtype) := by
  constructor
  · intro first second heq
    have hdifference : (first : G) * (second : G)⁻¹ ∈ kernel := by
      rw [← QuotientGroup.ker_mk' kernel]
      apply MonoidHom.mem_ker.mpr
      change (QuotientGroup.mk' kernel) ((first : G) * (second : G)⁻¹) = 1
      rw [map_mul, map_inv]
      change (QuotientGroup.mk' kernel) (first : G) = (QuotientGroup.mk' kernel) (second : G) at heq
      rw [heq, mul_inv_cancel]
    have hone := Subgroup.disjoint_def.mp hcomplement.isCompl.disjoint hdifference
      (complement.mul_mem first.property (complement.inv_mem second.property))
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  · intro element
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective kernel element
    have hmem : representative ∈ kernel ⊔ complement := by
      rw [hcomplement.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨⟨second, hsecond⟩, ?_⟩
    change (QuotientGroup.mk' kernel) second = (QuotientGroup.mk' kernel) (first * second)
    have hfirstZero : (QuotientGroup.mk' kernel) first = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [QuotientGroup.ker_mk']
      exact hfirst
    rw [map_mul, hfirstZero, one_mul]

theorem abelian_normal_complements_conjugate {G : Type u} [Group G] [Finite G]
    (kernel first second : Subgroup G) [kernel.Normal]
    (hcomm : IsMulCommutative kernel)
    (hfirst : kernel.IsComplement' first) (hsecond : kernel.IsComplement' second)
    (hcoprime : (Nat.card kernel).Coprime kernel.index) :
    ∃ conjugator ∈ kernel, first.map (MulAut.conj conjugator).toMonoidHom = second := by
  classical
  have : IsMulCommutative kernel := hcomm
  let : CommGroup kernel := IsMulCommutative.instCommGroup
  let quotient := QuotientGroup.mk' kernel
  let firstEquiv : first ≃* G ⧸ kernel := MulEquiv.ofBijective (quotient.comp first.subtype)
    (complement_quotient_restriction_bijective kernel first hfirst)
  let secondEquiv : second ≃* G ⧸ kernel := MulEquiv.ofBijective (quotient.comp second.subtype)
    (complement_quotient_restriction_bijective kernel second hsecond)
  let projection : second ≃* first := secondEquiv.trans firstEquiv.symm
  let liftHom : second →* G := first.subtype.comp projection.toMonoidHom
  have hliftImage : ∀ element : second, quotient (liftHom element) = quotient element := by
    intro element
    change firstEquiv (firstEquiv.symm (secondEquiv element)) = secondEquiv element
    exact firstEquiv.apply_symm_apply _
  let cocycle : second → kernel := fun element => ⟨(element : G) * (liftHom element)⁻¹, by
    have hmem : (element : G) * (liftHom element)⁻¹ ∈ quotient.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hliftImage, mul_inv_cancel]
    rw [QuotientGroup.ker_mk'] at hmem
    exact hmem⟩
  let actionHom : second →* MulAut kernel := MulAut.conjNormal.comp liftHom
  let : MulDistribMulAction second kernel := MulDistribMulAction.compHom kernel actionHom
  have hcocycle : ∀ left right : second, cocycle (left * right) = cocycle left * (left • cocycle right) := by
    intro left right
    apply Subtype.ext
    change ((left : G) * right) * (liftHom (left * right))⁻¹ =
      ((left : G) * (liftHom left)⁻¹) *
        (liftHom left * ((right : G) * (liftHom right)⁻¹) * (liftHom left)⁻¹)
    rw [map_mul]
    group
  have hcoprimeSecond : (Nat.card kernel).Coprime (Nat.card second) := by
    rw [← hsecond.symm.index_eq_card]
    exact hcoprime
  obtain ⟨fixed, hfixed⟩ := coprime_cocycle_has_fixed_point cocycle hcocycle hcoprimeSecond
  have hconjugateElement : ∀ element : second,
      (fixed : G) * liftHom element * (fixed : G)⁻¹ = element := by
    intro element
    have heq := congrArg (fun value : kernel => (value : G)) (hfixed element)
    change ((element : G) * (liftHom element)⁻¹) *
      (liftHom element * (fixed : G) * (liftHom element)⁻¹) = fixed at heq
    have hproduct : (element : G) * (fixed : G) * (liftHom element)⁻¹ = fixed := by
      simpa only [mul_assoc, inv_mul_cancel_left] using heq
    have hcancel := congrArg (fun value : G => value * liftHom element * (fixed : G)⁻¹) hproduct
    have helementEq : (element : G) = (fixed : G) * liftHom element * (fixed : G)⁻¹ := by
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hcancel
    exact helementEq.symm
  refine ⟨fixed, fixed.property, ?_⟩
  ext element
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    obtain ⟨representative, hrepresentative⟩ := projection.surjective ⟨preimage, hpreimage⟩
    have hvalue : liftHom representative = preimage := congrArg Subtype.val hrepresentative
    change (fixed : G) * preimage * (fixed : G)⁻¹ ∈ second
    rw [← hvalue, hconjugateElement]
    exact representative.property
  · intro hmem
    let representative : second := ⟨element, hmem⟩
    refine ⟨liftHom representative, (projection representative).property, ?_⟩
    exact hconjugateElement representative

end CFSG.RankThreeEvenClassification.Helpers
