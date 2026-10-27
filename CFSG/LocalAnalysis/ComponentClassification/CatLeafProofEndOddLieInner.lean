module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieDatum
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.FooteLit
  CFSG.LieType.Ree CFSG.Walter.Ree.Model
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem fixedSubgroup_mulAut_conj {G : Type*} [Group G] (x : G) :
    fixedSubgroup (MulAut.conj x) = centralizer ({x} : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj x g = g ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem orderOf_mulAut_conj_of_not_mem_center {G : Type*} [Group G] {x : G}
    (hx : orderOf x = 2) (hxZ : x ∉ center G) : orderOf (MulAut.conj x) = 2 := by
  have h2 : MulAut.conj x ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_prime h2 fun h1 => hxZ ?_
  rw [mem_center_iff]
  intro g
  have h3 : x * g * x⁻¹ = g := by
    have := congrArg (fun φ : MulAut G => φ g) h1
    simpa [MulAut.conj_apply] using this
  calc g * x = x * g * x⁻¹ * x := by rw [h3]
    _ = x * g := by group

theorem quasisimple_pComponents_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (e : G ≃* H) (h : ∀ L : Subgroup H, IsPComponent 2 L → IsQuasisimple L) :
    ∀ L : Subgroup G, IsPComponent 2 L → IsQuasisimple L := by
  intro L hL
  have hL' := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
    Nat.prime_two e).1 L).1 hL
  exact LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ e.injective).symm (h _ hL')

theorem not_mem_center_of_footeComponent {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {z : X} {K : Subgroup X} (hK : IsTwoComponentAt z K)
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hF : FooteFamilyType K) : z ∉ center X := by
  intro hz
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_footeFamilyType hs hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · rw [h, mem_bot] at hz
    have := hK.1
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  · have hb : (b : X) ∈ center X := h ▸ mem_top _
    exact hab (Subtype.ext (mem_center_iff.1 hb a))

theorem false_of_conj_quat {X : Type} [Group X] [Finite X] {z : X}
    (hq : ∀ L : Subgroup (fixedSubgroup (MulAut.conj z)), IsPComponent 2 L → IsQuasisimple L)
    (hQ : QuatComponentForm (fixedSubgroup (MulAut.conj z))) {K : Subgroup X}
    (hK : IsTwoComponentAt z K) (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hF : FooteFamilyType K) : False := by
  let Θ : centralizer ({z} : Set X) ≃* fixedSubgroup (MulAut.conj z) :=
    MulEquiv.subgroupCongr (fixedSubgroup_mulAut_conj z).symm
  exact false_of_isTwoComponentAt_of_quat (quasisimple_pComponents_of_mulEquiv Θ hq)
    (quatComponentForm_of_mulEquiv Θ hQ) hK hs hF

theorem false_of_untwisted_quat
    {τ : Tag}
    (hq : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      ∀ α : MulAut (adjointGroup τ F), α ^ 2 = 1 →
        ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L)
    (hQ : OddExcInnerDiagQuatForm τ) {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : UntwistedChevalleyModel X τ (p ^ f)) {z : X}
    {K : Subgroup X} (hK : IsTwoComponentAt z K) (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hF : FooteFamilyType K) : False := by
  obtain ⟨F, _, _, hF', ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have hFodd : Odd (Nat.card F) := by
    rw [hF']
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : Finite (adjointGroup τ F) := Finite.of_equiv _ e.toEquiv
  set y := e z with hy
  have hy2 : orderOf y = 2 := by rw [hy, MulEquiv.orderOf_eq]; exact hK.1
  have hyZ : y ∉ center (adjointGroup τ F) := by
    rw [center_adjointGroup_eq_bot, mem_bot]
    intro h1
    rw [h1, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hαo := orderOf_mulAut_conj_of_not_mem_center hy2 hyZ
  have hβg : ∀ h : adjointGroup τ F, (MulAut.conj y h : ModGL τ F) =
      (y : ModGL τ F) * rootDiagUnit τ 1 * (h : ModGL τ F) * (rootDiagUnit τ 1)⁻¹ *
        (y : ModGL τ F)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one, MulAut.conj_apply]
    rfl
  have hQ' := hQ F p f hp hp2 hF' (MulAut.conj y) y 1 hβg hαo
  have hq' := hq F hFodd (MulAut.conj y) (by rw [← hαo]; exact pow_orderOf_eq_one _)
  let Θ : centralizer ({z} : Set X) ≃* fixedSubgroup (MulAut.conj y) :=
    ((centralizer ({z} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr
        (LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e z)).trans
        (MulEquiv.subgroupCongr (fixedSubgroup_mulAut_conj y).symm))
  exact false_of_isTwoComponentAt_of_quat (quasisimple_pComponents_of_mulEquiv Θ hq')
    (quatComponentForm_of_mulEquiv Θ hQ') hK hs hF

end CFSG.ComponentClassification.CatLeafProof
