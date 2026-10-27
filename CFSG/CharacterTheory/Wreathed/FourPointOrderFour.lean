module

public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourBases
public import CFSG.CharacterTheory.Wreathed.FourPointCompleteModel

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderFour

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.FourPointLifts
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.FourPointCompleteModel

open scoped Classical Matrix

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_order_four_centralizer_and_odd_restriction_bases
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index)
    (hprincipalN : (basisN.representation principalN).character = 1)
    (basisC : FiniteIrreducibleCharacterBasis (orderFourCentralizer n S e))
    (principalC : basisC.index)
    (hprincipalC : (basisC.representation principalC).character = 1) :
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let H := centralizerOddCoreQuotient n S e
    let π := centralizerOddCoreMap n S e
    let A := centralizerFullCenterImage n hn S e
    let a : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let x := centralInvolution n S e
    let C := orderFourCentralizer n S e
    let R₀ : Subgroup G := R.map N.subtype ⊓ C
    let πC := orderFourMap n S e
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
      (CentralSL2.upperSL (ZMod 3) 1)
    let B₀N := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
    let B₀C := coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC
    let bN : Fin 2 → OddElements N → ℂ :=
      ![fun _ => 1, fun g => 3 * (if (g : N) ∈ R then 1 else 0) - 1]
    let bC : Fin 2 → OddElements C → ℂ :=
      ![fun _ => 1, fun g => 3 * (if ((g : C) : G) ∈ R₀ then 1 else 0) - 1]
    n = 2 ∧ Nat.card H = 96 ∧ A = Subgroup.center H ∧ Nat.card A = 4 ∧
      (∃ Φ : W ≃* H, Φ (u ^ 2) = π a) ∧
      orderOf a = 4 ∧ a ^ 2 = x ∧ C ≤ N ∧
      (∀ g : N, ∃ r ∈ R, ∃ c : N, (c : G) ∈ C ∧ g = r * c) ∧
      (∀ g : G, g ∈ R₀ ↔ g ∈ R.map N.subtype ∧ g * a = a * g) ∧
      R₀ = (CFSG.oddCore C).map C.subtype ∧
      Function.Surjective πC ∧ πC.ker.map C.subtype = R₀ ∧
      Nat.card N = 96 * Nat.card R ∧ Nat.card C = 96 * Nat.card R₀ ∧
      ¬ IsConj (a : G) (a : G)⁻¹ ∧
      (∀ Φ : W ≃* H, (∃ z : N, (z : G) ∈ C ∧ Odd (orderOf z) ∧ π z = Φ U₀) ∧
        ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
          z ∉ R ∧ x * z = z * x ∧ BlocksIsPPart 2 (x * z) x ∧ a * z = z * a ∧
            BlocksIsPPart 2 (a * z) a) ∧
      (∀ χ, χ ∈ B₀N ↔ ∃ θ : basisH.index,
        (basisN.representation χ).character = (basisH.representation θ).character ∘ π) ∧
      (∀ θ : basisH.index, ∃ χ ∈ B₀N,
        (basisN.representation χ).character = (basisH.representation θ).character ∘ π) ∧
      (∀ χ, χ ∈ B₀C ↔ ∃ θ : basisH.index,
        (basisC.representation χ).character = (basisH.representation θ).character ∘ πC) ∧
      (∀ θ : basisH.index, ∃ χ ∈ B₀C,
        (basisC.representation χ).character = (basisH.representation θ).character ∘ πC) ∧
      OddRestrictionComplexBasis basisN B₀N bN !![16, 8; 8, 12] ∧
      OddRestrictionComplexBasis basisC B₀C bC !![16, 8; 8, 12] ∧
      (∀ g : OddElements N, (g : N) = 1 → bN 0 g = 1 ∧ bN 1 g = 2) ∧
      (∀ g : OddElements C, (g : C) = 1 → bC 0 g = 1 ∧ bC 1 g = 2) ∧
      ∀ (Φ : W ≃* H) (z : N), (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
        (∀ g : OddElements N, (g : N) = z → bN 0 g = 1 ∧ bN 1 g = -1) ∧
        ∀ g : OddElements C, ((g : C) : G) = z → bC 0 g = 1 ∧ bC 1 g = -1 := by
  obtain rfl := FourPointResidual.four_point_parameter n hn S e alpha
  intro N R H π A a x C R₀ πC W u U₀ B₀N B₀C bN bC
  obtain ⟨-, hAcenter, -, hAcard, hHcard, -, -, -, ⟨Φ₀, hΦ₀u, -⟩, -, -, hiffN, hsurjN, -⟩ :=
    four_point_actual_centralizer_complete_model_and_principal_block hnonab 2 hn S e alpha ideal
      basisH principalH hprincipalH basisN principalN hprincipalN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haord : orderOf a = 4 := orderOf_centralizerModelHom_a 2 hn S e
  have hapow : a ^ 2 = x := centralizerModelHom_a_pow 2 hn S e
  have hxord : orderOf x = 2 := by
    rw [← hapow, orderOf_pow_of_dvd (by norm_num) (by rw [haord]; norm_num), haord]
  have hCN : C ≤ N := orderFourCentralizer_le 2 S e
  have hR₀ : πC.ker.map C.subtype = R₀ := orderFourMap_ker_map 2 hn S e
  have hR₀odd : Odd (Nat.card πC.ker) := orderFourMap_ker_odd 2 hn S e
  have hπC : Function.Surjective πC := orderFourMap_surjective 2 hn S e
  have hRodd : Odd (Nat.card π.ker) := by
    rw [show π.ker = R from QuotientGroup.ker_mk' R]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hlift : ∀ Φ : W ≃* H, ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
      z ∉ R ∧ x * z = z * x ∧ BlocksIsPPart 2 (x * z) x ∧ a * z = z * a ∧
        BlocksIsPPart 2 (a * z) a := by
    intro Φ z hzC hzodd hπz
    obtain ⟨hv3, -, -⟩ := odd_classes_of_equiv Φ
    have hza : z * a = a * z := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC)
    have hzx : z * x = x * z := by
      rw [← hapow]
      exact (Commute.pow_right (show Commute z a from hza) 2).eq
    have hcop : Nat.Coprime (orderOf z) 2 := Nat.coprime_two_right.mpr hzodd
    refine ⟨fun hzR => ?_, hzx.symm, ⟨z, rfl, hzx, ⟨1, hxord⟩, orderOf_pos z, hcop⟩, hza.symm,
      ⟨z, rfl, hza, ⟨2, haord⟩, orderOf_pos z, hcop⟩⟩
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hzR
    rw [hπz] at h1
    rw [h1, orderOf_one] at hv3
    exact absurd hv3 (by norm_num)
  have hQnormal := fourPointQ_normal 2 hn S e alpha
  have hQp : IsPGroup 2 (fourKlein.comap (alpha.toMonoidHom.comp
      (centralizerFullQuotientMap 2 hn S e))) :=
    IsPGroup.of_card (n := 4) (fourPointQ_card 2 hn S e alpha hHcard)
  obtain ⟨hiffC, hsurjC⟩ := orderFour_principal_block 2 hn S e _ hQp
    (fourPointQ_centralizer_le 2 hn S e alpha) ideal basisH basisC principalC hprincipalC
  obtain ⟨hv3, hvconj, hvcent⟩ := odd_classes_of_equiv Φ₀
  have hbasisN : OddRestrictionComplexBasis basisN B₀N bN !![16, 8; 8, 12] :=
    oddRestrictionComplexBasis_of_inflation π (centralizerOddCoreMap_surjective 2 S e) hRodd
      basisN basisH B₀N hiffN _ hv3 hvconj hHcard hvcent (fun g => g ∈ R)
      (fun g => (QuotientGroup.eq_one_iff g).symm)
  have hbasisC : OddRestrictionComplexBasis basisC B₀C bC !![16, 8; 8, 12] := by
    refine oddRestrictionComplexBasis_of_inflation πC hπC hR₀odd basisC basisH B₀C hiffC _ hv3
      hvconj hHcard hvcent (fun g => (g : G) ∈ R₀) fun g => ?_
    rw [← hR₀]
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).trans MonoidHom.mem_ker
  refine ⟨rfl, hHcard, hAcenter, hAcard, ⟨Φ₀, hΦ₀u⟩, haord, hapow, hCN,
    orderFour_factorization 2 hn S e, fun g => Subgroup.mem_inf.trans
      (and_congr_right fun _ => Subgroup.mem_centralizer_singleton_iff),
    orderFour_oddCore_inf 2 hn S e, hπC, hR₀, ?_, ?_, not_isConj_a_inv 2 hn S e,
    fun Φ => ⟨?_, hlift Φ⟩, hiffN, hsurjN, hiffC, hsurjC, hbasisN, hbasisC, ?_, ?_, ?_⟩
  · rw [card_involutionCentralizer_eq 2 S e, hHcard]
  · rw [card_orderFourCentralizer_eq 2 hn S e, hHcard]
  · obtain ⟨hv3', -, -⟩ := odd_classes_of_equiv Φ
    obtain ⟨c, hc⟩ := hπC (Φ U₀)
    refine ⟨Subgroup.inclusion hCN c, c.2, ?_, hc⟩
    rw [orderOf_injective _ (Subgroup.inclusion_injective hCN) c]
    exact odd_orderOf_of_odd_orderOf_map πC hR₀odd c (by rw [hc, hv3']; decide)
  · intro g hg
    simp only [bN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hg,
      R.one_mem, ite_true]
    norm_num
  · intro g hg
    have hg1 : ((g : C) : G) ∈ R₀ := by
      rw [hg]
      exact R₀.one_mem
    simp only [bC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hg1,
      ite_true]
    norm_num
  · intro Φ z hzC hzodd hπz
    have hzR := (hlift Φ z hzC hzodd hπz).1
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · have hgR : (g : N) ∉ R := hg ▸ hzR
      simp only [bN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hgR,
        ite_false]
      norm_num
    · have hgR : ((g : C) : G) ∉ R₀ := by
        rw [hg]
        intro hzR₀
        exact hzR ((Subgroup.mem_map_iff_mem N.subtype_injective).mp hzR₀.1)
      simp only [bC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hgR,
        ite_false]
      norm_num

end CFSG.Wreathed.FourPointOrderFour
