module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe u

variable {G : Type u} [Group G]

@[expose] def normalizerConj (L : Subgroup G) {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    MulAut L where
  toFun l := ⟨v * l * v⁻¹, (Subgroup.mem_normalizer_iff.mp hv l).mp l.2⟩
  invFun l := ⟨v⁻¹ * l * v, by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv) l).mp l.2⟩
  left_inv l := by
    ext
    simp [mul_assoc]
  right_inv l := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

@[simp] theorem normalizerConj_apply (L : Subgroup G) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    (normalizerConj L hv l : G) = v * l * v⁻¹ := rfl

@[expose] def quotientConj (L : Subgroup G) {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (L ⧸ CFSG.oddCore L) :=
  QuotientGroup.congr (CFSG.oddCore L) (CFSG.oddCore L) (normalizerConj L hv)
    (CFSG.ComponentClassification.OddCore.char_invariant (normalizerConj L hv))

theorem quotientConj_mk (L : Subgroup G) {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (l : L) : quotientConj L hv (QuotientGroup.mk l) = QuotientGroup.mk (normalizerConj L hv l) :=
  QuotientGroup.congr_mk _ _ _ _ l

theorem exists_quotient_involution (L : Subgroup G) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) (hv2 : v * v = 1) {X : Type*} [Group X]
    (E : L ⧸ CFSG.oddCore L ≃* X) :
    ∃ θ : MulAut X, (∀ l : L, θ (E (QuotientGroup.mk l)) =
        E (QuotientGroup.mk (normalizerConj L hv l))) ∧ ∀ x, θ (θ x) = x := by
  refine ⟨(E.symm.trans (quotientConj L hv)).trans E, fun l => ?_, fun x => ?_⟩
  · simp [quotientConj_mk]
  · obtain ⟨q, rfl⟩ := E.surjective x
    induction q using QuotientGroup.induction_on with
    | H l =>
      have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
      have hl : normalizerConj L hv (normalizerConj L hv l) = l := by
        ext
        simp [mul_assoc, hvv, ← mul_assoc v v, hv2]
      simp [quotientConj_mk, hl]

theorem commute_of_quotient_fixed [Finite G] {L U : Subgroup G} (helem : IsElementaryAbelian 2 U)
    {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G)) (l : L) (hl : (l : G) ∈ U)
    (hvl : v * l * v⁻¹ ∈ U)
    (hq : (QuotientGroup.mk (normalizerConj L hv l) : L ⧸ CFSG.oddCore L) = QuotientGroup.mk l) :
    Commute v l := by
  have hmem : (normalizerConj L hv l)⁻¹ * l ∈ CFSG.oddCore L := QuotientGroup.eq.mp hq
  set w : L := (normalizerConj L hv l)⁻¹ * l
  have hwU : (w : G) ∈ U := by
    simpa [w] using U.mul_mem (U.inv_mem hvl) hl
  have hw2 : w ^ 2 = 1 := Subtype.ext (by
    simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (A := U) (w : G) hwU)
  have hodd : Odd (orderOf w) := by
    have h := CFSG.ComponentClassification.OddCore.odd_card L
    have hdvd : orderOf (⟨w, hmem⟩ : CFSG.oddCore L) ∣ Nat.card (CFSG.oddCore L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat h hdvd
  have hw1 : w = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hw2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have heq : normalizerConj L hv l = l := inv_mul_eq_one.mp hw1
  have h := congrArg Subtype.val heq
  simp only [normalizerConj_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h)

theorem exists_point_involution {H : Subgroup G} {z u v : G}
    (hvu : v ∈ Subgroup.centralizer ({u} : Set G))
    (hv : v ∈ Subgroup.normalizer ((localInvolutionPointHull z u : Subgroup G) : Set G))
    (hv2 : v * v = 1) {X P : Type*} [Group X]
    (E : localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u) ≃* X)
    (act : X → P → P) (ψ : elementFixedSet H u ≃ P)
    (hψ : letI := hullFixedSetAction H z u
      ∀ (l : localInvolutionPointHull z u) (δ : elementFixedSet H u),
        ψ (l • δ) = act (E (QuotientGroup.mk l)) (ψ δ))
    (θ : MulAut X)
    (hθ : ∀ l, θ (E (QuotientGroup.mk l)) = E (QuotientGroup.mk (normalizerConj _ hv l))) :
    ∃ τ : P → P, (∀ x p, τ (act x p) = act (θ x) (τ p)) ∧ (∀ p, τ (τ p) = p) ∧
      ∀ δ : elementFixedSet H u, pointRightCosetMul H δ v = δ → τ (ψ δ) = ψ δ := by
  let := hullFixedSetAction H z u
  have hvinv : v⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := Subgroup.inv_mem _ hvu
  have hvv : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hv2, inv_one]
  let vΔ : elementFixedSet H u → elementFixedSet H u := fun δ =>
    ⟨pointRightCosetMul H δ v⁻¹, original_centralizer_preserves_full_fixedSet H u _ hvinv _ δ.2⟩
  have hcomm : ∀ (l : localInvolutionPointHull z u) (δ : elementFixedSet H u),
      vΔ (l • δ) = normalizerConj _ hv l • vΔ δ := by
    intro l δ
    apply Subtype.ext
    change pointRightCosetMul H (pointRightCosetMul H δ (l : G)⁻¹) v⁻¹ =
      pointRightCosetMul H (pointRightCosetMul H δ v⁻¹) (v * l * v⁻¹)⁻¹
    rw [pointRightCosetMul_mul, pointRightCosetMul_mul]
    congr 1
    group
  have hinvol : ∀ δ, vΔ (vΔ δ) = δ := by
    intro δ
    apply Subtype.ext
    change pointRightCosetMul H (pointRightCosetMul H δ v⁻¹) v⁻¹ = δ
    rw [pointRightCosetMul_mul, hvv, pointRightCosetMul_one]
  refine ⟨fun p => ψ (vΔ (ψ.symm p)), fun x p => ?_, fun p => ?_, fun δ hδ => ?_⟩
  · obtain ⟨q, rfl⟩ := E.surjective x
    induction q using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨δ, rfl⟩ := ψ.surjective p
      simp only
      rw [← hψ, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hcomm, hψ, hθ]
  · simp only [Equiv.symm_apply_apply, hinvol, Equiv.apply_symm_apply]
  · simp only [Equiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change pointRightCosetMul H δ v⁻¹ = δ
    calc pointRightCosetMul H δ v⁻¹ = pointRightCosetMul H (pointRightCosetMul H δ v) v⁻¹ := by
          rw [hδ]
      _ = δ := by rw [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]

theorem exists_ne_ne_of_two_lt_card {P : Type*} (hcard : 2 < Nat.card P) (a b : P) :
    ∃ c : P, c ≠ a ∧ c ≠ b := by
  by_contra hno
  push Not at hno
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hle : Nat.card P ≤ Nat.card ({a, b} : Set P) :=
    Nat.card_le_card_of_injective (fun c => ⟨c, by
      by_cases hc : c = a
      · exact Or.inl hc
      · exact Or.inr (hno c hc)⟩) (fun c d h => congrArg Subtype.val h)
  have h2 : Nat.card ({a, b} : Set P) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
  omega

theorem eq_self_of_commute_two_pretransitive {X P : Type*} [Group X] [MulAction X P]
    [MulAction.IsMultiplyPretransitive X P 2] (hcard : 2 < Nat.card P) (π : P → P)
    (hπ : ∀ (x : X) (p : P), π (x • p) = x • π p) (p : P) : π p = p := by
  by_contra hne
  obtain ⟨c, hcp, hcπ⟩ := exists_ne_ne_of_two_lt_card hcard p (π p)
  obtain ⟨x, hxp, hxπ⟩ := (MulAction.is_two_pretransitive_iff (G := X)).mp inferInstance
    (Ne.symm hne) (Ne.symm hcp)
  apply hcπ
  rw [← hxπ, ← hπ, hxp]

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
