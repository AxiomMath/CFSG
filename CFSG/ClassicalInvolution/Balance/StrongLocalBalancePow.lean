module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceFour

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralActionPow (k : ℕ) (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, x ^ k = 1 ∧ ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralActionPow.toralAction {k : ℕ} {ψ : K →* X} {F : Subgroup X}
    (h : ToralActionPow k ψ F) : ToralAction ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, -, hxa⟩ := hact f hf
  exact ⟨x, hxP, hxa⟩

theorem ToralActionPow.mono {k k' : ℕ} (hk : k ∣ k') {ψ : K →* X} {F : Subgroup X}
    (h : ToralActionPow k ψ F) : ToralActionPow k' ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f hf
  obtain ⟨c, rfl⟩ := hk
  exact ⟨x, hxP, by rw [pow_mul, hxk, one_pow], hxa⟩

theorem toralActionPow_four_iff {ψ : K →* X} {F : Subgroup X} :
    ToralActionPow 4 ψ F ↔ ToralActionFour ψ F := Iff.rfl

end Statement

@[expose] def StrongLocalTwoBalanceToralPowOn (k : ℕ) (t : StatedLieTag)
    (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionPow k ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralPowOn.mono {k : ℕ} {t : StatedLieTag}
    {Q Q' : ℕ → ℕ → ℕ → Prop} (h : StrongLocalTwoBalanceToralPowOn k t Q)
    (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralPowOn k t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)

theorem StrongLocalTwoBalanceToralPowOn.mono_order {k k' : ℕ} (hk : k ∣ k') {t : StatedLieTag}
    {Q : ℕ → ℕ → ℕ → Prop} (h : StrongLocalTwoBalanceToralPowOn k' t Q) :
    StrongLocalTwoBalanceToralPowOn k t Q :=
  fun n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral =>
    h n p e hp hq hfund hadm hp2 h5 X ψ hker hnorm F hcard hF2 hfaith (htoral.mono hk)

theorem strongLocalTwoBalanceToralPowOn_four_iff {t : StatedLieTag} {Q : ℕ → ℕ → ℕ → Prop} :
    StrongLocalTwoBalanceToralPowOn 4 t Q ↔ StrongLocalTwoBalanceToralFourOn t Q := Iff.rfl

theorem commute_of_strongLocalTwoBalanceToralPow {k : ℕ} {t : StatedLieTag}
    {Q : ℕ → ℕ → ℕ → Prop} (hSB : StrongLocalTwoBalanceToralPowOn k t Q) {n p e : ℕ}
    (hp : p.Prime) (hq : Q n p e) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {X : Type} [Group X] [Finite X]
    (ψ : (modelUniv t n p e hp).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X)) (htoral : ToralActionPow k ψ F) :
    ∀ d ∈ deltaCore F, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ x ∈ ψ.range, d * x = x * d := by
  set N : Subgroup X := Subgroup.normalizer (ψ.range : Set X) with hN
  have hrN : ψ.range ≤ N := Subgroup.le_normalizer
  set ψ' : (modelUniv t n p e hp).K →* ↥N := ψ.codRestrict N fun k => hrN ⟨k, rfl⟩ with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (modelUniv t n p e hp).K := fun y hy =>
    hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hy)))
  have hrange : ψ'.range = ψ.range.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hnorm' : ψ'.range.Normal := by
    rw [hrange, Subgroup.normal_subgroupOf_iff_le_normalizer hrN]
  set F' : Subgroup ↥N := F.subgroupOf N with hF'
  have hF'4 : Nat.card F' = 4 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f := by
    intro f hf hf1 hc
    refine hfaith f.1 hf (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    have hx' : (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := by
      rw [hrange]
      exact hx
    exact congrArg Subtype.val (hc _ hx')
  have htoral' : ToralActionPow k ψ' F' := by
    obtain ⟨P, hP, hact⟩ := htoral
    refine ⟨P, hP, fun f hf => ?_⟩
    obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
    exact ⟨x, hxP, hxk, fun y => Subtype.ext (hxa y)⟩
  have hSC := hSB n p e hp hq hfund hadm hp2 h5 ↥N ψ' hker' hnorm' F' hF'4 hF'2 hfaith' htoral'
  have hxmem : ∀ x (hx : x ∈ ψ.range), (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := fun x hx => by
    rw [hrange]
    exact hx
  intro d hd hdN x hx
  have hd' : (⟨d, hdN⟩ : ↥N) ∈ deltaCore F' := by
    rw [mem_deltaCore_iff]
    intro f' hf' hf'1
    have hf1 : (f' : X) ≠ 1 := fun h => hf'1 (Subtype.ext h)
    exact subgroupOf_involutionOddCore_le f' (Subgroup.mem_subgroupOf.mpr
      (mem_deltaCore_iff.mp hd (f' : X) hf' hf1))
  exact congrArg Subtype.val (hSC.1 _ hd' _ (hxmem x hx))

namespace Linear

open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem strongConclusion_gf_toral_two {p e n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) (ψ : SL(n, GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (htoral : ToralActionPow 2 ψ F) : StrongConclusion ψ.range F := by
  obtain ⟨P, hP, hact⟩ := htoral
  refine strongConclusion_gf_split hn hp2 h5 ψ hker hnorm hcard hF2 P hP fun f hf => ?_
  obtain ⟨x, hxP, hx2, hxa⟩ := hact f hf
  refine ⟨x, hxP, hxa, 1, one_ne_zero, ?_⟩
  have hxx : x * x = 1 := by rwa [pow_two] at hx2
  have := congrArg (fun z : SL(n, GaloisField p e) =>
    (z : Matrix (Fin n) (Fin n) (GaloisField p e))) hxx
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
  rw [this]
  simp

theorem strongLocalTwoBalanceToralPowOn_PSL_two :
    StrongLocalTwoBalanceToralPowOn 2 .PSL (fun _ _ _ => True) := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h3 : 3 ≤ m + 1
  · exact strongConclusion_gf_toral_two h3 hp2 h5 ψ hker hnorm hcard hF2 htoral
  · exfalso
    obtain rfl : m = 1 := by omega
    have he : e ≠ 0 := by
      rintro rfl
      simp at h5
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by
      rw [GaloisField.card p e he]
      omega
    exact false_of_toral_two (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) h4
      ψ hker hcard hF2 hfaith htoral.toralAction

end Linear

end CFSG.ClassicalInvolution.Balance.StrongBalance
