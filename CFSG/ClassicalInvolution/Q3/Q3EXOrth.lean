module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Models
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthGeom
public import CFSG.ClassicalInvolution.Uniform.U8Basic
public import CFSG.ClassicalInvolution.Uniform.U5Three2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Central

variable {X Y : Type} [Group X] [Finite X] [Group Y]

theorem twinFamily_of_central3 (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1) {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)}
    (hgen : ∀ R ∈ 𝓕, ModelFacts.Gen3 R) (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖)
    (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L) {a : ℕ} (hT : TwinFamily 𝓕 a) :
    TwinFamily 𝓖 a := by
  obtain ⟨F, hF, hinj, hcomm, htw⟩ := hT
  have heq : ∀ {A B : Subgroup X}, A ∈ 𝓕 → B ∈ 𝓕 → A.map π = B.map π → A = B :=
    fun hA hB h => Uniform.eq_of_map_eq_of_gen3 π hker hk3 (hgen _ hA) (hgen _ hB) h
  have hcm : ∀ {A B : Subgroup X}, A ∈ 𝓕 → (Commutes (A.map π) (B.map π) ↔ Commutes A B) := by
    intro A B hA
    constructor
    · intro h a ha b hb
      have h1 : ∀ a' ∈ A, π a' * π b = π b * π a' := fun a' ha' =>
        h (π a') ⟨a', ha', rfl⟩ (π b) ⟨b, hb, rfl⟩
      exact ModelFacts.commute_of_map_commute_of_gen3 π hker hk3 (hgen A hA) h1 a ha
    · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  refine ⟨fun i => (F i).map π, fun i => hmap _ (hF i), fun i j hij => ?_,
    fun i j hij => ?_, fun i j S' hS' => ?_⟩
  · exact hinj (heq (hF i) (hF j) hij)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm i j hij x hx y hy]
  · obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
    have key : ∀ k, (S.map π = (F k).map π ∨ Commutes (S.map π) ((F k).map π)) ↔
        (S = F k ∨ Commutes S (F k)) := by
      intro k
      rw [hcm hS]
      constructor
      · rintro (h | h)
        · exact Or.inl (heq hS (hF k) h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr h
    rw [key i, key j]
    exact htw i j S hS

end Central

section Ctx

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem twinFamily_fundSet_of_ctx3 [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hconj : ∀ R ∈ 𝓕, ∀ g : spinGroup Q, conjSub g R ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : spinGroup Q, R' = conjSub g R) {a : ℕ} (ha : 1 ≤ a)
    (hT : TwinFamily 𝓕 a) : TwinFamily (fundSet Q) a := by
  have hT' := hT
  obtain ⟨F, hF, -⟩ := hT'
  have hR₀ : F ⟨0, ha⟩ ∈ 𝓕 := hF _
  obtain ⟨fr₀, himg⟩ := c.hframe _ hR₀
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have h1 := ModelFacts.finrank_perp_add_four fr₀
    have h2 := c.hdim
    omega
  have hpos : 0 < Module.finrank 𝔽₃ (ι → 𝔽₃) := by
    have := c.hdim
    omega
  have : Nontrivial (ι → 𝔽₃) := Module.finrank_pos_iff.mp hpos
  have hcorr := spin_fund_correspondence odd_natCard_galoisField_three c.hQ hR₀ hconj
    (fun R hR => hsingle _ hR₀ R hR) fr₀ himg hperp
  refine twinFamily_of_central3 (spinAction Q) (ker_spinAction_le_center Q) ?_ c.hG3 hcorr.1
    hcorr.2 hT
  intro x hx h3
  have h2 : x * x = 1 := c.hker2 x hx
  have h : x ^ 3 = x ^ 2 * x := pow_succ x 2
  rw [h, pow_two, h2, one_mul] at h3
  exact h3

end Ctx

section Odd

theorem modelTwinClass_odd3 {n a : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) (ha : 2 ≤ a)
    (h : ModelTwinClass 3 .POmegaOdd n 1 a) : a = 2 := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hM : modelUniv .POmegaOdd n 3 1 Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaOdd n 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Fact.out).D.rank, k.val + 1 < n →
      IsLongestRoot (modelUniv .POmegaOdd n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaOdd n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaOdd)
      trivial hadm (by decide) (by decide) hR
  have hT : TwinFamily (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D)
      a := h
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaOdd) (by norm_num) Nat.prime_three trivial hadm
  generalize modelUniv .POmegaOdd n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hT hfin
  subst hM
  have : Finite (spinGroup (quadOdd n (GaloisField 3 1))) := hfin
  have hn0 : 0 < n := by omega
  have ctx := spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega))
    hG3 hsl2
  have hG : TwinFamily (fundSet (quadOdd n (GaloisField 3 1))) a :=
    twinFamily_fundSet_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
      (fun R hR R' hR' => hsingle _ hR R' hR') (by omega) hT
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  refine le_antisymm ?_ ha
  by_cases hn : n = 3
  · exact twinFamily_le_two_of_lt_eight hodd (by omega) hG
  · exact twinFamily_le_two_of_nine_le hodd ctx.hQ (by omega) hG

end Odd

section Minus

theorem modelTwinClass_minus3 {n a : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    (ha : 2 ≤ a) (h : ModelTwinClass 3 .POmegaMinus n 1 a) : a = 2 := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hM : modelUniv .POmegaMinus n 3 1 Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus n 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Fact.out).D.rank, k.val + 2 < n →
      IsLongestRoot (modelUniv .POmegaMinus n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaMinus n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR
  have hT : TwinFamily
      (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D) a := h
  have hfin : Finite (modelUniv .POmegaMinus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) Nat.prime_three trivial hadm
  generalize modelUniv .POmegaMinus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hT hfin
  subst hM
  have : Finite (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) := hfin
  have hn0 : 0 < n - 1 := by omega
  have ctx := spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2
  have hG : TwinFamily (fundSet (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) a :=
    twinFamily_fundSet_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
      (fun R hR R' hR' => hsingle _ hR R' hR') (by omega) hT
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  refine le_antisymm ?_ ha
  by_cases hn : n = 4
  · subst hn
    exact twinFamily_le_two_of_noOrth hodd
      (fun F₀ F₁ hF => false_of_orth_quadMinus_four3 h2 (minusCoeffs_irr 3 1)
        (by rw [natCard_galoisField_three]; norm_num) F₀ F₁ hF) hG
  · exact twinFamily_le_two_of_nine_le hodd ctx.hQ (by omega) hG

end Minus

section Plus

theorem modelTwinClass_plus3 {n a : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (h : ModelTwinClass 3 .POmegaPlus n 1 a) : a ≤ 2 ∨ (n = 4 ∧ a ≤ 4) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hM : modelUniv .POmegaPlus n 3 1 Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus n 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus n 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus n 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus n 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus n 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have hT : TwinFamily
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D) a := h
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  generalize modelUniv .POmegaPlus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hT hfin
  subst hM
  have : Finite (spinGroup (quadPlus n (GaloisField 3 1))) := hfin
  have ctx := spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2
  by_cases ha : a = 0
  · exact Or.inl (by omega)
  have hG : TwinFamily (fundSet (quadPlus n (GaloisField 3 1))) a :=
    twinFamily_fundSet_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
      (fun R hR R' hR' => hsingle _ hR R' hR') (by omega) hT
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  by_cases hn : n = 4
  · right
    exact ⟨hn, twinFamily_le_four_of_eight hodd (by omega) hG⟩
  · left
    exact twinFamily_le_two_of_nine_le hodd ctx.hQ (by omega) hG

end Plus

end CFSG.ClassicalInvolution.Q3.Q3W.EX
