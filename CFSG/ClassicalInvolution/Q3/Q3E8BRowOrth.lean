module

public import CFSG.ClassicalInvolution.Q3.Q3EXCentral
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowOrth
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts.E8D8 (framePlus frameOdd frameMinus framePlus_eq
  frameOdd_eq frameMinus_eq framePlus_coprime frameOdd_coprime frameMinus_coprime framePlus_pos
  card_frame_plus_eq card_frame_plus_six card_fundSet_mul)
open CFSG.ClassicalInvolution.ModelFacts.TG3 (spinCtx3_odd spinCtx3_plus spinCtx3_minus
  natCard_galoisField_three odd_natCard_galoisField_three two_ne_zero_three)
open CFSG.ClassicalInvolution.RouteD (conjSub_mem_fundamentalSubgroups modelUniv_POmegaPlus_eq
  nonempty_fund_odd nonempty_fund_plus nonempty_fund_minus)
open CFSG.ClassicalInvolution.Q3.Q3W.EX (Central3 central3_of_ctx3)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Arith

variable {p f q : ℕ}

theorem framePlus_eq_framePlus_four3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq3 : 3 ≤ q) {j : ℕ} (h : framePlus q j = framePlus q 4) : j = 4 := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framePlus_eq hqdef, framePlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framePlus_coprime hp hp2 hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem frameOdd_ne_framePlus_four3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq3 : 3 ≤ q) {j : ℕ} (h : frameOdd q j = framePlus q 4) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [frameOdd_eq hqdef, framePlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (frameOdd_coprime hp hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem frameMinus_ne_framePlus_four3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq3 : 3 ≤ q) {j : ℕ} (h : frameMinus q j = framePlus q 4) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have h' := h
  rw [frameMinus_eq hqdef, framePlus_eq hqdef] at h'
  have hx := pow_eq_of_mul_eq hp (frameMinus_coprime hp hp2 hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h'
  have hj : j = 3 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
    omega
  subst hj
  have e1 : frameMinus q 3 =
      (q ^ 6 + 1) * (q ^ 5 - 1) * q ^ 10 * ((q ^ 5 + 1) * (q ^ 4 - 1) * q ^ 8) := rfl
  have e2 : framePlus q 4 =
      (q ^ 6 - 1) * (q ^ 5 + 1) * q ^ 10 * ((q ^ 5 - 1) * (q ^ 4 + 1) * q ^ 8) := rfl
  rw [e1, e2] at h
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have hq5' : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq1
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  zify [hq4, hq5', hq6] at h
  have hqz : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have h0 : -2 * (q : ℤ) ^ 22 * ((q : ℤ) ^ 10 - 1) * ((q : ℤ) ^ 2 - 1) = 0 := by
    linear_combination h
  have hq2z : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
  have hq10z : (0 : ℤ) < (q : ℤ) ^ 10 - 1 := by
    have : (1 : ℤ) < (q : ℤ) ^ 10 := one_lt_pow₀ (by omega) (by norm_num)
    linarith
  have hpos : (0 : ℤ) < (q : ℤ) ^ 22 * ((q : ℤ) ^ 10 - 1) * ((q : ℤ) ^ 2 - 1) :=
    mul_pos (mul_pos (pow_pos (by omega) 22) hq10z) hq2z
  linarith

end Arith

set_option linter.unusedSectionVars false


section Abstract

variable {X : Type} [Group X] [Finite X] {K V W : Type} [Field K] [Finite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
  {Q₂ : QuadraticForm K W}

theorem card_commuting_map3 {Y : Type} [Group Y] {π : X →* Y} {𝓕 : Set (Subgroup X)}
    {𝓖 : Set (Subgroup Y)} (h : Central3 π 𝓕 𝓖) (R₀ : Subgroup X) :
    Nat.card {S : Subgroup X // S ∈ 𝓕 ∧ Commutes S R₀} =
      Nat.card {S' : Subgroup Y // S' ∈ 𝓖 ∧ Commutes S' (R₀.map π)} := by
  refine Nat.card_eq_of_bijective
    (fun S => ⟨S.1.map π, h.map_mem _ S.2.1, (h.commutes_iff S.2.1).mpr S.2.2⟩) ⟨?_, ?_⟩
  · intro S₁ S₂ hS
    exact Subtype.ext (h.map_inj S₁.2.1 S₂.2.1 (congrArg Subtype.val hS))
  · rintro ⟨S', hS', hc⟩
    obtain ⟨S, hS, rfl⟩ := h.surj S' hS'
    exact ⟨⟨S, hS, (h.commutes_iff hS).mp hc⟩, rfl⟩

theorem orth_layer_count3 (hodd : Odd (Nat.card K)) {π : X →* (V ≃ₗ[K] V)}
    {𝓕 : Set (Subgroup X)} (h : Central3 π 𝓕 (fundSet Q)) {R₀ : Subgroup X} (hR₀ : R₀ ∈ 𝓕)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) {N : ℕ}
    (hN : Nat.card {S : Subgroup X // S ∈ 𝓕 ∧ Commutes S R₀} = N) :
    2 * Nat.card (OFrame Q₂) +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  have : Finite V := Module.finite_of_finite K
  obtain ⟨i, F₀, hF₀, -⟩ := h.map_mem R₀ hR₀
  have hcard := card_commuting_map3 h R₀
  rw [hN, hF₀] at hcard
  obtain ⟨F₁, ι, hι, hinj, hrange⟩ := exists_frame_perp_emb e
  have h1 := two_mul_card_frames_perp hodd F₀
  rw [card_frames_perp_conj hodd F₀ F₁, card_frames_perp F₁ ι hι hinj hrange, ← hcard] at h1
  exact h1

theorem card_frame_eq_of_layer3 (hodd : Odd (Nat.card K)) {π : X →* (V ≃ₗ[K] V)}
    {𝓕 : Set (Subgroup X)} (h : Central3 π 𝓕 (fundSet Q)) {R₀ : Subgroup X} (hR₀ : R₀ ∈ 𝓕)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) {m F₁₂ : ℕ}
    (hN : Nat.card {S : Subgroup X // S ∈ 𝓕 ∧ Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) = 2 * F₁₂) :
    Nat.card (OFrame Q₂) = F₁₂ := by
  have h1 := orth_layer_count3 hodd h hR₀ e hN
  have h' : (m + 1) * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by ring
  omega

theorem card_fund_mul_of_central3 (hodd : Odd (Nat.card K)) {π : X →* (V ≃ₗ[K] V)}
    {𝓕 : Set (Subgroup X)} (h : Central3 π 𝓕 (fundSet Q)) :
    Nat.card 𝓕 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      2 * Nat.card (OFrame Q) := by
  have hbij : Nat.card 𝓕 = Nat.card (fundSet Q) := by
    refine Nat.card_eq_of_bijective (fun R => ⟨R.1.map π, h.map_mem _ R.2⟩) ⟨?_, ?_⟩
    · intro R₁ R₂ hR
      exact Subtype.ext (h.map_inj R₁.2 R₂.2 (congrArg Subtype.val hR))
    · rintro ⟨L, hL⟩
      obtain ⟨R, hR, rfl⟩ := h.surj L hL
      exact ⟨⟨R, hR⟩, rfl⟩
  rw [hbij]
  exact card_fundSet_mul hodd

end Abstract

namespace EB

section Models

theorem central3_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    Central3 (spinAction (quadOdd n 𝔽₃)) (fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃))
      (fundSet (quadOdd n 𝔽₃)) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaOdd n 3 1 Fact.out =
      ⟨spinGroup (quadOdd n 𝔽₃), oddDatum n 𝔽₃⟩ := rfl
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
      Nonempty (R ≃* SL(2, 𝔽₃)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaOdd)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaOdd) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_odd (p := 3) (f := 1) hn3
  generalize modelUniv .POmegaOdd n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne
  subst hM
  have : Finite (spinGroup (quadOdd n 𝔽₃)) := hfin
  have hn0 : 0 < n := by omega
  have ctx := spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega))
    hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

theorem central3_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    Central3 (spinAction (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (fundamentalSubgroups .POmegaMinus (minusDatum n (minusCoeffs_irr 3 1)))
      (fundSet (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaMinus n 3 1 Fact.out =
      ⟨spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
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
      Nonempty (R ≃* SL(2, 𝔽₃)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaMinus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_minus (p := 3) (f := 1) hn4
  generalize modelUniv .POmegaMinus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne
  subst hM
  have : Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := hfin
  have hn0 : 0 < n - 1 := by omega
  have ctx := spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

theorem central3_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) (hn3 : 3 ≤ n) :
    Central3 (spinAction (quadPlus n 𝔽₃))
      (fundamentalSubgroups .POmegaPlus (plusDatum n 𝔽₃ hn3)) (fundSet (quadPlus n 𝔽₃)) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaPlus n 3 1 Fact.out =
      ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ :=
    modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
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
      Nonempty (R ≃* SL(2, 𝔽₃)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_plus (p := 3) (f := 1) hn4
  generalize modelUniv .POmegaPlus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne
  subst hM
  have : Finite (spinGroup (quadPlus n 𝔽₃)) := hfin
  have ctx := spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

theorem finite_spin_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    Finite (spinGroup (quadOdd n 𝔽₃)) :=
  ModelFacts.finite_modelUniv (t := .POmegaOdd) (by norm_num) Nat.prime_three trivial hadm

theorem finite_spin_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
  ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) Nat.prime_three trivial hadm

theorem finite_spin_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) (hn3 : 3 ≤ n) :
    Finite (spinGroup (quadPlus n 𝔽₃)) := by
  have hfin := ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three
    trivial hadm
  rw [modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3] at hfin
  exact hfin

end Models

end EB

theorem card_fund12_mul3 :
    Nat.card (RouteD.TypeE8.Fund12 3 1) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField 3 1))) := by
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hn3 : 3 ≤ 6 := by norm_num
  have : Finite (spinGroup (quadPlus 6 𝔽₃)) := EB.finite_spin_plus hadm hn3
  have hC := EB.central3_plus hadm hn3
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 6 𝔽₃), plusDatum 6 𝔽₃ hn3⟩ →
      Nat.card {R : Subgroup M.K // R ∈ fundamentalSubgroups .POmegaPlus M.D} *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := 𝔽₃))) =
        2 * Nat.card (OFrame (quadPlus 6 𝔽₃)) := by
    intro M hM
    subst hM
    exact card_fund_mul_of_central3 odd_natCard_galoisField_three hC
  exact key _ (modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3)

theorem d8_false_odd3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField 3 1)))) : False := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_natCard_galoisField_three
  have h2 := two_ne_zero_three
  have hcard : Nat.card 𝔽₃ = 3 ^ 1 := by rw [natCard_galoisField_three]; norm_num
  have hq3 : 3 ≤ Nat.card 𝔽₃ := by rw [natCard_galoisField_three]
  have : Finite (spinGroup (quadOdd n 𝔽₃)) := EB.finite_spin_odd hadm
  have hC := EB.central3_odd hadm
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := card_frame_eq_of_layer3 (Q := quadOdd (j + 3) 𝔽₃) hodd hC hR₀
    ((oddIsometry 𝔽₃ (j + 2)).trans (hypSumCongr (oddIsometry 𝔽₃ (j + 1)))) hN hm
  rw [card_frame_plus_six] at key
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadOdd (0 + 1) 𝔽₃)) = 0 := card_frame_odd_one 𝔽₃ h2
    rw [e0] at key
    exact (framePlus_pos (by omega) 4).ne key
  · have e1 : Nat.card (OFrame (quadOdd (j + 1 + 1) 𝔽₃)) = frameOdd (Nat.card 𝔽₃) j :=
      card_frame_odd 𝔽₃ h2 j
    rw [e1] at key
    exact frameOdd_ne_framePlus_four3 Nat.prime_three (by norm_num) le_rfl hcard hq3 key

theorem d8_eq_plus3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField 3 1)))) : n = 8 := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hodd := odd_natCard_galoisField_three
  have hcard : Nat.card 𝔽₃ = 3 ^ 1 := by rw [natCard_galoisField_three]; norm_num
  have hq3 : 3 ≤ Nat.card 𝔽₃ := by rw [natCard_galoisField_three]
  have : Finite (spinGroup (quadPlus n 𝔽₃)) := EB.finite_spin_plus hadm hn3
  have hC := EB.central3_plus hadm hn3
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ →
      ∀ R₀ : Subgroup M.K, R₀ ∈ fundamentalSubgroups .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = m + 1 → n = 8 := by
    intro M hM R₀ hR₀ hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := card_frame_eq_of_layer3 (Q := quadPlus (j + 4) 𝔽₃) hodd hC hR₀
      ((plusIsometry 𝔽₃ (j + 3)).trans (hypSumCongr (plusIsometry 𝔽₃ (j + 2)))) hN hm
    rw [card_frame_plus_eq, card_frame_plus_six] at hk
    have := framePlus_eq_framePlus_four3 Nat.prime_three (by norm_num) le_rfl hcard hq3 hk
    omega
  exact key _ (modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) R₀ hR₀ hN

theorem d8_false_minus3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField 3 1)))) : False := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_natCard_galoisField_three
  have h2 := two_ne_zero_three
  have hirr := minusCoeffs_irr 3 1
  have hcard : Nat.card 𝔽₃ = 3 ^ 1 := by rw [natCard_galoisField_three]; norm_num
  have hq3 : 3 ≤ Nat.card 𝔽₃ := by rw [natCard_galoisField_three]
  have : Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    EB.finite_spin_minus hadm
  have hC := EB.central3_minus hadm
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := card_frame_eq_of_layer3
    (Q := quadMinus (j + 4) 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) hodd hC hR₀
    ((minusIsometry 𝔽₃ (j + 2) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).trans
      (hypSumCongr (minusIsometry 𝔽₃ (j + 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) hN hm
  rw [card_frame_plus_six] at key
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadMinus (0 + 2) 𝔽₃ (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = 0 := card_frame_minus_two 𝔽₃ hirr
    rw [e0] at key
    exact (framePlus_pos (by omega) 4).ne key
  · have e1 : Nat.card (OFrame (quadMinus (j + 1 + 2) 𝔽₃ (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = frameMinus (Nat.card 𝔽₃) j := card_frame_minus 𝔽₃ h2 hirr j
    rw [e1] at key
    exact frameMinus_ne_framePlus_four3 Nat.prime_three (by norm_num) le_rfl hcard hq3 key

end CFSG.ClassicalInvolution.Q3.Q3W
