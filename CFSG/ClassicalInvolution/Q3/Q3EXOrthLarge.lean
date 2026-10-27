module

public import CFSG.ClassicalInvolution.Q3.Q3EXCentral
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam hypComb hypComb_injective map_hypComb)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Count

variable {F : Type} [Field F] [Finite F]

theorem false_of_isHypFam_quadMinus3 (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F) {m : ℕ}
    (v : Fin (m + 1) → Bool → (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F))
    (hv : IsHypFam (quadMinus (m + 1) F b c) v) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  let e' : Fin (m + 1) × Bool ≃ Fin (m + 1) ⊕ Fin (m + 1) :=
    (Equiv.prodComm (Fin (m + 1)) Bool).trans (Equiv.boolProdEquivSum (Fin (m + 1)))
  let ψ₀ : (Fin (m + 1) ⊕ Fin (m + 1) → F) →ₗ[F]
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) :=
    (hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus (m + 1) F b c (ψ₀ w) = quadPlus (m + 1) F w := by
    intro w
    show quadMinus (m + 1) F b c (hypComb v (w ∘ e')) = _
    rw [map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (hypComb_injective hv).comp (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin (m + 1) ⊕ Fin (m + 1) → F) =
      Module.finrank F (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
    omega
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin (m + 1) ⊕ Fin (m + 1) → F // quadPlus (m + 1) F w = 0} =
      Nat.card {x : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) //
        quadMinus (m + 1) F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin (m + 1) ⊕ Fin (m + 1) → F // quadPlus (m + 1) F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus m
  have e2 : (Nat.card {x : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) //
      quadMinus (m + 1) F b c x = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ (m + 1) + 1) * ((Nat.card F : ℤ) ^ m - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr m
  rw [hcard] at e1
  have hq : (2 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1) -
      ((Nat.card F : ℤ) ^ (m + 1) + 1) * ((Nat.card F : ℤ) ^ m - 1) =
      2 * ((Nat.card F : ℤ) ^ m * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ m * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) m) (by linarith)
  linarith

theorem false_of_three_orth_quadMinus_six3 (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F)
    (F₀ F₁ F₂ : OFrame (quadMinus 6 F b c)) (h01 : F₁.span ≤ F₀.perp) (h02 : F₂.span ≤ F₀.perp)
    (h12 : F₂.span ≤ F₁.perp) : False := by
  obtain ⟨o01, o02, o03, o04⟩ := orth_pairs_of_span_le_perp h01
  obtain ⟨p01, p02, p03, p04⟩ := orth_pairs_of_span_le_perp h02
  obtain ⟨q01, q02, q03, q04⟩ := orth_pairs_of_span_le_perp h12
  let P : Fin 6 → HypPair (quadMinus 6 F b c) := ![F₀.P, F₀.P', F₁.P, F₁.P', F₂.P, F₂.P']
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [P] <;>
      first
      | exact absurd rfl hij
      | exact F₀.orth | exact F₀.orth.symm | exact F₁.orth | exact F₁.orth.symm
      | exact F₂.orth | exact F₂.orth.symm
      | exact o01 | exact o01.symm | exact o02 | exact o02.symm
      | exact o03 | exact o03.symm | exact o04 | exact o04.symm
      | exact p01 | exact p01.symm | exact p02 | exact p02.symm
      | exact p03 | exact p03.symm | exact p04 | exact p04.symm
      | exact q01 | exact q01.symm | exact q02 | exact q02.symm
      | exact q03 | exact q03.symm | exact q04 | exact q04.symm
  exact false_of_isHypFam_quadMinus3 (m := 5) h2 hirr h4 _ (isHypFam_of_pairs P hP)

theorem minus_twinWithinCentralizer_six3 (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin (quadMinus 6 F b c)).Nondegenerate) :
    TwinWithinCentralizer (fundSet (quadMinus 6 F b c)) := by
  have hdim : Module.finrank F (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → F) = 12 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  exact fundSet_twinWithinCentralizer_of hodd (fundSet_hubUnique hodd hQ (Or.inl (by omega)))
    fun F₀ F₁ F₂ h01 h02 h12 =>
      (false_of_three_orth_quadMinus_six3 h2 hirr h4 F₀ F₁ F₂ h01 h02 h12).elim

end Count

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups


section Facts

theorem yData3_odd {m : ℕ} (hm : 3 ≤ m) (hadm : StatedLieAdmissible .POmegaOdd m 3 1) :
    YData3 .POmegaOdd m := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .POmegaOdd m 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨W₁, hW₁⟩ := standardPair_oddDatum_edge (F := GaloisField 3 1) hm (i := 0) (by omega)
  have hl := ModelFacts.isLongestRoot_single .POmegaOdd m 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .POmegaOdd)
    (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D (k := ⟨0, by show 0 < m; omega⟩)
    (hl ⟨0, by show 0 < m; omega⟩ (by show 0 + 1 < m; omega))
  have hR₁ := rankOne_mem_fundamental (t := .POmegaOdd)
    (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D (k := ⟨1, by show 1 < m; omega⟩)
    (hl ⟨1, by show 1 < m; omega⟩ (by show 1 + 1 < m; omega))
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .POmegaOdd m Nat.prime_three trivial hadm).2⟩

theorem yData3_plus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaPlus m 3 1) :
    YData3 .POmegaPlus m := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hm3 : 3 ≤ m := by omega
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus m 3 1 hp trivial hadm (by decide) (by decide)
  have e := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  have hsc' : FundamentalSingleClass .POmegaPlus (plusDatum m (GaloisField 3 1) hm3) := by
    revert hsc
    rw [e]
    exact id
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField 3 1) hm3 hm
  have hR₀ := rankOne_mem_fundamentalSubgroups_plusDatum (K := GaloisField 3 1) hm3
    (⟨0, by show 0 < m; omega⟩ : Fin m)
  have hR₁ := rankOne_mem_fundamentalSubgroups_plusDatum (K := GaloisField 3 1) hm3
    (⟨1, by show 1 < m; omega⟩ : Fin m)
  refine ⟨hsc, perfectK_of_admissible hp trivial hadm, ?_, ?_, ?_,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .POmegaPlus m Nat.prime_three trivial hadm).2⟩
  · rw [e]
    exact pow3_of_mem_fundamental hsc' hR₀ (pow3_of_stdPair card_gf3 hW₁).1
  · rw [e]
    exact central_of_stdPair (p := 3) (f := 1)
      (Y := ⟨spinGroup (quadPlus m (GaloisField 3 1)), plusDatum m (GaloisField 3 1) hm3⟩)
      hsc' hR₀ hW₁
  · rw [e]
    exact std_of_stdPair (p := 3) (f := 1)
      (Y := ⟨spinGroup (quadPlus m (GaloisField 3 1)), plusDatum m (GaloisField 3 1) hm3⟩)
      hsc' hR₀ hR₁ hW₁

theorem yData3_minus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaMinus m 3 1) :
    YData3 .POmegaMinus m := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus m 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus m 3 1 hp trivial hadm (by decide) (by decide)
  have hirr := minusCoeffs_irr 3 1
  have hk0 : (⟨0, by omega⟩ : Fin (m - 1)).val + 1 < m - 1 := by simp only; omega
  have hk1 : (⟨1, by omega⟩ : Fin (m - 1)).val + 1 < m - 1 := by simp only; omega
  have hR₀ := rankOne_mem_fund_minus hirr hk0
  have hR₁ := rankOne_mem_fund_minus hirr hk1
  obtain ⟨W₁, hW₁⟩ := CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_minusDatum hirr
    (ModelFacts.two_ne_zero_galoisField 1 (by norm_num)) hm
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) rfl (by simp only; omega)
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    not_three_dvd_orderOf_of_isPGroup_two
      (modelFiniteCenterTwoGroup3 .POmegaMinus m Nat.prime_three trivial hadm).2⟩

end Facts

section Glue

open CFSG.ClassicalInvolution.ModelFacts.TG3 in
theorem oddGlueFacts3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) (hn : 4 ≤ n) :
    GlueFactsOn (modelFund 3 1 .POmegaOdd n) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_three
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
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaOdd) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_odd (p := 3) (f := 1) hn3
  show GlueFactsOn (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D)
  generalize modelUniv .POmegaOdd n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne ⊢
  subst hM
  have : Finite (spinGroup (quadOdd n (GaloisField 3 1))) := hfin
  have hn0 : 0 < n := by omega
  have ctx := spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega))
    hG3 hsl2
  have hC := EX.central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hker : ∃ ε ∈ (spinAction (quadOdd n (GaloisField 3 1))).ker,
      ∀ k ∈ (spinAction (quadOdd n (GaloisField 3 1))).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadOdd (n := n) (K := GaloisField 3 1) h2
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  exact ⟨hne, EX.FundTwinsExist.of_central3 hC (fun L hL => exists_isFundTwin_fundSet hodd hL),
    EX.FundHubUnique.of_central3 hC (fundSet_hubUnique hodd ctx.hQ (Or.inl (by omega))),
    EX.TwinWithinCentralizer.of_central3 hC (fundSet_twinWithinCentralizer hodd ctx.hQ (by omega)),
    EX.FundHasOrthogonal.of_central3 hC (fundSet_hasOrthogonal hodd ctx.hQ (by omega)),
    EX.TwinInvolutionKernel.of_central3 hodd ctx.hQ (by omega) hC hker⟩


open CFSG.ClassicalInvolution.ModelFacts.TG3 in
theorem plusGlueFacts3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) (hn : 5 ≤ n)
    (hn6 : n ≠ 6) : GlueFactsOn (modelFund 3 1 .POmegaPlus n) := by
  have hn4 : 4 ≤ n := by omega
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
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Fact.out).D).Nonempty := nonempty_fund_plus (p := 3) (f := 1) hn4
  show GlueFactsOn (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D)
  generalize modelUniv .POmegaPlus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne ⊢
  subst hM
  have : Finite (spinGroup (quadPlus n (GaloisField 3 1))) := hfin
  have ctx := spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2
  have hC := EX.central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hker : ∃ ε ∈ (spinAction (quadPlus n (GaloisField 3 1))).ker,
      ∀ k ∈ (spinAction (quadPlus n (GaloisField 3 1))).ker, k = 1 ∨ k = ε := by
    have : NeZero n := ⟨by omega⟩
    have h := coe_ker_spinMatrix_quadPlus (n := n) (K := GaloisField 3 1)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  exact ⟨hne, EX.FundTwinsExist.of_central3 hC (fun L hL => exists_isFundTwin_fundSet hodd hL),
    EX.FundHubUnique.of_central3 hC (fundSet_hubUnique hodd ctx.hQ (Or.inl (by omega))),
    EX.TwinWithinCentralizer.of_central3 hC (fundSet_twinWithinCentralizer hodd ctx.hQ (by omega)),
    EX.FundHasOrthogonal.of_central3 hC (fundSet_hasOrthogonal hodd ctx.hQ (by omega)),
    EX.TwinInvolutionKernel.of_central3 hodd ctx.hQ (by omega) hC hker⟩

open CFSG.ClassicalInvolution.ModelFacts.TG3 in
theorem minusGlueFacts3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) (hn : 5 ≤ n) :
    GlueFactsOn (modelFund 3 1 .POmegaMinus n) := by
  have hn4 : 4 ≤ n := by omega
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_three
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
  have hfin : Finite (modelUniv .POmegaMinus n 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_minus (p := 3) (f := 1) hn4
  show GlueFactsOn (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D)
  generalize modelUniv .POmegaMinus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne ⊢
  subst hM
  have : Finite (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) := hfin
  have hn0 : 0 < n - 1 := by omega
  have ctx := spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2
  have hC := EX.central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hker : ∃ ε ∈ (spinAction (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)).ker, ∀ k ∈ (spinAction (quadMinus n (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadMinus (n := n) (K := GaloisField 3 1)
      (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2) (minusCoeffs_irr 3 1)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  have hTC : TwinWithinCentralizer (fundSet (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := by
    by_cases h6 : n = 6
    · subst h6
      exact EX.minus_twinWithinCentralizer_six3 h2 (minusCoeffs_irr 3 1)
        (by rw [natCard_galoisField_three]; norm_num) hodd ctx.hQ
    · exact fundSet_twinWithinCentralizer hodd ctx.hQ (by omega)
  exact ⟨hne, EX.FundTwinsExist.of_central3 hC (fun L hL => exists_isFundTwin_fundSet hodd hL),
    EX.FundHubUnique.of_central3 hC (fundSet_hubUnique hodd ctx.hQ (Or.inl (by omega))),
    EX.TwinWithinCentralizer.of_central3 hC hTC,
    EX.FundHasOrthogonal.of_central3 hC (fundSet_hasOrthogonal hodd ctx.hQ (by omega)),
    EX.TwinInvolutionKernel.of_central3 hodd ctx.hQ (by omega) hC hker⟩


open CFSG.ClassicalInvolution.ModelFacts.TG3 in
theorem plusFourCliqueFacts3 : CliqueFactsOn (modelFund 3 1 .POmegaPlus 4) := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hn3 : 3 ≤ 4 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus 4 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_plus (p := 3) (f := 1) (le_refl 4)
  show CliqueFactsOn (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D)
  generalize modelUniv .POmegaPlus 4 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin hne ⊢
  subst hM
  have : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) := hfin
  have ctx := spinCtx3_plus hn3 (le_refl 4) hsingle hlong hG3 hsl2
  have hC := EX.central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne
  have hdim : Module.finrank (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hker : ∃ ε ∈ (spinAction (quadPlus 4 (GaloisField 3 1))).ker,
      ∀ k ∈ (spinAction (quadPlus 4 (GaloisField 3 1))).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadPlus (n := 4) (K := GaloisField 3 1)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero two_ne_zero_three
  have hfam := isHypFam_of_pairs (fun i : Fin 4 => plusPair (GaloisField 3 1) i)
    (fun i j hij => plusPair_orth hij)
  exact ⟨hne, EX.FundHasClique.of_central3 hC (fundSet_hasClique_of_family hodd (le_refl 4) _ hfam),
    EX.FundCliqueProd.of_central3 hodd (by omega) hC hker⟩

end Glue

section Shapes

theorem shapePiece3_odd_large (h3 : OddThreeFreeInput) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n 3 1) (hn : 4 ≤ n) :
    ShapePiece3 1 (CompData.model .POmegaOdd n) :=
  shapePiece3_of_glueFacts h3 (yData3_odd hadm.2.2.1 hadm) (oddGlueFacts3 hadm hn)

theorem shapePiece3_plus_large (h3 : OddThreeFreeInput) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 3 1) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    ShapePiece3 1 (CompData.model .POmegaPlus n) :=
  shapePiece3_of_glueFacts h3 (yData3_plus (by omega) hadm) (plusGlueFacts3 hadm hn hn6)

theorem shapePiece3_minus_large (h3 : OddThreeFreeInput) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 3 1) (hn : 5 ≤ n) :
    ShapePiece3 1 (CompData.model .POmegaMinus n) :=
  shapePiece3_of_glueFacts h3 (yData3_minus (by omega) hadm) (minusGlueFacts3 hadm hn)

theorem shapePiece3_plus_four (h3 : OddThreeFreeInput) :
    ShapePiece3 1 (CompData.model .POmegaPlus 4) :=
  shapePiece3_of_cliqueFacts h3 (yData3_plus (le_refl 4) ⟨Nat.prime_three, le_rfl, le_rfl⟩)
    plusFourCliqueFacts3

end Shapes

end CFSG.ClassicalInvolution.Q3.Q3W
