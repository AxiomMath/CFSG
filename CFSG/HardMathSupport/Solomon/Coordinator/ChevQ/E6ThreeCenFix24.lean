module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Dim
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Data
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.HardMathSupport.Malle.SeitzCube (wordProd_smul_E6)
open CFSG.LieType.Chevalley.RootWalk (hVecSum hVecSum_single hStep prod_weylElt_hVecSum)
open CFSG.StandardType.TableBExc.E6Three (gE6 wordE6G0 wordE6G1 wordE6G2
  mapsRootLines_rootDiagUnit)

set_option linter.unusedSectionVars false

@[expose] def cenFixZWord : List (Fin Tag.E6.rank) := wordE6G0 ++ wordE6G1 ++ wordE6G2

theorem cenFix_z_eq_wordProd :
    gE6 0 * gE6 1 * gE6 2 = (coxeterSystem Tag.E6).wordProd cenFixZWord := by
  rw [cenFixZWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
  rfl

@[expose] def cenFixReps : Fin 24 → Fin Tag.E6.rank → ℤ :=
  ![![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1], ![-1, -1, -2, -2, -2, -1],
    ![-1, -1, -2, -2, -1, -1], ![-1, -1, -2, -2, -1, 0], ![-1, -1, -1, -2, -2, -1],
    ![-1, -1, -1, -2, -1, -1], ![-1, -1, -1, -2, -1, 0], ![-1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0], ![-1, -1, -1, -1, 0, 0], ![-1, 0, -1, -1, -1, -1],
    ![-1, 0, -1, -1, -1, 0], ![-1, 0, -1, -1, 0, 0], ![-1, 0, -1, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0], ![0, -1, -1, -2, -2, -1], ![0, -1, -1, -2, -1, -1],
    ![0, -1, -1, -2, -1, 0], ![0, -1, -1, -1, -1, -1], ![0, -1, -1, -1, -1, 0],
    ![0, -1, -1, -1, 0, 0], ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, -1, 0]]

@[expose] def cenFixReps1 : Fin 24 → Fin Tag.E6.rank → ℤ :=
  ![![0, 1, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 0, -1, -1, -1, 0],
    ![0, 0, -1, -1, 0, 0], ![0, 0, -1, -1, -1, -1], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 0], ![1, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 0], ![0, 0, 0, -1, -1, 0], ![0, 0, 0, -1, 0, 0],
    ![0, 0, 0, -1, -1, -1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1]]

@[expose] def cenFixReps2 : Fin 24 → Fin Tag.E6.rank → ℤ :=
  ![![1, 1, 2, 3, 2, 1], ![0, -1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1], ![1, 0, 1, 1, 0, 0], ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1], ![0, -1, 0, -1, 0, 0],
    ![0, -1, 0, -1, -1, -1], ![0, -1, 0, -1, -1, 0], ![0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 2, 1], ![0, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 1, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, -1]]

theorem cenFix_z_smul_reps (i : Fin 24) :
    (coxeterSystem Tag.E6).wordProd cenFixZWord • cenFixReps i = cenFixReps1 i := by
  rw [wordProd_smul_E6]
  revert i
  decide +kernel

theorem cenFix_zz_smul_reps (i : Fin 24) :
    (coxeterSystem Tag.E6).wordProd cenFixZWord •
      (coxeterSystem Tag.E6).wordProd cenFixZWord • cenFixReps i = cenFixReps2 i := by
  rw [wordProd_smul_E6, wordProd_smul_E6]
  revert i
  decide +kernel

theorem cenFix_z2_smul_reps (i : Fin 24) :
    (coxeterSystem Tag.E6).wordProd (cenFixZWord ++ cenFixZWord) • cenFixReps i =
      cenFixReps2 i := by
  rw [wordProd_smul_E6]
  revert i
  decide +kernel

theorem cenFix_z2z2_smul_reps (i : Fin 24) :
    (coxeterSystem Tag.E6).wordProd (cenFixZWord ++ cenFixZWord) •
      (coxeterSystem Tag.E6).wordProd (cenFixZWord ++ cenFixZWord) • cenFixReps i =
        cenFixReps1 i := by
  rw [wordProd_smul_E6, wordProd_smul_E6]
  revert i
  decide +kernel

theorem cenFix_reps_ne_reps1 : cenFixReps 0 ≠ cenFixReps1 0 := by
  decide +kernel

theorem cenFix_reps_ne_reps2 : cenFixReps 0 ≠ cenFixReps2 0 := by
  decide +kernel

theorem cenFix_reps_mem : ∀ i, cenFixReps i ∈ rootFinset Tag.E6 := by
  decide +kernel

theorem cenFix_cover_mem : ∀ α ∈ rootFinset Tag.E6,
    ∃ i, α = cenFixReps i ∨ α = cenFixReps1 i ∨ α = cenFixReps2 i := by
  decide +kernel

theorem cenFix_hStep_one : ∀ j : Fin Tag.E6.rank,
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + cenFixZWord.foldr (hStep Tag.E6) (Pi.single j 1) +
      cenFixZWord.foldr (hStep Tag.E6) (cenFixZWord.foldr (hStep Tag.E6) (Pi.single j 1)) =
        0 := by
  decide +kernel

theorem cenFix_hStep_two : ∀ j : Fin Tag.E6.rank,
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
        (cenFixZWord ++ cenFixZWord).foldr (hStep Tag.E6) (Pi.single j 1) +
      (cenFixZWord ++ cenFixZWord).foldr (hStep Tag.E6)
        ((cenFixZWord ++ cenFixZWord).foldr (hStep Tag.E6) (Pi.single j 1)) = 0 := by
  decide +kernel

section Bound


theorem cenFix_reps_isRoot (i : Fin 24) : IsRoot Tag.E6 (cenFixReps i) :=
  mem_rootFinset.1 (cenFix_reps_mem i)

theorem cenFix_cover {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ i, α = cenFixReps i ∨ α = cenFixReps1 i ∨ α = cenFixReps2 i :=
  cenFix_cover_mem α (mem_rootFinset.2 hα)

theorem cenFix_exists_word {k : ℕ} (hk : k = 1 ∨ k = 2) :
    ∃ μ : List (Fin Tag.E6.rank),
      (gE6 0 * gE6 1 * gE6 2) ^ k = (coxeterSystem Tag.E6).wordProd μ ∧
      (coxeterSystem Tag.E6).wordProd μ ≠ 1 ∧
      (∀ j : Fin Tag.E6.rank, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
          μ.foldr (hStep Tag.E6) (Pi.single j 1) +
        μ.foldr (hStep Tag.E6) (μ.foldr (hStep Tag.E6) (Pi.single j 1)) = 0) ∧
      ∀ α, IsRoot Tag.E6 α → ∃ i, α = cenFixReps i ∨
        α = (coxeterSystem Tag.E6).wordProd μ • cenFixReps i ∨
        α = (coxeterSystem Tag.E6).wordProd μ • (coxeterSystem Tag.E6).wordProd μ •
          cenFixReps i := by
  rcases hk with rfl | rfl
  · refine ⟨cenFixZWord, by rw [pow_one]; exact cenFix_z_eq_wordProd, fun h => ?_,
      cenFix_hStep_one, fun α hα => ?_⟩
    · apply cenFix_reps_ne_reps1
      calc cenFixReps 0 = (1 : WeylGroup Tag.E6) • cenFixReps 0 := (one_smul _ _).symm
        _ = (coxeterSystem Tag.E6).wordProd cenFixZWord • cenFixReps 0 := by rw [h]
        _ = cenFixReps1 0 := cenFix_z_smul_reps 0
    · obtain ⟨i, h | h | h⟩ := cenFix_cover hα
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inl (h.trans (cenFix_z_smul_reps i).symm))⟩
      · exact ⟨i, Or.inr (Or.inr (h.trans (cenFix_zz_smul_reps i).symm))⟩
  · have hz2 : (gE6 0 * gE6 1 * gE6 2) ^ 2 =
        (coxeterSystem Tag.E6).wordProd (cenFixZWord ++ cenFixZWord) := by
      rw [CoxeterSystem.wordProd_append, ← cenFix_z_eq_wordProd, pow_two]
    refine ⟨cenFixZWord ++ cenFixZWord, hz2, fun h => ?_, cenFix_hStep_two, fun α hα => ?_⟩
    · apply cenFix_reps_ne_reps2
      calc cenFixReps 0 = (1 : WeylGroup Tag.E6) • cenFixReps 0 := (one_smul _ _).symm
        _ = (coxeterSystem Tag.E6).wordProd (cenFixZWord ++ cenFixZWord) • cenFixReps 0 := by
          rw [h]
        _ = cenFixReps2 0 := cenFix_z2_smul_reps 0
    · obtain ⟨i, h | h | h⟩ := cenFix_cover hα
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inr (h.trans (cenFix_z2z2_smul_reps i).symm))⟩
      · exact ⟨i, Or.inr (Or.inl (h.trans (cenFix_z2_smul_reps i).symm))⟩

theorem cenFix_hVecSum_add {K : Type} [Field K] (c d : Fin Tag.E6.rank → ℤ) :
    hVecSum K (c + d) = hVecSum K c + hVecSum K d := by
  simp only [hVecSum, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

theorem cenFix_hVecSum_zero {K : Type} [Field K] : hVecSum K (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  simp only [hVecSum, Pi.zero_apply, Int.cast_zero, zero_smul, Finset.sum_const_zero]

theorem cenFix_word_rootDiag_hVecSum {K : Type} [Field K] (μ : List (Fin Tag.E6.rank))
    (b : Fin Tag.E6.rank → Kˣ) (c : Fin Tag.E6.rank → ℤ) :
    (((weylWordElt .E6 K μ : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (hVecSum K c) =
      hVecSum K (μ.foldr (hStep Tag.E6) c) := by
  have hd : ((rootDiagUnit Tag.E6 b : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (hVecSum K c) = hVecSum K c := by
    change (rootDiag b : Module.End K (RootModule Tag.E6 K)) (hVecSum K c) = hVecSum K c
    simp only [hVecSum, map_sum, map_smul, CFSG.LieType.Chevalley.rootDiag_hVec]
  rw [Units.val_mul, Module.End.mul_apply, hd, coe_weylWordElt]
  exact prod_weylElt_hVecSum K μ c

theorem cenFix_finrank_ker_le {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    {S : Module.End K (RootModule Tag.E6 K)} (hS3 : ∀ x, S (S (S x)) = x)
    {v : WeylGroup Tag.E6} (hS : ∀ β, IsRoot Tag.E6 β → ∃ c : Kˣ,
      S (rootVec Tag.E6 K β) = (c : K) • rootVec Tag.E6 K (v • β))
    (hh : ∀ j, hVec Tag.E6 K j + S (hVec Tag.E6 K j) + S (S (hVec Tag.E6 K j)) = 0)
    {n : ℕ} (ρ : Fin n → Fin Tag.E6.rank → ℤ) (hρ : ∀ i, IsRoot Tag.E6 (ρ i))
    (hcov : ∀ α, IsRoot Tag.E6 α → ∃ i, α = ρ i ∨ α = v • ρ i ∨ α = v • v • ρ i) :
    Module.finrank K (LinearMap.ker (S - 1)) ≤ n := by
  obtain ⟨P, hP⟩ : ∃ P : Module.End K (RootModule Tag.E6 K), ∀ x, P x = x + S x + S (S x) :=
    ⟨1 + S + S * S, fun x => by
      simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply]⟩
  have hPS : ∀ x, P (S x) = P x := fun x => by
    rw [hP (S x), hP x, hS3]
    abel
  obtain ⟨f, hf⟩ : ∃ f : Fin n → RootModule Tag.E6 K, ∀ i, f i = P (rootVec Tag.E6 K (ρ i)) :=
    ⟨_, fun _ => rfl⟩
  have hbase : ∀ i, P (rootVec Tag.E6 K (ρ i)) ∈ Submodule.span K (Set.range f) := fun i => by
    rw [← hf i]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hstep : ∀ β, IsRoot Tag.E6 β → P (rootVec Tag.E6 K β) ∈ Submodule.span K (Set.range f) →
      P (rootVec Tag.E6 K (v • β)) ∈ Submodule.span K (Set.range f) := by
    intro β hβ hmem
    obtain ⟨c, hc⟩ := hS β hβ
    rw [← hPS (rootVec Tag.E6 K β), hc, map_smul] at hmem
    exact ((Submodule.span K (Set.range f)).smul_mem_iff c.ne_zero).1 hmem
  have hroot : ∀ α, IsRoot Tag.E6 α →
      P (rootVec Tag.E6 K α) ∈ Submodule.span K (Set.range f) := by
    intro α hα
    obtain ⟨i, rfl | rfl | rfl⟩ := hcov α hα
    · exact hbase i
    · exact hstep _ (hρ i) (hbase i)
    · exact hstep _ (CFSG.LieType.Chevalley.IsRoot.smul (hρ i) v) (hstep _ (hρ i) (hbase i))
  have hall : ∀ y, P y ∈ Submodule.span K (Set.range f) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | single l c =>
      rw [← Finsupp.smul_single_one, map_smul]
      refine Submodule.smul_mem _ c ?_
      rcases l with j | ⟨α, hα⟩
      · change P (hVec Tag.E6 K j) ∈ _
        rw [hP, hh j]
        exact Submodule.zero_mem _
      · have e : rootVec Tag.E6 K α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := dif_pos hα
        rw [← e]
        exact hroot α hα
  have hker : LinearMap.ker (S - 1) ≤ Submodule.span K (Set.range f) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    have e : P x = (3 : K) • x := by
      rw [hP, hx, hx, show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    have hx3 := hall x
    rw [e] at hx3
    exact ((Submodule.span K (Set.range f)).smul_mem_iff h3).1 hx3
  calc Module.finrank K (LinearMap.ker (S - 1))
      ≤ Module.finrank K (Submodule.span K (Set.range f)) := Submodule.finrank_mono hker
    _ ≤ Fintype.card (Fin n) := finrank_range_le_card f
    _ = n := Fintype.card_fin n

end Bound

section Fix


theorem cenFix_finrank_ker_le_of_word {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    {x : ModGL Tag.E6 K} (hx3 : x ^ 3 = 1) {μ : List (Fin Tag.E6.rank)}
    {b : Fin Tag.E6.rank → Kˣ}
    (hxb : x = (weylWordElt .E6 K μ : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b)
    (hF : ∀ j : Fin Tag.E6.rank, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
        μ.foldr (hStep Tag.E6) (Pi.single j 1) +
      μ.foldr (hStep Tag.E6) (μ.foldr (hStep Tag.E6) (Pi.single j 1)) = 0)
    (hcov : ∀ α, IsRoot Tag.E6 α → ∃ i, α = cenFixReps i ∨
      α = (coxeterSystem Tag.E6).wordProd μ • cenFixReps i ∨
      α = (coxeterSystem Tag.E6).wordProd μ • (coxeterSystem Tag.E6).wordProd μ •
        cenFixReps i) :
    Module.finrank K (LinearMap.ker ((x : Module.End K (RootModule Tag.E6 K)) - 1)) ≤ 24 := by
  have hS3 : ∀ y, (x : Module.End K (RootModule Tag.E6 K))
      ((x : Module.End K (RootModule Tag.E6 K)) ((x : Module.End K (RootModule Tag.E6 K)) y)) =
        y := fun y => by
    have e := congrArg (fun g : ModGL Tag.E6 K => (g : Module.End K (RootModule Tag.E6 K)) y) hx3
    simpa only [pow_three, Units.val_mul, Units.val_one, Module.End.one_apply,
      Module.End.mul_apply] using e
  have hmaps : MapsRootLines x ((coxeterSystem Tag.E6).wordProd μ) := by
    rw [hxb, ← mul_one ((coxeterSystem Tag.E6).wordProd μ)]
    exact (bm_mapsRootLines_weylWordElt (K := K) μ).mul
      (mapsRootLines_rootDiagUnit (τ := Tag.E6) (K := K) b)
  have hx : ∀ c, (x : Module.End K (RootModule Tag.E6 K)) (hVecSum K c) =
      hVecSum K (μ.foldr (hStep Tag.E6) c) := fun c => by
    rw [hxb]
    exact cenFix_word_rootDiag_hVecSum μ b c
  refine cenFix_finrank_ker_le h3 hS3 hmaps (fun j => ?_) cenFixReps cenFix_reps_isRoot hcov
  have e0 : hVecSum K ((Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      μ.foldr (hStep Tag.E6) (Pi.single j 1) +
        μ.foldr (hStep Tag.E6) (μ.foldr (hStep Tag.E6) (Pi.single j 1))) =
      hVecSum K (Pi.single j 1) + hVecSum K (μ.foldr (hStep Tag.E6) (Pi.single j 1)) +
        hVecSum K (μ.foldr (hStep Tag.E6) (μ.foldr (hStep Tag.E6) (Pi.single j 1))) := by
    rw [cenFix_hVecSum_add, cenFix_hVecSum_add]
  rw [hF j, cenFix_hVecSum_zero] at e0
  rw [← hVecSum_single (R := K) j, hx, hx]
  exact e0.symm

theorem finrank_ker_eq_24_of_bmMono_z {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) {s : adjointGroup Tag.E6 K} (hs3 : s ^ 3 = 1) {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hs : BmMono (MulAut.conj s) ((gE6 0 * gE6 1 * gE6 2) ^ k)) :
    Module.finrank K (LinearMap.ker
      (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : K) = 0 := by
      rw [Nat.cast_ofNat]
      exact h0
    exact hK3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 h0'))
  obtain ⟨μ, hμ, hne, hF, hcov⟩ := cenFix_exists_word hk
  rw [hμ] at hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one] at hs
    exact hne (BmMono.unique hK4 hs bmMono_one)
  have hx3 : (s : ModGL Tag.E6 K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hs3]
    rfl
  obtain ⟨b, hb⟩ := hs.exists_eq_word
  have hle := cenFix_finrank_ker_le_of_word h3 hx3 (e6Cen_coe_eq_of_conj_eq hK4 hb) hF hcov
  have hxL := CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
    (algebraMap K (AlgebraicClosure K)) s.2
  obtain ⟨a, ha3, ha1, hdim⟩ := KSNotAll24.exists_torus_conj_of_cube_one hK3 hxL hx3
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := fun h0 =>
    hK3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 3).1 h0))
  have key := KSNotAll24.finrank_ker_rootDiag_mem h3L ha3
    (fun h1 => hs1 (Subtype.ext (ha1 h1)))
  rw [← hdim] at key
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at key
  omega

end Fix

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
