module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6E7
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5
open CFSG.RankThree.E6 (charVal)

set_option linter.unusedSectionVars false

section E8Sylow

open CFSG.HardMathSupport.Curtis.UnitaryLevi

namespace Aux

theorem wordW_smul_foldr_E8 (l : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    wordW Tag.E8 l • v = l.foldr (reflect Tag.E8) v := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have e : wordW Tag.E8 (i :: l) = simple Tag.E8 i * wordW Tag.E8 l := by
      simp [wordW, List.prod_cons]
    rw [e, mul_smul, ih, simple_smul, List.foldr_cons]

theorem wordW_eq_of_foldr_E8 {l l' : List (Fin Tag.E8.rank)}
    (h : ∀ k : Fin Tag.E8.rank, l.foldr (reflect Tag.E8) (Pi.single k 1) =
      l'.foldr (reflect Tag.E8) (Pi.single k 1)) :
    wordW Tag.E8 l = wordW Tag.E8 l' :=
  ext_single fun k => by rw [wordW_smul_foldr_E8, wordW_smul_foldr_E8, h k]

@[expose] def lc1 : List (Fin Tag.E8.rank) := ([0, 2] : List (Fin 8))
@[expose] def lc2 : List (Fin Tag.E8.rank) := ([4, 5] : List (Fin 8))
@[expose] def lc3 : List (Fin Tag.E8.rank) :=
  ([3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1] : List (Fin 8))
@[expose] def lc4 : List (Fin Tag.E8.rank) :=
  ([6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3,
    2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7] : List (Fin 8))
@[expose] def lpi : List (Fin Tag.E8.rank) := ([3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 1, 0] : List (Fin 8))

@[expose] def wc1 : WeylGroup Tag.E8 := wordW Tag.E8 lc1
@[expose] def wc2 : WeylGroup Tag.E8 := wordW Tag.E8 lc2
@[expose] def wc3 : WeylGroup Tag.E8 := wordW Tag.E8 lc3
@[expose] def wc4 : WeylGroup Tag.E8 := wordW Tag.E8 lc4
@[expose] def wpi : WeylGroup Tag.E8 := wordW Tag.E8 lpi

theorem cube_of_word {l : List (Fin Tag.E8.rank)}
    (h : ∀ k : Fin Tag.E8.rank, (l ++ l ++ l).foldr (reflect Tag.E8) (Pi.single k 1) =
      ([] : List (Fin Tag.E8.rank)).foldr (reflect Tag.E8) (Pi.single k 1)) :
    wordW Tag.E8 l ^ 3 = 1 := by
  have h1 := wordW_eq_of_foldr_E8 h
  rw [wordW_append, wordW_append] at h1
  rw [pow_three, ← mul_assoc, h1]
  simp [wordW]

theorem mul_eq_of_word {l l' m m' : List (Fin Tag.E8.rank)}
    (h : ∀ k : Fin Tag.E8.rank, (l ++ l').foldr (reflect Tag.E8) (Pi.single k 1) =
      (m ++ m').foldr (reflect Tag.E8) (Pi.single k 1)) :
    wordW Tag.E8 l * wordW Tag.E8 l' = wordW Tag.E8 m * wordW Tag.E8 m' := by
  rw [← wordW_append, ← wordW_append]
  exact wordW_eq_of_foldr_E8 h

theorem wc1_cube : wc1 ^ 3 = 1 := cube_of_word (by decide +kernel)
theorem wc2_cube : wc2 ^ 3 = 1 := cube_of_word (by decide +kernel)
theorem wc3_cube : wc3 ^ 3 = 1 := cube_of_word (by decide +kernel)
theorem wc4_cube : wc4 ^ 3 = 1 := cube_of_word (by decide +kernel)
theorem wpi_cube : wpi ^ 3 = 1 := cube_of_word (by decide +kernel)

theorem wc1_wc2 : Commute wc1 wc2 := mul_eq_of_word (by decide +kernel)
theorem wc1_wc3 : Commute wc1 wc3 := mul_eq_of_word (by decide +kernel)
theorem wc2_wc3 : Commute wc2 wc3 := mul_eq_of_word (by decide +kernel)
theorem wc4_wc1 : Commute wc4 wc1 := mul_eq_of_word (by decide +kernel)
theorem wc4_wc2 : Commute wc4 wc2 := mul_eq_of_word (by decide +kernel)
theorem wc4_wc3 : Commute wc4 wc3 := mul_eq_of_word (by decide +kernel)
theorem wc4_wpi : Commute wc4 wpi := mul_eq_of_word (by decide +kernel)
theorem wpi_wc1 : SemiconjBy wpi wc1 wc2 := mul_eq_of_word (by decide +kernel)
theorem wpi_wc2 : SemiconjBy wpi wc2 wc3 := mul_eq_of_word (by decide +kernel)
theorem wpi_wc3 : SemiconjBy wpi wc3 wc1 := mul_eq_of_word (by decide +kernel)

@[expose] def nfN (a e₁ e₂ e₃ b : ℕ) : WeylGroup Tag.E8 :=
  wc4 ^ a * wc1 ^ e₁ * wc2 ^ e₂ * wc3 ^ e₃ * wpi ^ b

@[expose] def QE8 : Subgroup (WeylGroup Tag.E8) := Subgroup.closure {wc1, wc2, wc3, wc4, wpi}

theorem pow_succ_left (g : WeylGroup Tag.E8) (e : ℕ) (X : WeylGroup Tag.E8) :
    g * (g ^ e * X) = g ^ (e + 1) * X := by
  rw [← mul_assoc, ← pow_succ']

theorem semiconj_step {x y z : WeylGroup Tag.E8} (h : SemiconjBy x y z) (e : ℕ)
    (X : WeylGroup Tag.E8) : x * (y ^ e * X) = z ^ e * (x * X) := by
  rw [← mul_assoc, (h.pow_right e).eq, mul_assoc]

theorem nfN_assoc (a e₁ e₂ e₃ b : ℕ) :
    nfN a e₁ e₂ e₃ b = wc4 ^ a * (wc1 ^ e₁ * (wc2 ^ e₂ * (wc3 ^ e₃ * wpi ^ b))) := by
  simp only [nfN, mul_assoc]

theorem nf_mul_left {g : WeylGroup Tag.E8}
    (hg : g ∈ ({wc1, wc2, wc3, wc4, wpi} : Set (WeylGroup Tag.E8))) (a e₁ e₂ e₃ b : ℕ) :
    ∃ a' e₁' e₂' e₃' b' : ℕ, g * nfN a e₁ e₂ e₃ b = nfN a' e₁' e₂' e₃' b' := by
  rcases hg with h | h | h | h | h <;> rw [h]
  · refine ⟨a, e₁ + 1, e₂, e₃, b, ?_⟩
    rw [nfN_assoc, nfN_assoc, (wc4_wc1.symm.pow_right a).left_comm, pow_succ_left]
  · refine ⟨a, e₁, e₂ + 1, e₃, b, ?_⟩
    rw [nfN_assoc, nfN_assoc, (wc4_wc2.symm.pow_right a).left_comm,
      (wc1_wc2.symm.pow_right e₁).left_comm, pow_succ_left]
  · refine ⟨a, e₁, e₂, e₃ + 1, b, ?_⟩
    rw [nfN_assoc, nfN_assoc, (wc4_wc3.symm.pow_right a).left_comm,
      (wc1_wc3.symm.pow_right e₁).left_comm, (wc2_wc3.symm.pow_right e₂).left_comm,
      pow_succ_left]
  · refine ⟨a + 1, e₁, e₂, e₃, b, ?_⟩
    rw [nfN_assoc, nfN_assoc, pow_succ_left]
  · refine ⟨a, e₃, e₁, e₂, b + 1, ?_⟩
    rw [nfN_assoc, nfN_assoc, (wc4_wpi.symm.pow_right a).left_comm, semiconj_step wpi_wc1,
      semiconj_step wpi_wc2, semiconj_step wpi_wc3, ← pow_succ',
      ((wc1_wc3.pow_pow e₃ e₂).symm).left_comm, ((wc1_wc2.pow_pow e₃ e₁).symm).left_comm]

theorem gen_cube {g : WeylGroup Tag.E8}
    (hg : g ∈ ({wc1, wc2, wc3, wc4, wpi} : Set (WeylGroup Tag.E8))) : g ^ 3 = 1 := by
  rcases hg with h | h | h | h | h <;> rw [h]
  · exact wc1_cube
  · exact wc2_cube
  · exact wc3_cube
  · exact wc4_cube
  · exact wpi_cube

theorem exists_nfN_of_mem {x : WeylGroup Tag.E8} (hx : x ∈ QE8) :
    ∃ a e₁ e₂ e₃ b : ℕ, x = nfN a e₁ e₂ e₃ b := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, 0, 0, 0, by simp [nfN]⟩
  | mul_left g hg y _ ih =>
    obtain ⟨a, e₁, e₂, e₃, b, hy⟩ := ih
    obtain ⟨a', e₁', e₂', e₃', b', h⟩ := nf_mul_left hg a e₁ e₂ e₃ b
    exact ⟨a', e₁', e₂', e₃', b', by rw [hy, h]⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨a, e₁, e₂, e₃, b, hy⟩ := ih
    have hinv : g⁻¹ = g * g := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact gen_cube hg)
    obtain ⟨a', e₁', e₂', e₃', b', h⟩ := nf_mul_left hg a e₁ e₂ e₃ b
    obtain ⟨a'', e₁'', e₂'', e₃'', b'', h'⟩ := nf_mul_left hg a' e₁' e₂' e₃' b'
    exact ⟨a'', e₁'', e₂'', e₃'', b'', by rw [hy, hinv, mul_assoc, h, h']⟩

theorem nfN_mod (a e₁ e₂ e₃ b : ℕ) :
    nfN a e₁ e₂ e₃ b = nfN (a % 3) (e₁ % 3) (e₂ % 3) (e₃ % 3) (b % 3) := by
  simp only [nfN]
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      wc4_cube a,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      wc1_cube e₁,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      wc2_cube e₂,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      wc3_cube e₃,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      wpi_cube b]

@[expose] def nfE8 (v : Fin 5 → Fin 3) : WeylGroup Tag.E8 :=
  nfN (v 0 : ℕ) (v 1 : ℕ) (v 2 : ℕ) (v 3 : ℕ) (v 4 : ℕ)

@[expose] def mulVec8 (M : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) (u : Fin Tag.E8.rank → ℤ) :
    Fin Tag.E8.rank → ℤ := fun i =>
  M i ⟨0, by decide⟩ * u ⟨0, by decide⟩ + M i ⟨1, by decide⟩ * u ⟨1, by decide⟩ +
    M i ⟨2, by decide⟩ * u ⟨2, by decide⟩ + M i ⟨3, by decide⟩ * u ⟨3, by decide⟩ +
    M i ⟨4, by decide⟩ * u ⟨4, by decide⟩ + M i ⟨5, by decide⟩ * u ⟨5, by decide⟩ +
    M i ⟨6, by decide⟩ * u ⟨6, by decide⟩ + M i ⟨7, by decide⟩ * u ⟨7, by decide⟩

theorem sum_fin_E8 {R : Type*} [AddCommMonoid R] (f : Fin Tag.E8.rank → R) :
    ∑ k, f k = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩ := by
  have h : Tag.E8.rank = 8 := rfl
  rw [← Equiv.sum_comp (finCongr h).symm f, Fin.sum_univ_eight]
  rfl

theorem smul_eq_mulVec8 {g : WeylGroup Tag.E8} {M : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ}
    (hcol : ∀ k : Fin Tag.E8.rank, g • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => M i k)
    (u : Fin Tag.E8.rank → ℤ) : g • u = mulVec8 M u := by
  classical
  have hu : u = ∑ k, u k • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  ext i
  have h1 : (g • u) i = ∑ k, u k * M i k := by
    conv_lhs => rw [hu]
    rw [Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, hcol k, Pi.smul_apply, smul_eq_mul]
  rw [h1, sum_fin_E8]
  simp only [mulVec8]
  ring

theorem pow_smul_eq_iterate {g : WeylGroup Tag.E8} {M : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ}
    (h : ∀ u, g • u = mulVec8 M u) (n : ℕ) (u : Fin Tag.E8.rank → ℤ) :
    g ^ n • u = (mulVec8 M)^[n] u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, ih, Function.iterate_succ_apply]

@[expose] def Mc1E8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![0, 0, -1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, -1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def Mc2E8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, -1, 1, 0],
    ![0, 0, 0, 0, 1, -1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def Mc3E8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![1, -1, 0, 0, 0, 0, 1, 0],
    ![0, -2, 0, 1, 0, 0, 1, 0],
    ![0, -2, 1, 0, 0, 0, 2, 0],
    ![0, -3, 0, 1, 0, 0, 3, 0],
    ![0, -2, 0, 0, 1, 0, 2, 0],
    ![0, -1, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def Mc4E8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, -2],
    ![0, 1, 0, 0, 0, 0, 0, -3],
    ![0, 0, 1, 0, 0, 0, 0, -4],
    ![0, 0, 0, 1, 0, 0, 0, -6],
    ![0, 0, 0, 0, 1, 0, 0, -5],
    ![0, 0, 0, 0, 0, 1, 0, -4],
    ![0, 0, 0, 0, 0, 0, 1, -3],
    ![0, 0, 0, 0, 0, 0, 1, -2]]

@[expose] def MpiE8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![0, -1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, -1, 1, 1, 0, 0],
    ![0, 0, 0, -1, 2, 0, 0, 0],
    ![0, 0, 0, -2, 3, 0, 1, 0],
    ![0, 0, 1, -2, 2, 0, 1, 0],
    ![-1, 0, 1, -1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem Mc1E8_col : ∀ k : Fin Tag.E8.rank,
    wc1 • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => Mc1E8 i k := by
  intro k
  rw [wc1, wordW_smul_foldr_E8]
  revert k
  decide +kernel

theorem Mc2E8_col : ∀ k : Fin Tag.E8.rank,
    wc2 • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => Mc2E8 i k := by
  intro k
  rw [wc2, wordW_smul_foldr_E8]
  revert k
  decide +kernel

theorem Mc3E8_col : ∀ k : Fin Tag.E8.rank,
    wc3 • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => Mc3E8 i k := by
  intro k
  rw [wc3, wordW_smul_foldr_E8]
  revert k
  decide +kernel

theorem Mc4E8_col : ∀ k : Fin Tag.E8.rank,
    wc4 • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => Mc4E8 i k := by
  intro k
  rw [wc4, wordW_smul_foldr_E8]
  revert k
  decide +kernel

theorem MpiE8_col : ∀ k : Fin Tag.E8.rank,
    wpi • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = fun i => MpiE8 i k := by
  intro k
  rw [wpi, wordW_smul_foldr_E8]
  revert k
  decide +kernel

@[expose] def actE8 (v : Fin 5 → Fin 3) (u : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  (mulVec8 Mc4E8)^[(v 0 : ℕ)] ((mulVec8 Mc1E8)^[(v 1 : ℕ)] ((mulVec8 Mc2E8)^[(v 2 : ℕ)]
    ((mulVec8 Mc3E8)^[(v 3 : ℕ)] ((mulVec8 MpiE8)^[(v 4 : ℕ)] u))))

theorem nfE8_smul (v : Fin 5 → Fin 3) (u : Fin Tag.E8.rank → ℤ) : nfE8 v • u = actE8 v u := by
  simp only [nfE8, nfN, actE8, mul_smul, pow_smul_eq_iterate (smul_eq_mulVec8 Mc1E8_col),
    pow_smul_eq_iterate (smul_eq_mulVec8 Mc2E8_col), pow_smul_eq_iterate (smul_eq_mulVec8 Mc3E8_col),
    pow_smul_eq_iterate (smul_eq_mulVec8 Mc4E8_col), pow_smul_eq_iterate (smul_eq_mulVec8 MpiE8_col)]

theorem nfE8_mem (v : Fin 5 → Fin 3) : nfE8 v ∈ QE8 := by
  have hm : ∀ g ∈ ({wc1, wc2, wc3, wc4, wpi} : Set (WeylGroup Tag.E8)), g ∈ QE8 :=
    fun g hg => Subgroup.subset_closure hg
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (hm _ (by simp)) _) (pow_mem (hm _ (by simp)) _))
    (pow_mem (hm _ (by simp)) _)) (pow_mem (hm _ (by simp)) _)) (pow_mem (hm _ (by simp)) _)

theorem exists_nfE8_of_mem {x : WeylGroup Tag.E8} (hx : x ∈ QE8) : ∃ v, nfE8 v = x := by
  obtain ⟨a, e₁, e₂, e₃, b, hx'⟩ := exists_nfN_of_mem hx
  refine ⟨![⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨e₁ % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨e₂ % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨e₃ % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩], ?_⟩
  rw [hx', nfN_mod]
  rfl

@[expose] def keyVecE8 : Fin Tag.E8.rank → ℤ := ![1, 1, 0, 0, 1, 0, 0, 1]

@[expose] def decTableE8 : List (ℕ × ℕ) :=
  [(601850659377, 0), (601851808304, 81), (601883166193, 162), (601814907344, 27), (601816056367, 108), (601918918226, 189), (601886411314, 54), (601780304334, 135), (601847414256, 216), (601883165233, 9), (601919965744, 90), (601815008753, 171), (601847413200, 36), (601884213807, 117), (601850760786, 198), (601918917170, 63), (601848461774, 144), (601779256816, 225), (601815007793, 18), (601884314160, 99), (601850660337, 180), (601779255760, 45), (601848562223, 126), (601886412370, 207), (601850759730, 72), (601812810190, 153), (601814908400, 234), (601850660400, 3), (601851807281, 84), (601883165167, 165), (601814908367, 30), (601816055344, 111), (601918917200, 192), (601886412337, 57), (601780303311, 138), (601847413230, 219), (601883166256, 12), (601919964721, 93), (601815007727, 174), (601847414223, 39), (601884212784, 120), (601850759760, 201), (601918918193, 66), (601848460751, 147), (601779255790, 228), (601815008816, 21), (601884313137, 102), (601850659311, 183), (601779256783, 48), (601848561200, 129), (601886411344, 210), (601850760753, 75), (601812809167, 156), (601814907374, 237), (601850658351, 6), (601851809330, 87), (601883164144, 168), (601814906318, 33), (601816057393, 114), (601918916177, 195), (601886410288, 60), (601780305360, 141), (601847412207, 222), (601883164207, 15), (601919966770, 96), (601815006704, 177), (601847412174, 42), (601884214833, 123), (601850758737, 204), (601918916144, 69), (601848462800, 150), (601779254767, 231), (601815006767, 24), (601884315186, 105), (601850658288, 186), (601779254734, 51), (601848563249, 132), (601886410321, 213), (601850758704, 78), (601812811216, 159), (601814906351, 240), (495410557391, 1), (495411706318, 82), (495443064207, 163), (495374805358, 28), (495375954381, 109), (495478816240, 190), (495446309328, 55), (495340202348, 136), (495407312270, 217), (495443063247, 10), (495479863758, 91), (495374906767, 172), (495407311214, 37), (495444111821, 118), (495410658800, 199), (495478815184, 64), (495408359788, 145), (495339154830, 226), (495374905807, 19), (495444212174, 100), (495410558351, 181), (495339153774, 46), (495408460237, 127), (495446310384, 208), (495410657744, 73), (495372708204, 154), (495374806414, 235), (495410558414, 4), (495411705295, 85), (495443063181, 166), (495374806381, 31), (495375953358, 112), (495478815214, 193), (495446310351, 58), (495340201325, 139), (495407311244, 220), (495443064270, 13), (495479862735, 94), (495374905741, 175), (495407312237, 40), (495444110798, 121), (495410657774, 202), (495478816207, 67), (495408358765, 148), (495339153804, 229), (495374906830, 22), (495444211151, 103), (495410557325, 184), (495339154797, 49), (495408459214, 130), (495446309358, 211), (495410658767, 76), (495372707181, 157), (495374805388, 238), (495410556365, 7), (495411707344, 88), (495443062158, 169), (495374804332, 34), (495375955407, 115), (495478814191, 196), (495446308302, 61), (495340203374, 142), (495407310221, 223), (495443062221, 16), (495479864784, 97), (495374904718, 178), (495407310188, 43), (495444112847, 124), (495410656751, 205), (495478814158, 70), (495408360814, 151), (495339152781, 232), (495374904781, 25), (495444213200, 106), (495410556302, 187), (495339152748, 52), (495408461263, 133), (495446308335, 214), (495410656718, 79), (495372709230, 160), (495374804365, 241), (605211546259, 2), (605212695186, 83), (605244053075, 164), (605175794226, 29), (605176943249, 110), (605279805108, 191), (605247298196, 56), (605141191216, 137), (605208301138, 218), (605244052115, 11), (605280852626, 92), (605175895635, 173), (605208300082, 38), (605245100689, 119), (605211647668, 200), (605279804052, 65), (605209348656, 146), (605140143698, 227), (605175894675, 20), (605245201042, 101), (605211547219, 182), (605140142642, 47), (605209449105, 128), (605247299252, 209), (605211646612, 74), (605173697072, 155), (605175795282, 236), (605211547282, 5), (605212694163, 86), (605244052049, 167), (605175795249, 32), (605176942226, 113), (605279804082, 194), (605247299219, 59), (605141190193, 140), (605208300112, 221), (605244053138, 14), (605280851603, 95), (605175894609, 176), (605208301105, 41), (605245099666, 122), (605211646642, 203), (605279805075, 68), (605209347633, 149), (605140142672, 230), (605175895698, 23), (605245200019, 104), (605211546193, 185), (605140143665, 50), (605209448082, 131), (605247298226, 212), (605211647635, 77), (605173696049, 158), (605175794256, 239), (605211545233, 8), (605212696212, 89), (605244051026, 170), (605175793200, 35), (605176944275, 116), (605279803059, 197), (605247297170, 62), (605141192242, 143), (605208299089, 224), (605244051089, 17), (605280853652, 98), (605175893586, 179), (605208299056, 44), (605245101715, 125), (605211645619, 206), (605279803026, 71), (605209349682, 152), (605140141649, 233), (605175893649, 26), (605245202068, 107), (605211545170, 188), (605140141616, 53), (605209450131, 134), (605247297203, 215), (605211645586, 80), (605173698098, 161), (605175793233, 242)]

@[expose] def codeVecE8 (u : Fin Tag.E8.rank → ℤ) : ℕ :=
  (u 0 + 16).toNat + 32 * ((u 1 + 16).toNat + 32 * ((u 2 + 16).toNat + 32 * ((u 3 + 16).toNat +
    32 * ((u 4 + 16).toNat + 32 * ((u 5 + 16).toNat + 32 * ((u 6 + 16).toNat +
      32 * (u 7 + 16).toNat))))))

@[expose] def vOfCodeE8 (n : ℕ) : Fin 5 → Fin 3 := fun i => ⟨(n / 3 ^ (i : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩

@[expose] def decodeE8 (u : Fin Tag.E8.rank → ℤ) : Fin 5 → Fin 3 :=
  vOfCodeE8 (((decTableE8.find? fun p => p.1 == codeVecE8 u).map Prod.snd).getD 0)

theorem decodeE8_nf : ∀ v : Fin 5 → Fin 3, decodeE8 (actE8 v keyVecE8) = v := by
  decide +kernel

theorem nfE8_injective : Function.Injective nfE8 := by
  intro v w h
  have h' : actE8 v keyVecE8 = actE8 w keyVecE8 := by
    rw [← nfE8_smul, ← nfE8_smul, h]
  rw [← decodeE8_nf v, ← decodeE8_nf w, h']

theorem card_QE8 : Nat.card QE8 = 3 ^ 5 := by
  have hbij : Function.Bijective (fun v : Fin 5 → Fin 3 => (⟨nfE8 v, nfE8_mem v⟩ : QE8)) := by
    refine ⟨fun v w h => ?_, fun x => ?_⟩
    · simp only [Subtype.mk.injEq] at h
      exact nfE8_injective h
    · obtain ⟨v, hv⟩ := exists_nfE8_of_mem x.2
      exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  simp

theorem finite_WE8 : Finite (WeylGroup Tag.E8) :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8']
    norm_num)

noncomputable def QE8Sylow : Sylow 3 (WeylGroup Tag.E8) :=
  haveI := finite_WE8
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard QE8 (by
    rw [card_QE8, CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8',
      Nat.factorization_def _ Nat.prime_three]
    have : padicValNat 3 696729600 = 5 := by
      rw [show (696729600 : ℕ) = 3 ^ 5 * 2867200 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this])

theorem exists_conj_mem_QE8 (x : WeylGroup Tag.E8) (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ g : WeylGroup Tag.E8, g * x * g⁻¹ ∈ QE8 := by
  haveI := finite_WE8
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hx
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    show (x ^ n) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E8) QE8Sylow P
  have hxP : x ∈ (P : Subgroup (WeylGroup Tag.E8)) := hP' (Subgroup.mem_zpowers x)
  rw [← hg] at hxP
  refine ⟨g⁻¹, ?_⟩
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hxP
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hxP
  have hx' : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [inv_inv, hx']
  exact hs

@[expose] def e8n7 : Fin Tag.E8.rank := ⟨7, by decide⟩

theorem fix_pow_smul_E8 {w : WeylGroup Tag.E8} {x : Fin Tag.E8.rank → ℤ} (h : w • x = x)
    (n : ℕ) : w ^ n • x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

theorem gens_fix_e8n7 :
    wc1 • (Pi.single e8n7 1 : Fin Tag.E8.rank → ℤ) = Pi.single e8n7 1 ∧
      wc2 • (Pi.single e8n7 1 : Fin Tag.E8.rank → ℤ) = Pi.single e8n7 1 ∧
      wc3 • (Pi.single e8n7 1 : Fin Tag.E8.rank → ℤ) = Pi.single e8n7 1 ∧
      wpi • (Pi.single e8n7 1 : Fin Tag.E8.rank → ℤ) = Pi.single e8n7 1 := by
  simp only [wc1, wc2, wc3, wpi, wordW_smul_foldr_E8]
  decide +kernel

theorem nfE8_fix_of_zero {v : Fin 5 → Fin 3} (h0 : v 0 = 0) :
    nfE8 v • (Pi.single e8n7 1 : Fin Tag.E8.rank → ℤ) = Pi.single e8n7 1 := by
  obtain ⟨h1, h2, h3, hp⟩ := gens_fix_e8n7
  simp only [nfE8, nfN, h0, Fin.val_zero, pow_zero, one_mul, mul_smul, fix_pow_smul_E8 hp,
    fix_pow_smul_E8 h3, fix_pow_smul_E8 h2, fix_pow_smul_E8 h1]

@[expose] def actX (x : Fin 4 → Fin 3) (u : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  (mulVec8 Mc1E8)^[(x 0 : ℕ)] ((mulVec8 Mc2E8)^[(x 1 : ℕ)] ((mulVec8 Mc3E8)^[(x 2 : ℕ)]
    ((mulVec8 MpiE8)^[(x 3 : ℕ)] u)))

@[expose] def xPartE8 (v : Fin 5 → Fin 3) : Fin 4 → Fin 3 := ![v 1, v 2, v 3, v 4]

theorem actE8_eq (v : Fin 5 → Fin 3) (u : Fin Tag.E8.rank → ℤ) :
    actE8 v u = (mulVec8 Mc4E8)^[(v 0 : ℕ)] (actX (xPartE8 v) u) := rfl

@[expose] def IsListedRootE8 (u : Fin Tag.E8.rank → ℤ) : Prop :=
  ∃ k < Tag.E8.rootCertificate.roots.length, Tag.E8.rootCertificate.root k = u

instance (u : Fin Tag.E8.rank → ℤ) : Decidable (IsListedRootE8 u) := by
  unfold IsListedRootE8
  infer_instance

theorem isRoot_of_listed {u : Fin Tag.E8.rank → ℤ} (h : IsListedRootE8 u) : IsRoot Tag.E8 u :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)).2 h

@[expose] def goodXE8 : List ((Fin 4 → Fin 3) × (Fin Tag.E8.rank → ℤ)) :=
  [(![0, 0, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![0, 0, 0, 1], ![-1, -1, -2, -2, -2, -1, 0, 0]),
    (![0, 0, 0, 2], ![-1, -1, -2, -2, -2, -1, 0, 0]),
    (![0, 0, 1, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 0, 2, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 1, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![0, 1, 1, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 1, 2, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 1, 2, 1], ![-1, -1, -2, -2, -1, -1, 0, 0]),
    (![0, 1, 2, 2], ![0, -1, -1, -2, -1, -1, 0, 0]),
    (![0, 2, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![0, 2, 1, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 2, 1, 1], ![-1, -1, -2, -2, -1, 0, 0, 0]),
    (![0, 2, 1, 2], ![-1, -1, -1, -2, -1, 0, 0, 0]),
    (![0, 2, 2, 0], ![-1, 0, -1, 0, 0, 0, 0, 0]),
    (![1, 0, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![1, 0, 1, 0], ![0, 0, 0, 0, -1, -1, 0, 0]),
    (![1, 0, 2, 0], ![0, 0, 0, 0, -1, -1, 0, 0]),
    (![1, 0, 2, 1], ![0, -1, -1, -2, -1, -1, 0, 0]),
    (![1, 0, 2, 2], ![0, -1, -1, -2, -2, -1, 0, 0]),
    (![1, 1, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![1, 1, 1, 1], ![0, -1, -1, -2, -1, 0, 0, 0]),
    (![1, 1, 1, 2], ![-1, -1, -1, -2, -1, -1, 0, 0]),
    (![1, 2, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![1, 2, 0, 1], ![0, -1, -1, -2, -2, -1, 0, 0]),
    (![1, 2, 0, 2], ![-1, -1, -2, -2, -1, 0, 0, 0]),
    (![2, 0, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![2, 0, 1, 0], ![0, 0, 0, 0, -1, -1, 0, 0]),
    (![2, 0, 1, 1], ![-1, -1, -1, -2, -1, 0, 0, 0]),
    (![2, 0, 1, 2], ![-1, -1, -1, -2, -2, -1, 0, 0]),
    (![2, 0, 2, 0], ![0, 0, 0, 0, -1, -1, 0, 0]),
    (![2, 1, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![2, 1, 0, 1], ![-1, -1, -1, -2, -2, -1, 0, 0]),
    (![2, 1, 0, 2], ![-1, -1, -2, -2, -1, -1, 0, 0]),
    (![2, 2, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0]),
    (![2, 2, 2, 1], ![-1, -1, -1, -2, -1, -1, 0, 0]),
    (![2, 2, 2, 2], ![0, -1, -1, -2, -1, 0, 0, 0])]

theorem goodXE8_spec : ∀ p ∈ goodXE8, actX p.1 p.2 = p.2 ∧ mulVec8 Mc4E8 p.2 = p.2 ∧
    IsListedRootE8 p.2 := by
  decide +kernel

theorem nfE8_fix_of_good {v : Fin 5 → Fin 3} {p : (Fin 4 → Fin 3) × (Fin Tag.E8.rank → ℤ)}
    (hp : p ∈ goodXE8) (hpv : p.1 = xPartE8 v) : nfE8 v • p.2 = p.2 ∧ IsRoot Tag.E8 p.2 := by
  obtain ⟨h1, h2, h3⟩ := goodXE8_spec p hp
  refine ⟨?_, isRoot_of_listed h3⟩
  rw [nfE8_smul, actE8_eq, ← hpv, h1]
  exact Function.iterate_fixed h2 _

@[expose] def colE8 (v : Fin 5 → Fin 3) (m : Fin Tag.E8.rank) : Fin Tag.E8.rank → ℤ :=
  actE8 v (Pi.single m 1)

@[expose] def sum8 (f : Fin Tag.E8.rank → ZMod 3) : ZMod 3 :=
  f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
    f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩

theorem sum8_eq (f : Fin Tag.E8.rank → ZMod 3) : sum8 f = ∑ m, f m := (sum_fin_E8 f).symm

@[expose] def CertE8 {k : ℕ} (v : Fin 5 → Fin 3) (f : Fin k → Fin Tag.E8.rank)
    (C : Fin Tag.E8.rank → Fin k → ZMod 3) (Λ : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3) :
    Prop :=
  ∀ i j : Fin Tag.E8.rank,
    ((if i = j then 1 else 0 : ZMod 3) - ∑ l, C i l * (if f l = j then 1 else 0)) =
      sum8 fun m => Λ i m * (((colE8 v m j : ℤ) : ZMod 3) - (if m = j then 1 else 0))

instance {k : ℕ} (v : Fin 5 → Fin 3) (f : Fin k → Fin Tag.E8.rank)
    (C : Fin Tag.E8.rank → Fin k → ZMod 3) (Λ : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3) :
    Decidable (CertE8 v f C Λ) := by
  unfold CertE8
  infer_instance

@[expose] def rootFormE8 (C : Fin Tag.E8.rank → Fin 4 → ZMod 3) (α : Fin Tag.E8.rank → ℤ) :
    Fin 4 → ZMod 3 :=
  fun l => sum8 fun i => C i l * (α i : ZMod 3)

@[expose] def CovE8 (C : Fin Tag.E8.rank → Fin 4 → ZMod 3) : Prop :=
  ∀ φ : Fin 4 → ZMod 3, φ ≠ 0 → ∃ k < Tag.E8.rootCertificate.roots.length,
    rootFormE8 C (Tag.E8.rootCertificate.root k) = φ ∨
      rootFormE8 C (Tag.E8.rootCertificate.root k) = -φ

instance (C : Fin Tag.E8.rank → Fin 4 → ZMod 3) : Decidable (CovE8 C) := by
  unfold CovE8
  infer_instance

@[expose] def certs2E8 : List ((Fin 5 → Fin 3) × (Fin 2 → Fin Tag.E8.rank) × (Fin Tag.E8.rank → Fin 2 → ZMod 3) ×
    (Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3)) :=
  [(![1, 0, 0, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 2, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 1, 2, 1, 0, 1, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 0, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 2, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![1, 0, 0, 2, 1, 0, 1, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 0, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 2, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![2, 1, 0, 2, 0, 0, 0, 0], ![2, 1, 2, 1, 0, 0, 2, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 0, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 2, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![2, 1, 0, 2, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 2, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 0, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 1, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![1, 0, 2, 0, 2, 0, 1, 0], ![2, 1, 1, 2, 2, 0, 0, 0], ![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 0, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 1, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 2, 0, 1, 0], ![2, 1, 1, 2, 2, 0, 0, 0], ![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 0, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 1, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![1, 1, 2, 1, 2, 0, 0, 0], ![0, 1, 0, 2, 1, 0, 2, 0], ![1, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 0, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 1, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![1, 1, 2, 1, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 2, 0], ![1, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 1, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 2, 0, 0, 0], ![2, 1, 0, 2, 0, 0, 0, 0], ![1, 1, 0, 1, 2, 0, 1, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 1, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 2, 1, 0, 0, 0], ![2, 0, 0, 1, 2, 0, 0, 0], ![2, 1, 0, 2, 0, 0, 0, 0], ![2, 1, 2, 1, 2, 0, 1, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 1, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 2, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 2, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 1, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 2, 1, 0, 0, 0], ![1, 0, 0, 1, 2, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 1, 0, 2, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 1, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![1, 1, 0, 1, 2, 0, 1, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 1, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![2, 1, 2, 1, 2, 0, 1, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 1, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 1, 0, 0, 0], ![0, 2, 0, 2, 0, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![1, 0, 1, 1, 2, 0, 2, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 1, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 1, 0, 0, 0], ![0, 2, 0, 2, 0, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![2, 0, 0, 1, 2, 0, 2, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 2, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 1, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 1, 2, 0, 0, 0], ![2, 1, 1, 2, 0, 0, 1, 0], ![2, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 2, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 1, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 1, 2, 0, 0, 0], ![0, 1, 0, 2, 0, 0, 1, 0], ![2, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 2, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 1, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 1, 2, 0, 0, 0], ![0, 0, 2, 0, 2, 0, 2, 0], ![2, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 2, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 1, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 1, 2, 0, 0, 0], ![1, 0, 1, 0, 2, 0, 2, 0], ![2, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 2, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![1, 0, 2, 0, 2, 0, 1, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 2, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 1, 0, 2, 0, 1, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 0, 2, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 2, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 0, 2, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0], ![2, 1, 2, 0, 0, 0, 2, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 0, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 2, 0, 0, 0], ![1, 0, 0, 1, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![0, 2, 0, 0, 2, 0, 1, 0], ![2, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 0, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 2, 0, 0, 0], ![1, 0, 0, 1, 2, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 0, 2, 0, 1, 0], ![2, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 0, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 2, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 0, 0, 0, 2, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 0, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 2, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![2, 2, 0, 2, 1, 0, 0, 0], ![2, 2, 1, 0, 0, 0, 2, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 0, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 1, 2, 0, 0, 0], ![0, 2, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 2, 0, 0, 1, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 0, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 1, 2, 0, 0, 0], ![0, 2, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 1, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 0, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 0, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![1, 2, 2, 0, 0, 0, 2, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 0, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 0, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![2, 2, 1, 0, 0, 0, 2, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 1, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 2, 0, 0, 2, 0, 1, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![1, 2, 2, 0, 2, 0, 1, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 1, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 0, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 2, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 0, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 0, 0, 2, 1, 0, 2, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 1, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 1, 0, 2, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 1, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 2, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 2, 0], ![2, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 2, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![2, 2, 2, 1, 1, 0, 2, 0], ![2, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![2, 1, 0, 1, 2, 0, 1, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![0, 1, 2, 1, 2, 0, 1, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 2, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 1, 1, 2, 0, 0, 2, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 2, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![1, 1, 0, 2, 0, 0, 2, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 1, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![2, 1, 0, 1, 2, 0, 1, 0], ![1, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 2, 0, 1, 1, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![0, 1, 2, 1, 2, 0, 1, 0], ![1, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 2, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![2, 2, 2, 1, 1, 0, 2, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![2, 2, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 0, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 1, 2, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![1, 2, 1, 1, 0, 0, 1, 0], ![0, 0, 0, 2, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 0, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 1, 2, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 2, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 0, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 1, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 2, 0], ![2, 1, 1, 2, 2, 0, 0, 0], ![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 0, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 1, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0], ![0, 2, 2, 1, 1, 0, 2, 0], ![2, 1, 1, 2, 2, 0, 0, 0], ![1, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 0, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![2, 0, 2, 1, 1, 0, 1, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 0, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 2, 1, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 1, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 0, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![0, 1, 0, 2, 1, 0, 2, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 0, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 2, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0], ![2, 0, 2, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 0, 0, 0, 0], ![2, 0, 0, 1, 2, 0, 0, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![0, 2, 0, 0, 2, 0, 2, 0], ![1, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 2, 0, 0, 0, 0], ![2, 0, 0, 1, 2, 0, 0, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![1, 2, 2, 0, 2, 0, 2, 0], ![1, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 1, 0, 2, 1, 0, 1, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 2, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 1, 0], ![2, 1, 0, 2, 2, 0, 0, 0], ![2, 0, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 1, 2, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 0, 2, 0, 2, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 2, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 0, 0, 1, 2, 0, 0, 0], ![0, 2, 2, 2, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![1, 2, 2, 0, 2, 0, 2, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 0, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![2, 1, 1, 2, 0, 0, 1, 0], ![1, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 0, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![1, 1, 0, 2, 0, 0, 0, 0], ![1, 0, 2, 1, 2, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 0, 0], ![0, 1, 0, 2, 0, 0, 1, 0], ![1, 2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![2, 2, 0, 1, 1, 0, 2, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 0, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 2, 2, 2, 2, 0, 0, 0], ![0, 2, 2, 1, 1, 0, 2, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 1, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0], ![2, 2, 1, 1, 2, 0, 0, 0], ![0, 2, 2, 0, 0, 0, 1, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 1, 1], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![0, 1, 1, 1, 1, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0], ![2, 2, 1, 1, 2, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 1, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 1], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 1, 2, 0, 0, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 2, 2, 0, 2, 0], ![0, 0, 0, 2, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 1, 2], ![6, 7], ![![0, 0], ![0, 0], ![0, 0], ![0, 2], ![0, 0], ![0, 0], ![1, 0], ![0, 1]], ![![2, 2, 2, 1, 2, 0, 0, 0], ![0, 2, 0, 2, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 2, 2, 2, 0, 2, 0], ![0, 0, 0, 2, 2, 0, 0, 0], ![1, 2, 0, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]])]

@[expose] def certs4E8 : List ((Fin 5 → Fin 3) × (Fin 4 → Fin Tag.E8.rank) × (Fin Tag.E8.rank → Fin 4 → ZMod 3) ×
    (Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3)) :=
  [(![1, 1, 1, 1, 0], ![3, 5, 6, 7], ![![0, 2, 0, 2], ![0, 1, 0, 2], ![0, 2, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![1, 1, 0, 2, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 1, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 1, 0], ![3, 5, 6, 7], ![![0, 2, 0, 1], ![0, 1, 0, 1], ![0, 2, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 2, 0, 0, 1, 0], ![0, 2, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 1, 2, 0], ![3, 5, 6, 7], ![![0, 2, 0, 2], ![0, 2, 0, 1], ![0, 2, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![1, 1, 0, 2, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 2, 0], ![2, 1, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 1, 2, 0], ![3, 5, 6, 7], ![![0, 2, 0, 1], ![0, 2, 0, 2], ![0, 2, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 2, 0, 2, 0, 0, 1, 0], ![0, 2, 0, 0, 0, 0, 2, 0], ![1, 2, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 1, 0], ![3, 5, 6, 7], ![![0, 1, 0, 2], ![0, 2, 0, 2], ![0, 1, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 2, 0, 2, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 1, 0], ![1, 2, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 1, 0], ![3, 5, 6, 7], ![![0, 1, 0, 1], ![0, 2, 0, 1], ![0, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 1, 0, 2, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 1, 2, 2, 0], ![3, 5, 6, 7], ![![0, 1, 0, 2], ![0, 1, 0, 1], ![0, 1, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 2, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 2, 0], ![1, 0, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 1, 2, 2, 0], ![3, 5, 6, 7], ![![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 1, 0, 2, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 2, 0], ![0, 1, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 1, 0], ![3, 5, 6, 7], ![![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![1, 2, 0, 1, 0, 0, 2, 0], ![2, 0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 1, 0], ![3, 5, 6, 7], ![![0, 1, 0, 2], ![0, 1, 0, 1], ![0, 1, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 1, 0, 0, 2, 0], ![0, 2, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 1, 2, 0], ![3, 5, 6, 7], ![![0, 1, 0, 1], ![0, 2, 0, 1], ![0, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![1, 2, 0, 1, 0, 0, 2, 0], ![1, 0, 0, 0, 0, 0, 2, 0], ![0, 2, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 1, 2, 0], ![3, 5, 6, 7], ![![0, 1, 0, 2], ![0, 2, 0, 2], ![0, 1, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 1, 0, 0, 2, 0], ![0, 2, 0, 0, 0, 0, 2, 0], ![2, 1, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 1, 0], ![3, 5, 6, 7], ![![0, 2, 0, 1], ![0, 2, 0, 2], ![0, 2, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 1, 0, 0, 2, 0], ![0, 1, 0, 0, 0, 0, 1, 0], ![2, 1, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 1, 0], ![3, 5, 6, 7], ![![0, 2, 0, 2], ![0, 2, 0, 1], ![0, 2, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 2, 0, 1, 0, 0, 2, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![1, 2, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![1, 2, 2, 2, 0], ![3, 5, 6, 7], ![![0, 2, 0, 1], ![0, 1, 0, 1], ![0, 2, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 1, 0, 0, 2, 0], ![0, 1, 0, 0, 0, 0, 2, 0], ![2, 0, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]),
    (![2, 2, 2, 2, 0], ![3, 5, 6, 7], ![![0, 2, 0, 2], ![0, 1, 0, 2], ![0, 2, 0, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 2, 0, 1, 0, 0, 2, 0], ![2, 0, 0, 0, 0, 0, 2, 0], ![1, 2, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]])]

theorem certs2E8_ok : ∀ c ∈ certs2E8, CertE8 c.1 c.2.1 c.2.2.1 c.2.2.2 := by
  decide +kernel

theorem certs4E8_ok : ∀ c ∈ certs4E8, CertE8 c.1 c.2.1 c.2.2.1 c.2.2.2 ∧ CovE8 c.2.2.1 := by
  decide +kernel

theorem qcasesE8 : ∀ v : Fin 5 → Fin 3, v ≠ 0 → v 0 = 0 ∨ (∃ p ∈ goodXE8, p.1 = xPartE8 v) ∨
    (∃ c ∈ certs2E8, c.1 = v) ∨ (∃ c ∈ certs4E8, c.1 = v) := by
  decide +kernel

theorem fix_param_of_certE8 {k : ℕ} {v : Fin 5 → Fin 3} {f : Fin k → Fin Tag.E8.rank}
    {C : Fin Tag.E8.rank → Fin k → ZMod 3} {Λ : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3}
    (h : CertE8 v f C Λ) {z : Fin Tag.E8.rank → ZMod 3} (hz : nfE8 v ∈ dualWeylStabilizer z)
    (i : Fin Tag.E8.rank) : z i = ∑ l, C i l * z (f l) := by
  classical
  have hcol : ∀ m, ∑ j, ((colE8 v m j : ℤ) : ZMod 3) * z j = z m := by
    intro m
    have h1 := hz (Pi.single m 1)
    rw [nfE8_smul,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.charVal_single'] at h1
    exact h1
  have e : ∀ j, ((if i = j then 1 else 0 : ZMod 3) - ∑ l, C i l * (if f l = j then 1 else 0)) *
      z j = ∑ m, Λ i m * ((((colE8 v m j : ℤ) : ZMod 3) * z j) - (if m = j then z j else 0)) := by
    intro j
    rw [h i j, sum8_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  have key : ∑ j, ((if i = j then 1 else 0 : ZMod 3) -
      ∑ l, C i l * (if f l = j then 1 else 0)) * z j = 0 := by
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcol m, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ _), sub_self, mul_zero]
  have e2 : ∑ j, ((if i = j then 1 else 0 : ZMod 3) -
      ∑ l, C i l * (if f l = j then 1 else 0)) * z j = z i - ∑ l, C i l * z (f l) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [e2] at key
  exact sub_eq_zero.1 key

theorem card_fix_le_of_cert2E8 {v : Fin 5 → Fin 3} {f : Fin 2 → Fin Tag.E8.rank}
    {C : Fin Tag.E8.rank → Fin 2 → ZMod 3} {Λ : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3}
    (h : CertE8 v f C Λ) :
    Nat.card {z : Fin Tag.E8.rank → ZMod 3 // nfE8 v ∈ dualWeylStabilizer z} ≤ 9 := by
  classical
  have hinj : Function.Injective
      (fun z : {z : Fin Tag.E8.rank → ZMod 3 // nfE8 v ∈ dualWeylStabilizer z} =>
        fun l : Fin 2 => z.1 (f l)) := by
    intro z z' hzz
    apply Subtype.ext
    funext i
    rw [fix_param_of_certE8 h z.2 i, fix_param_of_certE8 h z'.2 i]
    exact Finset.sum_congr rfl fun l _ => by rw [show z.1 (f l) = z'.1 (f l) from congrFun hzz l]
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Fin 2 → ZMod 3) = 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  omega

theorem noRegTriple_of_cert4E8 {v : Fin 5 → Fin 3} {f : Fin 4 → Fin Tag.E8.rank}
    {C : Fin Tag.E8.rank → Fin 4 → ZMod 3} {Λ : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 3}
    (h : CertE8 v f C Λ) (hcov : CovE8 C) {z₁ z₂ z₃ : Fin Tag.E8.rank → ZMod 3}
    (h₁ : nfE8 v ∈ dualWeylStabilizer z₁) (h₂ : nfE8 v ∈ dualWeylStabilizer z₂)
    (h₃ : nfE8 v ∈ dualWeylStabilizer z₃) :
    ∃ α, IsRoot Tag.E8 α ∧ charVal z₁ α = 0 ∧ charVal z₂ α = 0 ∧ charVal z₃ α = 0 := by
  classical
  have hform : ∀ z, nfE8 v ∈ dualWeylStabilizer z → ∀ α : Fin Tag.E8.rank → ℤ,
      charVal z α = ∑ l, z (f l) * rootFormE8 C α l := by
    intro z hz α
    simp only [charVal, rootFormE8, sum8_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fix_param_of_certE8 h hz i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  let Φ : (Fin 4 → ZMod 3) → ZMod 3 × ZMod 3 × ZMod 3 := fun φ =>
    (∑ l, φ l * z₁ (f l), ∑ l, φ l * z₂ (f l), ∑ l, φ l * z₃ (f l))
  obtain ⟨φ, φ', hne, hΦ⟩ := Fintype.exists_ne_map_eq_of_card_lt Φ (by
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num)
  have hψ : φ - φ' ≠ 0 := sub_ne_zero.2 hne
  have hsub : ∀ z : Fin Tag.E8.rank → ZMod 3, ∑ l, φ l * z (f l) = ∑ l, φ' l * z (f l) →
      ∑ l, (φ - φ') l * z (f l) = 0 := by
    intro z hz
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hz, sub_self]
  have hz1 := hsub z₁ (congrArg Prod.fst hΦ)
  have hz2 := hsub z₂ (congrArg (fun t => t.2.1) hΦ)
  have hz3 := hsub z₃ (congrArg (fun t => t.2.2) hΦ)
  obtain ⟨kk, hkk, hαψ⟩ := hcov (φ - φ') hψ
  set α := Tag.E8.rootCertificate.root kk with hαdef
  have hα : IsRoot Tag.E8 α := isRoot_of_listed ⟨kk, hkk, rfl⟩
  have hval : ∀ z : Fin Tag.E8.rank → ZMod 3, nfE8 v ∈ dualWeylStabilizer z →
      ∑ l, (φ - φ') l * z (f l) = 0 → charVal z α = 0 := by
    intro z hz hz0
    rw [hform z hz α]
    rcases hαψ with e | e
    · rw [e]
      simpa [mul_comm] using hz0
    · rw [e]
      have : ∑ l, z (f l) * (-(φ - φ')) l = -∑ l, (φ - φ') l * z (f l) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.neg_apply]
        ring
      rw [this, hz0, neg_zero]
  exact ⟨α, hα, hval z₁ h₁ hz1, hval z₂ h₂ hz2, hval z₃ h₃ hz3⟩

theorem qgoodE8 (v : Fin 5 → Fin 3) (hv : v ≠ 0) :
    (∃ β, IsRoot Tag.E8 β ∧ (nfE8 v) • β = β) ∨
      Nat.card {z : Fin Tag.E8.rank → ZMod 3 // (nfE8 v) ∈ dualWeylStabilizer z} ≤ 9 ∨
      ∀ z₁ z₂ z₃ : Fin Tag.E8.rank → ZMod 3, (nfE8 v) ∈ dualWeylStabilizer z₁ → (nfE8 v) ∈ dualWeylStabilizer z₂ →
        (nfE8 v) ∈ dualWeylStabilizer z₃ →
          ∃ α, IsRoot Tag.E8 α ∧ charVal z₁ α = 0 ∧ charVal z₂ α = 0 ∧ charVal z₃ α = 0 := by
  rcases qcasesE8 v hv with h0 | ⟨p, hp, hpv⟩ | ⟨c, hc, hcv⟩ | ⟨c, hc, hcv⟩
  · exact Or.inl ⟨Pi.single e8n7 1, isRoot_single _ _, nfE8_fix_of_zero h0⟩
  · obtain ⟨h1, h2⟩ := nfE8_fix_of_good hp hpv
    exact Or.inl ⟨p.2, h2, h1⟩
  · rw [← hcv]
    exact Or.inr (Or.inl (card_fix_le_of_cert2E8 (certs2E8_ok c hc)))
  · obtain ⟨h1, h2⟩ := certs4E8_ok c hc
    rw [← hcv]
    exact Or.inr (Or.inr fun z₁ z₂ z₃ hz₁ hz₂ hz₃ => noRegTriple_of_cert4E8 h1 h2 hz₁ hz₂ hz₃)

end Aux

end E8Sylow

section E8Stab

open CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.PartOne.KE RootSpace

namespace Aux

theorem le_closure_of_le_inf3 {τ : Tag} {p : ℕ} [Fact p.Prime] (z₀ z₁ z₂ : Fin τ.rank → ZMod p)
    (H : Subgroup (WeylGroup τ))
    (hHU : H ≤ dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂)
    (hH : ¬ p ∣ Nat.card H) :
    H ≤ Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
      s = rootReflection α} := by
  classical
  have : Fintype H := Fintype.ofFinite _
  have hcard : (Fintype.card H : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card] at h
    exact hH h
  have hz : ∀ z : Fin τ.rank → ZMod p, H ≤ dualWeylStabilizer z →
      ∀ α, charVal (avgColumn H (intLift z)) α = 0 → charVal z α = 0 := by
    intro z hUz α h
    have h' := charVal_avgColumn_cast hUz α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact (mul_eq_zero.1 h').resolve_left hcard
  have hU0 : H ≤ dualWeylStabilizer z₀ := hHU.trans (inf_le_left.trans inf_le_left)
  have hU1 : H ≤ dualWeylStabilizer z₁ := hHU.trans (inf_le_left.trans inf_le_right)
  have hU2 : H ≤ dualWeylStabilizer z₂ := hHU.trans inf_le_right
  intro w hw
  have hwinv : w⁻¹ ∈ H := H.inv_mem hw
  have hfix : w ∈ weylStabilizer τ (dualVector (avgColumn H (intLift z₀)) +
      Real.sqrt 2 • dualVector (avgColumn H (intLift z₁)) +
      Real.sqrt 3 • dualVector (avgColumn H (intLift z₂))) := by
    rw [mem_weylStabilizer, map_add, map_add, map_smul, map_smul,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_ofLattice_dualVector, inner_ofLattice_dualVector, inner_ofLattice_dualVector] at h0
  obtain ⟨h0', h1', h2'⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3.int_eq_zero_of_add_sqrt_two_sqrt_three h0
  exact ⟨α, ⟨⟨⟨hα, hz z₀ hU0 α h0'⟩, ⟨hα, hz z₁ hU1 α h1'⟩⟩, ⟨hα, hz z₂ hU2 α h2'⟩⟩, rfl⟩

end Aux

theorem e8_cube_stab_fixes_root {L : Type} [Field L] (A : Subgroup (Fin Tag.E8.rank → Lˣ))
    (hA : Nat.card A = 3 ^ 3) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hreg : ∀ α, IsRoot Tag.E8 α → ∃ a ∈ A, rootChar a α ≠ 1)
    {y : WeylGroup Tag.E8} (hy : ∀ a ∈ A, ∀ v, rootChar a (y • v) = rootChar a v) (hy1 : y ≠ 1) :
    ∃ β, IsRoot Tag.E8 β ∧ y • β = β := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  haveI := Aux.finite_WE8
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hA
    norm_num at hA
  obtain ⟨i₀, hi₀⟩ : ∃ i, a₀ i ≠ 1 := by
    by_contra h
    push Not at h
    exact ha₀1 (funext h)
  have hζ : orderOf (a₀ i₀) = 3 :=
    orderOf_eq_prime (by simpa using congrFun (hA3 a₀ ha₀A) i₀) hi₀
  have hexp : ∀ a : Fin Tag.E8.rank → Lˣ, ∃ e : Fin Tag.E8.rank → ℕ,
      a ∈ A → ∀ i, a i = a₀ i₀ ^ e i := by
    intro a
    by_cases ha : a ∈ A
    · have : ∀ i, ∃ n : ℕ, a i = a₀ i₀ ^ n := fun i =>
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.exists_pow_eq_of_pow_three
          hζ (by simpa using congrFun (hA3 a ha) i)
      choose e he using this
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose e he using hexp
  set col : (Fin Tag.E8.rank → Lˣ) → Fin Tag.E8.rank → ZMod 3 := fun a i => (e a i : ZMod 3)
    with hcol
  have hchar : ∀ a ∈ A, ∀ l l' : Fin Tag.E8.rank → ℤ,
      rootChar a l = rootChar a l' ↔ charVal (col a) l = charVal (col a) l' :=
    fun a ha l l' => rootChar_eq_rootChar_iff hζ (e a) a (he a ha) l l'
  obtain ⟨a1, ha1, a2, ha2, a3, ha3, hgen⟩ :=
    SeitzExcOpenRest3.exists_three_gen_of_card_cube Nat.prime_three A hA hA3
  have hcl : ∀ H : Subgroup (Fin Tag.E8.rank → Lˣ), a1 ∈ H → a2 ∈ H → a3 ∈ H → A ≤ H := by
    intro H h1 h2 h3
    rw [hgen]
    exact (Subgroup.closure_le H).2 (by rintro _ (rfl | rfl | rfl) <;> assumption)
  set U := dualWeylStabilizer (col a1) ⊓ dualWeylStabilizer (col a2) ⊓
    dualWeylStabilizer (col a3) with hUdef
  have hk : ∀ α, ∀ b ∈ A, charVal (col b) α = 0 → b ∈ (rootCharHom (L := L) α).ker := by
    intro α b hb hz
    show rootChar b α = 1
    have := (hchar b hb α 0).2 (by rw [hz]; simp [charVal])
    rwa [rootChar_zero] at this
  have hempty : {s | ∃ α ∈ rootKernel (col a1) ∩ rootKernel (col a2) ∩ rootKernel (col a3),
      s = rootReflection α} = (∅ : Set (WeylGroup Tag.E8)) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨α, ⟨⟨⟨hα, h1⟩, ⟨-, h2⟩⟩, ⟨-, h3'⟩⟩, -⟩
    obtain ⟨a, haA, hane⟩ := hreg α hα
    exact hane (hcl _ (hk α a1 ha1 h1) (hk α a2 ha2 h2) (hk α a3 ha3 h3') haA)
  have hprime : ∀ u ∈ U, ¬ 3 ∣ orderOf u → u = 1 := by
    intro u hu h3
    have hH : Subgroup.zpowers u ≤ U := (Subgroup.zpowers_le).2 hu
    have hcard : ¬ 3 ∣ Nat.card (Subgroup.zpowers u) := by rw [Nat.card_zpowers]; exact h3
    have hle := Aux.le_closure_of_le_inf3 (col a1) (col a2) (col a3) _ hH hcard
    rw [hempty, Subgroup.closure_empty] at hle
    exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers u))
  have hyU : y ∈ U := ⟨⟨fun v => (hchar a1 ha1 _ _).1 (hy a1 ha1 v),
    fun v => (hchar a2 ha2 _ _).1 (hy a2 ha2 v)⟩, fun v => (hchar a3 ha3 _ _).1 (hy a3 ha3 v)⟩
  have hord : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨k, m, hm3, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  have hy3 : y ^ 3 ^ k = 1 := by
    refine hprime _ (U.pow_mem hyU _) fun hd => hm3 ?_
    refine hd.trans (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  obtain ⟨g, hg⟩ := Aux.exists_conj_mem_QE8 y ⟨k, hy3⟩
  obtain ⟨v, hv⟩ := Aux.exists_nfE8_of_mem hg
  have hyv : y = g⁻¹ * Aux.nfE8 v * g := by
    rw [hv]
    group
  have hv0 : v ≠ 0 := by
    intro h0
    apply hy1
    have h1 : Aux.nfE8 v = 1 := by
      rw [h0]
      simp [Aux.nfE8, Aux.nfN]
    rw [hyv, h1]
    group
  let T : (Fin Tag.E8.rank → ZMod 3) → Fin Tag.E8.rank → ZMod 3 :=
    fun z k => charVal z (g⁻¹ • (Pi.single k 1 : Fin Tag.E8.rank → ℤ))
  have hT : ∀ z (x : Fin Tag.E8.rank → ℤ), charVal (T z) x = charVal z (g⁻¹ • x) := by
    intro z x
    rw [charVal_smul_eq_sum z g⁻¹ x]
    rfl
  have hTfix : ∀ a ∈ A, Aux.nfE8 v ∈ dualWeylStabilizer (T (col a)) := by
    intro a ha x
    rw [hT, hT]
    have e1 : g⁻¹ • (Aux.nfE8 v • x) = y • (g⁻¹ • x) := by
      rw [hyv, mul_smul, mul_smul, smul_inv_smul]
    rw [e1]
    exact (hchar a ha _ _).1 (hy a ha (g⁻¹ • x))
  rcases Aux.qgoodE8 v hv0 with ⟨β, hβ, hβfix⟩ | hcard | hnoreg
  · refine ⟨g⁻¹ • β, CFSG.LieType.Chevalley.IsRoot.smul hβ _, ?_⟩
    rw [hyv, mul_smul, mul_smul, smul_inv_smul, hβfix]
  · exfalso
    have hinj : Function.Injective (fun a : A =>
        (⟨T (col a), hTfix a a.2⟩ :
          {z : Fin Tag.E8.rank → ZMod 3 // Aux.nfE8 v ∈ dualWeylStabilizer z})) := by
      intro a b hab
      have h1 : T (col a) = T (col b) := congrArg Subtype.val hab
      have h2 : col a = col b := by
        funext i
        have := congrArg (fun z => charVal z (g • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))) h1
        simp only [hT, inv_smul_smul,
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.charVal_single']
          at this
        exact this
      apply Subtype.ext
      funext i
      rw [he a a.2 i, he b b.2 i]
      have h3 : e a i % 3 = e b i % 3 :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).1 (congrFun h2 i)
      calc a₀ i₀ ^ e a i = a₀ i₀ ^ (e a i % orderOf (a₀ i₀)) := (pow_mod_orderOf _ _).symm
        _ = a₀ i₀ ^ (e b i % orderOf (a₀ i₀)) := by rw [hζ, h3]
        _ = a₀ i₀ ^ e b i := pow_mod_orderOf _ _
    have := Nat.card_le_card_of_injective _ hinj
    rw [hA] at this
    omega
  · exfalso
    obtain ⟨α, hα, h1, h2, h3⟩ := hnoreg _ _ _ (hTfix a1 ha1) (hTfix a2 ha2) (hTfix a3 ha3)
    rw [hT] at h1 h2 h3
    obtain ⟨a, haA, hane⟩ := hreg (g⁻¹ • α) (CFSG.LieType.Chevalley.IsRoot.smul hα _)
    exact hane (hcl _ (hk _ a1 ha1 h1) (hk _ a2 ha2 h2) (hk _ a3 ha3 h3) haA)

end E8Stab

section FixedRoot

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Malle.SeitzCube

theorem normalizesRGroup_of_fixed_root_E8 {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup .E8 K)} (D : LangPlaneData .E8 K E₀)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) (hwβ : D.w • β = β) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (AlgebraicClosure K) D.w hβ
  rw [hwβ] at hεc
  let V : Subgroup (ModGL Tag.E8 (AlgebraicClosure K)) :=
    { carrier := {x | ∃ t, ε * D.Fr t = t ∧ x = D.g0 * pinnedX Tag.E8 _ β t * D.g0⁻¹}
      mul_mem' := by
        rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
        refine ⟨s + t, by rw [map_add, mul_add, hs, ht], ?_⟩
        rw [pinnedX_add]
        group
      one_mem' := ⟨0, by rw [map_zero, mul_zero], by rw [pinnedX_zero]; group⟩
      inv_mem' := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨-t, by rw [map_neg, mul_neg, ht], ?_⟩
        rw [← pinnedX_neg]
        group }
  have hmemV : ∀ x, x ∈ V ↔ ∃ t, ε * D.Fr t = t ∧ x = D.g0 * pinnedX Tag.E8 _ β t * D.g0⁻¹ :=
    fun x => Iff.rfl
  have hVF : ∀ x ∈ V, Units.map (entrywiseHom D.Fr) x = x := by
    rintro _ ⟨t, ht, rfl⟩
    rw [map_mul, map_mul, map_inv, D.hg0, units_map_entrywiseHom_pinnedX]
    have e := hεc (D.Fr t)
    rw [ht] at e
    calc D.g0 * canonicalRep (coxeterSystem Tag.E8) _ D.w * pinnedX Tag.E8 _ β (D.Fr t) *
          (D.g0 * canonicalRep (coxeterSystem Tag.E8) _ D.w)⁻¹ =
        D.g0 * (canonicalRep (coxeterSystem Tag.E8) _ D.w * pinnedX Tag.E8 _ β (D.Fr t) *
          (canonicalRep (coxeterSystem Tag.E8) _ D.w)⁻¹) * D.g0⁻¹ := by group
      _ = D.g0 * pinnedX Tag.E8 _ β t * D.g0⁻¹ := by rw [e]
  have hVC : ∀ x ∈ V, x ∈ adjointGroup Tag.E8 (AlgebraicClosure K) := by
    rintro _ ⟨t, -, rfl⟩
    exact mul_mem (mul_mem D.hg0C (pinnedX_mem_adjointGroup β t)) (inv_mem D.hg0C)
  have hVrat : ∀ x ∈ V, ∃ y : adjointGroup Tag.E8 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) = x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ :=
      Subgroup.mem_map.1 (mem_map_baseChange_of_frobenius_fixed_E8 D.Fr D.hFr (hVC x hx) (hVF x hx))
    exact ⟨⟨y, hy⟩, hyx⟩
  set R : Subgroup (adjointGroup Tag.E8 K) :=
    (V.comap (baseChangeGL (algebraMap K (AlgebraicClosure K)))).comap
      (adjointGroup Tag.E8 K).subtype with hRdef
  have hmemR : ∀ y : adjointGroup Tag.E8 K, y ∈ R ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) ∈ V := fun y => Iff.rfl
  have hnorm : ∀ x ∈ E₀, ∀ y ∈ R, D.c * x * D.c⁻¹ * y * (D.c * x * D.c⁻¹)⁻¹ ∈ R := by
    intro x hx y hy
    obtain ⟨t, ht, hty⟩ := (hmemR y).1 hy
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    have hdx : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * x * D.c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
          D.g0 * rootDiagUnit Tag.E8 a * D.g0⁻¹ := by
      rw [ha, diagMap_apply]
      group
    have hT := (mem_twistedTorusOf.1 (SeitzExcOpenRest5.diagMap_mem_twistedTorus D hx)).2
    rw [← ha, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hT
    have htw := (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm β
    rw [hwβ] at htw
    have hχ : D.Fr ((rootChar a β : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
        ((rootChar a β : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
      have h1 := map_rootChar D.Fr a β
      have h2 : D.Fr ((rootChar a β : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
          ((Units.map D.Fr.toMonoidHom (rootChar a β) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K) := rfl
      rw [h2, h1, ← htw]
    refine (hmemR _).2 ⟨(rootChar a β : AlgebraicClosure K) * t, ?_, ?_⟩
    · rw [map_mul, hχ, mul_left_comm, ht]
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hdx, hty,
        ← rootDiagUnit_conj_pinnedX a hβ]
      group
  refine ⟨R.map (MulAut.conj D.c⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  ·
    have hq2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ε (n := Nat.card K - 1) (by omega)
    have hε0 : ε ≠ 0 := fun h => by rw [h, zero_mul] at hε; exact zero_ne_one hε
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at ht
      exact hε0 ht.symm
    have hPt : ε * D.Fr t = t := by
      rw [D.hFr t, show Nat.card K = (Nat.card K - 1) + 1 by omega, pow_succ, ht, ← mul_assoc, hε,
        one_mul]
    obtain ⟨y, hy⟩ := hVrat _ ⟨t, hPt, rfl⟩
    have hyR : y ∈ R := (hmemR y).2 (hy ▸ ⟨t, hPt, rfl⟩)
    intro hbot
    have hmem : (MulAut.conj D.c⁻¹).toMonoidHom y ∈ R.map (MulAut.conj D.c⁻¹).toMonoidHom :=
      ⟨y, hyR, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hy1 : y = 1 := (MulAut.conj D.c⁻¹).injective (hmem.trans (map_one _).symm)
    rw [hy1, OneMemClass.coe_one, map_one] at hy
    have hX : pinnedX Tag.E8 (AlgebraicClosure K) β t = 1 := by
      have h1 : D.g0⁻¹ * (D.g0 * pinnedX Tag.E8 _ β t * D.g0⁻¹) * D.g0 = 1 := by
        rw [← hy]
        group
      rw [← h1]
      group
    apply ht0
    apply pinnedX_injective Tag.E8 (AlgebraicClosure K) β
    rw [hX, pinnedX_zero]
  ·
    refine IsPGroup.map (fun y => ⟨1, Subtype.ext ?_⟩) _
    obtain ⟨t, -, hty⟩ := (hmemR y.1).1 y.2
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, map_pow, hty, OneMemClass.coe_one,
      OneMemClass.coe_one, map_one, conj_pow, e8Split_pinnedX_pow, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul, pinnedX_zero]
    group
  ·
    intro x hx
    have hz : ∀ z ∈ E₀, R.map (MulAut.conj (D.c * z * D.c⁻¹)).toMonoidHom ≤ R := by
      rintro z hz _ ⟨y, hy, rfl⟩
      exact hnorm z hz y hy
    have heq : R.map (MulAut.conj (D.c * x * D.c⁻¹)).toMonoidHom = R := by
      refine le_antisymm (hz x hx) ?_
      intro y hy
      refine ⟨(D.c * x⁻¹ * D.c⁻¹) * y * (D.c * x⁻¹ * D.c⁻¹)⁻¹, hnorm x⁻¹ (inv_mem hx) y hy, ?_⟩
      show (D.c * x * D.c⁻¹) * ((D.c * x⁻¹ * D.c⁻¹) * y * (D.c * x⁻¹ * D.c⁻¹)⁻¹) *
        (D.c * x * D.c⁻¹)⁻¹ = y
      group
    calc (R.map (MulAut.conj D.c⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom
        = (R.map (MulAut.conj (D.c * x * D.c⁻¹)).toMonoidHom).map
            (MulAut.conj D.c⁻¹).toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
          ext y
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      _ = R.map (MulAut.conj D.c⁻¹).toMonoidHom := by rw [heq]

end FixedRoot

section E8One

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem e8_regular_datum_fixes_root {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E8 K E₀) (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) (hw : D.w ≠ 1) :
    ∃ β, IsRoot Tag.E8 β ∧ D.w • β = β := by
  classical
  set A : Subgroup (Fin Tag.E8.rank → (AlgebraicClosure K)ˣ) :=
    (E₀.map (diagMap D)).comap (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) with hAdef
  have hinj : Function.Injective (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hrange : E₀.map (diagMap D) ≤ (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    exact ⟨a, ha⟩
  have hAmap : A.map (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) = E₀.map (diagMap D) :=
    Subgroup.map_comap_eq_self hrange
  have hA : Nat.card A = 3 ^ 3 := by
    rw [← Subgroup.card_map_of_injective hinj, hAmap,
      Subgroup.card_map_of_injective (diagMap_injective D), hc]
  have hmemA : ∀ a, a ∈ A ↔ ∃ x ∈ E₀, diagMap D x = rootDiagUnit Tag.E8 a := fun a =>
    Subgroup.mem_comap.trans Subgroup.mem_map
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := (hmemA a).1 ha
    apply hinj
    rw [map_pow, map_one]
    show rootDiagUnit Tag.E8 a ^ 3 = 1
    rw [← hxa, ← map_pow, hE₀.2 x hx, map_one]
  have hreg' : ∀ α, IsRoot Tag.E8 α → ∃ a ∈ A, rootChar a α ≠ 1 := by
    intro α hα
    by_contra h
    push Not at h
    apply hreg α hα
    intro x hx
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    exact ⟨a, by rw [ha, diagMap_apply], h a ((hmemA a).2 ⟨x, hx, ha.symm⟩)⟩
  have htw : ∀ a ∈ A, ∀ v, rootChar a (D.w • v) =
      rootChar (fun i => Units.map D.Fr.toMonoidHom (a i)) v := by
    intro a ha v
    obtain ⟨x, hx, hxa⟩ := (hmemA a).1 ha
    have hT := (mem_twistedTorusOf.1 (SeitzExcOpenRest5.diagMap_mem_twistedTorus D hx)).2
    rw [hxa, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hT
    exact (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm v
  have hFa : ∀ a ∈ A, (fun i => Units.map D.Fr.toMonoidHom (a i)) = a := by
    intro a ha
    funext i
    have e : Units.map D.Fr.toMonoidHom (a i) = a i ^ Nat.card K := Units.ext (by simp [D.hFr])
    rw [e, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5.Aux.pow_mod_three_of_cube
      (by simpa using congrFun (hA3 a ha) i), hK, pow_one]
  exact e8_cube_stab_fixes_root A hA hA3 hreg' (fun a ha v => by rw [htw a ha v, hFa a ha]) hw

theorem normalizesRGroup_E8_toral_of_mod_three_eq_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 1) {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) : NormalizesRGroup (ringChar K) E₀ := by
  by_cases hw : D.w = 1
  · exact SeitzExcOpenRest5.normalizesRGroup_of_native' (e8_normalizesRNative_of_split_datum D hw)
  · obtain ⟨β, hβ, hwβ⟩ := e8_regular_datum_fixes_root hK hE₀ hc D hreg hw
    exact normalizesRGroup_of_fixed_root_E8 D hβ hwβ

end E8One

section Residual

@[expose] def E7ToralNegCRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E7 K E₀,
        (∀ α : Fin Tag.E7.rank → ℤ, IsRoot .E7 α → ¬ D.Kills α) →
        (∃ u : Fin Tag.E7.rank → ℤ, D.w • u ≠ -u) → HyperGen 3 ⊤ E₀

@[expose] def E8ToralNegTwistRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E8 K →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E8 K E₀,
        (∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α → ¬ D.Kills α) → D.w ≠ 1 →
        (∃ u : Fin Tag.E8.rank → ℤ, D.w • u ≠ -u) → HyperGen 3 ⊤ E₀

@[expose] def SeitzThreeResidual6 : Prop :=
  ThreeNonToralCubeRest .F4 LieTypeIndex.F4 ∧
    SeitzGoodInnerExcThreeE6 ∧ SeitzGoodInnerExcThreeTwE6 ∧
    (E7ToralNegCRest ∧ E7NonToralTwoRest) ∧
    (E8ToralNegTwistRest ∧ ThreeNonToralCubeRest .E8 LieTypeIndex.E8)

end Residual

section Reduction

theorem seitzThreeResidual5_of_residual6 (h : SeitzThreeResidual6) : SeitzThreeResidual5 := by
  obtain ⟨hF4n, hE6, hTw, ⟨hE7t, hE7n⟩, ⟨hE8t, hE8n⟩⟩ := h
  refine ⟨hF4n, hE6, hTw, ⟨?_, hE7n⟩, ⟨?_, hE8n⟩⟩
  · intro K _ _ hK hs E₀ hE₀ hc hN D hreg
    by_cases hneg : ∀ u : Fin Tag.E7.rank → ℤ, D.w • u = -u
    · exact hyperGen_E7_of_neg_datum hK hs hE₀ hc D hneg
    · push Not at hneg
      exact hE7t K hK hs E₀ hE₀ hc hN D hreg hneg
  · intro K _ _ hK3 hs E₀ hE₀ hc hN D hreg hw hneg
    rcases mod_three_cases hK3 with h1 | h2
    · exact (hN (normalizesRGroup_E8_toral_of_mod_three_eq_one h1 hE₀ hc D hreg)).elim
    · exact hE8t K h2 hs E₀ hE₀ hc hN D hreg hw hneg

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

end
