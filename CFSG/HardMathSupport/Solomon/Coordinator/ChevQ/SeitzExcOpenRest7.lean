module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5
open CFSG.RankThree.E6 (charVal charVal_add charVal_neg charVal_smul)

open scoped Matrix

set_option linter.unusedSectionVars false

namespace SeitzExcOpenRest7Aux

section E7Sylow

open CFSG.HardMathSupport.Curtis.UnitaryLevi

theorem wordW_smul_foldr_E7 (l : List (Fin Tag.E7.rank)) (v : Fin Tag.E7.rank → ℤ) :
    wordW Tag.E7 l • v = l.foldr (reflect Tag.E7) v := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have e : wordW Tag.E7 (i :: l) = simple Tag.E7 i * wordW Tag.E7 l := by
      simp [wordW, List.prod_cons]
    rw [e, mul_smul, ih, simple_smul, List.foldr_cons]

theorem wordW_eq_of_foldr_E7 {l l' : List (Fin Tag.E7.rank)}
    (h : ∀ k : Fin Tag.E7.rank, l.foldr (reflect Tag.E7) (Pi.single k 1) =
      l'.foldr (reflect Tag.E7) (Pi.single k 1)) :
    wordW Tag.E7 l = wordW Tag.E7 l' :=
  ext_single fun k => by rw [wordW_smul_foldr_E7, wordW_smul_foldr_E7, h k]

@[expose] def e7lc1 : List (Fin Tag.E7.rank) := ([0, 2] : List (Fin 7))
@[expose] def e7lc2 : List (Fin Tag.E7.rank) := ([4, 5] : List (Fin 7))
@[expose] def e7lc3 : List (Fin Tag.E7.rank) :=
  ([3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1] : List (Fin 7))
@[expose] def e7lpi : List (Fin Tag.E7.rank) :=
  ([3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 1, 0] : List (Fin 7))

@[expose] def e7wc1 : WeylGroup Tag.E7 := wordW Tag.E7 e7lc1
@[expose] def e7wc2 : WeylGroup Tag.E7 := wordW Tag.E7 e7lc2
@[expose] def e7wc3 : WeylGroup Tag.E7 := wordW Tag.E7 e7lc3
@[expose] def e7wpi : WeylGroup Tag.E7 := wordW Tag.E7 e7lpi

theorem e7_cube_of_word {l : List (Fin Tag.E7.rank)}
    (h : ∀ k : Fin Tag.E7.rank, (l ++ l ++ l).foldr (reflect Tag.E7) (Pi.single k 1) =
      ([] : List (Fin Tag.E7.rank)).foldr (reflect Tag.E7) (Pi.single k 1)) :
    wordW Tag.E7 l ^ 3 = 1 := by
  have h1 := wordW_eq_of_foldr_E7 h
  rw [wordW_append, wordW_append] at h1
  rw [pow_three, ← mul_assoc, h1]
  simp [wordW]

theorem e7_mul_eq_of_word {l l' m m' : List (Fin Tag.E7.rank)}
    (h : ∀ k : Fin Tag.E7.rank, (l ++ l').foldr (reflect Tag.E7) (Pi.single k 1) =
      (m ++ m').foldr (reflect Tag.E7) (Pi.single k 1)) :
    wordW Tag.E7 l * wordW Tag.E7 l' = wordW Tag.E7 m * wordW Tag.E7 m' := by
  rw [← wordW_append, ← wordW_append]
  exact wordW_eq_of_foldr_E7 h

theorem e7wc1_cube : e7wc1 ^ 3 = 1 := e7_cube_of_word (by decide +kernel)
theorem e7wc2_cube : e7wc2 ^ 3 = 1 := e7_cube_of_word (by decide +kernel)
theorem e7wc3_cube : e7wc3 ^ 3 = 1 := e7_cube_of_word (by decide +kernel)
theorem e7wpi_cube : e7wpi ^ 3 = 1 := e7_cube_of_word (by decide +kernel)

theorem e7wc1_wc2 : Commute e7wc1 e7wc2 := e7_mul_eq_of_word (by decide +kernel)
theorem e7wc1_wc3 : Commute e7wc1 e7wc3 := e7_mul_eq_of_word (by decide +kernel)
theorem e7wc2_wc3 : Commute e7wc2 e7wc3 := e7_mul_eq_of_word (by decide +kernel)
theorem e7wpi_wc1 : SemiconjBy e7wpi e7wc1 e7wc2 := e7_mul_eq_of_word (by decide +kernel)
theorem e7wpi_wc2 : SemiconjBy e7wpi e7wc2 e7wc3 := e7_mul_eq_of_word (by decide +kernel)
theorem e7wpi_wc3 : SemiconjBy e7wpi e7wc3 e7wc1 := e7_mul_eq_of_word (by decide +kernel)

@[expose] def e7nfN (e₁ e₂ e₃ b : ℕ) : WeylGroup Tag.E7 :=
  e7wc1 ^ e₁ * e7wc2 ^ e₂ * e7wc3 ^ e₃ * e7wpi ^ b

@[expose] def QE7 : Subgroup (WeylGroup Tag.E7) := Subgroup.closure {e7wc1, e7wc2, e7wc3, e7wpi}

theorem e7_pow_succ_left (g : WeylGroup Tag.E7) (e : ℕ) (X : WeylGroup Tag.E7) :
    g * (g ^ e * X) = g ^ (e + 1) * X := by
  rw [← mul_assoc, ← pow_succ']

theorem e7_semiconj_step {x y z : WeylGroup Tag.E7} (h : SemiconjBy x y z) (e : ℕ)
    (X : WeylGroup Tag.E7) : x * (y ^ e * X) = z ^ e * (x * X) := by
  rw [← mul_assoc, (h.pow_right e).eq, mul_assoc]

theorem e7nfN_assoc (e₁ e₂ e₃ b : ℕ) :
    e7nfN e₁ e₂ e₃ b = e7wc1 ^ e₁ * (e7wc2 ^ e₂ * (e7wc3 ^ e₃ * e7wpi ^ b)) := by
  simp only [e7nfN, mul_assoc]

theorem e7nf_mul_left {g : WeylGroup Tag.E7}
    (hg : g ∈ ({e7wc1, e7wc2, e7wc3, e7wpi} : Set (WeylGroup Tag.E7))) (e₁ e₂ e₃ b : ℕ) :
    ∃ e₁' e₂' e₃' b' : ℕ, g * e7nfN e₁ e₂ e₃ b = e7nfN e₁' e₂' e₃' b' := by
  rcases hg with h | h | h | h <;> rw [h]
  · refine ⟨e₁ + 1, e₂, e₃, b, ?_⟩
    rw [e7nfN_assoc, e7nfN_assoc, e7_pow_succ_left]
  · refine ⟨e₁, e₂ + 1, e₃, b, ?_⟩
    rw [e7nfN_assoc, e7nfN_assoc, (e7wc1_wc2.symm.pow_right e₁).left_comm, e7_pow_succ_left]
  · refine ⟨e₁, e₂, e₃ + 1, b, ?_⟩
    rw [e7nfN_assoc, e7nfN_assoc, (e7wc1_wc3.symm.pow_right e₁).left_comm,
      (e7wc2_wc3.symm.pow_right e₂).left_comm, e7_pow_succ_left]
  · refine ⟨e₃, e₁, e₂, b + 1, ?_⟩
    rw [e7nfN_assoc, e7nfN_assoc, e7_semiconj_step e7wpi_wc1, e7_semiconj_step e7wpi_wc2,
      e7_semiconj_step e7wpi_wc3, ← pow_succ',
      ((e7wc1_wc3.pow_pow e₃ e₂).symm).left_comm, ((e7wc1_wc2.pow_pow e₃ e₁).symm).left_comm]

theorem e7_gen_cube {g : WeylGroup Tag.E7}
    (hg : g ∈ ({e7wc1, e7wc2, e7wc3, e7wpi} : Set (WeylGroup Tag.E7))) : g ^ 3 = 1 := by
  rcases hg with h | h | h | h <;> rw [h]
  · exact e7wc1_cube
  · exact e7wc2_cube
  · exact e7wc3_cube
  · exact e7wpi_cube

theorem exists_e7nfN_of_mem {x : WeylGroup Tag.E7} (hx : x ∈ QE7) :
    ∃ e₁ e₂ e₃ b : ℕ, x = e7nfN e₁ e₂ e₃ b := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, 0, 0, by simp [e7nfN]⟩
  | mul_left g hg y _ ih =>
    obtain ⟨e₁, e₂, e₃, b, hy⟩ := ih
    obtain ⟨e₁', e₂', e₃', b', h⟩ := e7nf_mul_left hg e₁ e₂ e₃ b
    exact ⟨e₁', e₂', e₃', b', by rw [hy, h]⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨e₁, e₂, e₃, b, hy⟩ := ih
    have hinv : g⁻¹ = g * g :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact e7_gen_cube hg)
    obtain ⟨e₁', e₂', e₃', b', h⟩ := e7nf_mul_left hg e₁ e₂ e₃ b
    obtain ⟨e₁'', e₂'', e₃'', b'', h'⟩ := e7nf_mul_left hg e₁' e₂' e₃' b'
    exact ⟨e₁'', e₂'', e₃'', b'', by rw [hy, hinv, mul_assoc, h, h']⟩

theorem e7nfN_mod (e₁ e₂ e₃ b : ℕ) :
    e7nfN e₁ e₂ e₃ b = e7nfN (e₁ % 3) (e₂ % 3) (e₃ % 3) (b % 3) := by
  simp only [e7nfN]
  rw [SeitzExcOpenRest5.Aux.pow_mod_three_of_cube e7wc1_cube e₁,
    SeitzExcOpenRest5.Aux.pow_mod_three_of_cube e7wc2_cube e₂,
    SeitzExcOpenRest5.Aux.pow_mod_three_of_cube e7wc3_cube e₃,
    SeitzExcOpenRest5.Aux.pow_mod_three_of_cube e7wpi_cube b]

@[expose] def nfE7 (v : Fin 4 → Fin 3) : WeylGroup Tag.E7 :=
  e7nfN (v 0 : ℕ) (v 1 : ℕ) (v 2 : ℕ) (v 3 : ℕ)

@[expose] def mulVec7 (M : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ) (u : Fin Tag.E7.rank → ℤ) :
    Fin Tag.E7.rank → ℤ := fun i =>
  M i ⟨0, by decide⟩ * u ⟨0, by decide⟩ + M i ⟨1, by decide⟩ * u ⟨1, by decide⟩ +
    M i ⟨2, by decide⟩ * u ⟨2, by decide⟩ + M i ⟨3, by decide⟩ * u ⟨3, by decide⟩ +
    M i ⟨4, by decide⟩ * u ⟨4, by decide⟩ + M i ⟨5, by decide⟩ * u ⟨5, by decide⟩ +
    M i ⟨6, by decide⟩ * u ⟨6, by decide⟩

theorem sum_fin_E7 {R : Type*} [AddCommMonoid R] (f : Fin Tag.E7.rank → R) :
    ∑ k, f k = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ := by
  have h : Tag.E7.rank = 7 := rfl
  rw [← Equiv.sum_comp (finCongr h).symm f, Fin.sum_univ_seven]
  rfl

theorem smul_eq_mulVec7 {g : WeylGroup Tag.E7} {M : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ}
    (hcol : ∀ k : Fin Tag.E7.rank, g • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = fun i => M i k)
    (u : Fin Tag.E7.rank → ℤ) : g • u = mulVec7 M u := by
  classical
  have hu : u = ∑ k, u k • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  ext i
  have h1 : (g • u) i = ∑ k, u k * M i k := by
    conv_lhs => rw [hu]
    rw [Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, hcol k, Pi.smul_apply, smul_eq_mul]
  rw [h1, sum_fin_E7]
  simp only [mulVec7]
  ring

theorem pow_smul_eq_iterate_E7 {g : WeylGroup Tag.E7} {M : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ}
    (h : ∀ u, g • u = mulVec7 M u) (n : ℕ) (u : Fin Tag.E7.rank → ℤ) :
    g ^ n • u = (mulVec7 M)^[n] u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, ih, Function.iterate_succ_apply]

@[expose] def Mc1E7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![0, 0, -1, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![1, 0, -1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1]]

@[expose] def Mc2E7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, -1, 1],
    ![0, 0, 0, 0, 1, -1, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

@[expose] def Mc3E7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![1, -1, 0, 0, 0, 0, 1],
    ![0, -2, 0, 1, 0, 0, 1],
    ![0, -2, 1, 0, 0, 0, 2],
    ![0, -3, 0, 1, 0, 0, 3],
    ![0, -2, 0, 0, 1, 0, 2],
    ![0, -1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

@[expose] def MpiE7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![0, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, -1, 1, 1, 0],
    ![0, 0, 0, -1, 2, 0, 0],
    ![0, 0, 0, -2, 3, 0, 1],
    ![0, 0, 1, -2, 2, 0, 1],
    ![-1, 0, 1, -1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

theorem Mc1E7_col : ∀ k : Fin Tag.E7.rank,
    e7wc1 • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = fun i => Mc1E7 i k := by
  intro k
  rw [e7wc1, wordW_smul_foldr_E7]
  revert k
  decide +kernel

theorem Mc2E7_col : ∀ k : Fin Tag.E7.rank,
    e7wc2 • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = fun i => Mc2E7 i k := by
  intro k
  rw [e7wc2, wordW_smul_foldr_E7]
  revert k
  decide +kernel

theorem Mc3E7_col : ∀ k : Fin Tag.E7.rank,
    e7wc3 • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = fun i => Mc3E7 i k := by
  intro k
  rw [e7wc3, wordW_smul_foldr_E7]
  revert k
  decide +kernel

theorem MpiE7_col : ∀ k : Fin Tag.E7.rank,
    e7wpi • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) = fun i => MpiE7 i k := by
  intro k
  rw [e7wpi, wordW_smul_foldr_E7]
  revert k
  decide +kernel

@[expose] def actE7 (v : Fin 4 → Fin 3) (u : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → ℤ :=
  (mulVec7 Mc1E7)^[(v 0 : ℕ)] ((mulVec7 Mc2E7)^[(v 1 : ℕ)] ((mulVec7 Mc3E7)^[(v 2 : ℕ)]
    ((mulVec7 MpiE7)^[(v 3 : ℕ)] u)))

theorem nfE7_smul (v : Fin 4 → Fin 3) (u : Fin Tag.E7.rank → ℤ) : nfE7 v • u = actE7 v u := by
  simp only [nfE7, e7nfN, actE7, mul_smul, pow_smul_eq_iterate_E7 (smul_eq_mulVec7 Mc1E7_col),
    pow_smul_eq_iterate_E7 (smul_eq_mulVec7 Mc2E7_col),
    pow_smul_eq_iterate_E7 (smul_eq_mulVec7 Mc3E7_col),
    pow_smul_eq_iterate_E7 (smul_eq_mulVec7 MpiE7_col)]

theorem nfE7_mem (v : Fin 4 → Fin 3) : nfE7 v ∈ QE7 := by
  have hm : ∀ g ∈ ({e7wc1, e7wc2, e7wc3, e7wpi} : Set (WeylGroup Tag.E7)), g ∈ QE7 :=
    fun g hg => Subgroup.subset_closure hg
  exact mul_mem (mul_mem (mul_mem (pow_mem (hm _ (by simp)) _) (pow_mem (hm _ (by simp)) _))
    (pow_mem (hm _ (by simp)) _)) (pow_mem (hm _ (by simp)) _)

theorem exists_nfE7_of_mem {x : WeylGroup Tag.E7} (hx : x ∈ QE7) : ∃ v, nfE7 v = x := by
  obtain ⟨e₁, e₂, e₃, b, hx'⟩ := exists_e7nfN_of_mem hx
  refine ⟨![⟨e₁ % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨e₂ % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨e₃ % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩], ?_⟩
  rw [hx', e7nfN_mod]
  rfl

@[expose] def keyVecE7 : Fin Tag.E7.rank → ℤ := ![-1, -1, -1, -1, -1, -1, 1]

@[expose] def decTableE7 : List (ℕ × ℕ) :=
  [(18773163503, 0), (18841353712, 27), (18807833137, 54), (18844667473, 9), (18912857714, 36), (18807833105, 63), (18808915536, 18), (18841353776, 45), (18843585106, 72), (18842369519, 3), (18807799280, 30), (18843484721, 57), (18913873489, 12), (18879303282, 39), (18843484689, 66), (18878121552, 21), (18807799344, 48), (18879236690, 75), (18840272367, 6), (18842402288, 33), (18875990577, 60), (18911776337, 15), (18913906290, 42), (18875990545, 69), (18876024400, 24), (18842402352, 51), (18911742546, 78), (18773163504, 1), (18841355761, 28), (18807835185, 55), (18844667474, 10), (18912859763, 37), (18807835153, 64), (18808915537, 19), (18841355825, 46), (18843587154, 73), (18842369520, 4), (18807801329, 31), (18843486769, 58), (18913873490, 13), (18879305331, 40), (18843486737, 67), (18878121553, 22), (18807801393, 49), (18879238738, 76), (18840272368, 7), (18842404337, 34), (18875992625, 61), (18911776338, 16), (18913908339, 43), (18875992593, 70), (18876024401, 25), (18842404401, 52), (18911744594, 79), (18773164528, 2), (18841354735, 29), (18807833135, 56), (18844668498, 11), (18912858737, 38), (18807833103, 65), (18808916561, 20), (18841354799, 47), (18843585104, 74), (18842370544, 5), (18807800303, 32), (18843484719, 59), (18913874514, 14), (18879304305, 41), (18843484687, 68), (18878122577, 23), (18807800367, 50), (18879236688, 77), (18840273392, 8), (18842403311, 35), (18875990575, 62), (18911777362, 17), (18913907313, 44), (18875990543, 71), (18876025425, 26), (18842403375, 53), (18911742544, 80)]

@[expose] def codeVecE7 (u : Fin Tag.E7.rank → ℤ) : ℕ :=
  (u 0 + 16).toNat + 32 * ((u 1 + 16).toNat + 32 * ((u 2 + 16).toNat + 32 * ((u 3 + 16).toNat +
    32 * ((u 4 + 16).toNat + 32 * ((u 5 + 16).toNat + 32 * (u 6 + 16).toNat)))))

@[expose] def vOfCodeE7 (n : ℕ) : Fin 4 → Fin 3 :=
  fun i => ⟨(n / 3 ^ (i : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩

@[expose] def decodeE7 (u : Fin Tag.E7.rank → ℤ) : Fin 4 → Fin 3 :=
  vOfCodeE7 (((decTableE7.find? fun p => p.1 == codeVecE7 u).map Prod.snd).getD 0)

theorem decodeE7_nf : ∀ v : Fin 4 → Fin 3, decodeE7 (actE7 v keyVecE7) = v := by
  decide +kernel

theorem nfE7_injective : Function.Injective nfE7 := by
  intro v w h
  have h' : actE7 v keyVecE7 = actE7 w keyVecE7 := by
    rw [← nfE7_smul, ← nfE7_smul, h]
  rw [← decodeE7_nf v, ← decodeE7_nf w, h']

theorem card_QE7 : Nat.card QE7 = 3 ^ 4 := by
  have hbij : Function.Bijective (fun v : Fin 4 → Fin 3 => (⟨nfE7 v, nfE7_mem v⟩ : QE7)) := by
    refine ⟨fun v w h => ?_, fun x => ?_⟩
    · simp only [Subtype.mk.injEq] at h
      exact nfE7_injective h
    · obtain ⟨v, hv⟩ := exists_nfE7_of_mem x.2
      exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  simp

theorem finite_WE7 : Finite (WeylGroup Tag.E7) :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7']
    norm_num)

noncomputable def QE7Sylow : Sylow 3 (WeylGroup Tag.E7) :=
  haveI := finite_WE7
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard QE7 (by
    rw [card_QE7, CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7',
      Nat.factorization_def _ Nat.prime_three]
    have : padicValNat 3 2903040 = 4 := by
      rw [show (2903040 : ℕ) = 3 ^ 4 * 35840 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this])

theorem exists_conj_mem_QE7 (x : WeylGroup Tag.E7) (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ g : WeylGroup Tag.E7, g * x * g⁻¹ ∈ QE7 := by
  haveI := finite_WE7
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hx
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    show (x ^ n) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E7) QE7Sylow P
  have hxP : x ∈ (P : Subgroup (WeylGroup Tag.E7)) := hP' (Subgroup.mem_zpowers x)
  rw [← hg] at hxP
  refine ⟨g⁻¹, ?_⟩
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hxP
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hxP
  have hx' : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [inv_inv, hx']
  exact hs

@[expose] def e7w3Word : List (Fin Tag.E7.rank) :=
  ([0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] : List (Fin 7))

@[expose] def e7w3 : WeylGroup Tag.E7 := wordW Tag.E7 e7w3Word

@[expose] def IsListedRootE7 (u : Fin Tag.E7.rank → ℤ) : Prop :=
  ∃ k < Tag.E7.rootCertificate.roots.length, Tag.E7.rootCertificate.root k = u

instance (u : Fin Tag.E7.rank → ℤ) : Decidable (IsListedRootE7 u) := by
  unfold IsListedRootE7
  infer_instance

theorem isRoot_of_listed_E7 {u : Fin Tag.E7.rank → ℤ} (h : IsListedRootE7 u) : IsRoot Tag.E7 u :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)).2 h

@[expose] def rootCertsE7a : List ((Fin 4 → Fin 3) × (Fin Tag.E7.rank → ℤ) ×
    (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 1], ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1]),
    (![0, 0, 0, 2], ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 2, 2, 2, 2]),
    (![0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0]),
    (![0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 1, 0, 0]),
    (![0, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 2, 1, 0, 1, 0]),
    (![0, 0, 2, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1]),
    (![0, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 2, 0, 1, 0]),
    (![0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 2, 2, 2, 2, 0]),
    (![0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2, 2]),
    (![0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 2, 1, 0, 1, 0]),
    (![0, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 2, 1, 0, 1, 0]),
    (![0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 0, 1]),
    (![0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 1, 0]),
    (![0, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 2, 2, 0, 1, 0]),
    (![0, 1, 2, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 0, 1]),
    (![0, 1, 2, 1], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1]),
    (![0, 1, 2, 2], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 2]),
    (![0, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]),
    (![0, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 2, 2, 2, 2, 0]),
    (![0, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 2, 2, 2, 2, 0]),
    (![0, 2, 1, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 1, 0, 2, 2]),
    (![0, 2, 1, 1], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 1]),
    (![0, 2, 1, 2], ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 2, 0, 2, 2, 2]),
    (![0, 2, 2, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 1, 0, 2, 2])]

@[expose] def rootCertsE7b : List ((Fin 4 → Fin 3) × (Fin Tag.E7.rank → ℤ) ×
    (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 1, 0, 1, 0]),
    (![0, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 2, 1, 2, 2, 0]),
    (![1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0]),
    (![1, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 1, 1, 0, 0]),
    (![1, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 1, 0, 0]),
    (![1, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 2, 2, 0, 0, 1]),
    (![1, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 1, 0, 0]),
    (![1, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 2, 2, 2, 0]),
    (![1, 0, 2, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 2, 2, 0, 0, 1]),
    (![1, 0, 2, 1], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 1]),
    (![1, 0, 2, 2], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 2, 2]),
    (![1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2, 2]),
    (![1, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 2, 2, 2, 0]),
    (![1, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 1, 0]),
    (![1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 2, 2, 1]),
    (![1, 1, 1, 2], ![0, 0, 1, 1, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 2]),
    (![1, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 2, 1, 2, 2, 0]),
    (![1, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 1, 1, 0, 0]),
    (![1, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]),
    (![1, 2, 0, 1], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 1]),
    (![1, 2, 0, 2], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 2, 2, 2, 2]),
    (![1, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 1, 1, 0, 0]),
    (![1, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 1, 1, 0, 1, 0]),
    (![1, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 2, 2, 2, 2, 0])]

@[expose] def rootCertsE7c : List ((Fin 4 → Fin 3) × (Fin Tag.E7.rank → ℤ) ×
    (Fin Tag.E7.rank → ℤ)) :=
  [(![1, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 2, 2, 2, 0]),
    (![2, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0]),
    (![2, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 1, 2, 0, 1, 0]),
    (![2, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 2, 0, 1, 0]),
    (![2, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 2]),
    (![2, 0, 1, 1], ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 1]),
    (![2, 0, 1, 2], ![0, 0, 1, 1, 1, 1, 0], ![0, 0, 2, 0, 0, 2, 2]),
    (![2, 0, 2, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 2]),
    (![2, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 1, 1, 0, 1, 0]),
    (![2, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 1, 1, 0, 0]),
    (![2, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2, 2]),
    (![2, 1, 0, 1], ![0, 0, 1, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1]),
    (![2, 1, 0, 2], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 2, 2, 2, 2]),
    (![2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 2, 1, 0, 1, 0]),
    (![2, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 1, 0, 0]),
    (![2, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 2, 2, 2, 0]),
    (![2, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 1, 0, 0]),
    (![2, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]),
    (![2, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 1, 0, 0]),
    (![2, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 0, 1, 0, 1, 0]),
    (![2, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 1, 2, 2, 0, 1, 0]),
    (![2, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0], ![0, 2, 1, 2, 0, 1, 0]),
    (![2, 2, 2, 1], ![0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1]),
    (![2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0, 2])]

@[expose] def rootCertsE7 : List ((Fin 4 → Fin 3) × (Fin Tag.E7.rank → ℤ) ×
    (Fin Tag.E7.rank → ℤ)) :=
  rootCertsE7a ++ rootCertsE7b ++ rootCertsE7c

@[expose] def conjCertsE7 : List ((Fin 4 → Fin 3) × List (Fin Tag.E7.rank)) :=
  [(![1, 1, 1, 0], ([5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![1, 1, 2, 0], ([1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![1, 2, 1, 0], ([4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![1, 2, 2, 0], ([4, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![2, 1, 1, 0], ([0, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![2, 1, 2, 0], ([0, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![2, 2, 1, 0], ([0, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7))),
    (![2, 2, 2, 0], ([0, 4, 1, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 0, 2, 3, 2] : List (Fin 7)))]

theorem rootCertsE7_ok : ∀ c ∈ rootCertsE7,
    (∀ i, (c.2.1 i - (actE7 c.1 c.2.2 i - c.2.2 i)) % 3 = 0) ∧ IsListedRootE7 c.2.1 := by
  decide +kernel

theorem conjCertsE7_ok : ∀ c ∈ conjCertsE7, ∀ k : Fin Tag.E7.rank,
    actE7 c.1 (c.2.foldr (reflect Tag.E7) (Pi.single k 1)) =
      (c.2 ++ e7w3Word).foldr (reflect Tag.E7) (Pi.single k 1) := by
  decide +kernel

theorem qcasesE7 : ∀ v : Fin 4 → Fin 3, v ≠ 0 →
    (∃ c ∈ rootCertsE7, c.1 = v) ∨ (∃ c ∈ conjCertsE7, c.1 = v) := by
  decide +kernel

theorem charVal_eq_zero_of_rootCertE7 {v : Fin 4 → Fin 3} {α u : Fin Tag.E7.rank → ℤ}
    (h : ∀ i, (α i - (actE7 v u i - u i)) % 3 = 0) {z : Fin Tag.E7.rank → ZMod 3}
    (hz : nfE7 v ∈ dualWeylStabilizer z) : charVal z α = 0 := by
  have e : α = (nfE7 v • u - u) + (α - (nfE7 v • u - u)) := by abel
  have h0 : charVal z (α - (nfE7 v • u - u)) = 0 := by
    unfold charVal
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : ((α - (nfE7 v • u - u)) i : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := h i
      rw [nfE7_smul]
      simp only [Pi.sub_apply]
      omega
    rw [hi, zero_mul]
  rw [e, charVal_add, h0, add_zero, CFSG.RankThree.PartOne.KE.charVal_sub, hz u, sub_self]

theorem nfE7_mul_eq_of_cert {v : Fin 4 → Fin 3} {l : List (Fin Tag.E7.rank)}
    (h : ∀ k : Fin Tag.E7.rank, actE7 v (l.foldr (reflect Tag.E7) (Pi.single k 1)) =
      (l ++ e7w3Word).foldr (reflect Tag.E7) (Pi.single k 1)) :
    nfE7 v * wordW Tag.E7 l = wordW Tag.E7 l * e7w3 := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, wordW_smul_foldr_E7, nfE7_smul, h k, e7w3, ← mul_smul, ← wordW_append,
    wordW_smul_foldr_E7]

end E7Sylow

section E7Stab

open CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.PartOne.KE RootSpace

theorem e7_cube_stab_conj {L : Type} [Field L] (A : Subgroup (Fin Tag.E7.rank → Lˣ))
    (hA : Nat.card A = 3 ^ 3) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hreg : ∀ α, IsRoot Tag.E7 α → ∃ a ∈ A, rootChar a α ≠ 1)
    {y : WeylGroup Tag.E7} (hy : ∀ a ∈ A, ∀ v, rootChar a (y • v) = rootChar a v) (hy1 : y ≠ 1) :
    ∃ g : WeylGroup Tag.E7, y = g * e7w3 * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  haveI := finite_WE7
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
  have hexp : ∀ a : Fin Tag.E7.rank → Lˣ, ∃ e : Fin Tag.E7.rank → ℕ,
      a ∈ A → ∀ i, a i = a₀ i₀ ^ e i := by
    intro a
    by_cases ha : a ∈ A
    · have : ∀ i, ∃ n : ℕ, a i = a₀ i₀ ^ n := fun i =>
        SeitzExcOpenRest5.Aux.exists_pow_eq_of_pow_three hζ (by simpa using congrFun (hA3 a ha) i)
      choose e he using this
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose e he using hexp
  set col : (Fin Tag.E7.rank → Lˣ) → Fin Tag.E7.rank → ZMod 3 := fun a i => (e a i : ZMod 3)
    with hcol
  have hchar : ∀ a ∈ A, ∀ l l' : Fin Tag.E7.rank → ℤ,
      rootChar a l = rootChar a l' ↔ charVal (col a) l = charVal (col a) l' :=
    fun a ha l l' => rootChar_eq_rootChar_iff hζ (e a) a (he a ha) l l'
  obtain ⟨a1, ha1, a2, ha2, a3, ha3, hgen⟩ :=
    SeitzExcOpenRest3.exists_three_gen_of_card_cube Nat.prime_three A hA hA3
  have hcl : ∀ H : Subgroup (Fin Tag.E7.rank → Lˣ), a1 ∈ H → a2 ∈ H → a3 ∈ H → A ≤ H := by
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
      s = rootReflection α} = (∅ : Set (WeylGroup Tag.E7)) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨α, ⟨⟨⟨hα, h1⟩, ⟨-, h2⟩⟩, ⟨-, h3'⟩⟩, -⟩
    obtain ⟨a, haA, hane⟩ := hreg α hα
    exact hane (hcl _ (hk α a1 ha1 h1) (hk α a2 ha2 h2) (hk α a3 ha3 h3') haA)
  have hprime : ∀ u ∈ U, ¬ 3 ∣ orderOf u → u = 1 := by
    intro u hu h3
    have hH : Subgroup.zpowers u ≤ U := (Subgroup.zpowers_le).2 hu
    have hcard : ¬ 3 ∣ Nat.card (Subgroup.zpowers u) := by rw [Nat.card_zpowers]; exact h3
    have hle := SeitzExcOpenRest6.Aux.le_closure_of_le_inf3 (col a1) (col a2) (col a3) _ hH hcard
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
  obtain ⟨g, hg⟩ := exists_conj_mem_QE7 y ⟨k, hy3⟩
  obtain ⟨v, hv⟩ := exists_nfE7_of_mem hg
  have hyv : y = g⁻¹ * nfE7 v * g := by
    rw [hv]
    group
  have hv0 : v ≠ 0 := by
    intro h0
    apply hy1
    have h1 : nfE7 v = 1 := by
      rw [h0]
      simp [nfE7, e7nfN]
    rw [hyv, h1]
    group
  let T : (Fin Tag.E7.rank → ZMod 3) → Fin Tag.E7.rank → ZMod 3 :=
    fun z k => charVal z (g⁻¹ • (Pi.single k 1 : Fin Tag.E7.rank → ℤ))
  have hT : ∀ z (x : Fin Tag.E7.rank → ℤ), charVal (T z) x = charVal z (g⁻¹ • x) := by
    intro z x
    rw [charVal_smul_eq_sum z g⁻¹ x]
    rfl
  have hTfix : ∀ a ∈ A, nfE7 v ∈ dualWeylStabilizer (T (col a)) := by
    intro a ha x
    rw [hT, hT]
    have e1 : g⁻¹ • (nfE7 v • x) = y • (g⁻¹ • x) := by
      rw [hyv, mul_smul, mul_smul, smul_inv_smul]
    rw [e1]
    exact (hchar a ha _ _).1 (hy a ha (g⁻¹ • x))
  rcases qcasesE7 v hv0 with ⟨c, hc, hcv⟩ | ⟨c, hc, hcv⟩
  · exfalso
    obtain ⟨h1, h2⟩ := rootCertsE7_ok c hc
    rw [hcv] at h1
    have hα : IsRoot Tag.E7 c.2.1 := isRoot_of_listed_E7 h2
    have hz : ∀ b ∈ A, charVal (col b) (g⁻¹ • c.2.1) = 0 := fun b hb => by
      rw [← hT]
      exact charVal_eq_zero_of_rootCertE7 h1 (hTfix b hb)
    obtain ⟨a, haA, hane⟩ := hreg (g⁻¹ • c.2.1) (CFSG.LieType.Chevalley.IsRoot.smul hα _)
    exact hane (hcl _ (hk _ a1 ha1 (hz a1 ha1)) (hk _ a2 ha2 (hz a2 ha2))
      (hk _ a3 ha3 (hz a3 ha3)) haA)
  · have hmul := nfE7_mul_eq_of_cert (conjCertsE7_ok c hc)
    rw [hcv] at hmul
    have hnf : nfE7 v = wordW Tag.E7 c.2 * e7w3 * (wordW Tag.E7 c.2)⁻¹ := by
      rw [← hmul]
      group
    refine ⟨g⁻¹ * wordW Tag.E7 c.2, ?_⟩
    rw [hyv, hnf]
    group

end E7Stab

section Transport

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.RankThree.PartOne.KE

theorem exists_torus_canonicalRep_conj {τ : Tag} (L : Type) [Field L] (g w w' : WeylGroup τ)
    (hw : w = g * w' * g⁻¹) :
    ∃ m ∈ torusGroup τ L, canonicalRep (coxeterSystem τ) L w * canonicalRep (coxeterSystem τ) L g =
      canonicalRep (coxeterSystem τ) L g * m * canonicalRep (coxeterSystem τ) L w' := by
  have hmono : ∀ x : WeylGroup τ, canonicalRep (coxeterSystem τ) L x ∈ monomialSubgroup τ L :=
    fun x => CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup L x
  have hmM : (canonicalRep (coxeterSystem τ) L g)⁻¹ * canonicalRep (coxeterSystem τ) L w *
      canonicalRep (coxeterSystem τ) L g * (canonicalRep (coxeterSystem τ) L w')⁻¹ ∈
        monomialSubgroup τ L :=
    mul_mem (mul_mem (mul_mem (inv_mem (hmono g)) (hmono w)) (hmono g)) (inv_mem (hmono w'))
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem τ) L g)⁻¹ *
      canonicalRep (coxeterSystem τ) L w * canonicalRep (coxeterSystem τ) L g *
        (canonicalRep (coxeterSystem τ) L w')⁻¹) 1 := by
    have h := ((((mapsRootLines_canonicalRep (R := L) g).inv).mul
      (mapsRootLines_canonicalRep (R := L) w)).mul (mapsRootLines_canonicalRep (R := L) g)).mul
        (mapsRootLines_canonicalRep (R := L) w').inv
    have e : g⁻¹ * w * g * w'⁻¹ = 1 := by rw [hw]; group
    rw [e] at h
    exact h
  refine ⟨_, E8Lift.mem_torusGroup_of_mapsRootLines_one hmM hmaps, ?_⟩
  group

theorem exists_langPlaneData_conj {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) (g w' : WeylGroup τ)
    (hw : D.w = g * w' * g⁻¹) :
    ∃ D' : LangPlaneData τ K A, D'.w = w' ∧ ∀ α, D'.Kills α → D.Kills (g • α) := by
  classical
  have hFn : ∀ x : WeylGroup τ, Units.map (entrywiseHom D.Fr)
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x) =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x := fun x =>
    E8Lift.units_map_entrywiseHom_canonicalRep D.Fr x
  obtain ⟨m, hm, hnwng⟩ := exists_torus_canonicalRep_conj (AlgebraicClosure K) g D.w w' hw
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  obtain ⟨t, ht, htL⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.exists_lang_supportedTorus_of_monomial
    (τ := τ) (Ω := AlgebraicClosure K) hq D.hFr
    (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')
    (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) w')
    (J := Set.univ) (fun β hβ => ⟨CFSG.LieType.Chevalley.IsRoot.smul hβ.1 _,
      fun i hi => absurd (Set.mem_univ i) hi⟩)
    m⁻¹ (E8Lift.torusGroup_le_supportedTorus_univ (inv_mem hm))
  have htH : t ∈ torusGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.supportedTorus_le_torusGroup _ ht
  have hkey : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * Units.map (entrywiseHom D.Fr) t =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' := by
    have hc : m * t = t * m := E8Lift.torusGroup_mul_comm hm htH
    have hFt : Units.map (entrywiseHom D.Fr) t =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')⁻¹ * (t * m⁻¹) *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' := by
      rw [← htL]
      group
    rw [hnwng, hFt]
    calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * m *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' *
            ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')⁻¹ * (t * m⁻¹) *
              canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')
        = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * (m * t) * m⁻¹ *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' := by group
      _ = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' := by rw [hc]; group
  have hngC : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g ∈
      adjointGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (coxeterSystem τ) (AlgebraicClosure K) g
  have htC : t ∈ adjointGroup τ (AlgebraicClosure K) :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' htH
  have hngN : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g ∈
      Subgroup.normalizer (torusGroup τ (AlgebraicClosure K) :
        Set (ModGL τ (AlgebraicClosure K))) := CFSG.LieType.Chevalley.canonicalRep_mem_normalizer g
  have hconjH : ∀ s ∈ torusGroup τ (AlgebraicClosure K),
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g)⁻¹ * s *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g ∈
          torusGroup τ (AlgebraicClosure K) := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hngN) s).1 hs
    simpa using this
  refine ⟨⟨w', D.Fr, D.hFr, D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t,
      mul_mem (mul_mem D.hg0C hngC) htC, ?_, D.c, ?_⟩, rfl, ?_⟩
  · rw [map_mul, map_mul, D.hg0, hFn g]
    calc D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * Units.map (entrywiseHom D.Fr) t
        = D.g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g *
            Units.map (entrywiseHom D.Fr) t) := by group
      _ = D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' := by rw [hkey]; group
  · intro x hx
    obtain ⟨s₀, hs₀, hs₀x⟩ := Subgroup.mem_map.1 (D.hc x hx)
    obtain ⟨hs₀H, hs₀F⟩ := mem_twistedTorusOf.1 hs₀
    refine Subgroup.mem_map.2 ⟨(canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t)⁻¹ *
      s₀ * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t), ?_, ?_⟩
    · refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
      · have e : (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t)⁻¹ * s₀ *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t) =
              t⁻¹ * ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g)⁻¹ * s₀ *
                canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g) * t := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem htH) (hconjH s₀ hs₀H)) htH
      · have hF₀ : Units.map (entrywiseHom D.Fr) s₀ =
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * s₀ *
              canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
          calc Units.map (entrywiseHom D.Fr) s₀
              = (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ *
                  (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
                    Units.map (entrywiseHom D.Fr) s₀ *
                      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹) *
                  canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by group
            _ = _ := by rw [hs₀F]
        have hk' : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g *
            Units.map (entrywiseHom D.Fr) t =
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ *
                (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
                  canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w') := by
          rw [← hkey]
          group
        rw [map_mul, map_mul, map_inv, map_mul, hFn g, hF₀]
        calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' *
              ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g *
                Units.map (entrywiseHom D.Fr) t)⁻¹ *
                ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * s₀ *
                  canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w) *
                (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g *
                  Units.map (entrywiseHom D.Fr) t)) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')⁻¹
            = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w' *
              (((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ *
                (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
                  canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w'))⁻¹ *
                ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * s₀ *
                  canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w) *
                ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ *
                  (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t *
                    canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w'))) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w')⁻¹ := by rw [hk']
          _ = (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t)⁻¹ * s₀ *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t) := by group
    · rw [← hs₀x]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · intro α hα x hx
    obtain ⟨s₀, hs₀, hs₀x⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hs₀H : s₀ ∈ torusGroup τ (AlgebraicClosure K) := (mem_twistedTorusOf.1 hs₀).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup hs₀H
    have hX : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 = s₀ := by
      rw [← hs₀x]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨a, by rw [ha, hX], ?_⟩
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_of_mem_torusGroup (hconjH s₀ hs₀H)
    have hiff : rootDiagUnit τ a = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g *
        rootDiagUnit τ b * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g)⁻¹ ↔
          ∀ v, rootChar a (g • v) = rootChar b v := rootDiagUnit_eq_conj_canonicalRep_iff a b g
    have hab : ∀ v, rootChar a (g • v) = rootChar b v := by
      refine hiff.1 ?_
      rw [ha, hb]
      group
    obtain ⟨a', ha', ha'α⟩ := hα x hx
    have ha'' : rootDiagUnit τ a' =
        (D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) *
          (D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t) := ha'
    have hX' : rootDiagUnit τ a' = rootDiagUnit τ b := by
      rw [ha'']
      have e : (D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) *
          (D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g * t) =
            t⁻¹ * ((canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g)⁻¹ *
              (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0) *
              canonicalRep (coxeterSystem τ) (AlgebraicClosure K) g) * t := by group
      rw [e, hX, ← hb]
      have hc : t⁻¹ * rootDiagUnit τ b = rootDiagUnit τ b * t⁻¹ :=
        E8Lift.torusGroup_mul_comm (inv_mem htH) (hb ▸ hconjH s₀ hs₀H)
      rw [hc]
      group
    have hab' : a' = b := CFSG.LieType.Chevalley.rootDiagUnit_injective hX'
    rw [hab, ← hab']
    exact ha'α

end Transport

section E8Stab

open CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.PartOne.KE RootSpace
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6.Aux

@[expose] def e8c0Word : List (Fin Tag.E8.rank) := lc1 ++ lc2 ++ lc3

@[expose] def e8c0 : WeylGroup Tag.E8 := wordW Tag.E8 e8c0Word

@[expose] def rootCertsE8a : List ((Fin 5 → Fin 3) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  [(![0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![0, 0, 0, 0, 2], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 2, 2, 2, 2, 0]),
    (![0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]),
    (![0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0]),
    (![0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![0, 0, 0, 2, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0]),
    (![0, 0, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 2, 2, 0, 0]),
    (![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2, 2, 0]),
    (![0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![0, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 0, 1, 0]),
    (![0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![0, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![0, 0, 1, 2, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 0, 1, 0]),
    (![0, 0, 1, 2, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1, 0]),
    (![0, 0, 1, 2, 2], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 2, 0]),
    (![0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![0, 0, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 2, 2, 0, 0]),
    (![0, 0, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 2, 2, 0, 0]),
    (![0, 0, 2, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 2, 2, 0]),
    (![0, 0, 2, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0]),
    (![0, 0, 2, 1, 2], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 2, 0, 2, 2, 2, 0]),
    (![0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 2, 2, 0]),
    (![0, 0, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![0, 0, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 2, 2, 0, 0]),
    (![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 0, 0, 0, 0]),
    (![0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0]),
    (![0, 1, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0]),
    (![0, 1, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 2, 2, 0, 0, 1, 0]),
    (![0, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0]),
    (![0, 1, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 2, 2, 0, 0]),
    (![0, 1, 0, 2, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 2, 2, 0, 0, 1, 0]),
    (![0, 1, 0, 2, 1], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 1, 0]),
    (![0, 1, 0, 2, 2], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 2, 2, 0]),
    (![0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2, 2, 0]),
    (![0, 1, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 2, 2, 0, 0]),
    (![0, 1, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 2, 2, 1, 0]),
    (![0, 1, 1, 1, 2], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 2, 0])]

@[expose] def rootCertsE8b : List ((Fin 5 → Fin 3) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  [(![0, 1, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 2, 2, 0, 0]),
    (![0, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0]),
    (![0, 1, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![0, 1, 2, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 1, 0]),
    (![0, 1, 2, 0, 2], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 2, 2, 2, 2, 0]),
    (![0, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0]),
    (![0, 1, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![0, 1, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 2, 2, 0, 0]),
    (![0, 1, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 2, 2, 0, 0]),
    (![0, 2, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]),
    (![0, 2, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0]),
    (![0, 2, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![0, 2, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 2, 0]),
    (![0, 2, 0, 1, 1], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0]),
    (![0, 2, 0, 1, 2], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 2, 0, 0, 2, 2, 0]),
    (![0, 2, 0, 2, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 2, 0]),
    (![0, 2, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![0, 2, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0]),
    (![0, 2, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2, 2, 0]),
    (![0, 2, 1, 0, 1], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![0, 2, 1, 0, 2], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 2, 2, 0]),
    (![0, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![0, 2, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0]),
    (![0, 2, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 2, 2, 0, 0]),
    (![0, 2, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0]),
    (![0, 2, 2, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![0, 2, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0]),
    (![0, 2, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![0, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![0, 2, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0]),
    (![0, 2, 2, 2, 1], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1, 0]),
    (![0, 2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 2, 0]),
    (![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 2, 0, 0, 1, 0]),
    (![1, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0, 1]),
    (![1, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![1, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 2, 0, 0, 1, 0]),
    (![1, 0, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![1, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 1, 0, 1]),
    (![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 2, 1, 0])]

@[expose] def rootCertsE8c : List ((Fin 5 → Fin 3) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  [(![1, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![1, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![1, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![1, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![1, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 2, 1, 0]),
    (![1, 0, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 0, 1, 0, 2]),
    (![1, 0, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 0, 1, 0, 1]),
    (![1, 0, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![1, 0, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 0, 1, 0, 1]),
    (![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![1, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 1, 0, 1]),
    (![1, 1, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0, 2]),
    (![1, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 0, 1, 0, 1]),
    (![1, 1, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 0, 1, 0, 1]),
    (![1, 1, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 0, 1, 0, 2]),
    (![1, 1, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![1, 1, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 0, 1, 0, 2]),
    (![1, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 1, 0, 2]),
    (![1, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0, 1]),
    (![1, 1, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![1, 1, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 1, 0, 2]),
    (![1, 1, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 0, 1, 0, 1]),
    (![1, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
    (![1, 2, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0]),
    (![1, 2, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![1, 2, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![1, 2, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0, 2]),
    (![1, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![1, 2, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 2]),
    (![1, 2, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 0, 1, 0, 2]),
    (![1, 2, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 0, 1, 0, 2]),
    (![1, 2, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 1]),
    (![1, 2, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![1, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![1, 2, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0]),
    (![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 2, 2]),
    (![2, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 0, 1, 0, 0, 2, 2]),
    (![2, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0, 2]),
    (![2, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![2, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 0, 1, 0, 0, 2, 2])]

@[expose] def rootCertsE8d : List ((Fin 5 → Fin 3) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  [(![2, 0, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![2, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 1, 0, 2]),
    (![2, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 2, 0, 1, 2, 2]),
    (![2, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![2, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 1, 0, 1, 0, 0]),
    (![2, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![2, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 2, 0, 1, 2, 2]),
    (![2, 0, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 0, 1, 0, 1]),
    (![2, 0, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 0, 1, 0, 2]),
    (![2, 0, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![2, 0, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 0, 1, 0, 2]),
    (![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 2, 2]),
    (![2, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 1, 0, 2]),
    (![2, 1, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0, 1]),
    (![2, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 0, 1, 0, 2]),
    (![2, 1, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 0, 1, 0, 2]),
    (![2, 1, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 0, 1, 0, 1]),
    (![2, 1, 1, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 2, 0, 1, 0, 0]),
    (![2, 1, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 2, 1, 0, 1, 0, 1]),
    (![2, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 1, 0, 1]),
    (![2, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0, 2]),
    (![2, 1, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![2, 1, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 1, 0, 1]),
    (![2, 1, 2, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 2, 0, 1, 0, 2]),
    (![2, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 2, 2]),
    (![2, 2, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0]),
    (![2, 2, 0, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 2, 0, 1, 0, 0]),
    (![2, 2, 0, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 1, 0, 1, 0, 0]),
    (![2, 2, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0, 1]),
    (![2, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 1, 0, 0]),
    (![2, 2, 1, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 1]),
    (![2, 2, 1, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 0, 1, 0, 1]),
    (![2, 2, 1, 2, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 2, 0, 1, 0, 1]),
    (![2, 2, 2, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 2]),
    (![2, 2, 2, 0, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0]),
    (![2, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 2, 2, 0, 1, 0, 0]),
    (![2, 2, 2, 1, 2], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 2, 1, 2, 0, 1, 0, 0])]

@[expose] def rootCertsE8 : List ((Fin 5 → Fin 3) × (Fin Tag.E8.rank → ℤ) ×
    (Fin Tag.E8.rank → ℤ)) :=
  rootCertsE8a ++ rootCertsE8b ++ rootCertsE8c ++ rootCertsE8d

@[expose] def conjCertsE8a : List ((Fin 5 → Fin 3) × List (Fin Tag.E8.rank)) :=
  [(![0, 1, 1, 1, 0], ([] : List (Fin 8))),
    (![0, 1, 1, 2, 0], ([1] : List (Fin 8))),
    (![0, 1, 2, 1, 0], ([4] : List (Fin 8))),
    (![0, 1, 2, 2, 0], ([1, 4] : List (Fin 8))),
    (![0, 2, 1, 1, 0], ([0] : List (Fin 8))),
    (![0, 2, 1, 2, 0], ([0, 1] : List (Fin 8))),
    (![0, 2, 2, 1, 0], ([0, 4] : List (Fin 8))),
    (![0, 2, 2, 2, 0], ([0, 1, 4] : List (Fin 8))),
    (![1, 0, 0, 0, 1], ([0, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 0, 0, 2], ([0, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 1, 1, 0], ([3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 1, 2, 0], ([3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 1, 2, 1], ([1, 3, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 1, 2, 2], ([0, 1, 2, 3, 1, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 2, 1, 0], ([3, 1, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 2, 1, 1], ([0, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 2, 1, 2], ([2, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 0, 2, 2, 0], ([3, 1, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 0, 1, 0], ([2, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 0, 2, 0], ([2, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 0, 2, 1], ([0, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 0, 2, 2], ([0, 2, 0, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 1, 0, 0], ([2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8)))]

@[expose] def conjCertsE8b : List ((Fin 5 → Fin 3) × List (Fin Tag.E8.rank)) :=
  [(![1, 1, 1, 1, 1], ([0, 2, 0, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 1, 1, 2], ([2, 4, 3, 1, 2, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 2, 0, 0], ([2, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 2, 0, 1], ([0, 2, 0, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 1, 2, 0, 2], ([0, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 0, 1, 0], ([3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 0, 1, 1], ([2, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 0, 1, 2], ([2, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 0, 2, 0], ([3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 1, 0, 0], ([6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 1, 0, 1], ([2, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 1, 0, 2], ([1, 3, 1, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 2, 0, 0], ([4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 2, 2, 1], ([2, 4, 3, 1, 2, 3, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![1, 2, 2, 2, 2], ([0, 2, 0, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 0, 0, 1], ([0, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 0, 0, 2], ([0, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 1, 1, 0], ([3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 1, 2, 0], ([3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 1, 2, 1], ([1, 3, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 1, 2, 2], ([0, 1, 2, 3, 1, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 2, 1, 0], ([3, 1, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 2, 1, 1], ([0, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8)))]

@[expose] def conjCertsE8c : List ((Fin 5 → Fin 3) × List (Fin Tag.E8.rank)) :=
  [(![2, 0, 2, 1, 2], ([2, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 0, 2, 2, 0], ([3, 1, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 0, 1, 0], ([2, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 0, 2, 0], ([2, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 0, 2, 1], ([0, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 0, 2, 2], ([0, 2, 0, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 1, 0, 0], ([2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 1, 1, 1], ([0, 2, 0, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 1, 1, 2], ([2, 4, 3, 1, 2, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 2, 0, 0], ([2, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 2, 0, 1], ([0, 2, 0, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 1, 2, 0, 2], ([0, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 0, 1, 0], ([3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 0, 1, 1], ([2, 3, 5, 4, 3, 1, 2, 3, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 0, 1, 2], ([2, 3, 1, 2, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 0, 2, 0], ([3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 1, 0, 0], ([6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 1, 0, 1], ([2, 3, 1, 2, 3, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 1, 0, 2], ([1, 3, 1, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 2, 0, 0], ([4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 2, 2, 1], ([2, 4, 3, 1, 2, 3, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8))),
    (![2, 2, 2, 2, 2], ([0, 2, 0, 3, 1, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5, 7, 6] : List (Fin 8)))]

@[expose] def conjCertsE8 : List ((Fin 5 → Fin 3) × List (Fin Tag.E8.rank)) :=
  conjCertsE8a ++ conjCertsE8b ++ conjCertsE8c

theorem rootCertsE8_ok : ∀ c ∈ rootCertsE8,
    (∀ i, (c.2.1 i - (actE8 c.1 c.2.2 i - c.2.2 i)) % 3 = 0) ∧ IsListedRootE8 c.2.1 := by
  decide +kernel

theorem conjCertsE8_ok : ∀ c ∈ conjCertsE8, ∀ k : Fin Tag.E8.rank,
    actE8 c.1 (c.2.foldr (reflect Tag.E8) (Pi.single k 1)) =
      (c.2 ++ e8c0Word).foldr (reflect Tag.E8) (Pi.single k 1) := by
  decide +kernel

theorem qcasesE8two : ∀ v : Fin 5 → Fin 3, v ≠ 0 →
    (∃ c ∈ rootCertsE8, c.1 = v) ∨ (∃ c ∈ certs4E8, c.1 = v) ∨ (∃ c ∈ conjCertsE8, c.1 = v) := by
  decide +kernel

theorem charVal_eq_zero_of_rootCertE8 {v : Fin 5 → Fin 3} {α u : Fin Tag.E8.rank → ℤ}
    (h : ∀ i, (α i - (actE8 v u i - u i)) % 3 = 0) {z : Fin Tag.E8.rank → ZMod 3}
    (hz : nfE8 v ∈ dualWeylStabilizer z) : charVal z α = 0 := by
  have e : α = (nfE8 v • u - u) + (α - (nfE8 v • u - u)) := by abel
  have h0 : charVal z (α - (nfE8 v • u - u)) = 0 := by
    unfold charVal
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : ((α - (nfE8 v • u - u)) i : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := h i
      rw [nfE8_smul]
      simp only [Pi.sub_apply]
      omega
    rw [hi, zero_mul]
  rw [e, charVal_add, h0, add_zero, CFSG.RankThree.PartOne.KE.charVal_sub, hz u, sub_self]

theorem nfE8_mul_eq_of_cert {v : Fin 5 → Fin 3} {l : List (Fin Tag.E8.rank)}
    (h : ∀ k : Fin Tag.E8.rank, actE8 v (l.foldr (reflect Tag.E8) (Pi.single k 1)) =
      (l ++ e8c0Word).foldr (reflect Tag.E8) (Pi.single k 1)) :
    nfE8 v * wordW Tag.E8 l = wordW Tag.E8 l * e8c0 := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, wordW_smul_foldr_E8, nfE8_smul, h k, e8c0, ← mul_smul, ← wordW_append,
    wordW_smul_foldr_E8]

theorem e8_cube_stab_conj {L : Type} [Field L] (A : Subgroup (Fin Tag.E8.rank → Lˣ))
    (hA : Nat.card A = 3 ^ 3) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hreg : ∀ α, IsRoot Tag.E8 α → ∃ a ∈ A, rootChar a α ≠ 1)
    {y : WeylGroup Tag.E8} (hy : ∀ a ∈ A, ∀ v, rootChar a (y • v) = rootChar a v) (hy1 : y ≠ 1) :
    ∃ g : WeylGroup Tag.E8, y = g * e8c0 * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  haveI := finite_WE8
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
        SeitzExcOpenRest5.Aux.exists_pow_eq_of_pow_three hζ (by simpa using congrFun (hA3 a ha) i)
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
    have hle := SeitzExcOpenRest6.Aux.le_closure_of_le_inf3 (col a1) (col a2) (col a3) _ hH hcard
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
  obtain ⟨g, hg⟩ := exists_conj_mem_QE8 y ⟨k, hy3⟩
  obtain ⟨v, hv⟩ := exists_nfE8_of_mem hg
  have hyv : y = g⁻¹ * nfE8 v * g := by
    rw [hv]
    group
  have hv0 : v ≠ 0 := by
    intro h0
    apply hy1
    have h1 : nfE8 v = 1 := by
      rw [h0]
      simp [nfE8, nfN]
    rw [hyv, h1]
    group
  let T : (Fin Tag.E8.rank → ZMod 3) → Fin Tag.E8.rank → ZMod 3 :=
    fun z k => charVal z (g⁻¹ • (Pi.single k 1 : Fin Tag.E8.rank → ℤ))
  have hT : ∀ z (x : Fin Tag.E8.rank → ℤ), charVal (T z) x = charVal z (g⁻¹ • x) := by
    intro z x
    rw [charVal_smul_eq_sum z g⁻¹ x]
    rfl
  have hTfix : ∀ a ∈ A, nfE8 v ∈ dualWeylStabilizer (T (col a)) := by
    intro a ha x
    rw [hT, hT]
    have e1 : g⁻¹ • (nfE8 v • x) = y • (g⁻¹ • x) := by
      rw [hyv, mul_smul, mul_smul, smul_inv_smul]
    rw [e1]
    exact (hchar a ha _ _).1 (hy a ha (g⁻¹ • x))
  rcases qcasesE8two v hv0 with ⟨c, hc, hcv⟩ | ⟨c, hc, hcv⟩ | ⟨c, hc, hcv⟩
  · exfalso
    obtain ⟨h1, h2⟩ := rootCertsE8_ok c hc
    rw [hcv] at h1
    have hα : IsRoot Tag.E8 c.2.1 := isRoot_of_listed h2
    have hz : ∀ b ∈ A, charVal (col b) (g⁻¹ • c.2.1) = 0 := fun b hb => by
      rw [← hT]
      exact charVal_eq_zero_of_rootCertE8 h1 (hTfix b hb)
    obtain ⟨a, haA, hane⟩ := hreg (g⁻¹ • c.2.1) (CFSG.LieType.Chevalley.IsRoot.smul hα _)
    exact hane (hcl _ (hk _ a1 ha1 (hz a1 ha1)) (hk _ a2 ha2 (hz a2 ha2))
      (hk _ a3 ha3 (hz a3 ha3)) haA)
  · exfalso
    obtain ⟨h1, h2⟩ := certs4E8_ok c hc
    rw [hcv] at h1
    obtain ⟨α, hα, h1', h2', h3'⟩ := noRegTriple_of_cert4E8 h1 h2 (hTfix a1 ha1) (hTfix a2 ha2)
      (hTfix a3 ha3)
    rw [hT] at h1' h2' h3'
    obtain ⟨a, haA, hane⟩ := hreg (g⁻¹ • α) (CFSG.LieType.Chevalley.IsRoot.smul hα _)
    exact hane (hcl _ (hk _ a1 ha1 h1') (hk _ a2 ha2 h2') (hk _ a3 ha3 h3') haA)
  · have hmul := nfE8_mul_eq_of_cert (conjCertsE8_ok c hc)
    rw [hcv] at hmul
    have hnf : nfE8 v = wordW Tag.E8 c.2 * e8c0 * (wordW Tag.E8 c.2)⁻¹ := by
      rw [← hmul]
      group
    refine ⟨g⁻¹ * wordW Tag.E8 c.2, ?_⟩
    rw [hyv, hnf]
    group

end E8Stab

section Plane

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_rootCharHom' {τ : Tag}
    {L : Type} [Field L] {E : Type*} [Group E] (ψ : E →* ModGL τ L)
    (hb : ∀ e, ∃ b : Fin τ.rank → Lˣ, rootDiagUnit τ b = ψ e) (v : Fin τ.rank → ℤ) :
    ∃ χ : E →* Lˣ, ∀ (e : E) (b : Fin τ.rank → Lˣ), rootDiagUnit τ b = ψ e →
      χ e = rootChar b v := by
  classical
  have hinj : Function.Injective (rootDiagUnitHom τ L) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hunique : ∀ (e : E) (b b' : Fin τ.rank → Lˣ), rootDiagUnit τ b = ψ e →
      rootDiagUnit τ b' = ψ e → b = b' := fun e b b' h h' => hinj (h.trans h'.symm)
  let b₀ : E → (Fin τ.rank → Lˣ) := fun e => Classical.choose (hb e)
  have hb₀ : ∀ e, rootDiagUnit τ (b₀ e) = ψ e := fun e => Classical.choose_spec (hb e)
  refine ⟨
    { toFun := fun e => rootChar (b₀ e) v
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · have h1 : rootDiagUnit τ (1 : Fin τ.rank → Lˣ) = ψ 1 := by
      rw [map_one]
      exact map_one (rootDiagUnitHom τ L)
    have := hunique 1 (b₀ 1) 1 (hb₀ 1) h1
    simp only [this]
    exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one v
  · intro e e'
    have hm : rootDiagUnit τ (b₀ e * b₀ e') = ψ (e * e') := by
      rw [map_mul, ← hb₀ e, ← hb₀ e']
      exact map_mul (rootDiagUnitHom τ L) _ _
    have := hunique (e * e') _ _ hm (hb₀ (e * e'))
    simp only [← this]
    exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul _ _ _
  · intro e b hbe
    have := hunique e b (b₀ e) hbe (hb₀ e)
    simp [this]

theorem nine_le_card_ker {Y : Type*} [Group Y] {E : Subgroup Y} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) {M : Type*} [Field M] (χ : E →* Mˣ) :
    3 ^ 2 ≤ Nat.card χ.ker := by
  classical
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hpE : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hrange : χ.range ≤ rootsOfUnity 3 M := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, hpE x, map_one]
  have hcr : Nat.card χ.range ≤ 3 :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity M 3)
  have hmul := Subgroup.card_mul_index χ.ker
  rw [Subgroup.index_ker, hcard] at hmul
  by_contra h
  push Not at h
  have h1 : Nat.card χ.ker * Nat.card χ.range < 3 ^ 2 * 3 := by
    calc Nat.card χ.ker * Nat.card χ.range ≤ Nat.card χ.ker * 3 := Nat.mul_le_mul_left _ hcr
      _ < 3 ^ 2 * 3 := Nat.mul_lt_mul_of_pos_right h (by norm_num)
  rw [hmul] at h1
  norm_num at h1

theorem hyperGen_of_lines_of_kills {τ : Tag} (hkill : LangPlaneKillsRoot τ) {K : Type} [Field K]
    [Finite K] [IsSimpleGroup (adjointGroup τ K)] (hK3 : ¬ 3 ∣ Nat.card K)
    {E₀ : Subgroup (adjointGroup τ K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData τ K E₀) {σ : Fin τ.rank → ℤ} (hσ : IsRoot τ σ)
    (hlines : ∀ y ∈ E₀, y ≠ 1 → (∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit τ a = diagMap D y ∧ rootChar a σ = 1) →
      Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E₀) :
    HyperGen 3 ⊤ E₀ := by
  classical
  have hbE : ∀ e : E₀, ∃ b : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ b = ((diagMap D).comp E₀.subtype) e := fun e =>
    exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D e.2)
  obtain ⟨χ, hχ⟩ := exists_rootCharHom' ((diagMap D).comp E₀.subtype) hbE σ
  set F : Subgroup (adjointGroup τ K) := χ.ker.map E₀.subtype with hFdef
  have hFE : F ≤ E₀ := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hFc : 3 ^ 2 ≤ Nat.card F := by
    rw [hFdef, Subgroup.card_map_of_injective E₀.subtype_injective]
    exact nine_le_card_ker hE₀ hc χ
  have hmemF : ∀ y ∈ F, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = diagMap D y ∧ rootChar a σ = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, hb⟩ := hbE z
    exact ⟨b, hb, by rw [← hχ z b hb]; exact hz⟩
  let DF : LangPlaneData τ K F :=
    ⟨D.w, D.Fr, D.hFr, D.g0, D.hg0C, D.hg0, D.c, fun x hx => D.hc x (hFE hx)⟩
  have hkF : DF.Kills σ := by
    intro x hx
    obtain ⟨a, ha, haσ⟩ := hmemF x hx
    exact ⟨a, by rw [ha, diagMap_apply], haσ⟩
  obtain ⟨u, hu1, hur, hucomm⟩ := hkill K F DF σ hσ hkF
  have hN : NormalizesRGroup (ringChar K) F := normalizesRGroup_of_commute hu1 hur hucomm
  have hFa : IsElemAbelian 3 F := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => hE₀.2 x (hFE hx)⟩
    have h := hE₀.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩
    have h' : (a : adjointGroup τ K) * b = b * a := congrArg Subtype.val h
    exact h'
  have hF1 : F ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hFc
    norm_num at hFc
  have hFgen : HyperGen 3 ⊤ F := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    haveI : CharP K (ringChar K) := ringChar.charP K
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hrp : ringChar K ≠ 3 := by
      intro h3
      apply hK3
      rw [Nat.card_eq_fintype_card, hn, h3]
      exact dvd_pow_self 3 n.ne_zero
    have hgen : RootInvariantHyperGeneration (adjointGroup τ K) (ringChar K) 3 := by
      intro A R hAC hA hA1 hRC hRr hR hAR
      have := hA
      exact ordinary_root_invariant_prime_subgroup_hyperplane_generation τ K (ringChar K) 3 hrp A
        hAC hA1 R hRC hRr hR hAR
    exact hyperGen_of_native (MulEquiv.refl _) hgen hFa hF1 hN
  intro x hx
  refine (Subgroup.closure_le _).2 ?_ (hFgen hx)
  rintro k ⟨-, B, hB, hBi, hcomm⟩
  have hBne : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.relIndex_bot_left] at hBi
    omega
  obtain ⟨⟨y, hyB⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine hlines y (hFE (hB hyB)) hy1' (hmemF y (hB hyB)) ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm y hyB).symm

end Plane

section LongestWords

open CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6.Aux

@[expose] def e7w0Word : List (Fin Tag.E7.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6] :
    List (Fin 7))

@[expose] def e8w0Word : List (Fin Tag.E8.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7,
    6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3,
    1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8))

theorem e7w0Word_fold : ∀ k : Fin Tag.E7.rank,
    e7w0Word.foldr (reflect Tag.E7) (Pi.single k 1) = -Pi.single k 1 := by
  decide +kernel

theorem e8w0Word_fold : ∀ k : Fin Tag.E8.rank,
    e8w0Word.foldr (reflect Tag.E8) (Pi.single k 1) = -Pi.single k 1 := by
  decide +kernel

theorem smul_eq_neg_of_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ k : Fin τ.rank, w • (Pi.single k 1 : Fin τ.rank → ℤ) = -Pi.single k 1)
    (u : Fin τ.rank → ℤ) : w • u = -u := by
  classical
  have hu : u = ∑ k, u k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  conv_rhs => rw [hu]
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, h k, smul_neg]

theorem e7w0_smul (u : Fin Tag.E7.rank → ℤ) : wordW Tag.E7 e7w0Word • u = -u :=
  smul_eq_neg_of_single (fun k => by rw [wordW_smul_foldr_E7, e7w0Word_fold]) u

theorem e8w0_smul (u : Fin Tag.E8.rank → ℤ) : wordW Tag.E8 e8w0Word • u = -u :=
  smul_eq_neg_of_single (fun k => by rw [wordW_smul_foldr_E8, e8w0Word_fold]) u

end LongestWords

section Datum

open CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_params_of_datum_two {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {E₀ : Subgroup (adjointGroup τ K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) (D : LangPlaneData τ K E₀)
    (hreg : ∀ α, IsRoot τ α → ¬ D.Kills α) :
    ∃ A : Subgroup (Fin τ.rank → (AlgebraicClosure K)ˣ), Nat.card A = 3 ^ 3 ∧
      (∀ a ∈ A, a ^ 3 = 1) ∧ (∀ α, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1) ∧
      ∀ a ∈ A, ∀ v, rootChar a (D.w • v) = (rootChar a v)⁻¹ := by
  classical
  set A : Subgroup (Fin τ.rank → (AlgebraicClosure K)ˣ) :=
    (E₀.map (diagMap D)).comap (rootDiagUnitHom τ (AlgebraicClosure K)) with hAdef
  have hinj : Function.Injective (rootDiagUnitHom τ (AlgebraicClosure K)) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hrange : E₀.map (diagMap D) ≤ (rootDiagUnitHom τ (AlgebraicClosure K)).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    exact ⟨a, ha⟩
  have hAmap : A.map (rootDiagUnitHom τ (AlgebraicClosure K)) = E₀.map (diagMap D) :=
    Subgroup.map_comap_eq_self hrange
  have hA : Nat.card A = 3 ^ 3 := by
    rw [← Subgroup.card_map_of_injective hinj, hAmap,
      Subgroup.card_map_of_injective (diagMap_injective D), hc]
  have hmemA : ∀ a, a ∈ A ↔ ∃ x ∈ E₀, diagMap D x = rootDiagUnit τ a := fun a =>
    Subgroup.mem_comap.trans Subgroup.mem_map
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := (hmemA a).1 ha
    apply hinj
    rw [map_pow, map_one]
    show rootDiagUnit τ a ^ 3 = 1
    rw [← hxa, ← map_pow, hE₀.2 x hx, map_one]
  have hreg' : ∀ α, IsRoot τ α → ∃ a ∈ A, rootChar a α ≠ 1 := by
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
  have hcube : ∀ a ∈ A, ∀ i, a i ^ 3 = 1 := fun a ha i => by
    simpa using congrFun (hA3 a ha) i
  have hFa : ∀ a ∈ A, (fun i => Units.map D.Fr.toMonoidHom (a i)) = a⁻¹ := by
    intro a ha
    funext i
    have e : Units.map D.Fr.toMonoidHom (a i) = a i ^ Nat.card K := Units.ext (by simp [D.hFr])
    rw [e, SeitzExcOpenRest5.Aux.pow_mod_three_of_cube (hcube a ha i), hK, Pi.inv_apply]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hcube a ha i]
  refine ⟨A, hA, hA3, hreg', fun a ha v => ?_⟩
  rw [htw a ha v, hFa a ha, SeitzExcOpenRest5.Aux.rootChar_inv']

theorem e7_regular_neg_datum_conj {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E7 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E7 K E₀) (hreg : ∀ α, IsRoot Tag.E7 α → ¬ D.Kills α)
    (hw : ∃ u : Fin Tag.E7.rank → ℤ, D.w • u ≠ -u) :
    ∃ g : WeylGroup Tag.E7, ∀ u : Fin Tag.E7.rank → ℤ, D.w • u = -((g * e7w3 * g⁻¹) • u) := by
  obtain ⟨A, hA, hA3, hreg', htw⟩ := exists_params_of_datum_two hK hE₀ hc D hreg
  have hy : ∀ a ∈ A, ∀ v, rootChar a ((wordW Tag.E7 e7w0Word * D.w) • v) = rootChar a v := by
    intro a ha v
    rw [mul_smul, e7w0_smul, SeitzExcOpenRest5.Aux.rootChar_neg', htw a ha v, inv_inv]
  have hy1 : wordW Tag.E7 e7w0Word * D.w ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := hw
    apply hu
    rw [eq_inv_of_mul_eq_one_right h1, inv_smul_eq_iff, e7w0_smul, neg_neg]
  obtain ⟨g, hg⟩ := e7_cube_stab_conj A hA hA3 hreg' hy hy1
  refine ⟨g, fun u => ?_⟩
  have e : D.w = (wordW Tag.E7 e7w0Word)⁻¹ * (g * e7w3 * g⁻¹) := by
    rw [← hg]
    group
  rw [e, mul_smul, inv_smul_eq_iff, e7w0_smul, neg_neg]

theorem e8_regular_neg_datum_conj {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E8 K E₀) (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α)
    (hw : ∃ u : Fin Tag.E8.rank → ℤ, D.w • u ≠ -u) :
    ∃ g : WeylGroup Tag.E8, ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -((g * e8c0 * g⁻¹) • u) := by
  obtain ⟨A, hA, hA3, hreg', htw⟩ := exists_params_of_datum_two hK hE₀ hc D hreg
  have hy : ∀ a ∈ A, ∀ v, rootChar a ((wordW Tag.E8 e8w0Word * D.w) • v) = rootChar a v := by
    intro a ha v
    rw [mul_smul, e8w0_smul, SeitzExcOpenRest5.Aux.rootChar_neg', htw a ha v, inv_inv]
  have hy1 : wordW Tag.E8 e8w0Word * D.w ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := hw
    apply hu
    rw [eq_inv_of_mul_eq_one_right h1, inv_smul_eq_iff, e8w0_smul, neg_neg]
  obtain ⟨g, hg⟩ := e8_cube_stab_conj A hA hA3 hreg' hy hy1
  refine ⟨g, fun u => ?_⟩
  have e : D.w = (wordW Tag.E8 e8w0Word)⁻¹ * (g * e8c0 * g⁻¹) := by
    rw [← hg]
    group
  rw [e, mul_smul, inv_smul_eq_iff, e8w0_smul, neg_neg]

theorem exists_e7_negC_datum {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E7 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E7 K E₀) (hreg : ∀ α, IsRoot Tag.E7 α → ¬ D.Kills α)
    (hw : ∃ u : Fin Tag.E7.rank → ℤ, D.w • u ≠ -u) :
    ∃ D' : LangPlaneData Tag.E7 K E₀, (∀ α, IsRoot Tag.E7 α → ¬ D'.Kills α) ∧
      ∀ u : Fin Tag.E7.rank → ℤ, D'.w • u = -(e7w3 • u) := by
  obtain ⟨g, hg⟩ := e7_regular_neg_datum_conj hK hE₀ hc D hreg hw
  obtain ⟨D', hD'w, hkill⟩ := exists_langPlaneData_conj D g (g⁻¹ * D.w * g) (by group)
  refine ⟨D', fun α hα hk => hreg _ (CFSG.LieType.Chevalley.IsRoot.smul hα g) (hkill α hk),
    fun u => ?_⟩
  rw [hD'w, mul_smul, mul_smul, hg, smul_neg, mul_smul, mul_smul]
  simp only [inv_smul_smul]

theorem exists_e8_negC_datum {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E8 K E₀) (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α)
    (hw : ∃ u : Fin Tag.E8.rank → ℤ, D.w • u ≠ -u) :
    ∃ D' : LangPlaneData Tag.E8 K E₀, (∀ α, IsRoot Tag.E8 α → ¬ D'.Kills α) ∧
      ∀ u : Fin Tag.E8.rank → ℤ, D'.w • u = -(e8c0 • u) := by
  obtain ⟨g, hg⟩ := e8_regular_neg_datum_conj hK hE₀ hc D hreg hw
  obtain ⟨D', hD'w, hkill⟩ := exists_langPlaneData_conj D g (g⁻¹ * D.w * g) (by group)
  refine ⟨D', fun α hα hk => hreg _ (CFSG.LieType.Chevalley.IsRoot.smul hα g) (hkill α hk),
    fun u => ?_⟩
  rw [hD'w, mul_smul, mul_smul, hg, smul_neg, mul_smul, mul_smul]
  simp only [inv_smul_smul]

theorem e7w3_smul (u : Fin Tag.E7.rank → ℤ) : e7w3 • u = e7T3W *ᵥ u := by
  have h : e7w3 = (coxeterSystem Tag.E7).wordProd e7T3Word := rfl
  rw [h]
  exact e7T3_weylImage u

theorem e8c0_eq : e8c0 = SeitzExcOpenRest6.Aux.wc1 * SeitzExcOpenRest6.Aux.wc2 *
    SeitzExcOpenRest6.Aux.wc3 := by
  rw [e8c0, e8c0Word, CFSG.HardMathSupport.Curtis.UnitaryLevi.wordW_append,
    CFSG.HardMathSupport.Curtis.UnitaryLevi.wordW_append]
  rfl

end Datum

end SeitzExcOpenRest7Aux

section Residual

@[expose] def E7NegCThreeRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E7 K E₀,
        (∀ α : Fin Tag.E7.rank → ℤ, IsRoot .E7 α → ¬ D.Kills α) →
        (∀ u : Fin Tag.E7.rank → ℤ, D.w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) → HyperGen 3 ⊤ E₀

@[expose] def E8NegCThreeRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E8 K →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E8 K E₀,
        (∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α → ¬ D.Kills α) →
        (∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -((SeitzExcOpenRest6.Aux.wc1 *
          SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u)) → HyperGen 3 ⊤ E₀

@[expose] def E7NegCLineRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E7 K E₀,
        (∀ α : Fin Tag.E7.rank → ℤ, IsRoot .E7 α → ¬ D.Kills α) →
        (∀ u : Fin Tag.E7.rank → ℤ, D.w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) →
        ∃ σ : Fin Tag.E7.rank → ℤ, IsRoot .E7 σ ∧ ∀ y ∈ E₀, y ≠ 1 →
          (∃ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
            rootDiagUnit .E7 a = diagMap D y ∧ rootChar a σ = 1) →
          Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E₀

@[expose] def E8NegCLineRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E8 K →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E8 K E₀,
        (∀ α : Fin Tag.E8.rank → ℤ, IsRoot .E8 α → ¬ D.Kills α) →
        (∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -((SeitzExcOpenRest6.Aux.wc1 *
          SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u)) →
        ∃ σ : Fin Tag.E8.rank → ℤ, IsRoot .E8 σ ∧ ∀ y ∈ E₀, y ≠ 1 →
          (∃ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
            rootDiagUnit .E8 a = diagMap D y ∧ rootChar a σ = 1) →
          Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E₀

end Residual

section Reduction

open SeitzExcOpenRest7Aux

theorem e7ToralNegCRest_of_rest (h : E7NegCThreeRest) : SeitzExcOpenRest6.E7ToralNegCRest := by
  intro K _ _ hK hs E₀ hE₀ hc hN D hreg hw
  obtain ⟨D', hreg', hD'⟩ := exists_e7_negC_datum hK hE₀ hc D hreg hw
  refine h K hK hs E₀ hE₀ hc hN D' hreg' fun u => ?_
  rw [hD', e7w3_smul, neg_smul, one_smul, Matrix.neg_mulVec]

theorem e8ToralNegTwistRest_of_rest (h : E8NegCThreeRest) :
    SeitzExcOpenRest6.E8ToralNegTwistRest := by
  intro K _ _ hK hs E₀ hE₀ hc hN D hreg _ hw
  obtain ⟨D', hreg', hD'⟩ := exists_e8_negC_datum hK hE₀ hc D hreg hw
  refine h K hK hs E₀ hE₀ hc hN D' hreg' fun u => ?_
  rw [hD', e8c0_eq]

theorem e7NegCThreeRest_of_lineRest (h : E7NegCLineRest) : E7NegCThreeRest := by
  intro K _ _ hK hs E₀ hE₀ hc hN D hreg hD
  haveI : IsSimpleGroup ↥(adjointGroup Tag.E7 K) :=
    isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K)
  obtain ⟨σ, hσ, hlines⟩ := h K hK hs E₀ hE₀ hc hN D hreg hD
  exact hyperGen_of_lines_of_kills langPlaneKillsRoot_E7 (by omega) hE₀ hc D hσ hlines

theorem e8NegCThreeRest_of_lineRest (h : E8NegCLineRest) : E8NegCThreeRest := by
  intro K _ _ hK hs E₀ hE₀ hc hN D hreg hD
  haveI : IsSimpleGroup ↥(adjointGroup Tag.E8 K) :=
    isSimpleGroup_adjointGroup_of_isQuasisimple (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K)
  obtain ⟨σ, hσ, hlines⟩ := h K hK hs E₀ hE₀ hc hN D hreg hD
  exact hyperGen_of_lines_of_kills langPlaneKillsRoot_E8 (by omega) hE₀ hc D hσ hlines

theorem seitzThreeResidual6_of_toral (hT : E7NegCLineRest ∧ E8NegCLineRest)
    (hrest : ThreeNonToralCubeRest .F4 LieTypeIndex.F4 ∧ SeitzGoodInnerExcThreeE6 ∧
      SeitzGoodInnerExcThreeTwE6 ∧ E7NonToralTwoRest ∧
        ThreeNonToralCubeRest .E8 LieTypeIndex.E8) :
    SeitzExcOpenRest6.SeitzThreeResidual6 :=
  ⟨hrest.1, hrest.2.1, hrest.2.2.1,
    ⟨e7ToralNegCRest_of_rest (e7NegCThreeRest_of_lineRest hT.1), hrest.2.2.2.1⟩,
    ⟨e8ToralNegTwistRest_of_rest (e8NegCThreeRest_of_lineRest hT.2), hrest.2.2.2.2⟩⟩

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
