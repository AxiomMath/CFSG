
module

public import CFSG.LocalAnalysis.OddStandard.ONanCMCentBase
public import Certificates.Data.ONanB2Tabs

public section

namespace CFSG.OddStandard.ONanRec.CM

theorem wordPerm_wpow (w : List ℕ) : ∀ n : ℕ, wordPerm (wpow w n) = wordPerm w ^ n
  | 0 => by simp [wpow, wordPerm]
  | n + 1 => by
    rw [show wpow w (n + 1) = w ++ wpow w n by simp [wpow, List.replicate_succ],
      wordPerm_append, wordPerm_wpow w n, pow_succ']

theorem lt12_append {v w : List ℕ} (hv : ∀ c ∈ v, c < 12) (hw : ∀ c ∈ w, c < 12) :
    ∀ c ∈ v ++ w, c < 12 := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact hv c h
  · exact hw c h

theorem lt12_wpow {w : List ℕ} (hw : ∀ c ∈ w, c < 12) (n : ℕ) : ∀ c ∈ wpow w n, c < 12 := by
  intro c hc
  simp only [wpow, List.mem_flatten, List.mem_replicate] at hc
  obtain ⟨l, ⟨-, rfl⟩, hc⟩ := hc
  exact hw c hc

theorem lt12_yW : ∀ c ∈ yW, c < 12 := by decide
theorem lt12_zW : ∀ c ∈ zW, c < 12 := by decide
theorem lt12_dW : ∀ c ∈ dW, c < 12 := by decide
theorem lt12_fW : ∀ c ∈ fW, c < 12 := by decide
theorem lt12_gW : ∀ c ∈ gW, c < 12 := by decide
theorem lt12_r1W : ∀ c ∈ r1W, c < 12 := by decide
theorem lt12_r2W : ∀ c ∈ r2W, c < 12 := by decide

theorem lt12_rW (i j : ℕ) : ∀ c ∈ rW i j, c < 12 :=
  lt12_append (lt12_wpow lt12_r1W i) (lt12_wpow lt12_r2W j)

theorem lt12_sW (k l : ℕ) : ∀ c ∈ sW k l, c < 12 :=
  lt12_append (lt12_wpow lt12_zW k) (lt12_wpow lt12_dW l)

theorem lt12_tGens : ∀ k : ℕ, ∀ c ∈ tGens[k]!, c < 12
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | k + 3 => by simp [tGens, show (default : List ℕ) = [] from rfl]

theorem lt12_tWord (l : List ℕ) : ∀ c ∈ tWord l, c < 12 := by
  intro c hc
  simp only [tWord, List.mem_flatMap] at hc
  obtain ⟨k, -, hc⟩ := hc
  exact lt12_tGens k c hc

theorem lt12_tGens' : ∀ s ∈ tGens, ∀ c ∈ s, c < 12 := by decide

theorem lt12_rWords : ∀ w ∈ rWords, ∀ c ∈ w, c < 12 := by
  intro w hw
  simp only [rWords, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨i, -, j, -, rfl⟩ := hw
  exact lt12_rW i j

theorem lt12_rsWords : ∀ w ∈ rsWords, ∀ c ∈ w, c < 12 := by
  intro w hw
  simp only [rsWords, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨i, -, j, -, k, -, l, -, rfl⟩ := hw
  exact lt12_append (lt12_rW i j) (lt12_sW k l)

theorem lt12_qWords : ∀ w ∈ qWords, ∀ c ∈ w, c < 12 := by
  intro w hw
  simp only [qWords, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨k, -, l, -, rfl⟩ := hw
  exact lt12_append (lt12_wpow lt12_yW k) (lt12_wpow lt12_fW l)

theorem lt12_swWords {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    ∀ v ∈ swWords w, ∀ c ∈ v, c < 12 := by
  intro v hv
  simp only [swWords, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨k, -, l, -, m, -, rfl⟩ := hv
  exact lt12_append (lt12_sW k l) (lt12_wpow hw m)

theorem rW_inj' : ∀ i j i' j' : Fin 3, rW i j = rW i' j' → i = i' ∧ j = j' := by
  decide

theorem rW_inj {i j i' j' : ℕ} (hi : i < 3) (hj : j < 3) (hi' : i' < 3) (hj' : j' < 3)
    (h : rW i j = rW i' j') : i = i' ∧ j = j' := by
  have := rW_inj' ⟨i, hi⟩ ⟨j, hj⟩ ⟨i', hi'⟩ ⟨j', hj'⟩ h
  simpa [Fin.ext_iff] using this

theorem mem_rWords {i j : ℕ} (hi : i < 3) (hj : j < 3) : rW i j ∈ rWords := by
  simp only [rWords, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨i, hi, j, hj, rfl⟩

@[expose] noncomputable def yP : Equiv.Perm (Fin 480) := wordPerm yW

@[expose] noncomputable def zP : Equiv.Perm (Fin 480) := wordPerm zW

@[expose] noncomputable def dP : Equiv.Perm (Fin 480) := wordPerm dW

@[expose] noncomputable def fP : Equiv.Perm (Fin 480) := wordPerm fW

@[expose] noncomputable def gP : Equiv.Perm (Fin 480) := wordPerm gW

@[expose] noncomputable def r1P : Equiv.Perm (Fin 480) := wordPerm r1W

@[expose] noncomputable def r2P : Equiv.Perm (Fin 480) := wordPerm r2W

@[expose] noncomputable def tPerm (l : List ℕ) : Equiv.Perm (Fin 480) := wordPerm (tWord l)

theorem wordPerm_rW (i j : ℕ) : wordPerm (rW i j) = r1P ^ i * r2P ^ j := by
  rw [rW, wordPerm_append, wordPerm_wpow, wordPerm_wpow]
  rfl

theorem wordPerm_sW (k l : ℕ) : wordPerm (sW k l) = zP ^ k * dP ^ l := by
  rw [sW, wordPerm_append, wordPerm_wpow, wordPerm_wpow]
  rfl

theorem wordPerm_genCode (h : cmLettersOK = true) (i : Fin 6) :
    wordPerm [2 * i.val] = genPerm i ∧ wordPerm [2 * i.val + 1] = (genPerm i)⁻¹ := by
  simp only [wordPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact ⟨rfl, letterPerm_odd h i.2⟩

theorem wordPerm_inv (h : cmLettersOK = true) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    wordPerm (invWord w) = (wordPerm w)⁻¹ :=
  wordPerm_invWord h w hw

theorem mem_M480_wordPerm (h : cmLettersOK = true) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    wordPerm w ∈ M480 :=
  wordPerm_mem h w hw

structure B2Facts : Prop where
  fP_comm : ∀ i : Fin 6, genPerm i * fP = fP * genPerm i
  zP_sq : zP * zP = fP
  conj_zP : ∀ i : Fin 6,
    genPerm i * zP * (genPerm i)⁻¹ = zP ∨ genPerm i * zP * (genPerm i)⁻¹ = zP⁻¹
  r1P_cube : r1P ^ 3 = 1
  r2P_cube : r2P ^ 3 = 1
  r_comm : r1P * r2P = r2P * r1P
  r_inj : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
    r1P ^ i * r2P ^ j = r1P ^ i' * r2P ^ j' → i = i' ∧ j = j'
  y_r1 : yP * r1P * yP⁻¹ = r2P ^ 2
  y_r2 : yP * r2P * yP⁻¹ = r1P
  irred : ∀ i j : ℕ, i < 3 → j < 3 → ¬ (i = 0 ∧ j = 0) →
    yP * (r1P ^ i * r2P ^ j) * yP⁻¹ ≠ 1 ∧
      yP * (r1P ^ i * r2P ^ j) * yP⁻¹ ≠ r1P ^ i * r2P ^ j ∧
      yP * (r1P ^ i * r2P ^ j) * yP⁻¹ ≠ r1P ^ i * r2P ^ j * (r1P ^ i * r2P ^ j)
  z_r1 : zP * r1P = r1P * zP
  z_r2 : zP * r2P = r2P * zP
  d_r1 : dP * r1P = r1P * dP
  d_r2 : dP * r2P = r2P * dP
  zP_four : zP ^ 4 = 1
  zP_sq_ne : zP * zP ≠ 1
  dP_sq : dP * dP = 1
  d_z : dP * zP * dP = zP⁻¹
  d_notin : ∀ k < 4, dP ≠ zP ^ k
  t_nodup : (tIdx.map tPerm).Nodup
  t_closed : ∀ l ∈ tIdx, ∀ s ∈ tGens, ∃ l' ∈ tIdx, tPerm l * wordPerm s = tPerm l'
  t_norm : ∀ s ∈ tGens, ∀ r ∈ [r1W, r2W],
    (∃ i j, i < 3 ∧ j < 3 ∧ wordPerm s * wordPerm r * (wordPerm s)⁻¹ = r1P ^ i * r2P ^ j) ∧
      ∃ i j, i < 3 ∧ j < 3 ∧ (wordPerm s)⁻¹ * wordPerm r * wordPerm s = r1P ^ i * r2P ^ j
  t_cent : ∀ l ∈ tIdx, tPerm l * zP = zP * tPerm l → tPerm l * dP = dP * tPerm l →
    ∃ k m, k < 4 ∧ m < 2 ∧ tPerm l = yP ^ k * fP ^ m
  t_quot : ∀ w ∈ [yW, yW ++ fW], ∀ l ∈ tIdx, (∃ m < 4, tPerm l * tPerm l = wordPerm w ^ m) →
    ∃ k n m, k < 4 ∧ n < 2 ∧ m < 4 ∧ tPerm l = zP ^ k * dP ^ n * wordPerm w ^ m
  yP_four : yP ^ 4 = 1
  yP_sq_ne : yP * yP ≠ 1

@[expose] def B2Chain : Prop :=
  ∀ g ∈ M480,
    ((∀ i : Fin 6, genPerm i * g = g * genPerm i) → g = 1 ∨ g = fP) ∧
      (g * r1P = r1P * g → g * r2P = r2P * g →
        ∃ i j k l, i < 3 ∧ j < 3 ∧ k < 4 ∧ l < 2 ∧ g = r1P ^ i * r2P ^ j * (zP ^ k * dP ^ l)) ∧
      (g * zP = zP * g → g * dP = dP * g → g * g * (g * g) = 1 → g * g ≠ 1 →
        ∃ i j k l, i < 3 ∧ j < 3 ∧ (k = 1 ∨ k = 3) ∧ l < 2 ∧
          g = r1P ^ i * r2P ^ j * yP ^ k * fP ^ l)

end CFSG.OddStandard.ONanRec.CM
