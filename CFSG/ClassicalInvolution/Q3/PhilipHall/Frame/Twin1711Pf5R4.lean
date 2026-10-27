module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5R4Data
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Words
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Count
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Sp6Data
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.R4K

open PkG Chain CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false

@[expose] def GB : ℕ → Equiv.Perm (Fin 36)
  | 0 => TwinE4Sp6.litA
  | 1 => TwinE4Sp6.litB
  | 2 => TwinE4Sp6.litA⁻¹
  | 3 => TwinE4Sp6.litB⁻¹
  | _ => 1

theorem prep_base : ∀ l, Rep 64 36 (baseGl.getD l (one 64 36)) (GB l)
  | 0 => ⟨by decide +kernel, by decide +kernel⟩
  | 1 => ⟨by decide +kernel, by decide +kernel⟩
  | 2 => ⟨by decide +kernel, by decide +kernel⟩
  | 3 => ⟨by decide +kernel, by decide +kernel⟩
  | l + 4 => by
    have : baseGl.getD (l + 4) (one 64 36) = one 64 36 :=
      getD_default' _ _ _ (by simp [baseGl])
    rw [this]
    exact Rep.one (by norm_num) (by norm_num)

@[expose] noncomputable def LG36 : ℕ → Equiv.Perm (Fin 36) := LG letterWords GB

theorem prepL (l : ℕ) : Rep 64 36 (GLt.getD l (one 64 36)) (LG36 l) := by
  have := prep_LG (by norm_num : 0 < 64) (by norm_num : 36 ≤ 64) prep_base letterWords l
  rwa [GLt_eq] at this

theorem prepW (w : List ℕ) : Rep 64 36 (evalW 64 36 GLt w) (permW LG36 w) := by
  have := prep_permW (by norm_num : 0 < 64) (by norm_num : 36 ≤ 64) prep_base letterWords w
  rwa [GLt_eq] at this

theorem invL_fix : ∀ l, 15 ≤ l → invL l = l := fun l hl => by
  unfold invL
  exact getD_default' _ _ _ (by simpa using hl)

theorem hIL : ∀ l, LG36 (invL l) = (LG36 l)⁻¹ := by
  refine LG_inv (by norm_num : 0 < 64) (by norm_num : 36 ≤ 64) prep_base letterWords
    (invL := invL) 15 (by decide) invL_fix ?_
  intro l hl
  have h := List.all_eq_true.1 invChk_true l (List.mem_range.2 hl)
  rw [beq_iff_eq] at h
  rw [GLt_eq]
  exact h

section Cert


theorem litA_mem : TwinE4Sp6.litA ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup, ← TwinE4Sp6.sp6A_eq]
  exact sp6Gens_mem _ (by simp [sp6Gens])

theorem litB_mem : TwinE4Sp6.litB ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup, ← TwinE4Sp6.sp6B_eq]
  exact sp6Gens_mem _ (by simp [sp6Gens])

theorem GB_mem : ∀ l, GB l ∈ co3X36
  | 0 => litA_mem
  | 1 => litB_mem
  | 2 => co3X36.inv_mem litA_mem
  | 3 => co3X36.inv_mem litB_mem
  | _ + 4 => co3X36.one_mem

theorem LG36_mem (l : ℕ) : LG36 l ∈ co3X36 := permW_mem GB GB_mem _

theorem r4_eq : sp6Rep4 = LG36 14 := by
  show (sp6InvRepWords.map (evalCodes sp6Gens)).getD 3 1 = _
  rw [TwinE4Sp6.sp6Gens_eq]
  exact Equiv.ext (by decide +kernel)

theorem repR4 : Rep 64 36 r4p sp6Rep4 := by
  rw [r4_eq]
  exact prepL 14

@[expose] noncomputable def elt (w : List ℕ) : Equiv.Perm (Fin 36) := permW LG36 w

theorem rows_sound : (∀ w ∈ rows, rowOk w = true) ∧ (rows.map rowVal).Pairwise (· < ·) :=
  let h := chainChk_sound rowVal rowOk rows 0 rows_chk
  ⟨h.1, h.2.1⟩

theorem gen_comm (i : ℕ) (hi : i < 5) : LG36 (4 + 2 * i) * LG36 14 = LG36 14 * LG36 (4 + 2 * i) := by
  have hr4 := r4Chk_true
  simp only [r4Chk, Bool.and_eq_true] at hr4
  have h := List.all_eq_true.1 hr4.2 i (List.mem_range.2 hi)
  rw [beq_iff_eq] at h
  have h3 : comp 64 36 (GLt.getD (4 + 2 * i) (one 64 36)) (GLt.getD 14 (one 64 36)) =
      comp 64 36 (GLt.getD 14 (one 64 36)) (GLt.getD (4 + 2 * i) (one 64 36)) := h
  have a := (prepL (4 + 2 * i)).comp (by norm_num : 0 < 64) (prepL 14)
  have b := (prepL 14).comp (by norm_num : 0 < 64) (prepL (4 + 2 * i))
  rw [h3] at a
  exact Rep.unique a b

theorem letter_comm {l : ℕ} (h1 : 4 ≤ l) (h2 : l < 14) : LG36 l * LG36 14 = LG36 14 * LG36 l := by
  have hcase : (∃ i, i < 5 ∧ l = 4 + 2 * i) ∨ (∃ i, i < 5 ∧ l = 4 + 2 * i + 1) := by
    by_cases hp : (l - 4) % 2 = 0
    · exact Or.inl ⟨(l - 4) / 2, by omega, by omega⟩
    · exact Or.inr ⟨(l - 4) / 2, by omega, by omega⟩
  rcases hcase with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact gen_comm i hi
  · have hinv : invL (4 + 2 * i) = 4 + 2 * i + 1 := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e : LG36 (4 + 2 * i + 1) = (LG36 (4 + 2 * i))⁻¹ := by rw [← hinv, hIL]
    rw [e]
    exact ((Commute.inv_left (gen_comm i hi))).eq

theorem permW_comm {w : List ℕ} (h : ∀ l ∈ w, 4 ≤ l ∧ l < 14) :
    permW LG36 w * LG36 14 = LG36 14 * permW LG36 w := by
  induction w with
  | nil => simp [permW_nil]
  | cons l w ih =>
    rw [permW_cons]
    have h1 := letter_comm (h l (List.mem_cons_self ..)).1 (h l (List.mem_cons_self ..)).2
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    calc LG36 l * permW LG36 w * LG36 14 = LG36 l * (permW LG36 w * LG36 14) := by group
      _ = LG36 l * (LG36 14 * permW LG36 w) := by rw [h2]
      _ = (LG36 l * LG36 14) * permW LG36 w := by group
      _ = LG36 14 * LG36 l * permW LG36 w := by rw [h1]
      _ = LG36 14 * (LG36 l * permW LG36 w) := by group

theorem elt_mem_cent {w : List ℕ} (hw : w ∈ rows) : elt w ∈ centralizerIn co3X36 sp6Rep4 := by
  have hok := (rows_sound.1 w hw)
  simp only [rowOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  refine ⟨permW_mem LG36 LG36_mem w, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [r4_eq]
  exact permW_comm hok.1

theorem nodup_elts : (rows.map elt).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  have h := rows_sound.2
  rw [List.pairwise_map] at h
  refine h.imp ?_
  intro a b hab heq
  have h1 := prepW a
  have h2 := prepW b
  have h3 : permW LG36 a = permW LG36 b := heq
  rw [h3] at h1
  exact absurd (Rep.inj (by norm_num) h1 h2) (ne_of_lt hab)

theorem rows_length' : (rows.map elt).length = Nat.card (centralizerIn co3X36 sp6Rep4) := by
  rw [List.length_map, rows_length, co3X36_involution_centralizers.2.2.2.2.1]

theorem no_sqrt_r4 {w : Equiv.Perm (Fin 36)} (hw : w ∈ co3X36) : w * w ≠ sp6Rep4 := by
  intro h
  have hc : w ∈ centralizerIn co3X36 sp6Rep4 := by
    refine ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc w * sp6Rep4 = w * (w * w) := by rw [h]
      _ = (w * w) * w := by group
      _ = sp6Rep4 * w := by rw [h]
  have hm := mem_of_nodup_card (centralizerIn co3X36 sp6Rep4) (rows.map elt) nodup_elts
    (fun x hx => by
      obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hx
      exact elt_mem_cent hwd) rows_length' hc
  obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hm
  have hok := rows_sound.1 wd hwd
  simp only [rowOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  apply hok.2
  have a := (prepW wd).comp (by norm_num : 0 < 64) (prepW wd)
  have e : permW LG36 wd * permW LG36 wd = sp6Rep4 := h
  rw [e] at a
  exact Rep.inj (by norm_num) a repR4

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.R4K
