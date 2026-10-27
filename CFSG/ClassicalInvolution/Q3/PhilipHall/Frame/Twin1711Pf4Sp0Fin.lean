module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0FinB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0MaxSem

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false


theorem LG_zero : LG GB 0 = TwinE4Sp6.litA := by
  have e : letterWords.getD 0 [] = [0] := rfl
  unfold LG
  rw [e, permW_single]
  rfl

theorem LG_one : LG GB 1 = TwinE4Sp6.litB := by
  have e : letterWords.getD 1 [] = [1] := rfl
  unfold LG
  rw [e, permW_single]
  rfl

theorem LG_two : LG GB 2 = TwinE4Sp6.litA⁻¹ := by
  have e : letterWords.getD 2 [] = [2] := rfl
  unfold LG
  rw [e, permW_single]
  rfl

theorem LG_three : LG GB 3 = TwinE4Sp6.litB⁻¹ := by
  have e : letterWords.getD 3 [] = [3] := rfl
  unfold LG
  rw [e, permW_single]
  rfl

theorem r2p_mem_omP : r2p ∈ omP := by
  unfold omP
  exact List.mem_cons_self ..

theorem mem_omP {p : ℕ} (h : p ∈ omP) : p = r2p ∨ ∃ r ∈ omRecs, r.getD 0 0 = p := by
  unfold omP at h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_map.1 h)

@[expose] def OmS : Set (Equiv.Perm (Fin 36)) := {s | ∃ p ∈ omP, PRep p s}

theorem om_stab {h : Equiv.Perm (Fin 36)} (hh : h ∈ co3X36) :
    ∀ s ∈ OmS, h * s * h⁻¹ ∈ OmS ∧ h⁻¹ * s * h ∈ OmS := by
  rw [co3X36_eq_closure] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    intro s hs
    rcases hx with rfl | rfl
    · have h1 := omClosed_sound prep_base invChk_true omClosed_true hs 0 (by norm_num)
      have h2 := omClosed_sound prep_base invChk_true omClosed_true hs 2 (by norm_num)
      rw [LG_zero] at h1
      rw [LG_two, inv_inv] at h2
      exact ⟨h1, h2⟩
    · have h1 := omClosed_sound prep_base invChk_true omClosed_true hs 1 (by norm_num)
      have h2 := omClosed_sound prep_base invChk_true omClosed_true hs 3 (by norm_num)
      rw [LG_one] at h1
      rw [LG_three, inv_inv] at h2
      exact ⟨h1, h2⟩
  | one => intro s hs; simpa using hs
  | mul x y _ _ ihx ihy =>
    intro s hs
    have e1 : x * y * s * (x * y)⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by group
    have e2 : (x * y)⁻¹ * s * (x * y) = y⁻¹ * (x⁻¹ * s * x) * y := by group
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (ihx _ (ihy s hs).1).1
    · rw [e2]; exact (ihy _ (ihx s hs).2).2
  | inv x _ ih =>
    intro s hs
    exact ⟨by simpa using (ih s hs).2, by simpa using (ih s hs).1⟩

theorem genLetter_cases {i l : ℕ} (h : genLetter i l = true) :
    (4 ≤ l ∧ l ≤ 9) ∨ l = 16 + i ∨ l = 20 + i := by
  simp only [genLetter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  tauto

theorem gen_sound {i : ℕ} (hi : i < 4) :
    ∃ wa wb : List ℕ, (∀ l ∈ wa, genLetter i l = true) ∧ (∀ l ∈ wb, genLetter i l = true) ∧
      permW (LG GB) wa = TwinE4Sp6.litA ∧ permW (LG GB) wb = TwinE4Sp6.litB := by
  have h := List.all_eq_true.1 genChk_true i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hwa, hwb⟩, hea⟩, heb⟩ := h
  refine ⟨genWords.getD (2 * i) [], genWords.getD (2 * i + 1) [], hwa, hwb, ?_, ?_⟩
  · have h1 := prepW (genWords.getD (2 * i) [])
    rw [hea] at h1
    exact PRep.unique h1 (prep_base 0)
  · have h1 := prepW (genWords.getD (2 * i + 1) [])
    rw [heb] at h1
    exact PRep.unique h1 (prep_base 1)

theorem sp0_maximal (g : ModSp0) (hg : g ∉ Sp0Core.TT r2H) :
    Subgroup.closure ((Sp0Core.TT r2H : Set ModSp0) ∪ {g}) = ⊤ := by
  set M := Subgroup.closure ((Sp0Core.TT r2H : Set ModSp0) ∪ {g}) with hM
  have hTM : ∀ x ∈ Sp0Core.TT r2H, x ∈ M := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hgM : g ∈ M := Subgroup.subset_closure (Or.inr rfl)
  have hR2 : R2 ∈ OmS := ⟨r2p, r2p_mem_omP, prepW [12, 12]⟩
  obtain ⟨p, hp, hps⟩ := (om_stab g.2 R2 hR2).1
  rcases mem_omP hp with h0 | ⟨r, hr, h0⟩
  · rw [h0] at hps
    exfalso
    apply hg
    rw [mem_TT_iff]
    apply Subtype.ext
    have h1 : (g : Equiv.Perm (Fin 36)) * R2 * (g : Equiv.Perm (Fin 36))⁻¹ = R2 :=
      PRep.unique hps (prepW [12, 12])
    show (g : Equiv.Perm (Fin 36)) * (r2H : Equiv.Perm (Fin 36)) =
      (r2H : Equiv.Perm (Fin 36)) * g
    rw [r2H_val]
    calc (g : Equiv.Perm (Fin 36)) * R2 = (g * R2 * (g : Equiv.Perm (Fin 36))⁻¹) * g := by group
      _ = R2 * g := by rw [h1]
  · rw [← h0] at hps
    have hrc := List.all_eq_true.1 omRecsChk_true r hr
    obtain ⟨hl, hi, hP⟩ := omRecChk_sound prep_base invChk_true hrc
    have hEq := PRep.unique hps hP
    set i := r.getD 1 0 with hidef
    have hcT : hm (r.drop 2) ∈ Sp0Core.TT r2H := hm_mem_TT hl
    set u : ModSp0 := (hm (r.drop 2) * hm [16 + i])⁻¹ * g with hu
    have hmv : (hm [16 + i] : Equiv.Perm (Fin 36)) = LG GB (16 + i) := by
      rw [hm_val, permW_single]
    have huT : u ∈ Sp0Core.TT r2H := by
      rw [mem_TT_iff]
      apply Subtype.ext
      show ((hm (r.drop 2) : Equiv.Perm (Fin 36)) * (hm [16 + i] : Equiv.Perm (Fin 36)))⁻¹ *
          (g : Equiv.Perm (Fin 36)) * (r2H : Equiv.Perm (Fin 36)) =
        (r2H : Equiv.Perm (Fin 36)) * (((hm (r.drop 2) : Equiv.Perm (Fin 36)) *
          (hm [16 + i] : Equiv.Perm (Fin 36)))⁻¹ * (g : Equiv.Perm (Fin 36)))
      rw [r2H_val, hmv, hm_val]
      set P := permW (LG GB) (r.drop 2)
      set Mp := LG GB (16 + i)
      set G0 := (g : Equiv.Perm (Fin 36))
      have hEq2 : G0 * R2 * G0⁻¹ = P * Mp * R2 * Mp⁻¹ * P⁻¹ := hEq
      have key : G0 * R2 = (P * Mp * R2 * Mp⁻¹ * P⁻¹) * G0 := by
        rw [← hEq2]; group
      calc (P * Mp)⁻¹ * G0 * R2 = (P * Mp)⁻¹ * (G0 * R2) := by group
        _ = (P * Mp)⁻¹ * ((P * Mp * R2 * Mp⁻¹ * P⁻¹) * G0) := by rw [key]
        _ = R2 * ((P * Mp)⁻¹ * G0) := by group
    have hmM : hm [16 + i] ∈ M := by
      have e : hm [16 + i] = (hm (r.drop 2))⁻¹ * g * u⁻¹ := by
        rw [hu]; group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem (hTM _ hcT)) hgM) (M.inv_mem (hTM _ huT))
    obtain ⟨wa, wb, hwa, hwb, hA, hB⟩ := gen_sound hi
    have hletters : ∀ l, genLetter i l = true → hm [l] ∈ M := by
      intro l hl'
      rcases genLetter_cases hl' with ⟨h1, h2⟩ | rfl | rfl
      · exact hTM _ (tLetters_single (by omega) (by omega))
      · exact hmM
      · have h11 : invL (16 + i) = 20 + i := by
          have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases this with h | h | h | h <;> rw [h] <;> rfl
        rw [← h11, hm_inv_letter]
        exact M.inv_mem hmM
    have hwaM : hm wa ∈ M := hm_mem_of_letters fun l hl' => hletters l (hwa l hl')
    have hwbM : hm wb ∈ M := hm_mem_of_letters fun l hl' => hletters l (hwb l hl')
    have hle : co3X36 ≤ M.map co3X36.subtype := by
      refine le_trans (le_of_eq co3X36_eq_closure) ?_
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact ⟨hm wa, hwaM, hA⟩
      · exact ⟨hm wb, hwbM, hB⟩
    refine eq_top_iff.2 fun k _ => ?_
    obtain ⟨m, hm', hmk⟩ := hle k.2
    have : m = k := Subtype.ext hmk
    rw [← this]
    exact hm'

theorem sp0TFacts : Sp0TFacts :=
  ⟨sp0_maximal, centE_bound, index_big⟩

theorem sp0_proved : NoSandwichAt ModSp0 := sp0_of_tfacts sp0TFacts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
