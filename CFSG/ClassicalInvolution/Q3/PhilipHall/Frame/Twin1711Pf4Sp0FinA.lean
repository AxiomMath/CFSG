module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Chk

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false

@[expose] def GB : ℕ → Equiv.Perm (Fin 36)
  | 0 => TwinE4Sp6.litA
  | 1 => TwinE4Sp6.litB
  | 2 => TwinE4Sp6.litA⁻¹
  | 3 => TwinE4Sp6.litB⁻¹
  | _ => 1

theorem prep_base : ∀ l, PRep (baseGl.getD l oneP) (GB l)
  | 0 => ⟨by decide +kernel, by decide +kernel⟩
  | 1 => ⟨by decide +kernel, by decide +kernel⟩
  | 2 => ⟨by decide +kernel, by decide +kernel⟩
  | 3 => ⟨by decide +kernel, by decide +kernel⟩
  | l + 4 => by
    have : baseGl.getD (l + 4) oneP = oneP := getD_default' _ _ _ (by simp [baseGl])
    rw [this]
    exact PRep.one

theorem invChk_true : invChk = true := by decide +kernel

theorem badChk_true : badChk = true := by decide +kernel

theorem hI : ∀ l, LG GB (invL l) = (LG GB l)⁻¹ := LG_inv prep_base invChk_true

theorem prepW (w : List ℕ) : PRep (evalW Sp0K.GL w) (permW (LG GB) w) := prep_permW prep_base w

theorem permW_append (G : ℕ → Equiv.Perm (Fin 36)) (a b : List ℕ) :
    permW G (a ++ b) = permW G a * permW G b := by
  simp [permW]

theorem permW_cons (G : ℕ → Equiv.Perm (Fin 36)) (l : ℕ) (w : List ℕ) :
    permW G (l :: w) = G l * permW G w := by
  simp [permW]

theorem permW_nil (G : ℕ → Equiv.Perm (Fin 36)) : permW G [] = 1 := rfl

theorem permW_single (G : ℕ → Equiv.Perm (Fin 36)) (l : ℕ) : permW G [l] = G l := by
  simp [permW]

theorem permW_mem {S : Subgroup (Equiv.Perm (Fin 36))} {G : ℕ → Equiv.Perm (Fin 36)}
    (h : ∀ l, G l ∈ S) (w : List ℕ) : permW G w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons l w ih => rw [permW_cons]; exact S.mul_mem (h l) ih

section Cert


theorem litA_mem : TwinE4Sp6.litA ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup, ← TwinE4Sp6.sp6A_eq]
  exact sp6Gens_mem _ (by simp [sp6Gens])

theorem litB_mem : TwinE4Sp6.litB ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup, ← TwinE4Sp6.sp6B_eq]
  exact sp6Gens_mem _ (by simp [sp6Gens])

theorem co3X36_eq_closure :
    co3X36 = Subgroup.closure {TwinE4Sp6.litA, TwinE4Sp6.litB} := by
  rw [← sp6Q_originalSubgroup, sp6Q, certificate_originalSubgroup, TwinE4Sp6.sp6Gens_eq]
  congr 1
  ext x
  simp

theorem GB_mem : ∀ l, GB l ∈ co3X36
  | 0 => litA_mem
  | 1 => litB_mem
  | 2 => co3X36.inv_mem litA_mem
  | 3 => co3X36.inv_mem litB_mem
  | _ + 4 => co3X36.one_mem

theorem LG_mem (l : ℕ) : LG GB l ∈ co3X36 := permW_mem GB_mem _

@[expose] def hm (w : List ℕ) : ModSp0 := ⟨permW (LG GB) w, permW_mem LG_mem w⟩

theorem hm_val (w : List ℕ) : (hm w : Equiv.Perm (Fin 36)) = permW (LG GB) w := rfl

theorem hm_append (a b : List ℕ) : hm (a ++ b) = hm a * hm b :=
  Subtype.ext (permW_append _ _ _)

theorem hm_cons (l : ℕ) (w : List ℕ) : hm (l :: w) = hm [l] * hm w :=
  Subtype.ext (by
    show permW (LG GB) (l :: w) = permW (LG GB) [l] * permW (LG GB) w
    rw [permW_cons, permW_single])

theorem hm_inv_letter (l : ℕ) : hm [invL l] = (hm [l])⁻¹ :=
  Subtype.ext (by
    show permW (LG GB) [invL l] = (permW (LG GB) [l])⁻¹
    rw [permW_single, permW_single, hI])

theorem hm_mem_of_letters {M : Subgroup ModSp0} {w : List ℕ} (h : ∀ l ∈ w, hm [l] ∈ M) :
    hm w ∈ M := by
  induction w with
  | nil => exact M.one_mem
  | cons l w ih =>
    rw [hm_cons]
    exact M.mul_mem (h l (List.mem_cons_self ..)) (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem rho_LG : rho () = LG GB 12 := by
  rw [TwinE4Sp6.rho_eq, TwinE4Sp6.sp6Gens_eq]
  exact Equiv.ext (by decide +kernel)

theorem jay_LG : jay () = LG GB 13 := by
  rw [TwinE4Sp6.jay_eq, TwinE4Sp6.sp6Gens_eq]
  exact Equiv.ext (by decide +kernel)

@[expose] def R2 : Equiv.Perm (Fin 36) := permW (LG GB) [12, 12]

theorem r2H_val : (r2H : Equiv.Perm (Fin 36)) = R2 := by
  show tab sp6Rep2 = _
  rw [TwinE4Sp6.r2_eq, TwinE4Sp6.sp6Gens_eq]
  exact Equiv.ext (by decide +kernel)

theorem r2H_eq : r2H = hm [12, 12] := Subtype.ext r2H_val

theorem LG_mem_K0 (l : ℕ) (hl : l = 12 ∨ l = 13) : LG GB l ∈ K0 := by
  rcases hl with rfl | rfl
  · rw [← rho_LG]; exact Subgroup.subset_closure (by simp)
  · rw [← jay_LG]; exact Subgroup.subset_closure (by simp)

theorem hm_mem_K0H {w : List ℕ} (h : ∀ l ∈ w, l = 12 ∨ l = 13) : hm w ∈ K0H := by
  show permW (LG GB) w ∈ K0
  induction w with
  | nil => exact K0.one_mem
  | cons l w ih =>
    rw [permW_cons]
    exact K0.mul_mem (LG_mem_K0 l (h l (List.mem_cons_self ..)))
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem L0w_letters : ∀ w ∈ L0w, ∀ l ∈ w, l = 12 ∨ l = 13 := by
  intro w hw l hl
  simp only [L0w, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hl <;> omega

@[expose] def tCommChk : Bool :=
  (List.range 12).all fun k =>
    compP (Sp0K.GL.getD (4 + k) oneP) r2p == compP r2p (Sp0K.GL.getD (4 + k) oneP)

theorem tCommChk_true : tCommChk = true := by decide +kernel

theorem letter_comm {l : ℕ} (h1 : 4 ≤ l) (h2 : l ≤ 15) : LG GB l * R2 = R2 * LG GB l := by
  have h := List.all_eq_true.1 tCommChk_true (l - 4) (List.mem_range.2 (by omega))
  have e : 4 + (l - 4) = l := by omega
  rw [e] at h
  have h3 : compP (Sp0K.GL.getD l oneP) r2p = compP r2p (Sp0K.GL.getD l oneP) := beq_iff_eq.1 h
  have hr : PRep r2p R2 := prepW [12, 12]
  have a := (prep_LG prep_base l).comp hr
  have b := hr.comp (prep_LG prep_base l)
  rw [h3] at a
  exact PRep.unique a b

theorem permW_comm {w : List ℕ} (h : ∀ l ∈ w, 4 ≤ l ∧ l ≤ 15) :
    permW (LG GB) w * R2 = R2 * permW (LG GB) w := by
  induction w with
  | nil => simp [permW_nil]
  | cons l w ih =>
    rw [permW_cons]
    have h1 := letter_comm (h l (List.mem_cons_self ..)).1 (h l (List.mem_cons_self ..)).2
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    calc LG GB l * permW (LG GB) w * R2 = LG GB l * (permW (LG GB) w * R2) := by group
      _ = LG GB l * (R2 * permW (LG GB) w) := by rw [h2]
      _ = (LG GB l * R2) * permW (LG GB) w := by group
      _ = R2 * LG GB l * permW (LG GB) w := by rw [h1]
      _ = R2 * (LG GB l * permW (LG GB) w) := by group

theorem hm_mem_TT {w : List ℕ} (h : ∀ l ∈ w, 4 ≤ l ∧ l ≤ 15) : hm w ∈ Sp0Core.TT r2H := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  apply Subtype.ext
  show permW (LG GB) w * (r2H : Equiv.Perm (Fin 36)) = (r2H : Equiv.Perm (Fin 36)) * permW (LG GB) w
  rw [r2H_val]
  exact permW_comm h

theorem mem_TT_iff {g : ModSp0} : g ∈ Sp0Core.TT r2H ↔ g * r2H = r2H * g := by
  simp [Sp0Core.TT, Subgroup.mem_centralizer_singleton_iff]

theorem tLetters_single {l : ℕ} (h1 : 4 ≤ l) (h2 : l ≤ 15) : hm [l] ∈ Sp0Core.TT r2H :=
  hm_mem_TT (by intro l' hl'; rw [List.mem_singleton.1 hl']; exact ⟨h1, h2⟩)

theorem mem_EE_of_conj {s x : ModSp0} (hs : s ∈ Sp0Core.TT r2H) (hx : x ∈ K0H) :
    s * x * s⁻¹ ∈ Sp0Core.EE K0H r2H :=
  (le_iSup₂ (f := fun s (_ : s ∈ Sp0Core.TT r2H) => conjSub s K0H) s hs) (conj_mem_conjSub hx)

theorem K0H_le_EE : K0H ≤ Sp0Core.EE K0H r2H := fun x hx => by
  have := mem_EE_of_conj (Subgroup.one_mem _) hx
  simpa using this

theorem hm_mem_EE_K0 {w : List ℕ} (h : ∀ l ∈ w, l = 12 ∨ l = 13) :
    hm w ∈ Sp0Core.EE K0H r2H := K0H_le_EE (hm_mem_K0H h)

theorem hm_conj_mem_EE {w : List ℕ} (h : ∀ l ∈ w, l = 12 ∨ l = 13) :
    hm ([10] ++ w ++ [11]) ∈ Sp0Core.EE K0H r2H := by
  have h11 : invL 10 = 11 := rfl
  have e : hm ([10] ++ w ++ [11]) = hm [10] * hm w * (hm [10])⁻¹ := by
    rw [hm_append, hm_append, ← hm_inv_letter, h11]
  rw [e]
  exact mem_EE_of_conj (tLetters_single (by norm_num) (by norm_num)) (hm_mem_K0H h)

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
