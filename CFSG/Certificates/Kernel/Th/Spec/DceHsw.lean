module

public import CFSG.Sporadic.Bridge.Common
import all CFSG.Sporadic.Bridge.Common
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Th.S.Hsw
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE

@[expose] def cdL (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wdN : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => cdL l + 256 * wdN w

@[expose] def enT (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wdN w

theorem wLet_zero {c W : ℕ} (hc : c < 256) : CFSG.KC.wLet (c + 256 * W) 0 = c := by
  unfold CFSG.KC.wLet
  change ((c + 256 * W) >>> (8 * 0)) &&& 255 = c
  rw [Nat.mul_zero, Nat.shiftRight_zero]
  change (c + 256 * W) &&& (2 ^ 8 - 1) = c
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem wLet_succ {c W : ℕ} (hc : c < 256) (i : ℕ) :
    CFSG.KC.wLet (c + 256 * W) (i + 1) = CFSG.KC.wLet W i := by
  unfold CFSG.KC.wLet
  change ((c + 256 * W) >>> (8 * (i + 1))) &&& 255 = (W >>> (8 * i)) &&& 255
  have h1 : (c + 256 * W) >>> 8 = W := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 8 = 256 from rfl,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hc, Nat.zero_add]
  have h : (c + 256 * W) >>> (8 * (i + 1)) = W >>> (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by ring, Nat.shiftRight_add, h1]
  rw [h]

theorem cdL_lt {l : ℕ × Bool} (hl : l.1 < 100) : cdL l < 256 := by
  unfold cdL
  split_ifs <;> omega

theorem letV_cdL {G : Type*} [Group G] (y : ℕ → G) {l : ℕ × Bool} (hl : l.1 < 100) :
    letV y (cdL l) = if l.2 then y l.1 else (y l.1)⁻¹ := by
  obtain ⟨g, b⟩ := l
  cases b
  · simp only [cdL, letV, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp only at hl; omega), if_neg (by omega)]
    congr 2
    omega
  · simp only [cdL, letV, ↓reduceIte, Nat.add_zero]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1
    omega

theorem bval_wdN {G : Type*} [Group G] (y : ℕ → G) :
    ∀ L : List (ℕ × Bool), (∀ l ∈ L, l.1 < 100) →
      bval y (wdN L) L.length = (L.map fun l => if l.2 then y l.1 else (y l.1)⁻¹).prod
  | [], _ => rfl
  | l :: L, h => by
    have hl := h l (by simp)
    have ih := bval_wdN y L (fun l' hl' => h l' (by simp [hl']))
    unfold bval at ih ⊢
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
      List.map_cons, List.prod_cons]
    rw [← ih]
    have e0 : CFSG.KC.wLet (wdN (l :: L)) 0 = cdL l := wLet_zero (cdL_lt hl)
    congr 1
    · rw [e0, letV_cdL y hl]
    · congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [show wdN (l :: L) = cdL l + 256 * wdN L from rfl, wLet_succ (cdL_lt hl)]

theorem bval_enT {G : Type*} [Group G] (y : ℕ → G) (L : List (ℕ × Bool))
    (hlen : L.length < 1024) (hg : ∀ l ∈ L, l.1 < 100) :
    bval y (wWord (enT L)) (wLen (enT L)) =
      (L.map fun l => if l.2 then y l.1 else (y l.1)⁻¹).prod := by
  have h1 : wLen (enT L) = L.length := by
    unfold wLen enT
    change ((4 * L.length + 4096 * wdN L) >>> 2) &&& 1023 = _
    have : (4 * L.length + 4096 * wdN L) >>> 2 = L.length + 1024 * wdN L := by
      rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 2 = 4 from rfl,
        show 4 * L.length + 4096 * wdN L = 4 * (L.length + 1024 * wdN L) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h2 : wWord (enT L) = wdN L := by
    unfold wWord enT
    change (4 * L.length + 4096 * wdN L) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 12 = 4096 from rfl,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [h1, h2]
  exact bval_wdN y L hg

open CFSG.Sporadic.Bridge TauCeti in
theorem mk_eq_wordProd_hsw (P : GroupPresentation) (w : List (Fin P.generatorCount × Bool)) :
    PresentedGroup.mk P.relatorSet (FreeGroup.mk w) =
      wordProd (presGen P) (w.map fun l => (l.1.val, l.2)) := by
  rw [← lift_mk P (presGen P) w]
  have h : PresentedGroup.mk P.relatorSet =
      FreeGroup.lift (fun i : Fin P.generatorCount => presGen P i.val) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, presGen, dite_eq_left i.isLt]
    rfl
  rw [h]

open CFSG.Sporadic.Bridge TauCeti in
theorem wordProd_relator_hsw (P : GroupPresentation) {v : List (ℕ × Bool)}
    (hv : v ∈ P.relatorLetters) : wordProd (presGen P) v = 1 := by
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← mk_eq_wordProd_hsw]
  exact PresentedGroup.one_of_mem (relators_mem P w hw)

open TauCeti in
theorem relatorLetters_lt (p : GroupPresentation) :
    ∀ L ∈ p.relatorLetters, ∀ l ∈ L, l.1 < p.generatorCount := by
  intro L hL l hl
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hL
  obtain ⟨w, -, rfl⟩ := hL
  rw [List.mem_map] at hl
  obtain ⟨letter, -, rfl⟩ := hl
  exact letter.1.isLt

open CFSG.Sporadic.Bridge TauCeti in
theorem hsw_rel_of_pres (p : GroupPresentation) (h1 : p.generatorCount = 8)
    (h2 : ∀ r ∈ p.relatorLetters, r.length < 1024) (h3 : p.relatorLetters.map enT = Hsw.list) :
    ∀ k < 39, bval (presGen p) (wWord (Hsw.sel k)) (wLen (Hsw.sel k)) = 1 := by
  intro k hk
  have hsel : Hsw.sel k = Hsw.list.getD k 0 := by
    have : ∀ k < 39, Hsw.sel k = Hsw.list.getD k 0 := by decide +kernel
    exact this k hk
  have hlen : k < p.relatorLetters.length := by
    have : (p.relatorLetters.map enT).length = 39 := by rw [h3]; rfl
    rw [List.length_map] at this
    omega
  have hget : Hsw.list.getD k 0 = enT (p.relatorLetters[k]) := by
    rw [← h3, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen), List.getElem_map]
  have hL : p.relatorLetters[k] ∈ p.relatorLetters := List.getElem_mem hlen
  have hg : ∀ l ∈ p.relatorLetters[k], l.1 < 100 := fun l hl => by
    have := relatorLetters_lt p _ hL l hl
    omega
  rw [hsel, hget, bval_enT (presGen p) _ (h2 _ hL) hg]
  exact wordProd_relator_hsw p hL

end CFSG.KC.Th.Spec.Dce

end
