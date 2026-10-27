module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Check
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L42Insp

open Equiv
open scoped Pointwise

abbrev A8 : Subgroup (Perm (Fin 8)) := alternatingGroup (Fin 8)

def tau0 : Perm (Fin 8) := wg [0, 2, 4, 6]

theorem pn_tau0 : pn tau0 = ptau0 := pn_wg _

def o : Perm (Fin 8) := gen 0

theorem o_eq_wg : o = wg [0] := by simp [wg, o]

theorem pn_o : pn o = pw [0] := by rw [o_eq_wg, pn_wg]

theorem tau0_sq : tau0 * tau0 = 1 := by
  apply pn_inj
  rw [pn_mul, pn_tau0, pn_one]
  decide +kernel

theorem tau0_fpf (i : Fin 8) : tau0 i ≠ i := by
  intro h
  have h1 := pd_pn tau0 i
  rw [pn_tau0, h] at h1
  revert i
  decide +kernel

theorem sign_tau0 : Perm.sign tau0 = 1 := by
  rw [tau0, sign_wg (by decide)]
  decide

theorem o_sq : o * o = 1 :=
  mul_eq_one_iff_eq_inv.mpr (gen_inv 0).symm

theorem sign_o : Perm.sign o = -1 := sign_gen (by norm_num)

theorem o_comm_tau0 : o * tau0 = tau0 * o := by
  apply pn_inj
  rw [pn_mul, pn_mul, pn_o, pn_tau0]
  decide +kernel

theorem exists_word_of_mem {a : Nat} (h : a ∈ p0L) : ∃ w ∈ p0W, pw w = a := by
  simpa [p0L] using h

def P0 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | pn σ ∈ p0L}
  mul_mem' := by
    intro σ τ hσ hτ
    obtain ⟨w₁, hw₁, e₁⟩ := exists_word_of_mem hσ
    obtain ⟨w₂, hw₂, e₂⟩ := exists_word_of_mem hτ
    show pn (σ * τ) ∈ p0L
    rw [pn_mul, ← e₁, ← e₂]
    exact p0_check.2.2.1 w₁ hw₁ w₂ hw₂
  one_mem' := by
    show pn 1 ∈ p0L
    rw [pn_one]
    exact p0_check.2.1
  inv_mem' := by
    intro σ hσ
    obtain ⟨w, hw, e⟩ := exists_word_of_mem hσ
    have hσw : σ = wg w := pn_inj (by rw [pn_wg, e])
    show pn σ⁻¹ ∈ p0L
    rw [hσw, wg_inv, pn_wg]
    exact p0_check.2.2.2.1 w hw

theorem mem_P0 {σ : Perm (Fin 8)} : σ ∈ P0 ↔ pn σ ∈ p0L := Iff.rfl

theorem P0_le_A8 : P0 ≤ A8 := by
  intro σ hσ
  obtain ⟨w, hw, e⟩ := exists_word_of_mem hσ
  have hσw : σ = wg w := pn_inj (by rw [pn_wg, e])
  have hev := List.all_eq_true.mp p0_check.1 w hw
  simp only [evenW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hev
  rw [Perm.mem_alternatingGroup]
  rw [hσw, sign_wg (fun i hi => by simpa using hev.1 i hi)]
  obtain ⟨k, hk⟩ : ∃ k, w.length = 2 * k := ⟨w.length / 2, by omega⟩
  rw [hk, pow_mul]
  norm_num

theorem card_P0 : Nat.card P0 = 64 := by
  have e : P0 ≃ {a // a ∈ p0L} :=
    { toFun := fun σ => ⟨pn σ.1, σ.2⟩
      invFun := fun a => ⟨wg (Classical.choose (exists_word_of_mem a.2)), by
        show pn _ ∈ p0L
        rw [pn_wg, (Classical.choose_spec (exists_word_of_mem a.2)).2]
        exact a.2⟩
      left_inv := fun σ => Subtype.ext (pn_inj (by
        show pn (wg _) = pn σ.1
        rw [pn_wg, (Classical.choose_spec (exists_word_of_mem σ.2)).2]))
      right_inv := fun a => Subtype.ext (by
        show pn (wg _) = a.1
        rw [pn_wg, (Classical.choose_spec (exists_word_of_mem a.2)).2]) }
  rw [Nat.card_congr e, card_subtype_mem p0_check.2.2.2.2.1, p0_check.2.2.2.2.2.1]

theorem cent_P0 {x : Perm (Fin 8)} (hxs : Perm.sign x = 1) (hx : ∀ p ∈ P0, p * x = x * p) :
    x = 1 ∨ x = tau0 := by
  have h := enum_complete_even s8_check hxs
  simp only [s8test, Bool.and_eq_true] at h
  have h1 := h.1
  have hgens : (p0genW.all fun g => pm (pn x) (pw g) == pm (pw g) (pn x)) = true := by
    rw [List.all_eq_true]
    intro g hg
    have hgP : wg g ∈ P0 := by
      rw [mem_P0, pn_wg]
      exact p0_check.2.2.2.2.2.2.2 g hg
    have h2 := congrArg pn (hx (wg g) hgP)
    rw [pn_mul, pn_mul, pn_wg] at h2
    simpa using h2.symm
  rw [hgens] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (pn_inj (by rw [h1, pn_one]))
  · exact Or.inr (pn_inj (by rw [h1, pn_tau0]))

theorem exists_key {u : Perm (Fin 8)} (hus : Perm.sign u = 1) (hu : u * u = 1) (hfix : ∀ i, u i ≠ i)
    (hne : u ≠ tau0) : ∃ e ∈ keyTbl, e.1 = pn u := by
  have h := enum_complete_even s8_check hus
  simp only [s8test, Bool.and_eq_true] at h
  have h2 := h.2
  have hsq : (pm (pn u) (pn u) == pone) = true := by
    rw [← pn_mul, hu, pn_one]
    simp
  have hnf : hasFix (pn u) = false := by
    unfold hasFix
    rw [Bool.eq_false_iff]
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨i, hi, hi'⟩ := hany
    rw [List.mem_range] at hi
    have h3 := pd_pn u ⟨i, hi⟩
    simp only [beq_iff_eq] at hi'
    exact hfix ⟨i, hi⟩ (Fin.ext (by rw [← h3]; exact hi'))
  have hne' : (pn u == ptau0) = false := by
    rw [Bool.eq_false_iff, ne_eq, beq_iff_eq, ← pn_tau0]
    exact fun h => hne (pn_inj h)
  rw [hsq, hnf, hne'] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.or_false, List.any_eq_true, beq_iff_eq] at h2
  exact h2

def gam (j : Nat) : Perm (Fin 8) := if h : j < 6 then swap 0 1 * swap 1 ⟨j + 2, by omega⟩ else 1

theorem pn_gam {j : Nat} (hj : j < 6) : pn (gam j) = pm (pswap 0 1) (pswap 1 (j + 2)) := by
  simp only [gam, hj, dite_true]
  rw [pn_mul, pn_swap_lit, pn_swap_lit]
  rfl

theorem pn_gam_inv {j : Nat} (hj : j < 6) : pn (gam j)⁻¹ = pm (pswap 1 (j + 2)) (pswap 0 1) := by
  simp only [gam, hj, dite_true, mul_inv_rev, swap_inv]
  rw [pn_mul, pn_swap_lit, pn_swap_lit]
  rfl

def wgam (w : List Nat) : Perm (Fin 8) :=
  (w.map fun n => if n % 2 = 0 then gam (n / 2) else (gam (n / 2))⁻¹).prod

theorem pn_wgam {w : List Nat} (hw : ∀ n ∈ w, n < 12) : pn (wgam w) = pwg w := by
  induction w with
  | nil => exact pn_one
  | cons n w ih =>
    have hn : n < 12 := hw n List.mem_cons_self
    have ih' := ih (fun m hm => hw m (List.mem_cons_of_mem n hm))
    simp only [wgam, pwg, List.map_cons, List.prod_cons, List.foldr_cons] at ih' ⊢
    rw [pn_mul, ih']
    congr 1
    unfold pgam
    split_ifs with h
    · exact pn_gam (by omega)
    · exact pn_gam_inv (by omega)

theorem wgam_mem {Y : Subgroup (Perm (Fin 8))} (hY : ∀ j, gam j ∈ Y) (w : List Nat) :
    wgam w ∈ Y := by
  unfold wgam
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨n, -, rfl⟩ := hx
  split_ifs
  · exact hY _
  · exact Y.inv_mem (hY _)

theorem alt_le_of_gamma {Y : Subgroup (Perm (Fin 8))} (hY : ∀ j, gam j ∈ Y) : A8 ≤ Y := by
  show alternatingGroup (Fin 8) ≤ Y
  rw [← Perm.closure_three_cycles_eq_alternating (α := Fin 8), Subgroup.closure_le]
  intro σ hσ
  have h3 : σ.IsThreeCycle := hσ
  obtain ⟨a, ha⟩ : ∃ a, a ∈ σ.support := by
    by_contra hne
    push Not at hne
    exact h3.ne_one (Equiv.Perm.support_eq_empty_iff.mp (Finset.eq_empty_of_forall_notMem hne))
  have hnd := h3.nodup_iff_mem_support.mpr ha
  have heq := h3.eq_swap_mul_swap_iff_mem_support.mpr ha
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨hmem, hrest, -⟩ := hnd
  have hab : a ≠ σ a := fun h => hmem (by simp [← h])
  have hac : a ≠ σ (σ a) := fun h => hmem (by simp [← h])
  have hbc : σ a ≠ σ (σ a) := fun h => hrest (by simp [← h])
  set b := σ a
  set c := σ b
  have hent := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp tri_check a.val
    (List.mem_range.2 a.isLt)) b.val (List.mem_range.2 b.isLt)) c.val (List.mem_range.2 c.isLt)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hent
  rcases hent with ((hab' | hbc') | hac') | ⟨hpw, hlet⟩
  · exact absurd (Fin.ext hab') hab
  · exact absurd (Fin.ext hbc') hbc
  · exact absurd (Fin.ext hac') hac
  · have hw : pn (wgam (triTbl.getD (64 * a.val + 8 * b.val + c.val) [])) =
        pn (swap a b * swap b c) := by
      rw [pn_wgam hlet, hpw, pn_mul, pn_swap_lit, pn_swap_lit]
    rw [heq, ← pn_inj hw]
    exact wgam_mem hY _

def wpb (B : List (List Nat)) (w : List Nat) : Perm (Fin 8) :=
  (w.map fun n => if n % 2 = 0 then wg (B.getD (n / 2) []) else (wg (B.getD (n / 2) []))⁻¹).prod

theorem pn_wpb_nil (B : List (List Nat)) : pn (wpb B []) = pwb B [] := by
  simp only [wpb, pwb, List.map_nil, List.prod_nil, List.foldr_nil]
  exact pn_one

theorem pn_wpb (B : List (List Nat)) (w : List Nat) : pn (wpb B w) = pwb B w := by
  induction w with
  | nil => exact pn_wpb_nil B
  | cons n w ih =>
    simp only [wpb, pwb, List.map_cons, List.prod_cons, List.foldr_cons] at ih ⊢
    rw [pn_mul, ih]
    by_cases h : n % 2 = 0
    · simp only [h, ↓reduceIte]
      rw [pn_wg]
    · simp only [h, ↓reduceIte]
      rw [wg_inv, pn_wg]

theorem wpb_mem {X : Subgroup (Perm (Fin 8))} {B : List (List Nat)}
    (hB : ∀ b, wg (B.getD b []) ∈ X) (w : List Nat) : wpb B w ∈ X := by
  unfold wpb
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨n, -, rfl⟩ := hx
  split_ifs
  · exact hB _
  · exact X.inv_mem (hB _)

theorem sign_of_evenW {w : List Nat} (h : evenW w = true) : Perm.sign (wg w) = 1 := by
  simp only [evenW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  rw [sign_wg (fun i hi => by simpa using h.1 i hi)]
  obtain ⟨k, hk⟩ : ∃ k, w.length = 2 * k := ⟨w.length / 2, by omega⟩
  rw [hk, pow_mul]
  norm_num

theorem getD_mem_or_nil (l : List (List Nat)) (b : Nat) : l.getD b [] ∈ l ∨ l.getD b [] = [] := by
  by_cases hb : b < l.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
    exact List.getElem_mem hb
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

theorem core1 {X : Subgroup (Perm (Fin 8))} (hXA : X ≤ A8)
    (hCX : ∀ c : Perm (Fin 8), Perm.sign c = 1 → c * tau0 = tau0 * c → c ∈ X)
    (hoX : ∀ y ∈ X, o * y * o ∈ X) : (∀ x ∈ X, x * tau0 = tau0 * x) ∨ A8 ≤ X := by
  by_cases hall : ∀ x ∈ X, x * tau0 = tau0 * x
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨y, hyX, hyn⟩ := hall
  have hysign : Perm.sign y = 1 := Perm.mem_alternatingGroup.mp (hXA hyX)
  obtain ⟨u, hu⟩ : ∃ u, u = y * tau0 * y⁻¹ := ⟨_, rfl⟩
  have hu2 : u * u = 1 := by
    calc u * u = y * (tau0 * tau0) * y⁻¹ := by rw [hu]; group
      _ = 1 := by rw [tau0_sq]; group
  have hufix : ∀ i, u i ≠ i := by
    intro i hi
    apply tau0_fpf (y⁻¹ i)
    have h1 : y (tau0 (y⁻¹ i)) = i := by
      have : (y * tau0 * y⁻¹) i = i := hu ▸ hi
      simpa using this
    have h2 := congrArg (fun z => y⁻¹ z) h1
    simpa using h2
  have hune : u ≠ tau0 := by
    intro h
    apply hyn
    calc y * tau0 = (y * tau0 * y⁻¹) * y := by group
      _ = tau0 * y := by rw [← hu, h]
  have husign : Perm.sign u = 1 := by
    rw [hu, map_mul, map_mul, map_inv, sign_tau0, hysign]
    simp
  obtain ⟨e, he, hkey⟩ := exists_key husign hu2 hufix hune
  obtain ⟨hi6, hev, hcomm, hrel⟩ := entry_check e he
  obtain ⟨c, hc⟩ : ∃ c, c = wg e.2.2 := ⟨_, rfl⟩
  obtain ⟨yi, hyi⟩ : ∃ yi, yi = wg (yw e.2.1) := ⟨_, rfl⟩
  have hcsign : Perm.sign c = 1 := by rw [hc]; exact sign_of_evenW hev
  have hccomm : c * tau0 = tau0 * c := by
    apply pn_inj
    rw [pn_mul, pn_mul, hc, pn_wg, pn_tau0]
    exact hcomm
  have hcX : c ∈ X := hCX c hcsign hccomm
  have hyisign : Perm.sign yi = 1 := by
    rw [hyi]
    exact sign_of_evenW (by
      have := gens_check.2 e.2.1 hi6
      exact this)
  have hR : c * (u * c⁻¹) * yi = yi * tau0 := by
    apply pn_inj
    have e1 : pn c = pw e.2.2 := by rw [hc, pn_wg]
    have e2 : pn c⁻¹ = pw e.2.2.reverse := by rw [hc, wg_inv, pn_wg]
    have e3 : pn yi = pw (yw e.2.1) := by rw [hyi, pn_wg]
    simp only [pn_mul, e1, e2, e3, ← hkey, pn_tau0]
    exact hrel
  have hR' : c * (u * c⁻¹) = yi * tau0 * yi⁻¹ := eq_mul_inv_of_mul_eq hR
  have huy : y * tau0 = u * y := by rw [hu]; group
  have hz : yi⁻¹ * c * y * tau0 = tau0 * (yi⁻¹ * c * y) := by
    calc yi⁻¹ * c * y * tau0 = yi⁻¹ * c * (y * tau0) := by group
      _ = yi⁻¹ * c * (u * y) := by rw [huy]
      _ = yi⁻¹ * (c * (u * c⁻¹)) * (c * y) := by group
      _ = yi⁻¹ * (yi * tau0 * yi⁻¹) * (c * y) := by rw [hR']
      _ = tau0 * (yi⁻¹ * c * y) := by group
  have hzX : yi⁻¹ * c * y ∈ X := by
    apply hCX _ _ hz
    rw [map_mul, map_mul, map_inv, hyisign, hcsign, hysign]
    simp
  have hyiX : yi ∈ X := by
    have h1 : yi = c * y * (yi⁻¹ * c * y)⁻¹ := by group
    rw [h1]
    exact X.mul_mem (X.mul_mem hcX hyX) (X.inv_mem hzX)
  have hB : ∀ b, wg ((blocks e.2.1).getD b []) ∈ X := by
    intro b
    generalize hx : (blocks e.2.1).getD b [] = x
    rcases getD_mem_or_nil (blocks e.2.1) b with hmem | hnil
    · rw [hx] at hmem
      simp only [blocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hg | hg | hg
      · have hg' := gens_check.1 _ hg
        apply hCX
        · exact sign_of_evenW hg'.1
        · apply pn_inj
          rw [pn_mul, pn_mul, pn_wg, pn_tau0]
          exact hg'.2
      · rw [hg, ← hyi]
        exact hyiX
      · rw [hg, wg_append, wg_append, ← hyi, ← o_eq_wg]
        simpa [mul_assoc] using hoX yi hyiX
    · rw [hx] at hnil
      subst hnil
      simp only [wg, List.map_nil, List.prod_nil]
      exact X.one_mem
  have hgam : ∀ j, gam j ∈ X := by
    intro j
    by_cases hj : j < 6
    · have h1 := cert_check e.2.1 hi6 j hj
      have h2 : gam j = wpb (blocks e.2.1) ((repCert.getD e.2.1 []).getD j []) := by
        apply pn_inj
        rw [pn_gam hj, pn_wpb, h1]
      rw [h2]
      exact wpb_mem hB _
    · simp only [gam, hj, dite_false]
      exact X.one_mem
  exact alt_le_of_gamma hgam

theorem tau0_comm_P0 : ∀ p ∈ P0, p * tau0 = tau0 * p := by
  intro p hp
  obtain ⟨w, hw, e⟩ := exists_word_of_mem hp
  have hpw : p = wg w := pn_inj (by rw [pn_wg, e])
  apply pn_inj
  rw [pn_mul, pn_mul, pn_tau0, ← e]
  exact (p0_check.2.2.2.2.2.2.1 (pw w) (List.mem_map.2 ⟨w, hw, rfl⟩)).symm

theorem tau0_ne_one : tau0 ≠ 1 := fun h => tau0_fpf 0 (by rw [h]; rfl)

theorem core0 {X : Subgroup (Perm (Fin 8))} {σ : Perm (Fin 8)} (hσ : Perm.sign σ = -1)
    (hσP : ∀ p, σ * p * σ⁻¹ ∈ P0 ↔ p ∈ P0) (hXA : X ≤ A8)
    (hCX : ∀ c : Perm (Fin 8), Perm.sign c = 1 → c * tau0 = tau0 * c → c ∈ X)
    (hσX : ∀ x ∈ X, σ * x * σ⁻¹ ∈ X) : (∀ x ∈ X, x * tau0 = tau0 * x) ∨ A8 ≤ X := by
  have hστ : σ * tau0 * σ⁻¹ = tau0 := by
    have hcent : ∀ p ∈ P0, p * (σ * tau0 * σ⁻¹) = (σ * tau0 * σ⁻¹) * p := by
      intro p hp
      have hp' : σ⁻¹ * p * σ ∈ P0 := by
        rw [← hσP]
        have : σ * (σ⁻¹ * p * σ) * σ⁻¹ = p := by group
        rw [this]
        exact hp
      have h1 := tau0_comm_P0 _ hp'
      calc p * (σ * tau0 * σ⁻¹) = σ * ((σ⁻¹ * p * σ) * tau0) * σ⁻¹ := by group
        _ = σ * (tau0 * (σ⁻¹ * p * σ)) * σ⁻¹ := by rw [h1]
        _ = (σ * tau0 * σ⁻¹) * p := by group
    have hsgn : Perm.sign (σ * tau0 * σ⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, sign_tau0, mul_comm (Perm.sign σ) 1, one_mul, mul_inv_cancel]
    rcases cent_P0 (x := σ * tau0 * σ⁻¹) hsgn hcent with h | h
    · exfalso
      apply tau0_ne_one
      calc tau0 = σ⁻¹ * (σ * tau0 * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hσc : σ * tau0 = tau0 * σ := by
    calc σ * tau0 = (σ * tau0 * σ⁻¹) * σ := by group
      _ = tau0 * σ := by rw [hστ]
  have hcsign : Perm.sign (o * σ) = 1 := by
    rw [map_mul, sign_o, hσ]
    simp
  have hcc : (o * σ) * tau0 = tau0 * (o * σ) := by
    rw [mul_assoc, hσc, ← mul_assoc, o_comm_tau0, mul_assoc]
  have hcX : o * σ ∈ X := hCX _ hcsign hcc
  have ho_inv : o⁻¹ = o := inv_eq_of_mul_eq_one_right o_sq
  have hoX : ∀ y ∈ X, o * y * o ∈ X := by
    intro y hy
    have h1 : (o * σ)⁻¹ * y * (o * σ) ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hcX) hy) hcX
    have h2 := hσX _ h1
    have h3 : σ * ((o * σ)⁻¹ * y * (o * σ)) * σ⁻¹ = o⁻¹ * y * o := by group
    rw [h3, ho_inv] at h2
    exact h2
  exact core1 hXA hCX hoX

theorem card_A8 : Nat.card A8 = 20160 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem sylow_conj {P : Subgroup (Perm (Fin 8))} (hPA : P ≤ A8) (hP : Nat.card P = 64) : ∃ g ∈ A8, ∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ P0 := by
  have hP0A : P0 ≤ A8 := P0_le_A8
  have hP02 : IsPGroup 2 P0 := IsPGroup.of_card (n := 6) (by rw [card_P0]; norm_num)
  let PH : Subgroup ↥A8 := P.subgroupOf A8
  let P0H : Subgroup ↥A8 := P0.subgroupOf A8
  have hPHc : Nat.card PH = 64 := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv
  have hP0Hc : Nat.card P0H = 64 := by
    rw [← card_P0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0A).toEquiv
  have hPH2 : IsPGroup 2 PH := IsPGroup.of_card (n := 6) (by rw [hPHc]; norm_num)
  have hP0H2 : IsPGroup 2 P0H := IsPGroup.of_card (n := 6) (by rw [hP0Hc]; norm_num)
  have hidx : ∀ Q : Subgroup ↥A8, Nat.card Q = 64 → ¬ 2 ∣ Q.index := by
    intro Q hQ
    have h1 := Subgroup.card_mul_index Q
    rw [hQ, card_A8] at h1
    omega
  let S : Sylow 2 ↥A8 := hPH2.toSylow (hidx PH hPHc)
  let S0 : Sylow 2 ↥A8 := hP0H2.toSylow (hidx P0H hP0Hc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥A8 S S0
  have hcoe : ∀ z : ↥A8, z ∈ (S0 : Subgroup ↥A8) ↔ ∃ y ∈ PH, g * y * g⁻¹ = z := by
    intro z
    have h1 : (S0 : Subgroup ↥A8) = ((g • S : Sylow 2 ↥A8) : Subgroup ↥A8) := by rw [hg]
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simp [MulAut.smul_def, MulAut.conj_apply]
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simp [MulAut.smul_def, MulAut.conj_apply]
  refine ⟨(g : Perm (Fin 8)), g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxA : x ∈ A8 := hPA hx
    have := (hcoe (g * ⟨x, hxA⟩ * g⁻¹)).mpr ⟨⟨x, hxA⟩, hx, rfl⟩
    exact this
  · intro hx
    have hxA : x ∈ A8 := by
      have h1 : (g : Perm (Fin 8))⁻¹ * ((g : Perm (Fin 8)) * x * (g : Perm (Fin 8))⁻¹) * (g : Perm (Fin 8))
          ∈ A8 := A8.mul_mem (A8.mul_mem (A8.inv_mem g.2) (hP0A hx)) g.2
      have h2 : (g : Perm (Fin 8))⁻¹ * ((g : Perm (Fin 8)) * x * (g : Perm (Fin 8))⁻¹) *
          (g : Perm (Fin 8)) = x := by group
      rwa [h2] at h1
    obtain ⟨y, hy, hyx⟩ := (hcoe ⟨(g : Perm (Fin 8)) * x * (g : Perm (Fin 8))⁻¹, A8.mul_mem
      (A8.mul_mem g.2 hxA) (A8.inv_mem g.2)⟩).mp hx
    have : y = ⟨x, hxA⟩ := by
      apply mul_left_cancel (a := g)
      apply mul_right_cancel (b := g⁻¹)
      exact hyx
    rw [this] at hy
    exact hy

theorem finite_main {P X : Subgroup (Perm (Fin 8))} {t σ : Perm (Fin 8)} (hPA : P ≤ A8)
    (hP : Nat.card P = 64) (hts : Perm.sign t = 1) (ht1 : t ≠ 1) (htP : ∀ p ∈ P, p * t = t * p)
    (hσ : Perm.sign σ = -1)
    (hσP : ∀ p, σ * p * σ⁻¹ ∈ P ↔ p ∈ P) (hXA : X ≤ A8)
    (hCX : ∀ c : Perm (Fin 8), Perm.sign c = 1 → c * t = t * c → c ∈ X)
    (hσX : ∀ x ∈ X, σ * x * σ⁻¹ ∈ X) : (∀ x ∈ X, x * t = t * x) ∨ A8 ≤ X := by
  obtain ⟨g, hgA, hgP⟩ := sylow_conj hPA hP
  have hgsign : Perm.sign g = 1 := Perm.mem_alternatingGroup.mp hgA
  have hP0mem : ∀ p, p ∈ P0 ↔ g⁻¹ * p * g ∈ P := by
    intro p
    rw [hgP (g⁻¹ * p * g)]
    have : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
    rw [this]
  have ht' : g * t * g⁻¹ = tau0 := by
    have hcent : ∀ p ∈ P0, p * (g * t * g⁻¹) = (g * t * g⁻¹) * p := by
      intro p hp
      have h1 := htP _ ((hP0mem p).mp hp)
      calc p * (g * t * g⁻¹) = g * ((g⁻¹ * p * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = (g * t * g⁻¹) * p := by group
    have hsgn : Perm.sign (g * t * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hgsign, hts]
      simp
    rcases cent_P0 hsgn hcent with h | h
    · exfalso
      apply ht1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  let X' : Subgroup (Perm (Fin 8)) := X.map (MulAut.conj g).toMonoidHom
  have hmemX' : ∀ x', x' ∈ X' ↔ g⁻¹ * x' * g ∈ X := by
    intro x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      rw [this]
      exact hx
    · intro h
      exact ⟨g⁻¹ * x' * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hres := core0 (X := X') (σ := g * σ * g⁻¹)
    (by rw [map_mul, map_mul, map_inv, hgsign, hσ]; simp)
    (by
      intro p
      rw [hP0mem, hP0mem p, ← hσP (g⁻¹ * p * g)]
      have : g⁻¹ * (g * σ * g⁻¹ * p * (g * σ * g⁻¹)⁻¹) * g = σ * (g⁻¹ * p * g) * σ⁻¹ := by group
      rw [this])
    (by
      intro x' hx'
      have h1 := hXA ((hmemX' x').mp hx')
      rw [Perm.mem_alternatingGroup] at h1 ⊢
      rw [map_mul, map_mul, map_inv, hgsign] at h1
      simpa [hgsign] using h1)
    (by
      intro c hc hcomm
      rw [hmemX']
      apply hCX
      · rw [map_mul, map_mul, map_inv, hgsign, hc]
        simp
      · rw [← ht'] at hcomm
        calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [hcomm]
          _ = t * (g⁻¹ * c * g) := by group)
    (by
      intro x' hx'
      rw [hmemX'] at hx' ⊢
      have := hσX _ hx'
      have e : g⁻¹ * (g * σ * g⁻¹ * x' * (g * σ * g⁻¹)⁻¹) * g = σ * (g⁻¹ * x' * g) * σ⁻¹ := by group
      rw [e]
      exact this)
  rcases hres with h | h
  · left
    intro x hx
    have h1 := h (g * x * g⁻¹) ((hmemX' _).mpr (by
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [this]
      exact hx))
    rw [← ht'] at h1
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = t * x := by group
  · right
    intro a ha
    have h1 : g * a * g⁻¹ ∈ X' := h (A8.mul_mem (A8.mul_mem hgA ha) (A8.inv_mem hgA))
    rw [hmemX'] at h1
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [e] at h1

end CFSG.QuasithinUnique.Vol2Native.L239.L42Insp
