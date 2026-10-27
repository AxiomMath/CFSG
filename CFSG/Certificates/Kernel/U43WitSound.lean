module

public import Certificates.Data.Kernel.U43Wit
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Mathlib.Algebra.Group.Subgroup.Finite
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord
import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.KC.U43Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.U43Case

variable {n w : Nat}

theorem neB_iff (a b : Nat) : neB a b = true ↔ a ≠ b := by
  unfold neB
  rw [bIf_eq]
  cases e : Nat.beq a b
  · simp only [Bool.false_eq_true, if_false, true_iff]
    exact Nat.ne_of_beq_eq_false e
  · simp only [if_true, Bool.false_eq_true, false_iff, not_not]
    exact Nat.eq_of_beq_eq_true e

theorem prep_unique {P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext (by rw [← hg x, ← hh x])

theorem prep_pp (hn : n < 2 ^ 32) {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (hQ : PRep n w Q h) : PRep n w (pp n w P Q) (g * h) :=
  prep_pcomp hn hP hQ

theorem prep_ppw (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {P : Nat} {g : Equiv.Perm (Fin n)}
    (hP : PRep n w P g) : ∀ a, PRep n w (ppw n w P a) (g ^ a)
  | 0 => by
    rw [pow_zero]
    exact prep_pidn hn hw
  | a + 1 => by
    rw [pow_succ']
    exact prep_pp (by omega) hP (prep_ppw hn hw hP a)

theorem eq_one_of_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {P : Nat} {g : Equiv.Perm (Fin n)}
    (hP : PRep n w P g) (h : Nat.beq P (pidn n w) = true) : g = 1 := by
  rw [Nat.eq_of_beq_eq_true h] at hP
  exact prep_unique hP (prep_pidn hn hw)

theorem cpAt_fin {t c : Nat} {τ γ : Equiv.Perm (Fin n)} (ht : PRep n w t τ) (hc : PRep n w c γ)
    (x : Fin n) : cpAt w t c x.val = ((τ * γ * τ) x).val := by
  unfold cpAt
  rw [ht x, hc (τ x), ht (γ (τ x))]
  simp only [Equiv.Perm.mul_apply]

theorem app_eq {a b : Equiv.Perm (Fin n)} (h : a = b) (x : Fin n) : a x = b x := by rw [h]

theorem kFailK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {t c k wk : Nat}
    {τ γ κ : Equiv.Perm (Fin n)} (ht : PRep n w t τ) (htt : τ * τ = 1) (hc : PRep n w c γ)
    (hk : PRep n w k κ) (h : kFailK n w t c k wk = true) (hkk : κ * κ = 1) (hk1 : κ ≠ 1)
    (hkcp : κ * (τ * γ * τ⁻¹) = τ * γ * τ⁻¹ * κ) (hkkp : κ * (τ * κ * τ⁻¹) = τ * κ * τ⁻¹ * κ)
    (hkc : κ * γ * κ⁻¹ = γ⁻¹) : False := by
  have hti : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right htt
  have hki : κ⁻¹ = κ := inv_eq_of_mul_eq_one_right hkk
  rw [hti] at hkcp hkkp
  rw [hki] at hkc
  have hkc' : κ * γ * κ * γ = 1 := by rw [hkc, inv_mul_cancel]
  unfold kFailK at h
  simp only [strictB_eq, bIf_eq, Nat.blt_eq] at h
  generalize Nat.land wk (nat_lit 7) = cd at h
  generalize Nat.shiftRight wk (nat_lit 3) = x at h
  split_ifs at h
  · exact hk1 (eq_one_of_pidn hn hw hk h)
  all_goals try exact absurd h (by decide)
  all_goals obtain ⟨x', rfl⟩ : ∃ x' : Fin n, x'.val = x := ⟨⟨x, ‹x < n›⟩, rfl⟩
  all_goals rw [neB_iff] at h
  · rw [hk x', hk (κ x')] at h
    have e := app_eq hkk x'
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
    exact h (by rw [e])
  · rw [cpAt_fin ht hc x', hk ((τ * γ * τ) x'), hk x', cpAt_fin ht hc (κ x')] at h
    have e := app_eq hkcp x'
    simp only [Equiv.Perm.mul_apply] at e h
    exact h (by rw [e])
  · rw [cpAt_fin ht hk x', hk ((τ * κ * τ) x'), hk x', cpAt_fin ht hk (κ x')] at h
    have e := app_eq hkkp x'
    simp only [Equiv.Perm.mul_apply] at e h
    exact h (by rw [e])
  · rw [hc x', hk (γ x'), hc (κ (γ x')), hk (γ (κ (γ x')))] at h
    have e := app_eq hkc' x'
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
    exact h (by rw [e])

theorem cFailK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {t y c wc N : Nat}
    {WK Y : Nat → Nat} {τ ψ γ : Equiv.Perm (Fin n)} {υ : Nat → Equiv.Perm (Fin n)}
    (ht : PRep n w t τ) (htt : τ * τ = 1) (hy : PRep n w y ψ) (hc : PRep n w c γ)
    (hY : ∀ j < N, PRep n w (Y j) (υ j)) (h : cFailK n w t y c wc WK N Y = true)
    (hc3 : orderOf γ = 3) (hccp : γ * (τ * γ * τ⁻¹) = τ * γ * τ⁻¹ * γ)
    (hycp : ψ * (τ * γ * τ⁻¹) = τ * γ * τ⁻¹ * ψ)
    (hrel : ∀ a b d : ℕ, a < 3 → b < 3 → d < 3 → ψ ^ a * γ ^ b * (τ * γ * τ⁻¹) ^ d = 1 →
      a = 0 ∧ b = 0 ∧ d = 0)
    {j : Nat} (hj : j < N) (hkk : υ j * υ j = 1) (hk1 : υ j ≠ 1)
    (hkcp : υ j * (τ * γ * τ⁻¹) = τ * γ * τ⁻¹ * υ j)
    (hkkp : υ j * (τ * υ j * τ⁻¹) = τ * υ j * τ⁻¹ * υ j)
    (hkc : υ j * γ * (υ j)⁻¹ = γ⁻¹) : False := by
  have hti : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right htt
  have h3 : γ * (γ * γ) = 1 := by rw [← pow_three, ← hc3, pow_orderOf_eq_one]
  unfold cFailK at h
  simp only [strictB_eq, bIf_eq, Nat.blt_eq] at h
  generalize Nat.land wc (nat_lit 7) = cd at h
  generalize Nat.shiftRight wc (nat_lit 3) = x at h
  split_ifs at h
  · rw [allN_iff] at h
    exact kFailK_sound hn hw ht htt hc (hY j hj) (h j hj) hkk hk1 hkcp hkkp hkc
  · rw [eq_one_of_pidn hn hw hc h, orderOf_one] at hc3
    exact absurd hc3 (by decide)
  · unfold relK at h
    simp only [strictB_eq, bIf_eq, Nat.blt_eq] at h
    split_ifs at h with ha hb hd hpos
    all_goals try exact absurd h (by decide)
    have he := h
    have hcp : PRep n w (cpP n w t c) (τ * γ * τ⁻¹) := by
      rw [hti]
      exact prep_pp (by omega) (prep_pp (by omega) ht hc) ht
    have e1 := eq_one_of_pidn hn hw (prep_pp (by omega)
      (prep_pp (by omega) (prep_ppw hn hw hy _) (prep_ppw hn hw hc _)) (prep_ppw hn hw hcp _)) he
    obtain ⟨ra, rb, rd⟩ := hrel _ _ _ ha hb hd e1
    rw [ra, rb, rd] at hpos
    exact absurd hpos (by decide)
  all_goals try exact absurd h (by decide)
  all_goals obtain ⟨x', rfl⟩ : ∃ x' : Fin n, x'.val = x := ⟨⟨x, ‹x < n›⟩, rfl⟩
  all_goals rw [neB_iff] at h
  · rw [hc x', hc (γ x'), hc (γ (γ x'))] at h
    have e := app_eq h3 x'
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
    exact h (by rw [e])
  · rw [hti] at hccp
    rw [cpAt_fin ht hc x', hc ((τ * γ * τ) x'), hc x', cpAt_fin ht hc (γ x')] at h
    have e := app_eq hccp x'
    simp only [Equiv.Perm.mul_apply] at e h
    exact h (by rw [e])
  · rw [hti] at hycp
    rw [cpAt_fin ht hc x', hy ((τ * γ * τ) x'), hy x', cpAt_fin ht hc (ψ x')] at h
    have e := app_eq hycp x'
    simp only [Equiv.Perm.mul_apply] at e h
    exact h (by rw [e])

theorem noSolK_at {t y N lo len : Nat} {WC WK Y : Nat → Nat}
    (h : noSolK n w t y WC WK N Y lo len = true) {i : Nat} (h1 : lo ≤ i) (h2 : i < lo + len)
    (hi : i < N) : cFailK n w t y (Y i) (WC i) WK N Y = true := by
  unfold noSolK at h
  rw [allN_iff] at h
  have e := h (i - lo) (by omega)
  simp only [strictB_eq, bIf_eq, Nat.add_eq, Nat.add_sub_cancel' h1, Nat.blt_eq, hi,
    ↓reduceIte] at e
  exact e

theorem treeK_at {G Y YP YL : Nat → Nat} {nG N lo len : Nat}
    (h : treeK n w G nG Y YP YL N lo len = true) {i : Nat} (h1 : lo ≤ i) (h2 : i < lo + len)
    (hi : i < N) (h0 : 0 < i) : YP i < i ∧ YL i < nG ∧ Y i = pp n w (G (YL i)) (Y (YP i)) := by
  unfold treeK at h
  rw [allN_iff] at h
  have e := h (i - lo) (by omega)
  have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.mp h0
  simp only [strictB_eq, bIf_eq, Nat.add_eq, Nat.add_sub_cancel' h1, Nat.blt_eq, Nat.beq_eq,
    hi, hi0, ↓reduceIte] at e
  split_ifs at e with e1 e2
  · exact ⟨e1, e2, by first | exact e | exact Nat.eq_of_beq_eq_true e⟩
  all_goals exact absurd e (by decide)

theorem sortK_inj {Y SG : Nat → Nat} {N : Nat} (h : sortK Y SG N = true) :
    ∀ i < N, ∀ j < N, Y i = Y j → i = j := by
  unfold sortK at h
  rw [allN_iff] at h
  have hs : ∀ i < N, SG i < N ∧ (i + 1 < N → Y (SG i) < Y (SG (i + 1))) := by
    intro i hi
    have e := h i hi
    beta_reduce at e
    rw [bAnd_eq, Bool.and_eq_true] at e
    obtain ⟨e1, e2⟩ := e
    rw [bIf_eq] at e2
    refine ⟨by simpa [Nat.blt_eq] using e1, fun h1 => ?_⟩
    have hb : Nat.blt (Nat.succ i) N = true := by simpa [Nat.blt_eq] using h1
    rw [if_pos hb] at e2
    simpa [Nat.blt_eq] using e2
  have hlt : ∀ b, b < N → ∀ a < b, Y (SG a) < Y (SG b) := by
    intro b
    induction b with
    | zero => intro _ a ha; omega
    | succ b ih =>
      intro hb a hab
      have step := (hs b (by omega)).2 hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
      · exact (ih (by omega) a hab).trans step
      · exact step
  let f : Fin N → Fin N := fun a => ⟨SG a, (hs a a.2).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : SG a = SG b := congrArg Fin.val hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h' => hne (Fin.ext h')) with hl | hl
    · have := hlt b b.2 a hl
      rw [e] at this
      exact lt_irrefl _ this
    · have := hlt a a.2 b hl
      rw [e] at this
      exact lt_irrefl _ this
  have hsurj := Finite.injective_iff_surjective.1 hf
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hsurj ⟨j, hj⟩
  have ea : SG a = i := congrArg Fin.val ha
  have eb : SG b = j := congrArg Fin.val hb
  have hab : a = b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h' => hne (Fin.ext h')) with hl | hl
    · have := hlt b b.2 a hl
      rw [ea, eb, hij] at this
      exact lt_irrefl _ this
    · have := hlt a a.2 b hl
      rw [ea, eb, hij] at this
      exact lt_irrefl _ this
  rw [← ea, ← eb, hab]

end CFSG.KC.U43Wit

end
