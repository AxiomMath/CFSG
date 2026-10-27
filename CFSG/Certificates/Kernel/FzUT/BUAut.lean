module

public import CFSG.Certificates.Kernel.FzUT.BUMaps
public import CFSG.Certificates.Kernel.FzUT.BU

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

theorem pmulP_lt64 : ∀ i j : Fin 64, pmulP i j < 64 := by decide +kernel

theorem commP_lt64 : ∀ i j : Fin 64, commP i j < 64 := by decide +kernel

theorem rhoBP_lt64 : ∀ i : Fin 64, rhoBP i < 64 := by decide +kernel

theorem pmulP_lt {i j : ℕ} (hi : i < 64) (hj : j < 64) : pmulP i j < 64 :=
  pmulP_lt64 ⟨i, hi⟩ ⟨j, hj⟩

theorem commP_lt {i j : ℕ} (hi : i < 64) (hj : j < 64) : commP i j < 64 :=
  commP_lt64 ⟨i, hi⟩ ⟨j, hj⟩

theorem rhoBP_lt {x : ℕ} (hx : x < 64) : rhoBP x < 64 := rhoBP_lt64 ⟨x, hx⟩

theorem pwP_lt (e : ℕ) {g : ℕ} (hg : g < 64) : pwP (e &&& 1) g < 64 := by
  unfold pwP
  have h : e &&& 1 ≤ 1 := Nat.and_le_right
  calc (e &&& 1) * g ≤ 1 * g := Nat.mul_le_mul_right g h
    _ < 64 := by omega

theorem evN_lt {g1 g2 g3 g4 : ℕ} (h1 : g1 < 64) (h2 : g2 < 64) (h3 : g3 < 64) (h4 : g4 < 64)
    (x : ℕ) : evN g1 g2 g3 g4 x < 64 :=
  pmulP_lt (pmulP_lt (pmulP_lt (pmulP_lt (pmulP_lt (pwP_lt _ h1) (pwP_lt _ h2)) (pwP_lt _ h3))
    (pwP_lt _ h4)) (pwP_lt _ (commP_lt h1 h3))) (pwP_lt _ (commP_lt h1 h4))

theorem cfP_lt {u v : ℕ} (hu : u < 64) (hv : v < 64) (x : ℕ) : cfP u v x < 64 :=
  evN_lt hu (rhoBP_lt hu) hv (rhoBP_lt hv) x

theorem fld_eq (e i : ℕ) : fld e i = e / 2 ^ (6 * i) % 64 := by
  change (e >>> (6 * i)) &&& (2 ^ 6 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_lt (e i : ℕ) : fld e i < 64 := by
  rw [fld_eq]
  exact Nat.mod_lt _ (by norm_num)

@[expose] noncomputable def tabN (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 6 i))) n

theorem tabN_spec (f : ℕ → ℕ) (n : ℕ) (hf : ∀ i < n, f i < 64) :
    tabN f n < 2 ^ (6 * n) ∧ ∀ x < n, tabN f n / 2 ^ (6 * x) % 64 = f x := by
  induction n with
  | zero => exact ⟨by simp [tabN], fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ n ih =>
    obtain ⟨hlt, hdig⟩ := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hfn : f n < 64 := hf n (Nat.lt_succ_self n)
    have hs : tabN f (n + 1) = f n * 2 ^ (6 * n) + tabN f n := by
      change Nat.lor (tabN f n) (Nat.shiftLeft (f n) (Nat.mul 6 n)) = _
      change tabN f n ||| f n <<< (6 * n) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]
    have hp : 2 ^ (6 * (n + 1)) = 64 * 2 ^ (6 * n) := by
      rw [Nat.mul_succ, Nat.pow_add]
      ring
    refine ⟨?_, ?_⟩
    · rw [hs, hp]
      calc f n * 2 ^ (6 * n) + tabN f n < f n * 2 ^ (6 * n) + 2 ^ (6 * n) :=
            Nat.add_lt_add_left hlt _
        _ = (f n + 1) * 2 ^ (6 * n) := (Nat.succ_mul _ _).symm
        _ ≤ 64 * 2 ^ (6 * n) := Nat.mul_le_mul_right _ hfn
    · intro x hx
      rw [hs]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hxn | hxn
      · have e1 : 6 * n = 6 * x + 6 + 6 * (n - x - 1) := by omega
        have hsplit : f n * 2 ^ (6 * n) = 2 ^ (6 * x) * (64 * (f n * 2 ^ (6 * (n - x - 1)))) := by
          rw [e1, Nat.pow_add, Nat.pow_add]
          ring
        rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos _), Nat.add_comm,
          Nat.add_mul_mod_self_left]
        exact hdig x hxn
      · rw [hxn, Nat.mul_comm (f n), Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt,
          Nat.add_zero, Nat.mod_eq_of_lt hfn]

theorem atP_tabP {f : ℕ → ℕ} (hf : ∀ i < 64, f i < 64) {x : ℕ} (hx : x < 64) :
    atP (tabP f) x = f x := by
  change fld (tabN f 64) x = f x
  rw [fld_eq]
  exact (tabN_spec f 64 hf).2 x hx

theorem enc_dec_lt {n : ℕ} (hn : n < 64) : enc (dec n) = n := enc_dec ⟨n, hn⟩

@[expose] noncomputable def cfD (h1 h3 : ℕ) : FzAutD := ⟨dec h1, dec (rhoBP h1), dec h3, dec (rhoBP h3)⟩

theorem enc_fzEv_cfD {h1 h3 : ℕ} (h1lt : h1 < 64) (h3lt : h3 < 64) (x : FzUT) :
    enc (fzEv (cfD h1 h3) x) = cfP h1 h3 (enc x) := by
  rw [← evN_eq]
  simp only [cfD, enc_dec_lt h1lt, enc_dec_lt h3lt, enc_dec_lt (rhoBP_lt h1lt), enc_dec_lt (rhoBP_lt h3lt)]
  rfl

theorem rhoBP_gens : rhoBP 1 = 2 ∧ rhoBP 2 = 3 ∧ rhoBP 4 = 8 ∧ rhoBP 8 = 12 := by decide +kernel

theorem gens_mul : ⁅fzE1, fzF1⁆ = fzE1 * fzF1 * fzE1 * fzF1 ∧
    ⁅fzE1, fzFW⁆ = fzE1 * fzFW * fzE1 * fzFW := by decide +kernel

theorem hAutT_sound {h1 h3 : ℕ} (h1lt : h1 < 64) (h3lt : h3 < 64)
    (h : hAutT (tabP (cfP h1 h3)) = true) :
    FzHom (cfD h1 h3) ∧ FzInj (cfD h1 h3) ∧
      ∀ x, fzEv (cfD h1 h3) (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (fzEv (cfD h1 h3) x)) := by
  set F := fzEv (cfD h1 h3) with hF
  have hlt : ∀ i < 64, cfP h1 h3 i < 64 := fun i _ => cfP_lt h1lt h3lt i
  have hat : ∀ y < 64, atP (tabP (cfP h1 h3)) y = cfP h1 h3 y := fun y hy => atP_tabP hlt hy
  have he : ∀ x, enc (F x) = cfP h1 h3 (enc x) := enc_fzEv_cfD h1lt h3lt
  simp only [hAutT, andB_true, Nat.beq_eq, allB_iff, impB_true] at h
  obtain ⟨hz, hk, hg, hr1, hr2, hr3, hr4⟩ := h
  rw [hat 0 (by norm_num)] at hz
  have h1F : F 1 = 1 := enc_injective (by rw [he, enc_one, hz])
  have hgen : ∀ g, (g = fzE1 ∨ g = fzEW ∨ g = fzF1 ∨ g = fzFW) → ∀ y, F (g * y) = F g * F y := by
    intro g hg' y
    apply enc_injective
    have hy := enc_lt y
    obtain ⟨g1, g2, g3, g4⟩ := hg (enc y) hy
    rw [he, ← pmulP_eq, ← pmulP_eq, he, he]
    rcases hg' with rfl | rfl | rfl | rfl
    · rw [enc_e1, ← hat _ (pmulP_lt (by norm_num) hy), g1, hat 1 (by norm_num), hat _ hy]
    · rw [enc_eW, ← hat _ (pmulP_lt (by norm_num) hy), g2, hat 2 (by norm_num), hat _ hy]
    · rw [enc_f1, ← hat _ (pmulP_lt (by norm_num) hy), g3, hat 4 (by norm_num), hat _ hy]
    · rw [enc_fW, ← hat _ (pmulP_lt (by norm_num) hy), g4, hat 8 (by norm_num), hat _ hy]
  have hmul : ∀ a b : FzUT, (∀ y, F (a * y) = F a * F y) → (∀ y, F (b * y) = F b * F y) →
      ∀ y, F (a * b * y) = F (a * b) * F y := by
    intro a b ha hb y
    rw [mul_assoc, ha, hb, ha b, mul_assoc]
  have hpw : ∀ (e : ZMod 2) (g : FzUT), (∀ y, F (g * y) = F g * F y) →
      ∀ y, F (fzPw e g * y) = F (fzPw e g) * F y := by
    intro e g hg' y
    unfold fzPw
    split_ifs
    · rw [one_mul, h1F, one_mul]
    · exact hg' y
  have hE1 := hgen fzE1 (Or.inl rfl)
  have hEW := hgen fzEW (Or.inr (Or.inl rfl))
  have hF1 := hgen fzF1 (Or.inr (Or.inr (Or.inl rfl)))
  have hFW := hgen fzFW (Or.inr (Or.inr (Or.inr rfl)))
  have hc1 : ∀ y, F (⁅fzE1, fzF1⁆ * y) = F ⁅fzE1, fzF1⁆ * F y := by
    rw [gens_mul.1]
    exact hmul _ _ (hmul _ _ (hmul _ _ hE1 hF1) hE1) hF1
  have hc2 : ∀ y, F (⁅fzE1, fzFW⁆ * y) = F ⁅fzE1, fzFW⁆ * F y := by
    rw [gens_mul.2]
    exact hmul _ _ (hmul _ _ (hmul _ _ hE1 hFW) hE1) hFW
  have hhom : FzHom (cfD h1 h3) := by
    intro x y
    change F (x * y) = F x * F y
    rw [fzUT_word x]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hpw _ _ hE1) (hpw _ _ hEW))
      (hpw _ _ hF1)) (hpw _ _ hFW)) (hpw _ _ hc1)) (hpw _ _ hc2) y
  refine ⟨hhom, ?_, ?_⟩
  · intro x hx
    apply enc_injective
    rw [enc_one]
    change F x = 1 at hx
    have h0 : cfP h1 h3 (enc x) = 0 := by rw [← he, hx, enc_one]
    exact hk (enc x) (enc_lt x) (by rw [hat _ (enc_lt x)]; exact h0)
  ·
    let Fm : FzUT →* FzUT := ⟨⟨F, h1F⟩, hhom⟩
    let R : FzUT →* FzUT := (fzRho0 * fzRho0 : MulAut FzUT).toMonoidHom
    have hgens : ∀ g, (g = fzE1 ∨ g = fzEW ∨ g = fzF1 ∨ g = fzFW) →
        F (fzRho0 (fzRho0 g)) = fzRho0 (fzRho0 (F g)) := by
      intro g hg'
      apply enc_injective
      rw [he, ← rhoBP_eq, ← rhoBP_eq, he]
      rcases hg' with rfl | rfl | rfl | rfl
      · rw [enc_e1, rhoBP_gens.1, ← hat 2 (by norm_num), ← hat 1 (by norm_num), hr1]
      · rw [enc_eW, rhoBP_gens.2.1, ← hat 3 (by norm_num), ← hat 2 (by norm_num), hr2]
      · rw [enc_f1, rhoBP_gens.2.2.1, ← hat 8 (by norm_num), ← hat 4 (by norm_num), hr3]
      · rw [enc_fW, rhoBP_gens.2.2.2, ← hat 12 (by norm_num), ← hat 8 (by norm_num), hr4]
    intro x
    have e1 := fzUT_hom_apply (Fm.comp R) x
    have e2 := fzUT_hom_apply (R.comp Fm) x
    change F (fzRho0 (fzRho0 x)) = _ at e1
    change fzRho0 (fzRho0 (F x)) = _ at e2
    rw [e1, e2]
    change fzEv ⟨F (fzRho0 (fzRho0 fzE1)), F (fzRho0 (fzRho0 fzEW)), F (fzRho0 (fzRho0 fzF1)),
      F (fzRho0 (fzRho0 fzFW))⟩ x = fzEv ⟨fzRho0 (fzRho0 (F fzE1)), fzRho0 (fzRho0 (F fzEW)),
      fzRho0 (fzRho0 (F fzF1)), fzRho0 (fzRho0 (F fzFW))⟩ x
    rw [hgens _ (Or.inl rfl), hgens _ (Or.inr (Or.inl rfl)), hgens _ (Or.inr (Or.inr (Or.inl rfl))),
      hgens _ (Or.inr (Or.inr (Or.inr rfl)))]

@[expose] noncomputable def autOfHom (d : FzAutD) (hh : FzHom d) (hi : FzInj d) : MulAut FzUT :=
  MulEquiv.ofBijective (⟨fzEv d, hh⟩ : FzUT →ₙ* FzUT) (by
    have h1 : fzEv d 1 = 1 := by
      have := hh 1 1
      rw [mul_one] at this
      exact mul_left_cancel (a := fzEv d 1) (by rw [mul_one]; exact this.symm)
    have hinv : ∀ y, fzEv d y⁻¹ = (fzEv d y)⁻¹ := by
      intro y
      have := hh y y⁻¹
      rw [mul_inv_cancel, h1] at this
      exact eq_inv_of_mul_eq_one_right this.symm
    have hinj : Function.Injective (fzEv d) := by
      intro x y hxy
      have hm : fzEv d (x * y⁻¹) = 1 := by
        rw [hh, hinv, hxy, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hi _ hm)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

theorem exists_cfAut {h1 h3 : ℕ} (h1lt : h1 < 64) (h3lt : h3 < 64)
    (h : hAutT (tabP (cfP h1 h3)) = true) :
    ∃ H : MulAut FzUT, (∀ x, enc (H x) = cfP h1 h3 (enc x)) ∧
      ∀ x, H (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (H x)) := by
  obtain ⟨hh, hi, hr⟩ := hAutT_sound h1lt h3lt h
  exact ⟨autOfHom _ hh hi, fun x => enc_fzEv_cfD h1lt h3lt x, hr⟩

end CFSG.KC.FzUT
