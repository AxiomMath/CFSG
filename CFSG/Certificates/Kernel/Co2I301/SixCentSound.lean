module

public import Certificates.Data.Kernel.Co2I301.SixCent
public import CFSG.Certificates.Kernel.Co2I301.SixSound

public section

namespace CFSG.KS.Co2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS

@[expose] def vg (g : Equiv.Perm (Fin 63)) (y : ℕ) : ℕ :=
  if h : 0 < y ∧ y < 64 then (g ⟨y - 1, by omega⟩ : ℕ) + 1 else 0

theorem vg_lt (g : Equiv.Perm (Fin 63)) (y : ℕ) : vg g y < 64 := by
  unfold vg
  split
  · have := (g ⟨y - 1, by omega⟩).2
    omega
  · omega

theorem vg_zero (g : Equiv.Perm (Fin 63)) : vg g 0 = 0 := by simp [vg]

theorem vg_pos (g : Equiv.Perm (Fin 63)) {y : ℕ} (h0 : 0 < y) (h : y < 64) : 0 < vg g y := by
  simp [vg, h0, h]

theorem vg_val (g : Equiv.Perm (Fin 63)) (p : Fin 63) : vg g (p + 1) = g p + 1 := by
  have h : 0 < (p : ℕ) + 1 ∧ (p : ℕ) + 1 < 64 := ⟨by omega, by omega⟩
  rw [vg, dif_pos h]
  congr 3

theorem vv_eq {P : ℕ} {g : Equiv.Perm (Fin 63)} (hP : R7 P g) {y : ℕ} (hy : y < 64) :
    vv P y = vg g y := by
  rcases Nat.eq_zero_or_pos y with rfl | h0
  · rfl
  · have hb : Nat.beq y 0 = false := beq_false (by omega)
    have e : vv P y = Nat.succ (pt P (Nat.pred y)) := by
      unfold vv
      rw [hb]
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, y = p + 1 := ⟨y - 1, by omega⟩
    rw [e, Nat.pred_succ, r7_apply hP ⟨p, by omega⟩]
    exact (vg_val g ⟨p, by omega⟩).symm

theorem vg_mul (g h : Equiv.Perm (Fin 63)) {y : ℕ} (hy : y < 64) :
    vg (g * h) y = vg g (vg h y) := by
  rcases Nat.eq_zero_or_pos y with rfl | h0
  · rw [vg_zero, vg_zero, vg_zero]
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, y = p + 1 := ⟨y - 1, by omega⟩
    have e := vg_val (g * h) ⟨p, by omega⟩
    rw [e, vg_val h ⟨p, by omega⟩, vg_val g, Equiv.Perm.mul_apply]

theorem vg_one {y : ℕ} (hy : y < 64) : vg 1 y = y := by
  rcases Nat.eq_zero_or_pos y with rfl | h0
  · exact vg_zero 1
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, y = p + 1 := ⟨y - 1, by omega⟩
    rw [vg_val 1 ⟨p, by omega⟩, Equiv.Perm.one_apply]

theorem vg_inv_l (g : Equiv.Perm (Fin 63)) {y : ℕ} (hy : y < 64) : vg g⁻¹ (vg g y) = y := by
  rw [← vg_mul _ _ hy, inv_mul_cancel, vg_one hy]

theorem vg_inv_r (g : Equiv.Perm (Fin 63)) {y : ℕ} (hy : y < 64) : vg g (vg g⁻¹ y) = y := by
  rw [← vg_mul _ _ hy, mul_inv_cancel, vg_one hy]

theorem vg_ext {g h : Equiv.Perm (Fin 63)} (H : ∀ y < 64, vg g y = vg h y) : g = h := by
  refine Equiv.ext fun p => Fin.ext ?_
  have e := H (p + 1) (by omega)
  rw [vg_val, vg_val] at e
  omega

@[expose] def Lin (g : Equiv.Perm (Fin 63)) : Prop :=
  ∀ a < 64, ∀ b < 64, vg g (Nat.xor a b) = Nat.xor (vg g a) (vg g b)

@[expose] def Form (F : ℕ → ℕ → ℕ) (g : Equiv.Perm (Fin 63)) : Prop :=
  ∀ a < 64, ∀ b < 64, F (vg g a) (vg g b) = F a b

theorem xor_lt64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : Nat.xor a b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem allN_true {n : ℕ} {f : ℕ → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  allN_spec h

theorem lin_of_linK {P : ℕ} {g : Equiv.Perm (Fin 63)} (hP : R7 P g) (h : linK P = true) :
    Lin g := by
  intro a ha b hb
  have e := beq_true (allN_true (allN_true h a ha) b hb)
  rwa [vv_eq hP (xor_lt64 ha hb), vv_eq hP ha, vv_eq hP hb] at e

theorem form_of_formK {F : ℕ → ℕ → ℕ} {P : ℕ} {g : Equiv.Perm (Fin 63)} (hP : R7 P g)
    (h : formK F (vv P) = true) : Form F g := by
  intro a ha b hb
  have e := beq_true (allN_true (allN_true h a ha) b hb)
  rwa [vv_eq hP ha, vv_eq hP hb] at e

theorem lin_mul {g h : Equiv.Perm (Fin 63)} (hg : Lin g) (hh : Lin h) : Lin (g * h) := by
  intro a ha b hb
  rw [vg_mul _ _ (xor_lt64 ha hb), hh a ha b hb, hg _ (vg_lt _ _) _ (vg_lt _ _), vg_mul _ _ ha,
    vg_mul _ _ hb]

theorem form_mul {F : ℕ → ℕ → ℕ} {g h : Equiv.Perm (Fin 63)} (hg : Form F g) (hh : Form F h) :
    Form F (g * h) := by
  intro a ha b hb
  rw [vg_mul _ _ ha, vg_mul _ _ hb, hg _ (vg_lt _ _) _ (vg_lt _ _), hh a ha b hb]

theorem lin_inv {g : Equiv.Perm (Fin 63)} (hg : Lin g) : Lin g⁻¹ := by
  intro a ha b hb
  have e := hg _ (vg_lt g⁻¹ a) _ (vg_lt g⁻¹ b)
  rw [vg_inv_r g ha, vg_inv_r g hb] at e
  rw [← e, vg_inv_l g (xor_lt64 (vg_lt _ _) (vg_lt _ _))]

theorem form_inv {F : ℕ → ℕ → ℕ} {g : Equiv.Perm (Fin 63)} (hg : Form F g) : Form F g⁻¹ := by
  intro a ha b hb
  have e := hg _ (vg_lt g⁻¹ a) _ (vg_lt g⁻¹ b)
  rw [vg_inv_r g ha, vg_inv_r g hb] at e
  exact e.symm

theorem lin_one : Lin 1 := by
  intro a ha b hb
  rw [vg_one ha, vg_one hb, vg_one (xor_lt64 ha hb)]

theorem form_one (F : ℕ → ℕ → ℕ) : Form F 1 := by
  intro a ha b hb
  rw [vg_one ha, vg_one hb]

theorem lin_form_of_mem {F : ℕ → ℕ → ℕ} {A B : Equiv.Perm (Fin 63)} (hA : Lin A ∧ Form F A)
    (hB : Lin B ∧ Form F B) {g : Equiv.Perm (Fin 63)} (hg : g ∈ Subgroup.closure {A, B}) :
    Lin g ∧ Form F g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hB
  | one => exact ⟨lin_one, form_one F⟩
  | mul x y _ _ hx hy => exact ⟨lin_mul hx.1 hy.1, form_mul hx.2 hy.2⟩
  | inv x _ hx => exact ⟨lin_inv hx.1, form_inv hx.2⟩

theorem bit_cases (m i : ℕ) : bit m i = 0 ∨ bit m i = 1 := by
  unfold bit
  change Nat.land (m >>> i) 1 = 0 ∨ Nat.land (m >>> i) 1 = 1
  change (m >>> i) &&& 1 = 0 ∨ (m >>> i) &&& 1 = 1
  rw [Nat.and_one_is_mod]
  omega

theorem mul_bit_lt {b a : ℕ} (hb : b = 0 ∨ b = 1) (ha : a < 64) : Nat.mul b a < 64 := by
  rcases hb with rfl | rfl
  · change 0 * a < 64
    omega
  · change 1 * a < 64
    omega

theorem vg_mul_bit {g : Equiv.Perm (Fin 63)} {b a : ℕ} (hb : b = 0 ∨ b = 1) :
    vg g (Nat.mul b a) = Nat.mul b (vg g a) := by
  rcases hb with rfl | rfl
  · change vg g (0 * a) = 0 * vg g a
    rw [Nat.zero_mul, Nat.zero_mul, vg_zero]
  · change vg g (1 * a) = 1 * vg g a
    rw [Nat.one_mul, Nat.one_mul]

theorem vg_xb6 {g : Equiv.Perm (Fin 63)} (hL : Lin g) {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 64)
    (h1 : a1 < 64) (h2 : a2 < 64) (h3 : a3 < 64) (h4 : a4 < 64) (h5 : a5 < 64) (m : ℕ) :
    vg g (xb6 a0 a1 a2 a3 a4 a5 m) =
      xb6 (vg g a0) (vg g a1) (vg g a2) (vg g a3) (vg g a4) (vg g a5) m := by
  have c := bit_cases m
  have l0 := mul_bit_lt (c 0) h0
  have l1 := mul_bit_lt (c 1) h1
  have l2 := mul_bit_lt (c 2) h2
  have l3 := mul_bit_lt (c 3) h3
  have l4 := mul_bit_lt (c 4) h4
  have l5 := mul_bit_lt (c 5) h5
  unfold xb6
  rw [hL _ (xor_lt64 (xor_lt64 (xor_lt64 (xor_lt64 l0 l1) l2) l3) l4) _ l5,
    hL _ (xor_lt64 (xor_lt64 (xor_lt64 l0 l1) l2) l3) _ l4,
    hL _ (xor_lt64 (xor_lt64 l0 l1) l2) _ l3, hL _ (xor_lt64 l0 l1) _ l2, hL _ l0 _ l1,
    vg_mul_bit (c 0), vg_mul_bit (c 1), vg_mul_bit (c 2), vg_mul_bit (c 3), vg_mul_bit (c 4),
    vg_mul_bit (c 5)]

theorem vg_eq_candM {XC : ℕ} {X g : Equiv.Perm (Fin 63)} (hX : R7 XC X) (hL : Lin g)
    (hc : g * X = X * g) {C : ℕ → ℕ} {v0 w1 w2 : ℕ} (hv : v0 < 64) (hw1 : w1 < 64)
    (hw2 : w2 < 64) (hb : ∀ x < 64, candM XC C v0 w1 w2 x = x) {x : ℕ} (hx : x < 64) :
    vg g x = candM XC C (vg g v0) (vg g w1) (vg g w2) x := by
  have hcomm : ∀ y < 64, vg g (vg X y) = vg X (vg g y) := fun y hy => by
    rw [← vg_mul _ _ hy, hc, vg_mul _ _ hy]
  have e1 : vv XC v0 = vg X v0 := vv_eq hX hv
  have e2 : vv XC (vv XC v0) = vg X (vg X v0) := by rw [e1, vv_eq hX (vg_lt _ _)]
  have e3 : vv XC (vv XC (vv XC v0)) = vg X (vg X (vg X v0)) := by
    rw [e2, vv_eq hX (vg_lt _ _)]
  have f1 : vv XC (vg g v0) = vg X (vg g v0) := vv_eq hX (vg_lt _ _)
  have f2 : vv XC (vv XC (vg g v0)) = vg X (vg X (vg g v0)) := by rw [f1, vv_eq hX (vg_lt _ _)]
  have f3 : vv XC (vv XC (vv XC (vg g v0))) = vg X (vg X (vg X (vg g v0))) := by
    rw [f2, vv_eq hX (vg_lt _ _)]
  have hx' := hb x hx
  unfold candM at hx' ⊢
  rw [e3, e2, e1] at hx'
  rw [f3, f2, f1]
  conv_lhs => rw [← hx']
  rw [vg_xb6 hL hv (vg_lt _ _) (vg_lt _ _) (vg_lt _ _) hw1 hw2,
    hcomm (vg X (vg X v0)) (vg_lt _ _), hcomm (vg X v0) (vg_lt _ _), hcomm v0 hv]

theorem eqK_spec {f g : ℕ → ℕ} (h : eqK f g = true) : ∀ x < 64, f x = g x := fun x hx =>
  beq_true (allN_true h x hx)

theorem eqK_of {f g : ℕ → ℕ} (h : ∀ x < 64, f x = g x) : eqK f g = true := by
  unfold eqK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro x hx
  rw [h x hx]
  exact Nat.beq_refl _

theorem formK_of {F : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (h : ∀ a < 64, ∀ b < 64, F (f a) (f b) = F a b) :
    formK F f = true := by
  unfold formK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro a ha
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro b hb
  rw [h a ha b hb]
  exact Nat.beq_refl _

theorem bAnd_tt {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem fw_cases {w1 w2 w3 y : ℕ} (h : y = w1 ∨ y = w2 ∨ y = w3) : ∃ i < 3, fw w1 w2 w3 i = y := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

theorem sixCentK_sound {F : ℕ → ℕ → ℕ} {C : ℕ → ℕ} {P0 P1 XC DC v0 w1 w2 w3 : ℕ}
    {A B X D : Equiv.Perm (Fin 63)} (h0 : R7 P0 A) (h1 : R7 P1 B) (hX : R7 XC X) (hD : R7 DC D)
    (h : sixCentK F C P0 P1 XC DC v0 w1 w2 w3 = true) :
    ∀ g ∈ Subgroup.closure {A, B}, g * X = X * g → g ^ 3 = 1 → g = 1 ∨ g = D ∨ g = D * D := by
  intro g hg hc h3
  unfold sixCentK at h
  obtain ⟨hv, h⟩ := bAnd_tt h
  obtain ⟨hw1p, h⟩ := bAnd_tt h
  obtain ⟨hw1, h⟩ := bAnd_tt h
  obtain ⟨hw2p, h⟩ := bAnd_tt h
  obtain ⟨hw2, h⟩ := bAnd_tt h
  obtain ⟨hl0, h⟩ := bAnd_tt h
  obtain ⟨hl1, h⟩ := bAnd_tt h
  obtain ⟨hf0, h⟩ := bAnd_tt h
  obtain ⟨hf1, h⟩ := bAnd_tt h
  obtain ⟨hx1, h⟩ := bAnd_tt h
  obtain ⟨hx2, h⟩ := bAnd_tt h
  obtain ⟨hfix, h⟩ := bAnd_tt h
  obtain ⟨hbas, hcand⟩ := bAnd_tt h
  have hv' : v0 < 64 := blt_true hv
  have hw1' : w1 < 64 := blt_true hw1
  have hw2' : w2 < 64 := blt_true hw2
  obtain ⟨hL, hF⟩ := lin_form_of_mem ⟨lin_of_linK h0 hl0, form_of_formK h0 hf0⟩
    ⟨lin_of_linK h1 hl1, form_of_formK h1 hf1⟩ hg
  have hfixed : ∀ w, 0 < w → w < 64 → vv XC w = w →
      vg g w = w1 ∨ vg g w = w2 ∨ vg g w = w3 := by
    intro w hw0 hw hxw
    have hXw : vg X w = w := by rw [← vv_eq hX hw]; exact hxw
    have hfx : vg X (vg g w) = vg g w := by
      rw [← vg_mul _ _ hw, ← hc, vg_mul _ _ hw, hXw]
    have hy := allN_true hfix (vg g w) (vg_lt _ _)
    have hne : Nat.beq (vg g w) 0 = false := beq_false (by have := vg_pos g hw0 hw; omega)
    have hfx' : Nat.beq (vv XC (vg g w)) (vg g w) = true := by
      rw [vv_eq hX (vg_lt _ _), hfx]
      exact Nat.beq_refl _
    have hy2 := (bIf_true ((bIf_true hy).1 hfx')).2 hne
    cases e1 : Nat.beq (vg g w) w1
    · have hy3 := (bIf_true hy2).2 e1
      cases e2 : Nat.beq (vg g w) w2
      · exact Or.inr (Or.inr (beq_true ((bIf_true hy3).2 e2)))
      · exact Or.inr (Or.inl (beq_true e2))
    · exact Or.inl (beq_true e1)
  obtain ⟨i, hi, ei⟩ := fw_cases (hfixed w1 (blt_true hw1p) hw1' (beq_true hx1))
  obtain ⟨j, hj, ej⟩ := fw_cases (hfixed w2 (blt_true hw2p) hw2' (beq_true hx2))
  have hok := allN_true (allN_true (allN_true hcand (vg g v0) (vg_lt _ _)) i hi) j hj
  rw [ei, ej] at hok
  have hM : ∀ x < 64, candM XC C (vg g v0) (vg g w1) (vg g w2) x = vg g x := fun x hx =>
    (vg_eq_candM hX hL hc hv' hw1' hw2' (eqK_spec hbas) hx).symm
  have hcube : eqK (fun x => candM XC C (vg g v0) (vg g w1) (vg g w2)
      (candM XC C (vg g v0) (vg g w1) (vg g w2) (candM XC C (vg g v0) (vg g w1) (vg g w2) x)))
      (fun x => x) = true := by
    refine eqK_of fun x hx => ?_
    rw [hM x hx, hM _ (vg_lt _ _), hM _ (vg_lt _ _), ← vg_mul _ _ (vg_lt _ _), ← vg_mul _ _ hx,
      ← pow_two, ← pow_succ, h3, vg_one hx]
  have hform : formK F (candM XC C (vg g v0) (vg g w1) (vg g w2)) = true := by
    refine formK_of fun a ha b hb => ?_
    rw [hM a ha, hM b hb]
    exact hF a ha b hb
  unfold candOK at hok
  have hok' := (bIf_true hok).1 hcube
  cases e1 : eqK (candM XC C (vg g v0) (vg g w1) (vg g w2)) (fun x => x)
  · have hok2 := (bIf_true hok').2 e1
    cases e2 : eqK (candM XC C (vg g v0) (vg g w1) (vg g w2)) (vv DC)
    · have hok3 := (bIf_true hok2).2 e2
      cases e3 : eqK (candM XC C (vg g v0) (vg g w1) (vg g w2)) (fun x => vv DC (vv DC x))
      · exact absurd ((bIf_true ((bIf_true hok3).2 e3)).1 hform) Bool.false_ne_true
      · refine Or.inr (Or.inr (vg_ext fun y hy => ?_))
        rw [← hM y hy, eqK_spec e3 y hy, vg_mul _ _ hy, vv_eq hD hy, vv_eq hD (vg_lt _ _)]
    · refine Or.inr (Or.inl (vg_ext fun y hy => ?_))
      rw [← hM y hy, eqK_spec e2 y hy, vv_eq hD hy]
  · refine Or.inl (vg_ext fun y hy => ?_)
    rw [← hM y hy, eqK_spec e1 y hy, vg_one hy]

end CFSG.KS.Co2I301

end
