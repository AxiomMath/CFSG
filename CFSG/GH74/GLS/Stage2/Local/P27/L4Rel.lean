module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Grp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q CFSG.GH74.GLS.Stage2.Local.P27.Psp4

variable {G : Type} [Group G]

structure Rel4 (a b a' b' t w : G) (M : ℕ) : Prop extends Rel a b a' b' t M where
  w_sq : w * w = 1
  tw : t * w = w * t
  wa : w * a * w⁻¹ = a⁻¹
  wb : w * b * w⁻¹ = a ^ (2 * M) * a⁻¹ * b

structure Core4 (z u τ x₀ y e : G) (n : ℕ) : Prop where
  four_dvd : 4 ∣ n
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  τ_ord : orderOf τ = n
  y_ord : orderOf y = n
  x₀_sq : x₀ * x₀ = 1
  x₀_τ : x₀ * τ * x₀⁻¹ = τ⁻¹
  x₀_not : x₀ ∉ zpowers τ
  e_sq : e * e = 1
  e_y : e * y * e⁻¹ = y⁻¹
  e_not : e ∉ zpowers y
  τ_y : τ * y = y * τ
  τ_e : τ * e = e * τ
  x₀_y : x₀ * y = y * x₀
  x₀_e : x₀ * e = e * x₀
  u_eq : u = τ ^ (n / 2)
  uz_eq : u * z = y ^ (n / 2)
  inter : (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) = ⊥

theorem false_of_sq_eq_one {g : G} {n : ℕ} (hn : 4 ≤ n) (hg : orderOf g = n) (hgg : g * g = 1) :
    False := by
  have h1 : g ^ 2 = 1 := by rw [pow_two]; exact hgg
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_mem_zpowers_of_inv {x g : G} {n : ℕ} (hn : 4 ≤ n) (hg : orderOf g = n)
    (hxg : x * g * x⁻¹ = g⁻¹) : x ∉ zpowers g := by
  intro hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hc : Commute (g ^ k) g := (Commute.refl g).zpow_left k
  have h1 : g ^ k * g * (g ^ k)⁻¹ = g := mul_inv_eq_iff_eq_mul.2 hc.eq
  rw [hxg] at h1
  exact false_of_sq_eq_one hn hg (mul_eq_one_iff_eq_inv.2 h1.symm)

theorem orderOf_eq_of_sq {x : G} {m : ℕ} (hm : 2 ∣ m) (h : orderOf (x * x) = m) :
    orderOf x = 2 * m := by
  rw [← pow_two, orderOf_pow' x two_ne_zero] at h
  rcases Nat.even_or_odd (orderOf x) with he | ho
  · have h2 : 2 ∣ orderOf x := even_iff_two_dvd.1 he
    rw [Nat.gcd_eq_right h2] at h
    omega
  · have h1 : Nat.gcd (orderOf x) 2 = 1 := Nat.coprime_two_right.2 ho
    rw [h1, Nat.div_one] at h
    have : Even (orderOf x) := by rw [h]; exact even_iff_two_dvd.2 hm
    exact absurd ho (Nat.not_odd_iff_even.2 this)

theorem commute_pow_of_inv {x δ : G} {M : ℕ} (hx : x * δ = δ⁻¹ * x) (hsq : δ ^ M * δ ^ M = 1) :
    x * δ ^ M = δ ^ M * x := by
  have h1 : SemiconjBy x (δ ^ M) ((δ⁻¹) ^ M) := (show SemiconjBy x δ δ⁻¹ from hx).pow_right M
  rw [inv_pow, inv_eq_of_mul_eq_one_right hsq] at h1
  exact h1.eq

theorem inter_eq_bot {z u τ x₀ y e : G} {n : ℕ} (h4 : 4 ∣ n) (hz1 : z ≠ 1) (hτ : orderOf τ = n)
    (hy : orderOf y = n) (hx0 : x₀ * x₀ = 1) (hx0τ : x₀ * τ * x₀⁻¹ = τ⁻¹) (he : e * e = 1)
    (hey : e * y * e⁻¹ = y⁻¹) (hτy : τ * y = y * τ) (hτe : τ * e = e * τ) (hu : u = τ ^ (n / 2))
    (huz : u * z = y ^ (n / 2)) :
    (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) = ⊥ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hz1
    have h1 : u * z = 1 := by rw [huz]; simp
    rw [hu] at h1
    simpa using h1
  have hn4 : 4 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h4
  have : NeZero n := ⟨hn0⟩
  have hτn : τ ^ n = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hyn : y ^ n = 1 := hy ▸ pow_orderOf_eq_one y
  have hτ2 : orderOf τ = 2 * (n / 2) := by rw [hτ]; omega
  have hy2 : orderOf y = 2 * (n / 2) := by rw [hy]; omega
  have hx0c : ¬ Commute x₀ τ := by
    intro hc
    have h1 : x₀ * τ * x₀⁻¹ = τ := mul_inv_eq_iff_eq_mul.2 hc.eq
    rw [hx0τ] at h1
    exact false_of_sq_eq_one hn4 hτ (mul_eq_one_iff_eq_inv.2 h1.symm)
  have hec : ¬ Commute e y := by
    intro hc
    have h1 : e * y * e⁻¹ = y := mul_inv_eq_iff_eq_mul.2 hc.eq
    rw [hey] at h1
    exact false_of_sq_eq_one hn4 hy (mul_eq_one_iff_eq_inv.2 h1.symm)
  have hτy' : Commute τ y := hτy
  have hτe' : Commute τ e := hτe
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [mem_bot]
  obtain ⟨i, hi⟩ := (mem_dihedral_iff n hτn hx0 hx0τ).1 hg1
  obtain ⟨j, hj⟩ := (mem_dihedral_iff n hyn he hey).1 hg2
  rcases hi with hi | hi <;> rcases hj with hj | hj
  ·
    have e1 : τ ^ i = y ^ j := hi.symm.trans hj
    have h1 : e * y ^ j * e⁻¹ = (y ^ j)⁻¹ := by rw [← conj_pow, hey, inv_pow]
    have h2 : e * τ ^ i * e⁻¹ = τ ^ i := mul_inv_eq_iff_eq_mul.2 ((hτe'.pow_left i).eq.symm)
    have h3 : (y ^ j)⁻¹ = y ^ j := by rw [← h1, ← e1]; exact h2
    have hsq : y ^ j * y ^ j = 1 := by nth_rewrite 1 [← h3]; exact inv_mul_cancel _
    rcases eq_one_or_pow_half hy2 hsq with h4 | h4
    · rw [hj]; exact h4
    · have hτsq : τ ^ i * τ ^ i = 1 := by rw [e1]; exact hsq
      rcases eq_one_or_pow_half hτ2 hτsq with h5 | h5
      · rw [hi]; exact h5
      · exfalso
        apply hz1
        have h6 : u = u * z := by rw [huz, ← h4, ← e1, h5, hu]
        exact mul_left_cancel (a := u) (by rw [mul_one]; exact h6.symm)
  ·
    exfalso
    have e1 : e * y ^ j = τ ^ i := hj.symm.trans hi
    have e2 : e = τ ^ i * (y ^ j)⁻¹ := eq_mul_inv_of_mul_eq e1
    apply hec
    rw [e2]
    exact (hτy'.pow_left i).mul_left ((Commute.refl y).pow_left j).inv_left
  ·
    exfalso
    have e1 : x₀ * τ ^ i = y ^ j := hi.symm.trans hj
    have e2 : x₀ = y ^ j * (τ ^ i)⁻¹ := eq_mul_inv_of_mul_eq e1
    apply hx0c
    rw [e2]
    exact (hτy'.symm.pow_left j).mul_left ((Commute.refl τ).pow_left i).inv_left
  ·
    exfalso
    have hg : τ * (x₀ * τ ^ i) = (x₀ * τ ^ i) * τ := by
      rw [hi.symm.trans hj]
      exact (hτe'.mul_right (hτy'.pow_right j)).eq
    apply hx0c
    show x₀ * τ = τ * x₀
    refine mul_right_cancel (b := τ ^ i) ?_
    calc (x₀ * τ) * τ ^ i = x₀ * (τ * τ ^ i) := mul_assoc _ _ _
      _ = x₀ * (τ ^ i * τ) := by rw [(Commute.pow_right (Commute.refl τ) i).eq]
      _ = (x₀ * τ ^ i) * τ := (mul_assoc _ _ _).symm
      _ = τ * (x₀ * τ ^ i) := hg.symm
      _ = (τ * x₀) * τ ^ i := (mul_assoc _ _ _).symm

namespace Rel4

variable {a b a' b' t w : G} {M : ℕ}

theorem w_inv (h : Rel4 a b a' b' t w M) : w⁻¹ = w := inv_eq_of_mul_eq_one_right h.w_sq

theorem wa_eq (h : Rel4 a b a' b' t w M) : w * a = a⁻¹ * w := mul_inv_eq_iff_eq_mul.1 h.wa

theorem w_t (h : Rel4 a b a' b' t w M) : w * t * w⁻¹ = t := mul_inv_eq_iff_eq_mul.2 h.tw.symm

theorem w_tinv (h : Rel4 a b a' b' t w M) : w * t⁻¹ * w⁻¹ = t⁻¹ := by
  calc w * t⁻¹ * w⁻¹ = (w * t * w⁻¹)⁻¹ := by group
    _ = t⁻¹ := by rw [h.w_t]

theorem wa' (h : Rel4 a b a' b' t w M) : w * a' * w⁻¹ = a'⁻¹ := by
  have h2 : a' = t * a * t⁻¹ := by rw [h.t_inv]; exact h.tat.symm
  calc w * a' * w⁻¹ = (w * t * w⁻¹) * (w * a * w⁻¹) * (w * t⁻¹ * w⁻¹) := by rw [h2]; group
    _ = t * a⁻¹ * t⁻¹ := by rw [h.w_t, h.wa, h.w_tinv]
    _ = (t * a * t⁻¹)⁻¹ := by group
    _ = a'⁻¹ := by rw [← h2]

theorem wb' (h : Rel4 a b a' b' t w M) : w * b' * w⁻¹ = a ^ (2 * M) * a'⁻¹ * b' := by
  have h2 : b' = t * b * t⁻¹ := by rw [h.t_inv]; exact h.tbt.symm
  have h3 : t * a ^ (2 * M) * t⁻¹ = a ^ (2 * M) := by rw [← conj_pow, h.t_inv, h.tat, h.z_eq]
  have h4 : t * a * t⁻¹ = a' := by rw [h.t_inv]; exact h.tat
  calc w * b' * w⁻¹ = (w * t * w⁻¹) * (w * b * w⁻¹) * (w * t⁻¹ * w⁻¹) := by rw [h2]; group
    _ = t * (a ^ (2 * M) * a⁻¹ * b) * t⁻¹ := by rw [h.w_t, h.wb, h.w_tinv]
    _ = (t * a ^ (2 * M) * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹) := by group
    _ = a ^ (2 * M) * a'⁻¹ * b' := by rw [h3, h4, ← h2]

theorem z_inv (h : Rel4 a b a' b' t w M) : (a ^ (2 * M))⁻¹ = a ^ (2 * M) :=
  inv_eq_of_mul_eq_one_right h.aN_sq

theorem z_comm_a (_h : Rel4 a b a' b' t w M) : a ^ (2 * M) * a = a * a ^ (2 * M) :=
  (Commute.pow_left (Commute.refl a) (2 * M)).eq

theorem z_comm_b (h : Rel4 a b a' b' t w M) : a ^ (2 * M) * b = b * a ^ (2 * M) := by
  have h1 := (show SemiconjBy b a a⁻¹ from h.qg.bcomm).pow_right (2 * M)
  rw [inv_pow, h.z_inv] at h1
  exact h1.eq.symm

theorem z_comm_a' (h : Rel4 a b a' b' t w M) : a ^ (2 * M) * a' = a' * a ^ (2 * M) := by
  rw [← h.z_eq]; exact (Commute.pow_left (Commute.refl a') (2 * M)).eq

theorem z_comm_b' (h : Rel4 a b a' b' t w M) : a ^ (2 * M) * b' = b' * a ^ (2 * M) :=
  (Commute.pow_left (show Commute a b' from h.c_ab) (2 * M)).eq

theorem z_comm_t (h : Rel4 a b a' b' t w M) : a ^ (2 * M) * t = t * a ^ (2 * M) := by
  have h1 := (show SemiconjBy t a a' from h.ta).pow_right (2 * M)
  rw [h.z_eq] at h1
  exact h1.eq.symm

theorem z_comm_w (h : Rel4 a b a' b' t w M) : a ^ (2 * M) * w = w * a ^ (2 * M) := by
  have h1 := (show SemiconjBy w a a⁻¹ from h.wa_eq).pow_right (2 * M)
  rw [inv_pow, h.z_inv] at h1
  exact h1.eq.symm

theorem aM_inv (h : Rel4 a b a' b' t w M) : (a ^ M)⁻¹ = a ^ (2 * M) * a ^ M := by
  have h1 : a ^ (2 * M) * a ^ M * a ^ M = 1 := by
    rw [mul_assoc, ← pow_add, ← two_mul]; exact h.aN_sq
  exact (eq_inv_of_mul_eq_one_left h1).symm

theorem sc_b0_a (h : Rel4 a b a' b' t w M) : SemiconjBy (b * b') a a⁻¹ := by
  have e : (b * b') * a = a⁻¹ * (b * b') := by simpa using h.b0_zpow_a 1
  exact e

theorem sc_b0_a' (h : Rel4 a b a' b' t w M) : SemiconjBy (b * b') a' a'⁻¹ := by
  have e : (b * b') * a' = a'⁻¹ * (b * b') := by simpa using h.b0_zpow_a' 1
  exact e

theorem dl2_inv (h : Rel4 a b a' b' t w M) : (a * a')⁻¹ = a⁻¹ * a'⁻¹ := by
  rw [mul_inv_rev]; exact h.commute_a_a'.inv_inv.eq.symm

theorem sc_b0_dl2 (h : Rel4 a b a' b' t w M) : SemiconjBy (b * b') (a * a') (a * a')⁻¹ := by
  rw [h.dl2_inv]; exact h.sc_b0_a.mul_right h.sc_b0_a'

theorem dl2_M_sq (h : Rel4 a b a' b' t w M) : (a * a') ^ M * (a * a') ^ M = 1 := by
  have := pow_orderOf_eq_one (a * a')
  rwa [h.orderOf_dl2, two_mul, pow_add] at this

theorem u_eq_dl2_pow (h : Rel4 a b a' b' t w M) : a ^ M * a' ^ M = (a * a') ^ M :=
  (Commute.mul_pow h.commute_a_a' M).symm

theorem u_sq (h : Rel4 a b a' b' t w M) : (a ^ M * a' ^ M) * (a ^ M * a' ^ M) = 1 := by
  rw [h.u_eq_dl2_pow]; exact h.dl2_M_sq

theorem u_ne_one (h : Rel4 a b a' b' t w M) : a ^ M * a' ^ M ≠ 1 := by
  rw [h.u_eq_dl2_pow]; exact h.dl2_M_ne_one

theorem u_ne_z (h : Rel4 a b a' b' t w M) : a ^ M * a' ^ M ≠ a ^ (2 * M) := by
  intro e
  apply h.dl1_M_ne_one
  have h1 := h.dl2_M
  rw [← h.u_eq_dl2_pow, e] at h1
  exact mul_right_cancel (b := a ^ (2 * M)) (by rw [one_mul]; exact h1.symm)

theorem b_u (h : Rel4 a b a' b' t w M) :
    b * (a ^ M * a' ^ M) * b⁻¹ = (a ^ M * a' ^ M) * a ^ (2 * M) := by
  have h1 : SemiconjBy b (a ^ M) ((a⁻¹) ^ M) :=
    (show SemiconjBy b a a⁻¹ from h.qg.bcomm).pow_right M
  have h2 : SemiconjBy b (a' ^ M) (a' ^ M) := (show SemiconjBy b a' a' from h.c_ba).pow_right M
  have h3 := h1.mul_right h2
  have hz1 : Commute (a ^ (2 * M)) (a ^ M) := (Commute.refl a).pow_pow _ _
  have hz2 : Commute (a ^ (2 * M)) (a' ^ M) := by
    rw [← h.z_eq]; exact (Commute.refl a').pow_pow _ _
  rw [mul_inv_eq_iff_eq_mul, h3.eq]
  congr 1
  rw [inv_pow, h.aM_inv]
  calc a ^ (2 * M) * a ^ M * a' ^ M = a ^ M * a ^ (2 * M) * a' ^ M := by rw [hz1.eq]
    _ = a ^ M * (a ^ (2 * M) * a' ^ M) := by rw [mul_assoc]
    _ = a ^ M * (a' ^ M * a ^ (2 * M)) := by rw [hz2.eq]
    _ = a ^ M * a' ^ M * a ^ (2 * M) := by rw [mul_assoc]

theorem sc_w_a (h : Rel4 a b a' b' t w M) : SemiconjBy w a a⁻¹ := h.wa_eq

theorem sc_w_ainv (h : Rel4 a b a' b' t w M) : SemiconjBy w a⁻¹ a := by
  have := h.sc_w_a.inv_right
  rwa [inv_inv] at this

theorem sc_w_a' (h : Rel4 a b a' b' t w M) : SemiconjBy w a' a'⁻¹ := by
  have e : w * a' = a'⁻¹ * w := mul_inv_eq_iff_eq_mul.1 h.wa'
  exact e

theorem sc_w_a'inv (h : Rel4 a b a' b' t w M) : SemiconjBy w a'⁻¹ a' := by
  have := h.sc_w_a'.inv_right
  rwa [inv_inv] at this

theorem w_dl2 (h : Rel4 a b a' b' t w M) : w * (a * a') * w⁻¹ = (a * a')⁻¹ := by
  calc w * (a * a') * w⁻¹ = (w * a * w⁻¹) * (w * a' * w⁻¹) := by group
    _ = a⁻¹ * a'⁻¹ := by rw [h.wa, h.wa']
    _ = (a * a')⁻¹ := h.dl2_inv.symm

theorem w_b0 (h : Rel4 a b a' b' t w M) : w * (b * b') * w⁻¹ = (a * a')⁻¹ * (b * b') := by
  have hza : Commute (a ^ (2 * M)) a := h.z_comm_a
  have hzb : Commute (a ^ (2 * M)) b := h.z_comm_b
  have hP : Commute (a ^ (2 * M)) (a⁻¹ * b) := hza.inv_right.mul_right hzb
  have hba : b * a'⁻¹ = a'⁻¹ * b := (show Commute b a' from h.c_ba).inv_right.eq
  calc w * (b * b') * w⁻¹ = (w * b * w⁻¹) * (w * b' * w⁻¹) := by group
    _ = (a ^ (2 * M) * a⁻¹ * b) * (a ^ (2 * M) * a'⁻¹ * b') := by rw [h.wb, h.wb']
    _ = a ^ (2 * M) * ((a⁻¹ * b) * a ^ (2 * M)) * (a'⁻¹ * b') := by simp only [mul_assoc]
    _ = a ^ (2 * M) * (a ^ (2 * M) * (a⁻¹ * b)) * (a'⁻¹ * b') := by rw [← hP.eq]
    _ = (a ^ (2 * M) * a ^ (2 * M)) * (a⁻¹ * b * (a'⁻¹ * b')) := by simp only [mul_assoc]
    _ = a⁻¹ * b * (a'⁻¹ * b') := by rw [h.aN_sq, one_mul]
    _ = a⁻¹ * (b * a'⁻¹) * b' := by simp only [mul_assoc]
    _ = a⁻¹ * (a'⁻¹ * b) * b' := by rw [hba]
    _ = (a⁻¹ * a'⁻¹) * (b * b') := by simp only [mul_assoc]
    _ = (a * a')⁻¹ * (b * b') := by rw [h.dl2_inv]

theorem tau_sq (h : Rel4 a b a' b' t w M) :
    (w * (b * b')) * (w * (b * b')) = (a * a')⁻¹ := by
  have h1 : w * (b * b') * w = (a * a')⁻¹ * (b * b') := by
    have := h.w_b0; rwa [h.w_inv] at this
  calc (w * (b * b')) * (w * (b * b')) = (w * (b * b') * w) * (b * b') := by simp only [mul_assoc]
    _ = ((a * a')⁻¹ * (b * b')) * (b * b') := by rw [h1]
    _ = (a * a')⁻¹ * ((b * b') * (b * b')) := by simp only [mul_assoc]
    _ = (a * a')⁻¹ := by rw [h.b0_sq, mul_one]

theorem tau_inv (h : Rel4 a b a' b' t w M) :
    (w * (b * b'))⁻¹ = (w * (b * b')) * (a * a') := by
  have h1 := h.tau_sq
  calc (w * (b * b'))⁻¹ = (w * (b * b')) * ((w * (b * b')) * (w * (b * b')))⁻¹ := by group
    _ = (w * (b * b')) * ((a * a')⁻¹)⁻¹ := by rw [h1]
    _ = (w * (b * b')) * (a * a') := by rw [inv_inv]

theorem tau_comm_a (h : Rel4 a b a' b' t w M) : Commute (w * (b * b')) a :=
  h.sc_w_ainv.mul_left h.sc_b0_a

theorem tau_comm_a' (h : Rel4 a b a' b' t w M) : Commute (w * (b * b')) a' :=
  h.sc_w_a'inv.mul_left h.sc_b0_a'

theorem tau_comm_t (h : Rel4 a b a' b' t w M) : Commute (w * (b * b')) t :=
  Commute.mul_left (show Commute w t from h.tw.symm) (show Commute (b * b') t from h.t_b0.symm)

theorem tau_comm_dl2 (h : Rel4 a b a' b' t w M) : Commute (w * (b * b')) (a * a') :=
  h.tau_comm_a.mul_right h.tau_comm_a'

theorem orderOf_tau (h : Rel4 a b a' b' t w M) : orderOf (w * (b * b')) = 2 * (2 * M) := by
  apply orderOf_eq_of_sq (dvd_mul_right 2 M)
  rw [h.tau_sq, orderOf_inv]
  exact h.orderOf_dl2

theorem tau_pow (h : Rel4 a b a' b' t w M) : (w * (b * b')) ^ (2 * M) = a ^ M * a' ^ M := by
  rw [pow_mul, pow_two, h.tau_sq, inv_pow, h.u_eq_dl2_pow]
  exact inv_eq_of_mul_eq_one_right h.dl2_M_sq

theorem u_comm_a (h : Rel4 a b a' b' t w M) : (a ^ M * a' ^ M) * a = a * (a ^ M * a' ^ M) :=
  (((Commute.refl a).pow_left M).mul_left (h.commute_a_a'.symm.pow_left M)).eq

theorem u_comm_b0 (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * (b * b') = (b * b') * (a ^ M * a' ^ M) := by
  rw [h.u_eq_dl2_pow]
  have e : (b * b') * (a * a') = (a * a')⁻¹ * (b * b') := h.sc_b0_dl2
  exact (commute_pow_of_inv e h.dl2_M_sq).symm

theorem u_comm_t (h : Rel4 a b a' b' t w M) : (a ^ M * a' ^ M) * t = t * (a ^ M * a' ^ M) := by
  rw [h.u_eq_dl2_pow]
  exact ((Commute.pow_right (show Commute t (a * a') from commute_of_conj h.t_dl2) M).eq).symm

theorem u_comm_w (h : Rel4 a b a' b' t w M) : (a ^ M * a' ^ M) * w = w * (a ^ M * a' ^ M) := by
  rw [h.u_eq_dl2_pow]
  have e : w * (a * a') = (a * a')⁻¹ * w := mul_inv_eq_iff_eq_mul.1 h.w_dl2
  exact (commute_pow_of_inv e h.dl2_M_sq).symm

theorem u_comm_tau (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * (w * (b * b')) = (w * (b * b')) * (a ^ M * a' ^ M) :=
  (Commute.mul_right (show Commute (a ^ M * a' ^ M) w from h.u_comm_w)
    (show Commute (a ^ M * a' ^ M) (b * b') from h.u_comm_b0)).eq

theorem u_comm_y (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * (a * (w * (b * b'))) = (a * (w * (b * b'))) * (a ^ M * a' ^ M) :=
  (Commute.mul_right (show Commute (a ^ M * a' ^ M) a from h.u_comm_a)
    (show Commute (a ^ M * a' ^ M) (w * (b * b')) from h.u_comm_tau)).eq

theorem u_comm_z (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * a ^ (2 * M) = a ^ (2 * M) * (a ^ M * a' ^ M) := by
  have hz1 : Commute (a ^ (2 * M)) (a ^ M) := (Commute.refl a).pow_pow _ _
  have hz2 : Commute (a ^ (2 * M)) (a' ^ M) := by
    rw [← h.z_eq]; exact (Commute.refl a').pow_pow _ _
  exact (hz1.mul_right hz2).eq.symm

theorem u_comm_x0 (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * (a ^ (2 * M) * (b * b') * t)
      = (a ^ (2 * M) * (b * b') * t) * (a ^ M * a' ^ M) :=
  (Commute.mul_right
    (Commute.mul_right (show Commute (a ^ M * a' ^ M) (a ^ (2 * M)) from h.u_comm_z)
      (show Commute (a ^ M * a' ^ M) (b * b') from h.u_comm_b0))
    (show Commute (a ^ M * a' ^ M) t from h.u_comm_t)).eq

theorem u_comm_e (h : Rel4 a b a' b' t w M) :
    (a ^ M * a' ^ M) * (t * (a ^ M * a' ^ M)) = (t * (a ^ M * a' ^ M)) * (a ^ M * a' ^ M) :=
  (Commute.mul_right (show Commute (a ^ M * a' ^ M) t from h.u_comm_t) (Commute.refl _)).eq

theorem y_sq (h : Rel4 a b a' b' t w M) :
    (a * (w * (b * b'))) * (a * (w * (b * b'))) = a * a'⁻¹ := by
  have hc : (w * (b * b')) * a = a * (w * (b * b')) := h.tau_comm_a.eq
  calc (a * (w * (b * b'))) * (a * (w * (b * b')))
      = a * ((w * (b * b')) * a) * (w * (b * b')) := by simp only [mul_assoc]
    _ = a * (a * (w * (b * b'))) * (w * (b * b')) := by rw [hc]
    _ = (a * a) * ((w * (b * b')) * (w * (b * b'))) := by simp only [mul_assoc]
    _ = (a * a) * (a * a')⁻¹ := by rw [h.tau_sq]
    _ = a * a'⁻¹ := by rw [h.dl2_inv]; group

theorem orderOf_y (h : Rel4 a b a' b' t w M) : orderOf (a * (w * (b * b'))) = 2 * (2 * M) := by
  apply orderOf_eq_of_sq (dvd_mul_right 2 M)
  rw [h.y_sq]
  exact h.orderOf_dl1

theorem y_pow (h : Rel4 a b a' b' t w M) :
    (a * (w * (b * b'))) ^ (2 * M) = (a ^ M * a' ^ M) * a ^ (2 * M) := by
  rw [pow_mul, pow_two, h.y_sq]
  have h1 := h.dl2_M
  rw [← h.u_eq_dl2_pow] at h1
  calc (a * a'⁻¹) ^ M = (a * a'⁻¹) ^ M * (a ^ (2 * M) * a ^ (2 * M)) := by rw [h.aN_sq, mul_one]
    _ = ((a * a'⁻¹) ^ M * a ^ (2 * M)) * a ^ (2 * M) := by rw [mul_assoc]
    _ = (a ^ M * a' ^ M) * a ^ (2 * M) := by rw [← h1]

theorem tau_y (h : Rel4 a b a' b' t w M) :
    (w * (b * b')) * (a * (w * (b * b'))) = (a * (w * (b * b'))) * (w * (b * b')) :=
  (h.tau_comm_a.mul_right (Commute.refl _)).eq

theorem tau_e (h : Rel4 a b a' b' t w M) :
    (w * (b * b')) * (t * (a ^ M * a' ^ M)) = (t * (a ^ M * a' ^ M)) * (w * (b * b')) :=
  (h.tau_comm_t.mul_right (show Commute (w * (b * b')) (a ^ M * a' ^ M) from h.u_comm_tau.symm)).eq

theorem commute_z_b0 (h : Rel4 a b a' b' t w M) : Commute (a ^ (2 * M)) (b * b') :=
  Commute.mul_right (show Commute (a ^ (2 * M)) b from h.z_comm_b)
    (show Commute (a ^ (2 * M)) b' from h.z_comm_b')

theorem x0_sq (h : Rel4 a b a' b' t w M) :
    (a ^ (2 * M) * (b * b') * t) * (a ^ (2 * M) * (b * b') * t) = 1 := by
  have hzt : Commute (a ^ (2 * M)) t := h.z_comm_t
  have hBt : Commute (b * b') t := h.t_b0.symm
  rw [← pow_two, Commute.mul_pow (hzt.mul_left hBt), Commute.mul_pow h.commute_z_b0, pow_two,
    pow_two, pow_two, h.aN_sq, h.b0_sq, h.t_sq, mul_one, mul_one]

theorem sc_b0_tau (h : Rel4 a b a' b' t w M) :
    SemiconjBy (b * b') (w * (b * b')) (w * (b * b'))⁻¹ := by
  show (b * b') * (w * (b * b')) = (w * (b * b'))⁻¹ * (b * b')
  rw [mul_inv_rev, h.b0_inv, h.w_inv]
  simp only [mul_assoc]

theorem sc_b0t_tau (h : Rel4 a b a' b' t w M) :
    SemiconjBy ((b * b') * t) (w * (b * b')) (w * (b * b'))⁻¹ :=
  h.sc_b0_tau.mul_left h.tau_comm_t.symm

theorem sc_x0_tau (h : Rel4 a b a' b' t w M) :
    SemiconjBy (a ^ (2 * M) * (b * b') * t) (w * (b * b')) (w * (b * b'))⁻¹ := by
  have hzτ : Commute (a ^ (2 * M)) (w * (b * b')) :=
    (show Commute (a ^ (2 * M)) w from h.z_comm_w).mul_right h.commute_z_b0
  rw [mul_assoc]
  exact (show SemiconjBy (a ^ (2 * M)) (w * (b * b'))⁻¹ (w * (b * b'))⁻¹ from
    hzτ.inv_right).mul_left h.sc_b0t_tau

theorem x0_tau (h : Rel4 a b a' b' t w M) :
    (a ^ (2 * M) * (b * b') * t) * (w * (b * b')) * (a ^ (2 * M) * (b * b') * t)⁻¹
      = (w * (b * b'))⁻¹ :=
  mul_inv_eq_iff_eq_mul.2 h.sc_x0_tau.eq

theorem x0_not (h : Rel4 a b a' b' t w M) :
    a ^ (2 * M) * (b * b') * t ∉ zpowers (w * (b * b')) :=
  not_mem_zpowers_of_inv (n := 2 * (2 * M)) (by have := h.one_le; omega) h.orderOf_tau h.x0_tau

theorem sc_b0t_a (h : Rel4 a b a' b' t w M) : SemiconjBy ((b * b') * t) a a'⁻¹ :=
  h.sc_b0_a'.mul_left (show SemiconjBy t a a' from h.ta)

theorem sc_x0_a (h : Rel4 a b a' b' t w M) :
    SemiconjBy (a ^ (2 * M) * (b * b') * t) a a'⁻¹ := by
  have hza : Commute (a ^ (2 * M)) a'⁻¹ :=
    (show Commute (a ^ (2 * M)) a' from h.z_comm_a').inv_right
  rw [mul_assoc]
  exact (show SemiconjBy (a ^ (2 * M)) a'⁻¹ a'⁻¹ from hza).mul_left h.sc_b0t_a

theorem a'inv_tauinv (h : Rel4 a b a' b' t w M) :
    a'⁻¹ * (w * (b * b'))⁻¹ = a * (w * (b * b')) := by
  have h1 : a'⁻¹ * (a * a') = a := by rw [h.c_aa]; group
  rw [h.tau_inv]
  calc a'⁻¹ * ((w * (b * b')) * (a * a')) = a'⁻¹ * ((a * a') * (w * (b * b'))) := by
        rw [h.tau_comm_dl2.eq]
    _ = (a'⁻¹ * (a * a')) * (w * (b * b')) := (mul_assoc _ _ _).symm
    _ = a * (w * (b * b')) := by rw [h1]

theorem x0_y (h : Rel4 a b a' b' t w M) :
    (a ^ (2 * M) * (b * b') * t) * (a * (w * (b * b')))
      = (a * (w * (b * b'))) * (a ^ (2 * M) * (b * b') * t) := by
  have := (h.sc_x0_a.mul_right h.sc_x0_tau).eq
  rwa [h.a'inv_tauinv] at this

theorem x0_e (h : Rel4 a b a' b' t w M) :
    (a ^ (2 * M) * (b * b') * t) * (t * (a ^ M * a' ^ M))
      = (t * (a ^ M * a' ^ M)) * (a ^ (2 * M) * (b * b') * t) := by
  have hzt : Commute (a ^ (2 * M)) t := h.z_comm_t
  have hBt : Commute (b * b') t := h.t_b0.symm
  have h1 : Commute (a ^ (2 * M) * (b * b') * t) t := (hzt.mul_left hBt).mul_left (Commute.refl t)
  have h2 : Commute (a ^ (2 * M) * (b * b') * t) (a ^ M * a' ^ M) :=
    (show Commute (a ^ M * a' ^ M) (a ^ (2 * M) * (b * b') * t) from h.u_comm_x0).symm
  exact (h1.mul_right h2).eq

theorem commute_t_u (h : Rel4 a b a' b' t w M) : Commute t (a ^ M * a' ^ M) :=
  (show Commute (a ^ M * a' ^ M) t from h.u_comm_t).symm

theorem e_sq (h : Rel4 a b a' b' t w M) :
    (t * (a ^ M * a' ^ M)) * (t * (a ^ M * a' ^ M)) = 1 := by
  rw [← pow_two, Commute.mul_pow h.commute_t_u, pow_two, pow_two, h.t_sq, h.u_sq, mul_one]

theorem sc_t_y (h : Rel4 a b a' b' t w M) :
    SemiconjBy t (a * (w * (b * b'))) (a' * (w * (b * b'))) :=
  (show SemiconjBy t a a' from h.ta).mul_right
    (show SemiconjBy t (w * (b * b')) (w * (b * b')) from h.tau_comm_t.symm)

theorem sc_e_y (h : Rel4 a b a' b' t w M) :
    SemiconjBy (t * (a ^ M * a' ^ M)) (a * (w * (b * b'))) (a' * (w * (b * b'))) :=
  h.sc_t_y.mul_left
    (show SemiconjBy (a ^ M * a' ^ M) (a * (w * (b * b'))) (a * (w * (b * b'))) from h.u_comm_y)

theorem y_inv (h : Rel4 a b a' b' t w M) : (a * (w * (b * b')))⁻¹ = a' * (w * (b * b')) := by
  calc (a * (w * (b * b')))⁻¹ = (w * (b * b'))⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = ((w * (b * b')) * (a * a')) * a⁻¹ := by rw [h.tau_inv]
    _ = (w * (b * b')) * a' := by rw [h.c_aa]; group
    _ = a' * (w * (b * b')) := h.tau_comm_a'.eq

theorem e_y (h : Rel4 a b a' b' t w M) :
    (t * (a ^ M * a' ^ M)) * (a * (w * (b * b'))) * (t * (a ^ M * a' ^ M))⁻¹
      = (a * (w * (b * b')))⁻¹ := by
  rw [h.y_inv]
  exact mul_inv_eq_iff_eq_mul.2 h.sc_e_y.eq

theorem e_not (h : Rel4 a b a' b' t w M) :
    t * (a ^ M * a' ^ M) ∉ zpowers (a * (w * (b * b'))) :=
  not_mem_zpowers_of_inv (n := 2 * (2 * M)) (by have := h.one_le; omega) h.orderOf_y h.e_y

theorem core (h : Rel4 a b a' b' t w M) :
    Core4 (a ^ (2 * M)) (a ^ M * a' ^ M) (w * (b * b')) (a ^ (2 * M) * (b * b') * t)
      (a * (w * (b * b'))) (t * (a ^ M * a' ^ M)) (2 * (2 * M)) where
  four_dvd := ⟨M, by ring⟩
  z_sq := h.aN_sq
  z_ne_one := h.aN_ne_one'
  τ_ord := h.orderOf_tau
  y_ord := h.orderOf_y
  x₀_sq := h.x0_sq
  x₀_τ := h.x0_tau
  x₀_not := h.x0_not
  e_sq := h.e_sq
  e_y := h.e_y
  e_not := h.e_not
  τ_y := h.tau_y
  τ_e := h.tau_e
  x₀_y := h.x0_y
  x₀_e := h.x0_e
  u_eq := by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact h.tau_pow.symm
  uz_eq := by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact h.y_pow.symm
  inter := inter_eq_bot (u := a ^ M * a' ^ M) (n := 2 * (2 * M)) ⟨M, by ring⟩ h.aN_ne_one'
    h.orderOf_tau h.orderOf_y
    h.x0_sq h.x0_tau h.e_sq h.e_y h.tau_y h.tau_e
    (by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact h.tau_pow.symm)
    (by rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact h.y_pow.symm)

end Rel4

end CFSG.GH74.GLS.Stage2.Local.P27.L4
