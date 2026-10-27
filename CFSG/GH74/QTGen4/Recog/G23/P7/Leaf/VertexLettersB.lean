module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.VertexLettersA
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.VL

variable {G : Type} [Group G]

@[expose] def cj (g x : G) : G := g⁻¹ * x * g

@[simp] theorem cj_mul (g x y : G) : cj g (x * y) = cj g x * cj g y := by
  simp [cj, mul_assoc]

@[simp] theorem cj_one (g : G) : cj g 1 = 1 := by simp [cj]

@[simp] theorem cj_inv (g x : G) : cj g x⁻¹ = (cj g x)⁻¹ := by simp [cj, mul_assoc]

theorem cj_pow (g x : G) (n : ℕ) : cj g (x ^ n) = cj g x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, cj_mul, ih, pow_succ]

theorem cj_cj (g h x : G) : cj h (cj g x) = cj (g * h) x := by
  simp [cj, mul_assoc]

@[expose] def cjHom (g : G) : G →* G where
  toFun := cj g
  map_one' := cj_one g
  map_mul' := cj_mul g

@[simp] theorem cjHom_apply (g x : G) : cjHom g x = cj g x := rfl

theorem zpw_add {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (m n : ZMod 3) :
    zpw x (m + n) = zpw x m * zpw x n := by
  unfold zpw
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem zpw_zero {X : Type*} [Group X] (x : X) : zpw x 0 = 1 := by
  simp [zpw]

theorem zpw_one {X : Type*} [Group X] (x : X) : zpw x 1 = x := by
  have : (1 : ZMod 3).val = 1 := rfl
  simp [zpw, this]

theorem zpw_neg {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (m : ZMod 3) :
    zpw x (-m) = (zpw x m)⁻¹ := by
  have h := zpw_add hx m (-m)
  rw [add_neg_cancel, zpw_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem zpw_natCast {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (k : ℕ) :
    x ^ k = zpw x (k : ZMod 3) := by
  unfold zpw
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

theorem zpw_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (x : X) (n : ZMod 3) :
    f (zpw x n) = zpw (f x) n := by
  simp [zpw]

theorem zpw_cj (g x : G) (n : ZMod 3) : cj g (zpw x n) = zpw (cj g x) n := by
  simp [zpw, cj_pow]

theorem zpw_mul' {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (m n : ZMod 3) :
    zpw (zpw x m) n = zpw x (m * n) := by
  unfold zpw
  rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hx]

theorem zpw_eq_one {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (hne : x ≠ 1) {n : ZMod 3}
    (h : zpw x n = 1) : n = 0 := by
  have h3 : orderOf x = 3 := orderOf_eq_prime hx hne
  have h4 : orderOf x ∣ n.val := orderOf_dvd_of_pow_eq_one h
  rw [h3] at h4
  have hlt : n.val < 3 := ZMod.val_lt n
  have h5 : n.val = 0 := by omega
  exact (ZMod.val_eq_zero n).1 h5

theorem cj_eq_of_comm {g x : G} (hgx : g * x = x * g) : cj g x = x := by
  calc cj g x = g⁻¹ * (x * g) := by simp only [cj]; group
    _ = g⁻¹ * (g * x) := by rw [hgx]
    _ = x := by group

theorem eq_one_of_sq_eq_one {u : G} (hu3 : u ^ 3 = 1) (h : u = u⁻¹) : u = 1 := by
  have h1 : u * u = 1 := by
    have := mul_eq_one_iff_eq_inv.2 h
    exact this
  calc u = u * (u * u) := by rw [h1, mul_one]
    _ = u ^ 3 := by simp [pow_succ, mul_assoc]
    _ = 1 := hu3

theorem zpw_pow3 {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (n : ZMod 3) : zpw x n ^ 3 = 1 := by
  unfold zpw
  rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

theorem pow_comm_formula {σ x₂ x₄ : G} {k : ℕ} (hσ₂ : σ * x₂ = x₂ * σ) (hσ₄ : σ * x₄ = x₄ * σ)
    (h24 : x₂ * x₄ = σ ^ k * (x₄ * x₂)) (n m : ℕ) :
    x₂ ^ n * x₄ ^ m = σ ^ (k * n * m) * (x₄ ^ m * x₂ ^ n) := by
  have c2 : ∀ j : ℕ, σ ^ j * x₂ = x₂ * σ ^ j := fun j => (Commute.pow_left hσ₂ j).eq
  have c4 : ∀ j : ℕ, σ ^ j * x₄ = x₄ * σ ^ j := fun j => (Commute.pow_left hσ₄ j).eq
  have step1 : ∀ n : ℕ, x₂ ^ n * x₄ = σ ^ (k * n) * (x₄ * x₂ ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x₂ ^ (n + 1) * x₄ = x₂ * (x₂ ^ n * x₄) := by rw [pow_succ', mul_assoc]
        _ = x₂ * (σ ^ (k * n) * (x₄ * x₂ ^ n)) := by rw [ih]
        _ = σ ^ (k * n) * (x₂ * x₄) * x₂ ^ n := by
          rw [← mul_assoc, ← mul_assoc, ← c2 (k * n)]; simp [mul_assoc]
        _ = σ ^ (k * (n + 1)) * (x₄ * x₂ ^ (n + 1)) := by
          rw [h24, pow_succ', mul_add, mul_one, pow_add]
          simp only [mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    calc x₂ ^ n * x₄ ^ (m + 1) = (x₂ ^ n * x₄ ^ m) * x₄ := by rw [pow_succ, mul_assoc]
      _ = σ ^ (k * n * m) * (x₄ ^ m * x₂ ^ n) * x₄ := by rw [ih]
      _ = σ ^ (k * n * m) * (x₄ ^ m * (x₂ ^ n * x₄)) := by simp only [mul_assoc]
      _ = σ ^ (k * n * m) * (x₄ ^ m * (σ ^ (k * n) * (x₄ * x₂ ^ n))) := by rw [step1 n]
      _ = σ ^ (k * n * m) * (σ ^ (k * n) * (x₄ ^ m * (x₄ * x₂ ^ n))) := by
          have : x₄ ^ m * σ ^ (k * n) = σ ^ (k * n) * x₄ ^ m :=
            ((Commute.pow_left hσ₄ (k * n)).symm.pow_left m).eq
          rw [← mul_assoc (x₄ ^ m), this]; simp only [mul_assoc]
      _ = σ ^ (k * n * (m + 1)) * (x₄ ^ (m + 1) * x₂ ^ n) := by
          rw [← mul_assoc (σ ^ (k * n * m)), ← pow_add, pow_succ, mul_assoc (x₄ ^ m)]
          congr 2

structure HeisData (σ x₁ x₂ x₃ x₄ : G) (c : ZMod 3) : Prop where
  σ3 : σ ^ 3 = 1
  x₁3 : x₁ ^ 3 = 1
  x₂3 : x₂ ^ 3 = 1
  x₃3 : x₃ ^ 3 = 1
  x₄3 : x₄ ^ 3 = 1
  σx₁ : σ * x₁ = x₁ * σ
  σx₂ : σ * x₂ = x₂ * σ
  σx₃ : σ * x₃ = x₃ * σ
  σx₄ : σ * x₄ = x₄ * σ
  x₁x₂ : x₁ * x₂ = x₂ * x₁
  x₁x₃ : x₁ * x₃ = x₃ * x₁
  x₁x₄ : x₁ * x₄ = x₄ * x₁
  x₃x₂ : x₃ * x₂ = x₂ * x₃
  x₃x₄ : x₃ * x₄ = x₄ * x₃
  x₂x₄ : x₂ * x₄ = σ ^ c.val * (x₄ * x₂)

@[expose] def phi (σ x₁ x₂ x₃ x₄ : G) {c : ZMod 3} (x : VG c) : G :=
  zpw σ x.s * (zpw x₁ x.p₁ * zpw x₃ x.p₃) * (zpw x₂ x.p₂ * zpw x₄ x.p₄)

theorem comm_zpw {u v : G} (huv : u * v = v * u) (m n : ZMod 3) :
    zpw u m * zpw v n = zpw v n * zpw u m :=
  (Commute.pow_pow (show Commute u v from huv) m.val n.val).eq

section Heis

variable {σ x₁ x₂ x₃ x₄ : G} {c : ZMod 3}

theorem HeisData.A_mul (hd : HeisData σ x₁ x₂ x₃ x₄ c) (a b d a' b' d' : ZMod 3) :
    (zpw σ a * (zpw x₁ b * zpw x₃ d)) * (zpw σ a' * (zpw x₁ b' * zpw x₃ d')) =
      zpw σ (a + a') * (zpw x₁ (b + b') * zpw x₃ (d + d')) := by
  have hPQ : zpw σ a' * (zpw x₁ b * zpw x₃ d) = (zpw x₁ b * zpw x₃ d) * zpw σ a' := by
    rw [← mul_assoc, comm_zpw hd.σx₁ a' b, mul_assoc, comm_zpw hd.σx₃ a' d, ← mul_assoc]
  have hQQ : (zpw x₁ b * zpw x₃ d) * (zpw x₁ b' * zpw x₃ d') =
      zpw x₁ (b + b') * zpw x₃ (d + d') := by
    have hc : Commute (zpw x₃ d) (zpw x₁ b') :=
      Commute.pow_pow (show Commute x₃ x₁ from hd.x₁x₃.symm) d.val b'.val
    rw [Commute.mul_mul_mul_comm hc, ← zpw_add hd.x₁3, ← zpw_add hd.x₃3]
  calc (zpw σ a * (zpw x₁ b * zpw x₃ d)) * (zpw σ a' * (zpw x₁ b' * zpw x₃ d'))
      = zpw σ a * ((zpw x₁ b * zpw x₃ d) * zpw σ a') * (zpw x₁ b' * zpw x₃ d') := by
        simp only [mul_assoc]
    _ = zpw σ a * (zpw σ a' * (zpw x₁ b * zpw x₃ d)) * (zpw x₁ b' * zpw x₃ d') := by rw [hPQ]
    _ = zpw σ (a + a') * ((zpw x₁ b * zpw x₃ d) * (zpw x₁ b' * zpw x₃ d')) := by
        rw [zpw_add hd.σ3]; simp only [mul_assoc]
    _ = _ := by rw [hQQ]

theorem HeisData.B_mul (hd : HeisData σ x₁ x₂ x₃ x₄ c) (p q r t : ZMod 3) :
    (zpw x₂ p * zpw x₄ q) * (zpw x₂ r * zpw x₄ t) =
      zpw σ (-(c * q * r)) * (zpw x₂ (p + r) * zpw x₄ (q + t)) := by
  have key : zpw x₄ q * zpw x₂ r = zpw σ (-(c * q * r)) * (zpw x₂ r * zpw x₄ q) := by
    have h := pow_comm_formula hd.σx₂ hd.σx₄ hd.x₂x₄ r.val q.val
    have h2 : zpw x₂ r * zpw x₄ q = zpw σ (c * r * q) * (zpw x₄ q * zpw x₂ r) := by
      have e : σ ^ (c.val * r.val * q.val) = zpw σ (c * r * q) := by
        rw [zpw_natCast hd.σ3]; push_cast; simp
      unfold zpw at *
      rw [← e]; exact h
    have h3 : zpw x₄ q * zpw x₂ r = (zpw σ (c * r * q))⁻¹ * (zpw x₂ r * zpw x₄ q) := by
      rw [h2, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h3, ← zpw_neg hd.σ3]; ring_nf
  have hσx₂ : zpw σ (-(c * q * r)) * zpw x₂ p = zpw x₂ p * zpw σ (-(c * q * r)) :=
    comm_zpw hd.σx₂ _ _
  calc (zpw x₂ p * zpw x₄ q) * (zpw x₂ r * zpw x₄ t)
      = zpw x₂ p * (zpw x₄ q * zpw x₂ r) * zpw x₄ t := by simp only [mul_assoc]
    _ = zpw x₂ p * (zpw σ (-(c * q * r)) * (zpw x₂ r * zpw x₄ q)) * zpw x₄ t := by rw [key]
    _ = zpw σ (-(c * q * r)) * (zpw x₂ p * zpw x₂ r * (zpw x₄ q * zpw x₄ t)) := by
        rw [← mul_assoc (zpw x₂ p), ← hσx₂]; simp only [mul_assoc]
    _ = _ := by rw [← zpw_add hd.x₂3, ← zpw_add hd.x₄3]

theorem HeisData.phi_mul (hd : HeisData σ x₁ x₂ x₃ x₄ c) (x y : VG c) :
    phi σ x₁ x₂ x₃ x₄ (x * y) = phi σ x₁ x₂ x₃ x₄ x * phi σ x₁ x₂ x₃ x₄ y := by
  have cσ₂ : Commute σ x₂ := hd.σx₂
  have cσ₄ : Commute σ x₄ := hd.σx₄
  have c₁₂ : Commute x₁ x₂ := hd.x₁x₂
  have c₁₄ : Commute x₁ x₄ := hd.x₁x₄
  have c₃₂ : Commute x₃ x₂ := hd.x₃x₂
  have c₃₄ : Commute x₃ x₄ := hd.x₃x₄
  have hAB : Commute (zpw σ y.s * (zpw x₁ y.p₁ * zpw x₃ y.p₃)) (zpw x₂ x.p₂ * zpw x₄ x.p₄) :=
    Commute.mul_left
      (Commute.mul_right (Commute.pow_pow cσ₂ _ _) (Commute.pow_pow cσ₄ _ _))
      (Commute.mul_left
        (Commute.mul_right (Commute.pow_pow c₁₂ _ _) (Commute.pow_pow c₁₄ _ _))
        (Commute.mul_right (Commute.pow_pow c₃₂ _ _) (Commute.pow_pow c₃₄ _ _)))
  have hσC : zpw σ (-(c * x.p₄ * y.p₂)) * (zpw x₁ (x.p₁ + y.p₁) * zpw x₃ (x.p₃ + y.p₃)) =
      (zpw x₁ (x.p₁ + y.p₁) * zpw x₃ (x.p₃ + y.p₃)) * zpw σ (-(c * x.p₄ * y.p₂)) := by
    rw [← mul_assoc, comm_zpw hd.σx₁, mul_assoc, comm_zpw hd.σx₃, ← mul_assoc]
  have hA := hd.A_mul x.s x.p₁ x.p₃ y.s y.p₁ y.p₃
  have hB := hd.B_mul x.p₂ x.p₄ y.p₂ y.p₄
  have hs : x.s + y.s - c * x.p₄ * y.p₂ = x.s + y.s + -(c * x.p₄ * y.p₂) := by ring
  unfold phi
  simp only [VG.mul_def]
  set A₁ := zpw σ x.s * (zpw x₁ x.p₁ * zpw x₃ x.p₃)
  set A₂ := zpw σ y.s * (zpw x₁ y.p₁ * zpw x₃ y.p₃)
  set B₁ := zpw x₂ x.p₂ * zpw x₄ x.p₄
  set B₂ := zpw x₂ y.p₂ * zpw x₄ y.p₄
  have e1 : A₁ * B₁ * (A₂ * B₂) = (A₁ * A₂) * (B₁ * B₂) := by
    calc A₁ * B₁ * (A₂ * B₂) = A₁ * (B₁ * A₂) * B₂ := by simp only [mul_assoc]
      _ = A₁ * (A₂ * B₁) * B₂ := by rw [hAB.eq]
      _ = (A₁ * A₂) * (B₁ * B₂) := by simp only [mul_assoc]
  rw [e1, hA, hB, hs]
  calc _ = zpw σ (x.s + y.s) * (zpw x₁ (x.p₁ + y.p₁) * zpw x₃ (x.p₃ + y.p₃)) *
        (zpw σ (-(c * x.p₄ * y.p₂)) * (zpw x₂ (x.p₂ + y.p₂) * zpw x₄ (x.p₄ + y.p₄))) := by
        rw [zpw_add hd.σ3]
        calc _ = zpw σ (x.s + y.s) * (zpw σ (-(c * x.p₄ * y.p₂)) *
              (zpw x₁ (x.p₁ + y.p₁) * zpw x₃ (x.p₃ + y.p₃))) *
              (zpw x₂ (x.p₂ + y.p₂) * zpw x₄ (x.p₄ + y.p₄)) := by simp only [mul_assoc]
          _ = zpw σ (x.s + y.s) * ((zpw x₁ (x.p₁ + y.p₁) * zpw x₃ (x.p₃ + y.p₃)) *
              zpw σ (-(c * x.p₄ * y.p₂))) *
              (zpw x₂ (x.p₂ + y.p₂) * zpw x₄ (x.p₄ + y.p₄)) := by rw [hσC]
          _ = _ := by simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem HeisData.phi_one (hd : HeisData σ x₁ x₂ x₃ x₄ c) : phi σ x₁ x₂ x₃ x₄ (1 : VG c) = 1 := by
  simp [phi, VG.one_def, zpw_zero]

@[expose] def HeisData.hom (hd : HeisData σ x₁ x₂ x₃ x₄ c) : VG c →* G where
  toFun := phi σ x₁ x₂ x₃ x₄
  map_one' := hd.phi_one
  map_mul' := hd.phi_mul

@[simp] theorem HeisData.hom_apply (hd : HeisData σ x₁ x₂ x₃ x₄ c) (x : VG c) :
    hd.hom x = phi σ x₁ x₂ x₃ x₄ x := rfl

theorem HeisData.hom_gσ (hd : HeisData σ x₁ x₂ x₃ x₄ c) : hd.hom VG.gσ = σ := by
  simp [phi, VG.gσ, zpw_zero, zpw_one]

theorem HeisData.hom_g₁ (hd : HeisData σ x₁ x₂ x₃ x₄ c) : hd.hom VG.g₁ = x₁ := by
  simp [phi, VG.g₁, zpw_zero, zpw_one]

theorem HeisData.hom_g₂ (hd : HeisData σ x₁ x₂ x₃ x₄ c) : hd.hom VG.g₂ = x₂ := by
  simp [phi, VG.g₂, zpw_zero, zpw_one]

theorem HeisData.hom_g₃ (hd : HeisData σ x₁ x₂ x₃ x₄ c) : hd.hom VG.g₃ = x₃ := by
  simp [phi, VG.g₃, zpw_zero, zpw_one]

theorem HeisData.hom_g₄ (hd : HeisData σ x₁ x₂ x₃ x₄ c) : hd.hom VG.g₄ = x₄ := by
  simp [phi, VG.g₄, zpw_zero, zpw_one]

theorem HeisData.comp_hom (hd : HeisData σ x₁ x₂ x₃ x₄ c) (ψ : G →* G)
    (g₀ g₁' g₂' g₃' g₄' : VG c) (h0 : ψ σ = hd.hom g₀) (h1 : ψ x₁ = hd.hom g₁')
    (h2 : ψ x₂ = hd.hom g₂') (h3 : ψ x₃ = hd.hom g₃') (h4 : ψ x₄ = hd.hom g₄') (x : VG c) :
    ψ (hd.hom x) = hd.hom (VG.ext5 g₀ g₁' g₂' g₃' g₄' x) := by
  have hx := VG.eq_prod c x
  calc ψ (hd.hom x)
      = ψ (hd.hom (zpw VG.gσ x.s * (zpw VG.g₁ x.p₁ * zpw VG.g₃ x.p₃) *
          (zpw VG.g₂ x.p₂ * zpw VG.g₄ x.p₄))) := by rw [← hx]
    _ = _ := by
        simp only [map_mul, zpw_map, hd.hom_gσ, hd.hom_g₁, hd.hom_g₂, hd.hom_g₃, hd.hom_g₄, h0, h1,
          h2, h3, h4, VG.ext5]

end Heis

theorem inv_eq_mul_self {a : G} (ha : a ^ 3 = 1) : a⁻¹ = a * a :=
  inv_eq_of_mul_eq_one_right (by rw [← ha]; simp [pow_succ, mul_assoc])

theorem rel_I4 {a b : G} (hr : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1) :
    b * a * b⁻¹ * a * b * a⁻¹ = 1 := by
  calc b * a * b⁻¹ * a * b * a⁻¹ = a * (b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a)⁻¹ * a⁻¹ := by group
    _ = 1 := by rw [hr]; group

theorem rel_I5 {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hr : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1) : a * b * (a * b) * (b * a * (b * a)) = 1 := by
  have h4 := rel_I4 hr
  have hbb : b * b = b⁻¹ := (inv_eq_mul_self hb).symm
  have e1 : b * a * b⁻¹ * a * b = a := by
    calc b * a * b⁻¹ * a * b = (b * a * b⁻¹ * a * b * a⁻¹) * a := by group
      _ = a := by rw [h4, one_mul]
  calc a * b * (a * b) * (b * a * (b * a)) = a * b * a * (b * b) * a * b * a := by group
    _ = a * b * a * b⁻¹ * a * b * a := by rw [hbb]
    _ = a * (b * a * b⁻¹ * a * b) * a := by group
    _ = 1 := by
      rw [e1]
      calc a * a * a = a ^ 3 := by simp [pow_succ, mul_assoc]
        _ = 1 := ha

theorem rel_inv_sq {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hr : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1) :
    a⁻¹ * b⁻¹ * (a⁻¹ * b⁻¹) = a * b * (a * b) := by
  have h5 := rel_I5 ha hb hr
  have : a⁻¹ * b⁻¹ * (a⁻¹ * b⁻¹) = (b * a * (b * a))⁻¹ := by group
  rw [this]
  exact (eq_inv_of_mul_eq_one_left h5).symm

theorem sq_comm_b {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hr : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1) :
    a * b * (a * b) * b = b * (a * b * (a * b)) := by
  have h5 := rel_I5 ha hb hr
  set z := a * b * (a * b) with hz
  have hz1 : b * z * b⁻¹ = z⁻¹ := by
    have : z * (b * z * b⁻¹) = 1 := by
      rw [← h5, hz]; group
    exact eq_inv_of_mul_eq_one_right this
  have hb111 : b * b * b = 1 := by
    rw [← hb]; simp [pow_succ, mul_assoc]
  have hz3 : b * z⁻¹ * b⁻¹ = z := by
    have : b * z⁻¹ * b⁻¹ = (b * z * b⁻¹)⁻¹ := by group
    rw [this, hz1, inv_inv]
  have hz2 : z⁻¹ = z := by
    have : z = z⁻¹ :=
      calc z = (b * b * b) * z * (b * b * b)⁻¹ := by rw [hb111]; group
        _ = b * (b * (b * z * b⁻¹) * b⁻¹) * b⁻¹ := by group
        _ = b * (b * z⁻¹ * b⁻¹) * b⁻¹ := by rw [hz1]
        _ = b * z * b⁻¹ := by rw [hz3]
        _ = z⁻¹ := hz1
    exact this.symm
  have : b * z * b⁻¹ = z := by rw [hz1, hz2]
  calc z * b = (b * z * b⁻¹) * b := by rw [this]
    _ = b * z := by group

structure VHc (σ a b z : G) (M : Subgroup G) (w₁ w₂ : G) : Prop where
  a3 : a ^ 3 = 1
  b3 : b ^ 3 = 1
  rel : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1
  z_def : z = (a * b) ^ 2
  Ma : ∀ m ∈ M, a * m * a⁻¹ ∈ M
  Mb : ∀ m ∈ M, b * m * b⁻¹ ∈ M
  σ_mem : σ ∈ M
  σ3 : σ ^ 3 = 1
  σ_ne : σ ≠ 1
  σ_M : ∀ m ∈ M, σ * m = m * σ
  σ_a : σ * a = a * σ
  σ_b : σ * b = b * σ
  card_M : Nat.card M = 243
  exp3 : ∀ m ∈ M, m ^ 3 = 1
  comm_le : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ
  w₁_mem : w₁ ∈ M
  w₁_cent : ∀ m ∈ M, m * w₁ = w₁ * m
  w₁_ne : w₁ ≠ 1
  w₂_mem : w₂ ∈ M
  w₂_nc : ∃ m ∈ M, m * w₂ ≠ w₂ * m
  a_w₁ : a * w₁ = w₁ * a
  a_w₂ : a * w₂ = w₂ * a
  z_w₁ : z * w₁ * z⁻¹ = w₁⁻¹
  z_w₂ : z * w₂ * z⁻¹ = w₂⁻¹

namespace VHc

variable {σ a b z : G} {M : Subgroup G} {w₁ w₂ : G}

theorem z_def' (h : VHc σ a b z M w₁ w₂) : z = a * b * (a * b) := by rw [h.z_def, sq]

theorem Ma' (h : VHc σ a b z M w₁ w₂) {m : G} (hm : m ∈ M) : a⁻¹ * m * a ∈ M := by
  have e : a⁻¹ = a * a := inv_eq_mul_self h.a3
  have : a⁻¹ * m * a = a * (a * m * a⁻¹) * a⁻¹ := by
    calc a⁻¹ * m * a = (a * a) * m * (a * a)⁻¹ := by rw [← e]; group
      _ = a * (a * m * a⁻¹) * a⁻¹ := by group
  rw [this]
  exact h.Ma _ (h.Ma m hm)

theorem Mb' (h : VHc σ a b z M w₁ w₂) {m : G} (hm : m ∈ M) : b⁻¹ * m * b ∈ M := by
  have e : b⁻¹ = b * b := inv_eq_mul_self h.b3
  have : b⁻¹ * m * b = b * (b * m * b⁻¹) * b⁻¹ := by
    calc b⁻¹ * m * b = (b * b) * m * (b * b)⁻¹ := by rw [← e]; group
      _ = b * (b * m * b⁻¹) * b⁻¹ := by group
  rw [this]
  exact h.Mb _ (h.Mb m hm)

theorem cj_b_mem (h : VHc σ a b z M w₁ w₂) {m : G} (hm : m ∈ M) : cj b m ∈ M := h.Mb' hm

theorem σ_z (h : VHc σ a b z M w₁ w₂) : σ * z = z * σ := by
  rw [h.z_def']
  exact ((Commute.mul_right (show Commute σ a from h.σ_a) (show Commute σ b from h.σ_b)).mul_right
    (Commute.mul_right (show Commute σ a from h.σ_a) (show Commute σ b from h.σ_b))).eq

theorem cent_cj_b (h : VHc σ a b z M w₁ w₂) {x : G} (hc : ∀ m ∈ M, m * x = x * m) :
    ∀ m ∈ M, m * cj b x = cj b x * m := by
  intro m hm
  have := hc (b * m * b⁻¹) (h.Mb m hm)
  calc m * cj b x = b⁻¹ * (b * m * b⁻¹ * x) * b := by simp only [cj]; group
    _ = b⁻¹ * (x * (b * m * b⁻¹)) * b := by rw [this]
    _ = cj b x * m := by simp only [cj]; group

theorem cj_cube (h : VHc σ a b z M w₁ w₂) (x : G) : cj b (cj b (cj b x)) = x := by
  have hb : b * b * b = 1 := by rw [← h.b3]; simp [pow_succ, mul_assoc]
  calc cj b (cj b (cj b x)) = cj (b * (b * b)) x := by rw [cj_cj, cj_cj]
    _ = x := by rw [← mul_assoc, hb]; simp [cj]

theorem cj_sq (h : VHc σ a b z M w₁ w₂) (x : G) : cj b (cj b x) = b * x * b⁻¹ := by
  rw [cj_cj, ← inv_eq_mul_self h.b3]; simp [cj]

theorem D3 (h : VHc σ a b z M w₁ w₂) {w : G} (haw : a * w = w * a) (hzw : z * w * z⁻¹ = w⁻¹) :
    cj a (cj b w) = b * w⁻¹ * b⁻¹ := by
  have hbab : b * a * b = a⁻¹ * z := by rw [h.z_def']; group
  have hz : z * w⁻¹ * z⁻¹ = w := by
    calc z * w⁻¹ * z⁻¹ = (z * w * z⁻¹)⁻¹ := by group
      _ = w := by rw [hzw, inv_inv]
  have haw' : a⁻¹ * w * a = w := by
    calc a⁻¹ * w * a = a⁻¹ * (w * a) := mul_assoc _ _ _
      _ = a⁻¹ * (a * w) := by rw [haw]
      _ = w := by group
  have h1 : (b * a * b) * w⁻¹ * (b * a * b)⁻¹ = w := by
    rw [hbab]
    calc a⁻¹ * z * w⁻¹ * (a⁻¹ * z)⁻¹ = a⁻¹ * (z * w⁻¹ * z⁻¹) * a := by group
      _ = w := by rw [hz, haw']
  calc cj a (cj b w) = (b * a)⁻¹ * w * (b * a) := by simp only [cj]; group
    _ = (b * a)⁻¹ * ((b * a * b) * w⁻¹ * (b * a * b)⁻¹) * (b * a) := by rw [h1]
    _ = b * w⁻¹ * b⁻¹ := by group

theorem kernel_aux (h : VHc σ a b z M w₁ w₂) {s : ZMod 3} {u u' : G}
    (hau : a * u = u * a) (hau' : a * u' = u' * a)
    (hzu : z * u * z⁻¹ = u⁻¹) (hzu' : z * u' * z⁻¹ = u'⁻¹) (hu3 : u ^ 3 = 1) (hu'3 : u' ^ 3 = 1)
    (h1 : zpw σ s * (u * cj b u') = 1) : u' = 1 ∧ u = 1 ∧ s = 0 := by
  have hD := h.D3 hau' hzu'
  have hσa : cj a (zpw σ s) = zpw σ s :=
    cj_eq_of_comm (Commute.pow_left (show Commute σ a from h.σ_a) s.val).eq.symm
  have hσz : z * zpw σ s = zpw σ s * z :=
    (Commute.pow_right (show Commute z σ from h.σ_z.symm) s.val).eq
  have h2 := congrArg (cj a) h1
  rw [cj_mul, cj_mul, hσa, cj_eq_of_comm hau, hD, cj_one] at h2
  have h3 : cj b u' = b * u'⁻¹ * b⁻¹ := by
    have := h1.trans h2.symm
    exact mul_left_cancel (mul_left_cancel this)
  have hE : cj b u' = (cj b (cj b u'))⁻¹ :=
    calc cj b u' = b * u'⁻¹ * b⁻¹ := h3
      _ = cj b (cj b u'⁻¹) := (h.cj_sq _).symm
      _ = (cj b (cj b u'))⁻¹ := by rw [cj_inv, cj_inv]
  have e1 : cj b u' * cj b (cj b u') = 1 := mul_eq_one_iff_eq_inv.2 hE
  have e2 : cj b (cj b u') * u' = 1 := by
    have := congrArg (cj b) e1
    rwa [cj_mul, h.cj_cube, cj_one] at this
  have e3 : cj b (cj b u') = u'⁻¹ := eq_inv_of_mul_eq_one_left e2
  have e4 : cj b u' = u' := by
    rw [e3] at e1
    exact mul_inv_eq_one.1 e1
  have hu' : u' = 1 := by
    apply eq_one_of_sq_eq_one hu'3
    calc u' = cj b (cj b u') := by rw [e4, e4]
      _ = u'⁻¹ := e3
  subst hu'
  rw [cj_one, mul_one] at h1
  have hu : u = 1 := by
    have h4 : u = (zpw σ s)⁻¹ := eq_inv_of_mul_eq_one_right h1
    apply eq_one_of_sq_eq_one hu3
    calc u = (zpw σ s)⁻¹ := h4
      _ = z * (zpw σ s)⁻¹ * z⁻¹ := by
        have hc : Commute z (zpw σ s) := hσz
        rw [hc.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
      _ = z * u * z⁻¹ := by rw [h4]
      _ = u⁻¹ := hzu
  subst hu
  rw [mul_one] at h1
  exact ⟨rfl, rfl, zpw_eq_one h.σ3 h.σ_ne h1⟩

theorem exists_c (h : VHc σ a b z M w₁ w₂) :
    ∃ c : ZMod 3, w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (h.comm_le w₂ h.w₂_mem (cj b w₂) (h.cj_b_mem h.w₂_mem))
  refine ⟨(k : ZMod 3), ?_⟩
  have h3 : σ ^ (3 : ℤ) = 1 := by exact_mod_cast h.σ3
  have hk' : σ ^ k = σ ^ ((k : ZMod 3).val) := by
    rw [zpow_eq_zpow_emod k h3, ← zpow_natCast]
    congr 1
    rw [ZMod.val_intCast]; rfl
  calc w₂ * cj b w₂ = (w₂ * cj b w₂ * w₂⁻¹ * (cj b w₂)⁻¹) * (cj b w₂ * w₂) := by group
    _ = _ := by rw [← hk, hk']

theorem heisData (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) :
    HeisData σ w₁ w₂ (cj b w₁) (cj b w₂) c where
  σ3 := h.σ3
  x₁3 := h.exp3 _ h.w₁_mem
  x₂3 := h.exp3 _ h.w₂_mem
  x₃3 := h.exp3 _ (h.cj_b_mem h.w₁_mem)
  x₄3 := h.exp3 _ (h.cj_b_mem h.w₂_mem)
  σx₁ := h.σ_M _ h.w₁_mem
  σx₂ := h.σ_M _ h.w₂_mem
  σx₃ := h.σ_M _ (h.cj_b_mem h.w₁_mem)
  σx₄ := h.σ_M _ (h.cj_b_mem h.w₂_mem)
  x₁x₂ := (h.w₁_cent _ h.w₂_mem).symm
  x₁x₃ := (h.w₁_cent _ (h.cj_b_mem h.w₁_mem)).symm
  x₁x₄ := (h.w₁_cent _ (h.cj_b_mem h.w₂_mem)).symm
  x₃x₂ := (h.cent_cj_b h.w₁_cent _ h.w₂_mem).symm
  x₃x₄ := (h.cent_cj_b h.w₁_cent _ (h.cj_b_mem h.w₂_mem)).symm
  x₂x₄ := hc

theorem sq_one_of_ne_zero : ∀ q : ZMod 3, q ≠ 0 → q * q = 1 := by decide

theorem zpw_inv_base {X : Type*} [Group X] (x : X) (n : ZMod 3) : zpw x⁻¹ n = (zpw x n)⁻¹ := by
  simp [zpw]

theorem comm_w (h : VHc σ a b z M w₁ w₂) (p q : ZMod 3) :
    Commute (zpw w₁ p) (zpw w₂ q) :=
  Commute.pow_pow (show Commute w₁ w₂ from (h.w₁_cent w₂ h.w₂_mem).symm) _ _

theorem good_a (h : VHc σ a b z M w₁ w₂) (p q : ZMod 3) :
    a * (zpw w₁ p * zpw w₂ q) = (zpw w₁ p * zpw w₂ q) * a :=
  (Commute.mul_right (Commute.pow_right (show Commute a w₁ from h.a_w₁) p.val)
    (Commute.pow_right (show Commute a w₂ from h.a_w₂) q.val)).eq

theorem good_z (h : VHc σ a b z M w₁ w₂) (p q : ZMod 3) :
    z * (zpw w₁ p * zpw w₂ q) * z⁻¹ = (zpw w₁ p * zpw w₂ q)⁻¹ := by
  have hconj : ∀ (x : G) (n : ZMod 3), z * zpw x n * z⁻¹ = zpw (z * x * z⁻¹) n := by
    intro x n
    have := zpw_cj z⁻¹ x n
    simpa [cj] using this
  calc z * (zpw w₁ p * zpw w₂ q) * z⁻¹
      = (z * zpw w₁ p * z⁻¹) * (z * zpw w₂ q * z⁻¹) := by group
    _ = (zpw w₁ p)⁻¹ * (zpw w₂ q)⁻¹ := by
      rw [hconj, hconj, h.z_w₁, h.z_w₂, zpw_inv_base, zpw_inv_base]
    _ = (zpw w₁ p * zpw w₂ q)⁻¹ := by
      rw [mul_inv_rev]; exact (h.comm_w p q).inv_inv.eq

theorem good_pow3 (h : VHc σ a b z M w₁ w₂) (p q : ZMod 3) :
    (zpw w₁ p * zpw w₂ q) ^ 3 = 1 := by
  rw [(h.comm_w p q).mul_pow, zpw_pow3 (h.exp3 _ h.w₁_mem), zpw_pow3 (h.exp3 _ h.w₂_mem), mul_one]

theorem indep (h : VHc σ a b z M w₁ w₂) {p q : ZMod 3} (hpq : zpw w₁ p * zpw w₂ q = 1) :
    p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    have hB : zpw w₂ q = (zpw w₁ p)⁻¹ := eq_inv_of_mul_eq_one_right hpq
    have hcent : ∀ m ∈ M, m * zpw w₂ q = zpw w₂ q * m := by
      intro m hm
      rw [hB]
      have hc : Commute m (zpw w₁ p) :=
        Commute.pow_right (show Commute m w₁ from h.w₁_cent m hm) _
      exact hc.inv_right.eq
    have hw : w₂ = zpw (zpw w₂ q) q := by
      rw [zpw_mul' (h.exp3 _ h.w₂_mem)]
      rw [sq_one_of_ne_zero q hq, zpw_one]
    obtain ⟨m, hm, hne⟩ := h.w₂_nc
    apply hne
    have hc : Commute m (zpw w₂ q) := hcent m hm
    have key : Commute m (zpw (zpw w₂ q) q) := Commute.pow_right hc _
    rw [← hw] at key
    exact key.eq
  subst hq
  rw [zpw_zero, mul_one] at hpq
  exact ⟨zpw_eq_one (h.exp3 _ h.w₁_mem) h.w₁_ne hpq, rfl⟩

theorem phi_eq (h : VHc σ a b z M w₁ w₂) {c : ZMod 3} (hd : HeisData σ w₁ w₂ (cj b w₁) (cj b w₂) c)
    (x : VG c) :
    phi σ w₁ w₂ (cj b w₁) (cj b w₂) x =
      zpw σ x.s * ((zpw w₁ x.p₁ * zpw w₂ x.p₂) * cj b (zpw w₁ x.p₃ * zpw w₂ x.p₄)) := by
  have hc : Commute (zpw (cj b w₁) x.p₃) (zpw w₂ x.p₂) :=
    Commute.pow_pow (show Commute (cj b w₁) w₂ from hd.x₃x₂) _ _
  rw [cj_mul, zpw_cj, zpw_cj]
  unfold phi
  rw [mul_assoc, Commute.mul_mul_mul_comm hc]

theorem phi_injective (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) : Function.Injective (h.heisData hc).hom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : phi σ w₁ w₂ (cj b w₁) (cj b w₂) x = 1 := hx
  rw [h.phi_eq (h.heisData hc) x] at hx'
  obtain ⟨hu', hu, hs⟩ := h.kernel_aux (good_a h _ _) (good_a h _ _) (good_z h _ _) (good_z h _ _)
    (good_pow3 h _ _) (good_pow3 h _ _) hx'
  obtain ⟨hp₁, hp₂⟩ := h.indep hu
  obtain ⟨hp₃, hp₄⟩ := h.indep hu'
  ext <;> simp [VG.one_def, hs, hp₁, hp₂, hp₃, hp₄]

theorem phi_mem (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) (x : VG c) : (h.heisData hc).hom x ∈ M := by
  show phi σ w₁ w₂ (cj b w₁) (cj b w₂) x ∈ M
  unfold phi
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h.σ_mem _)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ h.w₁_mem _) (Subgroup.pow_mem _ (h.cj_b_mem h.w₁_mem) _)))
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ h.w₂_mem _) (Subgroup.pow_mem _ (h.cj_b_mem h.w₂_mem) _))

theorem phi_surj (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) : ∀ m ∈ M, ∃ x : VG c, (h.heisData hc).hom x = m := by
  let f : VG c → M := fun x => ⟨(h.heisData hc).hom x, h.phi_mem hc x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact h.phi_injective hc (congrArg Subtype.val hxy)
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by rw [h.card_M]; norm_num)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [h.card_M, VG.card_VG])
  intro m hm
  obtain ⟨x, hx⟩ := hbij.2 ⟨m, hm⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem z_comm_b (h : VHc σ a b z M w₁ w₂) : z * b = b * z := by
  rw [h.z_def']; exact sq_comm_b h.a3 h.b3 h.rel

theorem cj_z (h : VHc σ a b z M w₁ w₂) (x : G) : z * cj b x * z⁻¹ = cj b (z * x * z⁻¹) := by
  have hc : Commute z b := h.z_comm_b
  have c1 : z * b⁻¹ = b⁻¹ * z := hc.inv_right.eq
  have c2 : b * z⁻¹ = z⁻¹ * b := hc.symm.inv_right.eq
  calc z * cj b x * z⁻¹ = (z * b⁻¹) * x * (b * z⁻¹) := by simp only [cj]; group
    _ = (b⁻¹ * z) * x * (z⁻¹ * b) := by rw [c1, c2]
    _ = cj b (z * x * z⁻¹) := by simp only [cj]; group

theorem c_ne_zero (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) : c ≠ 0 := by
  intro hc0
  subst hc0
  have hc0 : Commute w₂ (cj b w₂) := by
    have : w₂ * cj b w₂ = cj b w₂ * w₂ := by simpa using hc
    exact this
  obtain ⟨m, hm, hne⟩ := h.w₂_nc
  obtain ⟨x, rfl⟩ := h.phi_surj hc m hm
  apply hne
  have hd := h.heisData hc
  show phi σ w₁ w₂ (cj b w₁) (cj b w₂) x * w₂ = w₂ * phi σ w₁ w₂ (cj b w₁) (cj b w₂) x
  have cσ : Commute σ w₂ := h.σ_M _ h.w₂_mem
  have c1 : Commute w₁ w₂ := (h.w₁_cent w₂ h.w₂_mem).symm
  have c3 : Commute (cj b w₁) w₂ := hd.x₃x₂
  have key : Commute (phi σ w₁ w₂ (cj b w₁) (cj b w₂) x) w₂ :=
    Commute.mul_left
      (Commute.mul_left (Commute.pow_left cσ _)
        (Commute.mul_left (Commute.pow_left c1 _) (Commute.pow_left c3 _)))
      (Commute.mul_left (Commute.pow_left (Commute.refl w₂) _) (Commute.pow_left hc0.symm _))
  exact key.eq

theorem D2_aux (h : VHc σ a b z M w₁ w₂) {c : ZMod 3}
    (hc : w₂ * cj b w₂ = σ ^ c.val * (cj b w₂ * w₂)) (hc0 : c ≠ 0) {η : VG c}
    (hη : (h.heisData hc).hom η = cj b (cj b w₂)) :
    cj b (cj b w₁) = (h.heisData hc).hom (VG.g₁ * VG.g₃)⁻¹ := by
  have hd := h.heisData hc
  have hinj := h.phi_injective hc
  obtain ⟨ζ, hζ⟩ := h.phi_surj hc _ (h.cj_b_mem (h.cj_b_mem h.w₁_mem))
  have hcent : ∀ m ∈ M, m * cj b (cj b w₁) = cj b (cj b w₁) * m :=
    h.cent_cj_b (h.cent_cj_b h.w₁_cent)
  have hζ2 : ζ * VG.g₂ = VG.g₂ * ζ := by
    apply hinj
    rw [map_mul, map_mul, hζ, hd.hom_g₂]
    exact (hcent _ h.w₂_mem).symm
  have hζ4 : ζ * VG.g₄ = VG.g₄ * ζ := by
    apply hinj
    rw [map_mul, map_mul, hζ, hd.hom_g₄]
    exact (hcent _ (h.cj_b_mem h.w₂_mem)).symm
  obtain ⟨hp₂, hp₄⟩ := VG.central_aux c hc0 ζ hζ2 hζ4
  have hzw : z * cj b (cj b w₁) * z⁻¹ = (cj b (cj b w₁))⁻¹ := by
    rw [h.cj_z, h.cj_z, h.z_w₁, cj_inv, cj_inv]
  have hzinv : ∀ x : G, cjHom z⁻¹ x = z * x * z⁻¹ := fun x => by simp [cj]
  have hs : ζ.s = 0 := by
    apply VG.sigma_aux c ζ hp₂ hp₄
    apply hinj
    have key := hd.comp_hom (cjHom z⁻¹) VG.gσ VG.g₁⁻¹ VG.g₂⁻¹ VG.g₃⁻¹ VG.g₄⁻¹
      (by rw [hd.hom_gσ, hzinv, h.σ_z.symm]; group)
      (by rw [map_inv, hd.hom_g₁, hzinv, h.z_w₁])
      (by rw [map_inv, hd.hom_g₂, hzinv, h.z_w₂])
      (by rw [map_inv, hd.hom_g₃, hzinv, h.cj_z, h.z_w₁, cj_inv])
      (by rw [map_inv, hd.hom_g₄, hzinv, h.cj_z, h.z_w₂, cj_inv]) ζ
    rw [← key, hzinv, hζ, hzw, map_inv, hζ]
  have hζ' : ζ = ⟨0, ζ.p₁, 0, ζ.p₃, 0⟩ := by ext <;> simp [hs, hp₂, hp₄]
  have key := hd.comp_hom (cjHom b) VG.gσ VG.g₃ VG.g₄ ζ η
    (by rw [hd.hom_gσ]; exact cj_eq_of_comm h.σ_b.symm)
    (by rw [hd.hom_g₃]; rfl)
    (by rw [hd.hom_g₄]; rfl)
    (by rw [hζ]; rfl)
    (by rw [hη]; rfl) ζ
  have hext : VG.ext5 VG.gσ VG.g₃ VG.g₄ ζ η ζ = VG.g₁ := by
    apply hinj
    rw [← key, hd.hom_g₁]
    show cj b (hd.hom ζ) = w₁
    rw [hζ, h.cj_cube]
  rw [hζ'] at hext
  obtain ⟨e1, e2⟩ := VG.d2_aux c ζ.p₁ ζ.p₃ η hext
  have hζ'' : ζ = (VG.g₁ * VG.g₃)⁻¹ := by
    rw [hζ', e1, e2]; exact VG.d2_eq c
  rw [← hζ, hζ'']

theorem D2 (h : VHc σ a b z M w₁ w₂) : cj b (cj b w₁) = (w₁ * cj b w₁)⁻¹ := by
  obtain ⟨c, hc⟩ := h.exists_c
  have hd := h.heisData hc
  obtain ⟨η, hη⟩ := h.phi_surj hc _ (h.cj_b_mem (h.cj_b_mem h.w₂_mem))
  rw [h.D2_aux hc (h.c_ne_zero hc) hη, map_inv, map_mul, hd.hom_g₁, hd.hom_g₃]

theorem vertex_coords (h : VHc σ a b z M w₁ w₂) :
    ∃ (c : ZMod 3) (hd : HeisData σ w₁ w₂ (cj b w₁) (cj b w₂) c) (η : VG c),
      c ≠ 0 ∧ Function.Injective hd.hom ∧ (∀ m ∈ M, ∃ x, hd.hom x = m) ∧
      (∀ x, cj b (hd.hom x) = hd.hom (VG.tauV η x)) ∧
      (∀ x, cj a (hd.hom x) = hd.hom (VG.alphaV η x)) ∧
      VG.tauV η η = VG.g₂ ∧ VG.relV η VG.g₄ = VG.g₄ := by
  obtain ⟨c, hc⟩ := h.exists_c
  have hd := h.heisData hc
  have hc0 := h.c_ne_zero hc
  have hinj := h.phi_injective hc
  obtain ⟨η, hη⟩ := h.phi_surj hc _ (h.cj_b_mem (h.cj_b_mem h.w₂_mem))
  have hD2 := h.D2_aux hc hc0 hη
  have hτ : ∀ x, cj b (hd.hom x) = hd.hom (VG.tauV η x) := fun x =>
    hd.comp_hom (cjHom b) VG.gσ VG.g₃ VG.g₄ (VG.g₁ * VG.g₃)⁻¹ η
      (by rw [hd.hom_gσ]; exact cj_eq_of_comm h.σ_b.symm)
      (by rw [hd.hom_g₃]; rfl)
      (by rw [hd.hom_g₄]; rfl)
      (by rw [← hD2]; rfl)
      (by rw [hη]; rfl) x
  have hw₁ : cj a (cj b w₁) = hd.hom (VG.g₁ * VG.g₃) := by
    rw [h.D3 h.a_w₁ h.z_w₁, ← h.cj_sq]
    simp only [cj_inv]
    rw [h.D2, inv_inv, map_mul, hd.hom_g₁, hd.hom_g₃]
  have hw₂ : cj a (cj b w₂) = hd.hom η⁻¹ := by
    rw [h.D3 h.a_w₂ h.z_w₂, ← h.cj_sq, map_inv, hη]
    simp only [cj_inv]
  have hα : ∀ x, cj a (hd.hom x) = hd.hom (VG.alphaV η x) := fun x =>
    hd.comp_hom (cjHom a) VG.gσ VG.g₁ VG.g₂ (VG.g₁ * VG.g₃) η⁻¹
      (by rw [hd.hom_gσ]; exact cj_eq_of_comm h.σ_a.symm)
      (by rw [hd.hom_g₁]; exact cj_eq_of_comm h.a_w₁)
      (by rw [hd.hom_g₂]; exact cj_eq_of_comm h.a_w₂)
      hw₁ hw₂ x
  have hEτ : VG.tauV η η = VG.g₂ := by
    apply hinj
    rw [← hτ, hη, h.cj_cube, hd.hom_g₂]
  have hrel : ∀ x : G, cj a (cj b (cj b (cj a (cj a (cj b (cj a (cj a (cj b (cj b x)))))))))= x := by
    intro x
    simp only [cj_cj]
    have : b * b * a * a * b * a * a * b * b * a = 1 := by
      calc b * b * a * a * b * a * a * b * b * a
          = (b * b) * (a * a) * b * (a * a) * (b * b) * a := by group
        _ = b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a := by
          rw [← inv_eq_mul_self h.b3, ← inv_eq_mul_self h.a3]
        _ = 1 := h.rel
    rw [this]; simp [cj]
  have hEr : VG.relV η VG.g₄ = VG.g₄ := by
    apply hinj
    have := hrel (hd.hom VG.g₄)
    simp only [hτ, hα] at this
    exact this
  exact ⟨c, hd, η, hc0, hinj, h.phi_surj hc, hτ, hα, hEτ, hEr⟩

end VHc

end CFSG.GH74.QTGen4.Recog.G23.P7.VL
