module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup QuaternionGroup

theorem swap_natCast_inj {N a b : ℕ} (ha : a < N) (hb : b < N) :
    ((a : ZMod N) = (b : ZMod N)) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem swap_four_k (k : ℕ) : (4 : ZMod (2 * (2 * k))) * (k : ZMod (2 * (2 * k))) = 0 := by
  have h : ((2 * (2 * k) : ℕ) : ZMod (2 * (2 * k))) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

theorem swap_two_k_add_self (k : ℕ) :
    ((2 * k : ℕ) : ZMod (2 * (2 * k))) + ((2 * k : ℕ) : ZMod (2 * (2 * k))) = 0 := by
  have h : ((2 * (2 * k) : ℕ) : ZMod (2 * (2 * k))) = 0 := ZMod.natCast_self _
  push_cast at h ⊢
  linear_combination h

theorem swap_k_add_k (k : ℕ) :
    (k : ZMod (2 * (2 * k))) + (k : ZMod (2 * (2 * k))) = ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  push_cast; ring

theorem swap_two_k_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    ((2 * k : ℕ) : ZMod (2 * (2 * k))) ≠ 0 := by
  intro h
  have := (swap_natCast_inj (N := 2 * (2 * k)) (a := 2 * k) (b := 0) (by omega) (by omega)).1
    (by rw [h, Nat.cast_zero])
  omega

theorem swap_two_ne_zero {k : ℕ} (hk : 1 ≤ k) : (2 : ZMod (2 * (2 * k))) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod (2 * (2 * k))) = ((0 : ℕ) : ZMod (2 * (2 * k))) := by
    rw [Nat.cast_ofNat, h, Nat.cast_zero]
  have := (swap_natCast_inj (N := 2 * (2 * k)) (a := 2) (b := 0) (by omega) (by omega)).1 h2
  omega

theorem swap_double_eq_zero {k : ℕ} (hk : 1 ≤ k) {i : ZMod (2 * (2 * k))} (h : i + i = 0) :
    i = 0 ∨ i = ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  have hN : NeZero (2 * (2 * k)) := ⟨by omega⟩
  have hv : i = (i.val : ZMod (2 * (2 * k))) := (ZMod.natCast_zmod_val i).symm
  have hlt : i.val < 2 * (2 * k) := ZMod.val_lt i
  have h2 : ((2 * i.val : ℕ) : ZMod (2 * (2 * k))) = 0 := by
    push_cast
    rw [← hv, two_mul i]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨c, hc⟩ := h2
  have hc2 : c < 2 := by
    by_contra hcon
    have hcon' : 2 ≤ c := Nat.le_of_not_lt hcon
    nlinarith
  interval_cases c
  · left
    rw [hv]
    have : i.val = 0 := by omega
    rw [this]; simp
  · right
    rw [hv]
    have : i.val = 2 * k := by omega
    rw [this]

theorem swap_Q_zeta_sq (k : ℕ) :
    (a ((2 * k : ℕ) : ZMod (2 * (2 * k))) : QuaternionGroup (2 * k)) *
      a ((2 * k : ℕ) : ZMod (2 * (2 * k))) = 1 := by
  rw [a_mul_a, swap_two_k_add_self, a_zero]

theorem swap_Q_zeta_ne_one {k : ℕ} (hk : 1 ≤ k) :
    (a ((2 * k : ℕ) : ZMod (2 * (2 * k))) : QuaternionGroup (2 * k)) ≠ 1 := by
  rw [one_def]
  intro h
  exact swap_two_k_ne_zero hk (a.inj h)

theorem swap_Q_w_sq (k : ℕ) :
    (xa 0 : QuaternionGroup (2 * k)) * xa 0 = a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  rw [xa_mul_xa]; simp

theorem swap_Q_o_sq (k : ℕ) :
    (a (k : ZMod (2 * (2 * k))) : QuaternionGroup (2 * k)) * a (k : ZMod (2 * (2 * k))) =
      a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  rw [a_mul_a, swap_k_add_k]

theorem swap_Q_comm (k : ℕ) :
    (xa 0 : QuaternionGroup (2 * k)) * a (k : ZMod (2 * (2 * k))) =
      a ((2 * k : ℕ) : ZMod (2 * (2 * k))) * (a (k : ZMod (2 * (2 * k))) * xa 0) := by
  rw [xa_mul_a, a_mul_xa, a_mul_xa]
  congr 1
  push_cast
  linear_combination swap_four_k k

theorem swap_Q_central_zeta (k : ℕ) (g : QuaternionGroup (2 * k)) :
    a ((2 * k : ℕ) : ZMod (2 * (2 * k))) * g = g * a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  cases g with
  | a j => rw [a_mul_a, a_mul_a, add_comm]
  | xa j =>
    rw [a_mul_xa, xa_mul_a]
    congr 1
    linear_combination (-1 : ZMod (2 * (2 * k))) * swap_two_k_add_self k

theorem swap_Q_central_eq {k : ℕ} (hk : 1 ≤ k) {g : QuaternionGroup (2 * k)}
    (h : ∀ x : QuaternionGroup (2 * k), g * x = x * g) :
    g = 1 ∨ g = a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  cases g with
  | xa j =>
    exfalso
    have h1 := h (a 1)
    rw [xa_mul_a, a_mul_xa] at h1
    have h2 := xa.inj h1
    apply swap_two_ne_zero hk
    linear_combination h2
  | a i =>
    have h1 := h (xa 0)
    rw [a_mul_xa, xa_mul_a] at h1
    have h2 := xa.inj h1
    have h3 : i + i = 0 := by linear_combination -h2
    rcases swap_double_eq_zero hk h3 with rfl | rfl
    · left; exact a_zero
    · right; rfl

theorem swap_Q_invol {k : ℕ} (hk : 1 ≤ k) {g : QuaternionGroup (2 * k)} (h : g * g = 1)
    (hne : g ≠ 1) : g = a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  cases g with
  | xa j =>
    exfalso
    rw [xa_mul_xa] at h
    apply swap_Q_zeta_ne_one hk
    rw [show ((2 * k : ℕ) : ZMod (2 * (2 * k))) + j - j = ((2 * k : ℕ) : ZMod (2 * (2 * k))) by
      ring] at h
    exact h
  | a i =>
    rw [a_mul_a] at h
    have h3 := a.inj (h.trans one_def)
    rcases swap_double_eq_zero hk h3 with rfl | rfl
    · exact absurd a_zero hne
    · rfl

theorem swap_Q_central_mul_self {k : ℕ} (hk : 1 ≤ k) {g : QuaternionGroup (2 * k)}
    (h : ∀ x : QuaternionGroup (2 * k), g * x = x * g) : g * g = 1 := by
  rcases swap_Q_central_eq hk h with rfl | rfl
  · exact one_mul 1
  · exact swap_Q_zeta_sq k

theorem swap_Q_sq_eq (k : ℕ) (α β γ : Bool) (h : ¬ (β = false ∧ γ = false)) :
    (cond α (a ((2 * k : ℕ) : ZMod (2 * (2 * k))) : QuaternionGroup (2 * k)) 1 *
        cond β (xa 0) 1 * cond γ (a (k : ZMod (2 * (2 * k)))) 1) *
      (cond α (a ((2 * k : ℕ) : ZMod (2 * (2 * k))) : QuaternionGroup (2 * k)) 1 *
        cond β (xa 0) 1 * cond γ (a (k : ZMod (2 * (2 * k)))) 1) =
      a ((2 * k : ℕ) : ZMod (2 * (2 * k))) := by
  cases α <;> cases β <;> cases γ <;>
    simp_all [a_mul_a, a_mul_xa, xa_mul_a, xa_mul_xa, swap_k_add_k]
  linear_combination swap_four_k k

section Conjugation

variable {T : Type*} [Group T]

theorem swap_inv_eq {u : T} (hu : u * u = 1) : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu

theorem swap_conj_mem_left {P₁ P₂ : Subgroup T} {u : T} (hu : u * u = 1)
    (hu1 : P₁.map (MulAut.conj u).toMonoidHom = P₂) {g : T} (hg : g ∈ P₁) : u * g * u ∈ P₂ := by
  have hmem : (MulAut.conj u).toMonoidHom g ∈ P₂ := hu1 ▸ Subgroup.mem_map_of_mem _ hg
  simpa [MulAut.conj_apply, swap_inv_eq hu] using hmem

theorem swap_conj_mem_right {P₁ P₂ : Subgroup T} {u : T} (hu : u * u = 1)
    (hu1 : P₁.map (MulAut.conj u).toMonoidHom = P₂) {g : T} (hg : g ∈ P₂) : u * g * u ∈ P₁ := by
  rw [← hu1] at hg
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have : u * ((MulAut.conj u).toMonoidHom h) * u = h := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, swap_inv_eq hu]
    calc u * (u * h * u) * u = (u * u) * h * (u * u) := by group
      _ = h := by rw [hu]; group
  rw [this]; exact hh

theorem swap_conj_sq {u ζ g : T} (hu : u * u = 1) (huζ : u * ζ * u = ζ) (hg : g * g = ζ) :
    (u * g * u) * (u * g * u) = ζ := by
  calc (u * g * u) * (u * g * u) = u * (g * (u * u) * g) * u := by group
    _ = u * (g * g) * u := by rw [hu, mul_one]
    _ = ζ := by rw [hg, huζ]

theorem swap_comm_conj {u ζ : T} (hu : u * u = 1) (huζ : u * ζ * u = ζ) : ζ * u = u * ζ := by
  calc ζ * u = (u * ζ * u) * u := by rw [huζ]
    _ = u * ζ * (u * u) := by group
    _ = u * ζ := by rw [hu, mul_one]

theorem swap_conj_rel {u ζ w o : T} (hu : u * u = 1) (huζ : u * ζ * u = ζ)
    (hwo : w * o = ζ * (o * w)) :
    (u * w * u) * (u * o * u) = ζ * ((u * o * u) * (u * w * u)) := by
  have e1 : (u * w * u) * (u * o * u) = u * (w * o) * u := by
    calc (u * w * u) * (u * o * u) = u * w * (u * u) * o * u := by group
      _ = u * (w * o) * u := by rw [hu]; group
  have e2 : (u * ζ * u) * ((u * o * u) * (u * w * u)) = u * (ζ * (o * w)) * u := by
    calc (u * ζ * u) * ((u * o * u) * (u * w * u))
        = u * ζ * (u * u) * o * (u * u) * w * u := by group
      _ = u * (ζ * (o * w)) * u := by rw [hu]; group
  rw [e1, hwo, ← e2, huζ]

theorem swap_pair_sq {g g' ζ : T} (hcomm : g * g' = g' * g) (hg : g * g = ζ) (hg' : g' * g' = ζ)
    (hζ : ζ * ζ = 1) : (g * g') * (g * g') = 1 := by
  calc (g * g') * (g * g') = g * (g' * g) * g' := by group
    _ = g * (g * g') * g' := by rw [hcomm]
    _ = (g * g) * (g' * g') := by group
    _ = 1 := by rw [hg, hg', hζ]

theorem swap_pair_fix {u g : T} (hu : u * u = 1) (hcomm : g * (u * g * u) = (u * g * u) * g) :
    u * (g * (u * g * u)) * u = g * (u * g * u) := by
  calc u * (g * (u * g * u)) * u = (u * g * u) * g * (u * u) := by group
    _ = g * (u * g * u) := by rw [hu, mul_one, ← hcomm]

theorem swap_pair_comm {g g' h h' ζ : T}
    (hgh : g * h = ζ * (h * g)) (hgh' : g' * h' = ζ * (h' * g'))
    (c1 : g' * h = h * g') (c2 : g * h' = h' * g)
    (z1 : ζ * h = h * ζ) (z2 : ζ * g = g * ζ) (hζ : ζ * ζ = 1) :
    (g * g') * (h * h') = (h * h') * (g * g') := by
  have hzhg : ζ * (h * g) = (h * g) * ζ := by
    calc ζ * (h * g) = (ζ * h) * g := by group
      _ = h * (ζ * g) := by rw [z1]; group
      _ = h * (g * ζ) := by rw [z2]
      _ = (h * g) * ζ := by group
  calc (g * g') * (h * h') = g * (g' * h) * h' := by group
    _ = g * (h * g') * h' := by rw [c1]
    _ = (g * h) * (g' * h') := by group
    _ = (ζ * (h * g)) * (ζ * (h' * g')) := by rw [hgh, hgh']
    _ = ((h * g) * ζ) * (ζ * (h' * g')) := by rw [hzhg]
    _ = (h * g) * (ζ * ζ) * (h' * g') := by group
    _ = (h * g) * (h' * g') := by rw [hζ, mul_one]
    _ = h * (g * h') * g' := by group
    _ = h * (h' * g) * g' := by rw [c2]
    _ = (h * h') * (g * g') := by group

theorem swap_zeta_mul_comm {ζ g g' : T} (h1 : ζ * g = g * ζ) (h2 : ζ * g' = g' * ζ) :
    ζ * (g * g') = (g * g') * ζ := by
  calc ζ * (g * g') = (ζ * g) * g' := by group
    _ = g * (ζ * g') := by rw [h1]; group
    _ = g * (g' * ζ) := by rw [h2]
    _ = (g * g') * ζ := by group

theorem swap_regroup {c w w' o o' : T} (h : w' * o = o * w') (α β γ : Bool) :
    cond α c 1 * cond β (w * w') 1 * cond γ (o * o') 1 =
      (cond α c 1 * cond β w 1 * cond γ o 1) * (cond β w' 1 * cond γ o' 1) := by
  cases α <;> cases β <;> cases γ <;>
    simp [mul_assoc, (Commute.left_comm (show Commute w' o from h))]

theorem swap_conj_mem_of_mul {P₁ P₂ : Subgroup T} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    {u : T} (hu : u * u = 1) {p₁ p₂ : T} (hp₁ : p₁ ∈ P₁) (hp₂ : p₂ ∈ P₂) (hup : p₁ * p₂ = u)
    {g : T} (hg : g ∈ P₁) : u * g * u ∈ P₁ := by
  have h : u * g * u = p₁ * g * p₁⁻¹ := by
    calc u * g * u = u * g * u⁻¹ := by rw [swap_inv_eq hu]
      _ = (p₁ * p₂) * g * (p₁ * p₂)⁻¹ := by rw [hup]
      _ = p₁ * (p₂ * g) * p₂⁻¹ * p₁⁻¹ := by group
      _ = p₁ * (g * p₂) * p₂⁻¹ * p₁⁻¹ := by rw [← hc g hg p₂ hp₂]
      _ = p₁ * g * p₁⁻¹ := by group
  rw [h]
  exact mul_mem (mul_mem hp₁ hg) (inv_mem hp₁)

theorem swap_independent {P₁ P₂ : Subgroup T} {u ζ w o : T}
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hu : u * u = 1)
    (hu₁ : ∀ g ∈ P₁, u * g * u ∈ P₂)
    (hw : w ∈ P₁) (ho : o ∈ P₁) (hζ₁ : ζ ∈ P₁) (hζne : ζ ≠ 1)
    (hw'sq : (u * w * u) * (u * w * u) = ζ)
    (hZ : ∀ z ∈ P₁, z ∈ P₂ → z * z = 1)
    (hind : ∀ α β γ : Bool,
      (cond α ζ 1 * cond β w 1 * cond γ o 1) * (cond α ζ 1 * cond β w 1 * cond γ o 1) = 1 →
        β = false ∧ γ = false)
    (α β γ δ : Bool)
    (h : cond α ζ 1 * cond β (w * (u * w * u)) 1 * cond γ (o * (u * o * u)) 1 * cond δ u 1 = 1) :
    α = false ∧ β = false ∧ γ = false ∧ δ = false := by
  have hw' : u * w * u ∈ P₂ := hu₁ w hw
  have ho' : u * o * u ∈ P₂ := hu₁ o ho
  have hcomm : (u * w * u) * o = o * (u * w * u) := (hc o ho _ hw').symm
  rw [swap_regroup hcomm] at h
  have hp₁ : cond α ζ 1 * cond β w 1 * cond γ o 1 ∈ P₁ := by
    refine mul_mem (mul_mem ?_ ?_) ?_
    · cases α <;> simp [hζ₁, one_mem]
    · cases β <;> simp [hw, one_mem]
    · cases γ <;> simp [ho, one_mem]
  have hp₂ : cond β (u * w * u) 1 * cond γ (u * o * u) 1 ∈ P₂ := by
    refine mul_mem ?_ ?_
    · cases β <;> simp [hw', one_mem]
    · cases γ <;> simp [ho', one_mem]
  cases δ
  · simp only [Bool.cond_false, mul_one] at h
    have hp₁₂ : cond α ζ 1 * cond β w 1 * cond γ o 1 ∈ P₂ := by
      have : cond α ζ 1 * cond β w 1 * cond γ o 1 =
          (cond β (u * w * u) 1 * cond γ (u * o * u) 1)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]; exact inv_mem hp₂
    obtain ⟨hβ, hγ⟩ := hind α β γ (hZ _ hp₁ hp₁₂)
    subst hβ hγ
    cases α
    · simp
    · simp at h; exact absurd h hζne
  · simp only [Bool.cond_true] at h
    exfalso
    have hup : (cond α ζ 1 * cond β w 1 * cond γ o 1) *
        (cond β (u * w * u) 1 * cond γ (u * o * u) 1) = u :=
      (eq_inv_of_mul_eq_one_left h).trans (swap_inv_eq hu)
    have hmem := swap_conj_mem_of_mul hc hu hp₁ hp₂ hup hw
    have := hZ _ hmem hw'
    rw [hw'sq] at this
    exact hζne this

end Conjugation

theorem swap_cond_mul_cond {G : Type*} [Group G] {g : G} (hg : g * g = 1) (α β : Bool) :
    cond α g 1 * cond β g 1 = cond (xor α β) g 1 := by
  cases α <;> cases β <;> simp [hg]

theorem swap_sixteen_le_card {G : Type*} [Group G] [IsMulCommutative G] [Finite G]
    {g₀ g₁ g₂ g₃ : G} (h₀ : g₀ * g₀ = 1) (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1)
    (h₃ : g₃ * g₃ = 1)
    (hind : ∀ α β γ δ : Bool, cond α g₀ 1 * cond β g₁ 1 * cond γ g₂ 1 * cond δ g₃ 1 = 1 →
      α = false ∧ β = false ∧ γ = false ∧ δ = false) : 16 ≤ Nat.card G := by
  let F : Bool × Bool × Bool × Bool → G := fun v =>
    cond v.1 g₀ 1 * cond v.2.1 g₁ 1 * cond v.2.2.1 g₂ 1 * cond v.2.2.2 g₃ 1
  have hmul : ∀ v w : Bool × Bool × Bool × Bool, F v * F w =
      F (xor v.1 w.1, xor v.2.1 w.2.1, xor v.2.2.1 w.2.2.1, xor v.2.2.2 w.2.2.2) := by
    intro v w
    simp only [F, ← swap_cond_mul_cond h₀, ← swap_cond_mul_cond h₁, ← swap_cond_mul_cond h₂,
      ← swap_cond_mul_cond h₃]
    ac_rfl
  have hinj : Function.Injective F := by
    intro v w hvw
    have h1 : F v * F w = 1 := by
      rw [hvw]
      have := hmul w w
      simp only [Bool.xor_self] at this
      rw [this]
      simp [F]
    rw [hmul] at h1
    obtain ⟨h1, h2, h3, h4⟩ := hind _ _ _ _ h1
    have hx : ∀ p q : Bool, xor p q = false → p = q := by decide
    exact Prod.ext (hx _ _ h1) (Prod.ext (hx _ _ h2) (Prod.ext (hx _ _ h3) (hx _ _ h4)))
  have := Nat.card_le_card_of_injective F hinj
  simpa [Nat.card_prod] using this

theorem swap_closure_isElementaryAbelian {T : Type*} [Group T] {s : Set T}
    (hcomm : s.Pairwise Commute) (hsq : ∀ x ∈ s, x * x = 1) :
    IsElementaryAbelian 2 (Subgroup.closure s) := by
  have hc : IsMulCommutative (Subgroup.closure s) := Subgroup.isMulCommutative_closure hcomm
  refine { toIsMulCommutative := hc, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  apply Subtype.ext
  show (x : T) ^ 2 = 1
  refine Subgroup.closure_induction (p := fun z _ => z ^ 2 = 1)
    (fun y hy => by rw [sq]; exact hsq y hy) (by simp) ?_ ?_ x.2
  · intro y z hy hz hy2 hz2
    have hyz : Commute y z := congrArg Subtype.val
      (mul_comm' (⟨y, hy⟩ : Subgroup.closure s) ⟨z, hz⟩)
    rw [hyz.mul_pow, hy2, hz2, one_mul]
  · intro y _ hy2
    simpa only [inv_pow, inv_one] using congrArg Inv.inv hy2

section Main

variable {T : Type*} [Group T]

theorem swap_exists_E [Finite T] {P₁ P₂ : Subgroup T} {u ζ w o : T}
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hu : u * u = 1)
    (hu1 : P₁.map (MulAut.conj u).toMonoidHom = P₂)
    (hw : w ∈ P₁) (ho : o ∈ P₁) (hζ₁ : ζ ∈ P₁)
    (hζ : ζ * ζ = 1) (hζne : ζ ≠ 1) (hwsq : w * w = ζ) (hosq : o * o = ζ)
    (hζw : ζ * w = w * ζ) (hζo : ζ * o = o * ζ) (hwo : w * o = ζ * (o * w))
    (huζ : u * ζ * u = ζ)
    (hZ : ∀ z ∈ P₁, z ∈ P₂ → z * z = 1)
    (hind : ∀ α β γ : Bool,
      (cond α ζ 1 * cond β w 1 * cond γ o 1) * (cond α ζ 1 * cond β w 1 * cond γ o 1) = 1 →
        β = false ∧ γ = false) :
    ∃ E : Subgroup T, E ≤ P₁ ⊔ P₂ ⊔ Subgroup.zpowers u ∧ IsElementaryAbelian 2 ↥E ∧
      16 ≤ Nat.card ↥E := by
  have hu₁ : ∀ g ∈ P₁, u * g * u ∈ P₂ := fun g hg => swap_conj_mem_left hu hu1 hg
  have hw' : u * w * u ∈ P₂ := hu₁ w hw
  have ho' : u * o * u ∈ P₂ := hu₁ o ho
  have hζu : ζ * u = u * ζ := swap_comm_conj hu huζ
  have hw'sq : (u * w * u) * (u * w * u) = ζ := swap_conj_sq hu huζ hwsq
  have ho'sq : (u * o * u) * (u * o * u) = ζ := swap_conj_sq hu huζ hosq
  have hww' : w * (u * w * u) = (u * w * u) * w := hc w hw _ hw'
  have hoo' : o * (u * o * u) = (u * o * u) * o := hc o ho _ ho'
  have hwo' : w * (u * o * u) = (u * o * u) * w := hc w hw _ ho'
  have hw'o : (u * w * u) * o = o * (u * w * u) := (hc o ho _ hw').symm
  have hζw' : ζ * (u * w * u) = (u * w * u) * ζ := by
    have h1 : Commute ζ u := hζu
    have h2 : Commute ζ w := hζw
    exact ((h1.mul_right h2).mul_right h1).eq
  have hζo' : ζ * (u * o * u) = (u * o * u) * ζ := by
    have h1 : Commute ζ u := hζu
    have h2 : Commute ζ o := hζo
    exact ((h1.mul_right h2).mul_right h1).eq
  have hwo'' : (u * w * u) * (u * o * u) = ζ * ((u * o * u) * (u * w * u)) :=
    swap_conj_rel hu huζ hwo
  have hx_sq : (w * (u * w * u)) * (w * (u * w * u)) = 1 := swap_pair_sq hww' hwsq hw'sq hζ
  have hy_sq : (o * (u * o * u)) * (o * (u * o * u)) = 1 := swap_pair_sq hoo' hosq ho'sq hζ
  have hxu : u * (w * (u * w * u)) * u = w * (u * w * u) := swap_pair_fix hu hww'
  have hyu : u * (o * (u * o * u)) * u = o * (u * o * u) := swap_pair_fix hu hoo'
  have hxy : (w * (u * w * u)) * (o * (u * o * u)) = (o * (u * o * u)) * (w * (u * w * u)) :=
    swap_pair_comm hwo hwo'' hw'o hwo' hζo hζw hζ
  have hζx : ζ * (w * (u * w * u)) = (w * (u * w * u)) * ζ := swap_zeta_mul_comm hζw hζw'
  have hζy : ζ * (o * (u * o * u)) = (o * (u * o * u)) * ζ := swap_zeta_mul_comm hζo hζo'
  have hxu' := swap_comm_conj hu hxu
  have hyu' := swap_comm_conj hu hyu
  set x := w * (u * w * u) with hx
  set y := o * (u * o * u) with hy
  have hpair : ({ζ, x, y, u} : Set T).Pairwise Commute := by
    intro p hp q hq _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
        | exact Commute.refl _
        | assumption
        | exact Commute.symm (by assumption)
  have hsq : ∀ s ∈ ({ζ, x, y, u} : Set T), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> assumption
  have hE := swap_closure_isElementaryAbelian hpair hsq
  have hle : Subgroup.closure ({ζ, x, y, u} : Set T) ≤ P₁ ⊔ P₂ ⊔ Subgroup.zpowers u := by
    rw [Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hζ₁)
    · exact Subgroup.mem_sup_left (Subgroup.mul_mem_sup hw hw')
    · exact Subgroup.mem_sup_left (Subgroup.mul_mem_sup ho ho')
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨Subgroup.closure {ζ, x, y, u}, hle, hE, ?_⟩
  have := hE.toIsMulCommutative
  have hcoe : ∀ (b : Bool) (g : ↥(Subgroup.closure ({ζ, x, y, u} : Set T))),
      ((cond b g 1 : ↥(Subgroup.closure ({ζ, x, y, u} : Set T))) : T) = cond b (g : T) 1 := by
    intro b g; cases b <;> rfl
  exact swap_sixteen_le_card
    (g₀ := ⟨ζ, Subgroup.subset_closure (by simp)⟩) (g₁ := ⟨x, Subgroup.subset_closure (by simp)⟩)
    (g₂ := ⟨y, Subgroup.subset_closure (by simp)⟩) (g₃ := ⟨u, Subgroup.subset_closure (by simp)⟩)
    (Subtype.ext hζ) (Subtype.ext hx_sq) (Subtype.ext hy_sq) (Subtype.ext hu)
    (fun α β γ δ h => by
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_one, hcoe] at h'
      exact swap_independent hc hu hu₁ hw ho hζ₁ hζne hw'sq hZ hind α β γ δ h')

theorem swap_main [Finite T] {P₁ P₂ : Subgroup T} {k : ℕ} (hk : 1 ≤ k)
    (φ : QuaternionGroup (2 * k) →* T) (hφ : Function.Injective φ)
    (hφ₁ : ∀ q, φ q ∈ P₁) (hφ₂ : ∀ p ∈ P₁, ∃ q, φ q = p)
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    {u : T} (hu : u * u = 1) (hu1 : P₁.map (MulAut.conj u).toMonoidHom = P₂) :
    ∃ E : Subgroup T, E ≤ P₁ ⊔ P₂ ⊔ Subgroup.zpowers u ∧ IsElementaryAbelian 2 ↥E ∧
      16 ≤ Nat.card ↥E := by
  have hZq : ∀ z ∈ P₁, z ∈ P₂ → ∃ q, φ q = z ∧ ∀ g, q * g = g * q := by
    intro z hz₁ hz₂
    obtain ⟨q, hq⟩ := hφ₂ z hz₁
    refine ⟨q, hq, fun g => hφ ?_⟩
    rw [map_mul, map_mul, hq]
    exact (hc _ (hφ₁ g) z hz₂).symm
  have hZ : ∀ z ∈ P₁, z ∈ P₂ → z * z = 1 := by
    intro z hz₁ hz₂
    obtain ⟨q, hq, hcen⟩ := hZq z hz₁ hz₂
    rw [← hq, ← map_mul, swap_Q_central_mul_self hk hcen, map_one]
  have hex : ∃ z ∈ P₁ ⊓ P₂, z ≠ 1 := by
    by_contra hall
    have hbot : P₁ ⊓ P₂ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hz1
      exact hall ⟨z, hz, hz1⟩
    rw [hbot, Subgroup.card_bot] at hinf
    omega
  have hζne : φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) ≠ 1 := fun h =>
    swap_Q_zeta_ne_one hk (hφ (h.trans (map_one φ).symm))
  have hζ₂ : φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) ∈ P₂ := by
    obtain ⟨z, hz, hz1⟩ := hex
    obtain ⟨q, hq, hcen⟩ := hZq z hz.1 hz.2
    rcases swap_Q_central_eq hk hcen with rfl | rfl
    · exact absurd (hq.symm.trans (map_one φ)) hz1
    · rw [hq]; exact hz.2
  have hζ : φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) *
      φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) = 1 := by
    rw [← map_mul, swap_Q_zeta_sq, map_one]
  have huζ : u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u =
      φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) := by
    have hv := swap_conj_mem_right hu hu1 hζ₂
    obtain ⟨q, hq⟩ := hφ₂ _ hv
    have hvv : u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u *
        (u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u) = 1 := by
      calc u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u *
          (u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u)
          = u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * (u * u) *
              φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u := by group
        _ = u * (φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) *
              φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k))))) * u := by rw [hu]; group
        _ = 1 := by rw [hζ, mul_one, hu]
    have hqq : q * q = 1 := by
      apply hφ
      rw [map_mul, hq, map_one]
      exact hvv
    have hq1 : q ≠ 1 := by
      intro h1
      rw [h1, map_one] at hq
      apply hζne
      calc φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k))))
          = (u * u) * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * (u * u) := by rw [hu]; group
        _ = u * (u * φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))) * u) * u := by group
        _ = 1 := by rw [← hq, mul_one, hu]
    rw [← hq, swap_Q_invol hk hqq hq1]
  have hind : ∀ α β γ : Bool,
      (cond α (φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k))))) 1 * cond β (φ (xa 0)) 1 *
        cond γ (φ (a (k : ZMod (2 * (2 * k))))) 1) *
      (cond α (φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k))))) 1 * cond β (φ (xa 0)) 1 *
        cond γ (φ (a (k : ZMod (2 * (2 * k))))) 1) = 1 → β = false ∧ γ = false := by
    intro α β γ h
    by_contra hne
    have hcond : ∀ (b : Bool) (q : QuaternionGroup (2 * k)), φ (cond b q 1) = cond b (φ q) 1 := by
      intro b q; cases b <;> simp
    have key := congrArg φ (swap_Q_sq_eq k α β γ hne)
    simp only [map_mul, hcond] at key
    exact hζne (key.symm.trans h)
  exact swap_exists_E (ζ := φ (a ((2 * k : ℕ) : ZMod (2 * (2 * k)))))
    (w := φ (xa 0)) (o := φ (a (k : ZMod (2 * (2 * k))))) hc hu hu1 (hφ₁ _) (hφ₁ _) (hφ₁ _) hζ hζne
    (by simpa only [map_mul] using congrArg φ (swap_Q_w_sq k))
    (by simpa only [map_mul] using congrArg φ (swap_Q_o_sq k))
    (by simpa only [map_mul] using congrArg φ (swap_Q_central_zeta k (xa 0)))
    (by simpa only [map_mul] using congrArg φ (swap_Q_central_zeta k (a (k : ZMod (2 * (2 * k))))))
    (by simpa only [map_mul] using congrArg φ (swap_Q_comm k)) huζ hZ hind

end Main

theorem swap_elementary_abelian_sixteen {T : Type} [Group T] [Finite T] {n : ℕ} (hn : 2 ≤ n)
    {P₁ P₂ : Subgroup T} (h₁ : IVK.IsQuaternionTwoGroup ↥P₁ (n + 1))
    (h₂ : IVK.IsQuaternionTwoGroup ↥P₂ (n + 1))
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    {u : T} (hu : u * u = 1) (hu1 : P₁.map (MulAut.conj u).toMonoidHom = P₂) :
    ∃ E : Subgroup T, E ≤ P₁ ⊔ P₂ ⊔ Subgroup.zpowers u ∧ IsElementaryAbelian 2 ↥E ∧
      16 ≤ Nat.card ↥E := by
  obtain ⟨_, _⟩ := h₂
  obtain ⟨_, ⟨e⟩⟩ := h₁
  have hk : 2 ^ (n + 1 - 2) = 2 * 2 ^ (n - 2) := by
    rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ, mul_comm]
  rw [hk] at e
  exact swap_main Nat.one_le_two_pow (P₁.subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective) (fun q => (e.symm q).2)
    (fun p hp => ⟨e ⟨p, hp⟩, by simp⟩) hc hinf hu hu1

end CFSG.GH74.GLS.Stage1.Main
