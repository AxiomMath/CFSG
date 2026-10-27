module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.CGT.Stroth77

section Relations

variable {H : Type*} [Group H]

@[expose] def eqns201 (m : ℕ) (c a b uv t u f : H) : List (H × H) :=
  [(c ^ 2 ^ m, 1), (a ^ 2 ^ (m + 2), 1), (b ^ 2 ^ (m + 2), 1),
    (c * a, a * c), (c * b, b * c), (a * b, b * a),
    (uv⁻¹ * c * uv, c ^ (-3 : ℤ) * a ^ (-4 : ℤ) * b ^ (-4 : ℤ)),
    (uv⁻¹ * a * uv, c * a * b ^ (2 * 2 ^ m + 2)),
    (uv⁻¹ * b * uv, c * a ^ (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * b),
    (t⁻¹ * c * t, c * a ^ 4), (t⁻¹ * a * t, a ^ (2 * 2 ^ m - 1 : ℤ)),
    (t⁻¹ * b * t, c ^ (-2 * 2 ^ m - 1 : ℤ) * a ^ (-2 * 2 ^ m - 2 : ℤ) * b ^ (-2 * 2 ^ m - 1 : ℤ)),
    (u⁻¹ * c * u, c), (u⁻¹ * a * u, b), (u⁻¹ * b * u, a),
    (f⁻¹ * c * f, c⁻¹), (f⁻¹ * a * f, a⁻¹ * a ^ 2 ^ (m + 1)),
    (f⁻¹ * b * f, b⁻¹ * b ^ 2 ^ (m + 1)),
    (uv * uv, 1), (t * t, 1), (u * u, 1), (uv * t, t * uv), (uv * u, u * uv),
    (t * u, u * uv * t),
    (f * f, 1), (f⁻¹ * uv * f, (c * a * b) ^ 2 * uv), (f⁻¹ * t * f, a⁻¹ ^ 2 * t),
    (f⁻¹ * u * f, u)]

@[expose] def Rel201 (m : ℕ) (c a b uv t u f : H) : Prop :=
  ∀ p ∈ eqns201 m c a b uv t u f, p.1 = p.2

theorem eqns201_map {H' : Type*} [Group H'] (φ : H →* H') (m : ℕ) (c a b uv t u f : H) :
    (eqns201 m c a b uv t u f).map (Prod.map φ φ) =
      eqns201 m (φ c) (φ a) (φ b) (φ uv) (φ t) (φ u) (φ f) := by
  simp [eqns201]

theorem Rel201.map {H' : Type*} [Group H'] {m : ℕ} {c a b uv t u f : H}
    (h : Rel201 m c a b uv t u f) (φ : H →* H') :
    Rel201 m (φ c) (φ a) (φ b) (φ uv) (φ t) (φ u) (φ f) := by
  intro p hp
  rw [← eqns201_map, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact congrArg φ (h q hq)

end Relations

namespace Rel201

variable {H : Type*} [Group H] {m : ℕ} {c a b uv t u f : H} (h : Rel201 m c a b uv t u f)
include h

theorem c_pow : c ^ 2 ^ m = 1 := h (c ^ 2 ^ m, 1) (by simp [eqns201])
theorem a_pow : a ^ 2 ^ (m + 2) = 1 := h (a ^ 2 ^ (m + 2), 1) (by simp [eqns201])
theorem b_pow : b ^ 2 ^ (m + 2) = 1 := h (b ^ 2 ^ (m + 2), 1) (by simp [eqns201])
theorem ca : c * a = a * c := h (c * a, a * c) (by simp [eqns201])
theorem cb : c * b = b * c := h (c * b, b * c) (by simp [eqns201])
theorem ab : a * b = b * a := h (a * b, b * a) (by simp [eqns201])
theorem uv_c : uv⁻¹ * c * uv = c ^ (-3 : ℤ) * a ^ (-4 : ℤ) * b ^ (-4 : ℤ) :=
  h (uv⁻¹ * c * uv, c ^ (-3 : ℤ) * a ^ (-4 : ℤ) * b ^ (-4 : ℤ)) (by simp [eqns201])
theorem uv_a : uv⁻¹ * a * uv = c * a * b ^ (2 * 2 ^ m + 2) :=
  h (uv⁻¹ * a * uv, c * a * b ^ (2 * 2 ^ m + 2)) (by simp [eqns201])
theorem uv_b : uv⁻¹ * b * uv = c * a ^ (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * b :=
  h (uv⁻¹ * b * uv, c * a ^ (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * b) (by simp [eqns201])
theorem t_c : t⁻¹ * c * t = c * a ^ 4 := h (t⁻¹ * c * t, c * a ^ 4) (by simp [eqns201])
theorem t_a : t⁻¹ * a * t = a ^ (2 * 2 ^ m - 1 : ℤ) :=
  h (t⁻¹ * a * t, a ^ (2 * 2 ^ m - 1 : ℤ)) (by simp [eqns201])
theorem t_b : t⁻¹ * b * t =
    c ^ (-2 * 2 ^ m - 1 : ℤ) * a ^ (-2 * 2 ^ m - 2 : ℤ) * b ^ (-2 * 2 ^ m - 1 : ℤ) :=
  h (t⁻¹ * b * t, c ^ (-2 * 2 ^ m - 1 : ℤ) * a ^ (-2 * 2 ^ m - 2 : ℤ) * b ^ (-2 * 2 ^ m - 1 : ℤ))
    (by simp [eqns201])
theorem u_c : u⁻¹ * c * u = c := h (u⁻¹ * c * u, c) (by simp [eqns201])
theorem u_a : u⁻¹ * a * u = b := h (u⁻¹ * a * u, b) (by simp [eqns201])
theorem u_b : u⁻¹ * b * u = a := h (u⁻¹ * b * u, a) (by simp [eqns201])
theorem f_c : f⁻¹ * c * f = c⁻¹ := h (f⁻¹ * c * f, c⁻¹) (by simp [eqns201])
theorem f_a : f⁻¹ * a * f = a⁻¹ * a ^ 2 ^ (m + 1) :=
  h (f⁻¹ * a * f, a⁻¹ * a ^ 2 ^ (m + 1)) (by simp [eqns201])
theorem f_b : f⁻¹ * b * f = b⁻¹ * b ^ 2 ^ (m + 1) :=
  h (f⁻¹ * b * f, b⁻¹ * b ^ 2 ^ (m + 1)) (by simp [eqns201])
theorem uv_sq : uv * uv = 1 := h (uv * uv, 1) (by simp [eqns201])
theorem t_sq : t * t = 1 := h (t * t, 1) (by simp [eqns201])
theorem u_sq : u * u = 1 := h (u * u, 1) (by simp [eqns201])
theorem uv_t : uv * t = t * uv := h (uv * t, t * uv) (by simp [eqns201])
theorem uv_u : uv * u = u * uv := h (uv * u, u * uv) (by simp [eqns201])
theorem t_u : t * u = u * uv * t := h (t * u, u * uv * t) (by simp [eqns201])
theorem f_sq : f * f = 1 := h (f * f, 1) (by simp [eqns201])
theorem f_uv : f⁻¹ * uv * f = (c * a * b) ^ 2 * uv :=
  h (f⁻¹ * uv * f, (c * a * b) ^ 2 * uv) (by simp [eqns201])
theorem f_t : f⁻¹ * t * f = a⁻¹ ^ 2 * t := h (f⁻¹ * t * f, a⁻¹ ^ 2 * t) (by simp [eqns201])
theorem f_u : f⁻¹ * u * f = u := h (f⁻¹ * u * f, u) (by simp [eqns201])

theorem uv_inv : uv⁻¹ = uv := inv_eq_of_mul_eq_one_right h.uv_sq
theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
theorem u_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right h.u_sq
theorem f_inv : f⁻¹ = f := inv_eq_of_mul_eq_one_right h.f_sq

theorem uv_mul_uv (x : H) : uv * (uv * x) = x := by rw [← mul_assoc, h.uv_sq, one_mul]
theorem t_mul_t (x : H) : t * (t * x) = x := by rw [← mul_assoc, h.t_sq, one_mul]
theorem u_mul_u (x : H) : u * (u * x) = x := by rw [← mul_assoc, h.u_sq, one_mul]
theorem t_mul_uv (x : H) : t * (uv * x) = uv * (t * x) := by rw [← mul_assoc, ← h.uv_t, mul_assoc]

theorem u_mul_uv (x : H) : u * (uv * x) = uv * (u * x) := by
  rw [← mul_assoc, ← h.uv_u, mul_assoc]

theorem u_t : u * t = uv * t * u := by
  have h1 : u * (t * u) * u = u * (u * uv * t) * u := by rw [h.t_u]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, h.u_sq, one_mul, mul_assoc, h.u_sq, mul_one] at h1
  rw [h1]

theorem u_mul_t (x : H) : u * (t * x) = uv * (t * (u * x)) := by
  rw [← mul_assoc, h.u_t, mul_assoc, mul_assoc]

theorem t_uv : t * uv = uv * t := h.uv_t.symm
theorem u_uv : u * uv = uv * u := h.uv_u.symm
theorem u_t' : u * t = uv * (t * u) := by rw [h.u_t, mul_assoc]

end Rel201

section Torus

variable {H : Type*} [Group H] {m : ℕ} {c a b : H}

@[expose] noncomputable def zmodPowHom201 {K : Type*} [CommGroup K] (k : ℕ) (x : K)
    (hx : x ^ 2 ^ k = 1) : ZMod (2 ^ k) →+ Additive K :=
  ZMod.lift (2 ^ k) ⟨zmultiplesHom (Additive K) (Additive.ofMul x), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hx, ofMul_one]⟩

theorem zmodPowHom201_one {K : Type*} [CommGroup K] (k : ℕ) (x : K) (hx : x ^ 2 ^ k = 1) :
    zmodPowHom201 k x hx 1 = Additive.ofMul x := by
  have h := ZMod.lift_coe (2 ^ k) ⟨zmultiplesHom (Additive K) (Additive.ofMul x), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hx, ofMul_one]⟩ 1
  simpa [zmodPowHom201] using h

theorem card_closure_cab_le201 (hc : c ^ 2 ^ m = 1) (ha : a ^ 2 ^ (m + 2) = 1)
    (hb : b ^ 2 ^ (m + 2) = 1) (hca : c * a = a * c) (hcb : c * b = b * c) (hab : a * b = b * a) :
    Finite (Subgroup.closure ({c, a, b} : Set H)) ∧
      Nat.card (Subgroup.closure ({c, a, b} : Set H)) ≤ 2 ^ (3 * m + 4) := by
  classical
  set K := Subgroup.closure ({c, a, b} : Set H) with hK
  have hpair : ({c, a, b} : Set H).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hca | exact hca.symm | exact hcb | exact hcb.symm | exact hab | exact hab.symm
  letI : CommGroup K := Subgroup.closureCommGroupOfComm hpair
  let c' : K := ⟨c, Subgroup.subset_closure (by simp)⟩
  let a' : K := ⟨a, Subgroup.subset_closure (by simp)⟩
  let b' : K := ⟨b, Subgroup.subset_closure (by simp)⟩
  have hc' : c' ^ 2 ^ m = 1 := Subtype.ext (by simpa [c'] using hc)
  have ha' : a' ^ 2 ^ (m + 2) = 1 := Subtype.ext (by simpa [a'] using ha)
  have hb' : b' ^ 2 ^ (m + 2) = 1 := Subtype.ext (by simpa [b'] using hb)
  let Φ : ZMod (2 ^ m) × ZMod (2 ^ (m + 2)) × ZMod (2 ^ (m + 2)) →+ Additive K :=
    (zmodPowHom201 m c' hc').comp (AddMonoidHom.fst _ _) +
      (zmodPowHom201 (m + 2) a' ha').comp ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _)) +
      (zmodPowHom201 (m + 2) b' hb').comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))
  have hΦc : Φ (1, 0, 0) = Additive.ofMul c' := by
    simp [Φ, zmodPowHom201_one]
  have hΦa : Φ (0, 1, 0) = Additive.ofMul a' := by
    simp [Φ, zmodPowHom201_one]
  have hΦb : Φ (0, 0, 1) = Additive.ofMul b' := by
    simp [Φ, zmodPowHom201_one]
  have key : ∀ z : K, z ∈ Subgroup.closure (((↑) : K → H) ⁻¹' {c, a, b}) →
      ∃ v, Φ v = Additive.ofMul z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · exact ⟨(1, 0, 0), by rw [hΦc]; exact congrArg Additive.ofMul (Subtype.ext hx.symm)⟩
      · exact ⟨(0, 1, 0), by rw [hΦa]; exact congrArg Additive.ofMul (Subtype.ext hx.symm)⟩
      · exact ⟨(0, 0, 1), by rw [hΦb]; exact congrArg Additive.ofMul (Subtype.ext hx.symm)⟩
    | one => exact ⟨0, map_zero Φ⟩
    | mul x y _ _ hx hy =>
      obtain ⟨v, hv⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨v + w, by rw [map_add, hv, hw]; rfl⟩
    | inv x _ hx =>
      obtain ⟨v, hv⟩ := hx
      exact ⟨-v, by rw [map_neg, hv]; rfl⟩
  have hsurj : Function.Surjective Φ := fun y =>
    key (Additive.toMul y) (by rw [Subgroup.closure_closure_coe_preimage]; exact Subgroup.mem_top _)
  have hfin : Finite (Additive K) := Finite.of_surjective Φ hsurj
  refine ⟨Finite.of_equiv _ Additive.toMul, ?_⟩
  calc Nat.card K = Nat.card (Additive K) := (Nat.card_congr Additive.toMul).symm
    _ ≤ Nat.card (ZMod (2 ^ m) × ZMod (2 ^ (m + 2)) × ZMod (2 ^ (m + 2))) :=
        Nat.card_le_card_of_surjective Φ hsurj
    _ = 2 ^ (3 * m + 4) := by
        simp only [Nat.card_prod, Nat.card_zmod]
        ring

end Torus

section NormalForm

variable {H : Type*} [Group H] {m : ℕ} {c a b uv t u f : H}

@[expose] def word201 (uv t u : H) (α β γ : Fin 2) : H := uv ^ (α : ℕ) * t ^ (β : ℕ) * u ^ (γ : ℕ)

theorem uv_mul_word201 (h : Rel201 m c a b uv t u f) (α β γ : Fin 2) :
    uv * word201 uv t u α β γ = word201 uv t u (α + 1) β γ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [word201, mul_assoc, h.uv_mul_uv, h.uv_sq]

theorem t_mul_word201 (h : Rel201 m c a b uv t u f) (α β γ : Fin 2) :
    t * word201 uv t u α β γ = word201 uv t u α (β + 1) γ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [word201, mul_assoc, h.t_mul_uv, h.t_mul_t, h.t_sq, h.t_uv]

theorem u_mul_word201 (h : Rel201 m c a b uv t u f) (α β γ : Fin 2) :
    u * word201 uv t u α β γ = word201 uv t u (α + β) β (γ + 1) := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    simp [word201, mul_assoc, h.u_mul_uv, h.u_mul_t, h.u_mul_u, h.u_sq, h.uv_mul_uv, h.uv_sq,
      h.u_uv, h.u_t']

@[expose] def normalForm201 (c a b uv t u f : H) : Set H :=
  {x | ∃ d ∈ Subgroup.closure ({c, a, b} : Set H), ∃ δ α β γ : Fin 2,
    x = d * f ^ (δ : ℕ) * word201 uv t u α β γ}

theorem conj_mem_closure_cab201 {g : H} (hg : g * g = 1)
    (h1 : g⁻¹ * c * g ∈ Subgroup.closure ({c, a, b} : Set H))
    (h2 : g⁻¹ * a * g ∈ Subgroup.closure ({c, a, b} : Set H))
    (h3 : g⁻¹ * b * g ∈ Subgroup.closure ({c, a, b} : Set H))
    {d : H} (hd : d ∈ Subgroup.closure ({c, a, b} : Set H)) :
    g * d * g⁻¹ ∈ Subgroup.closure ({c, a, b} : Set H) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hle : Subgroup.closure ({c, a, b} : Set H) ≤
      (Subgroup.closure ({c, a, b} : Set H)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hx with rfl | rfl | rfl
    · simpa [hginv] using h1
    · simpa [hginv] using h2
    · simpa [hginv] using h3
  simpa [MulAut.conj_apply] using hle hd

theorem mem_closure_cab201_c : c ∈ Subgroup.closure ({c, a, b} : Set H) :=
  Subgroup.subset_closure (by simp)

theorem mem_closure_cab201_a : a ∈ Subgroup.closure ({c, a, b} : Set H) :=
  Subgroup.subset_closure (by simp)

theorem mem_closure_cab201_b : b ∈ Subgroup.closure ({c, a, b} : Set H) :=
  Subgroup.subset_closure (by simp)

theorem Rel201.conj_mem (h : Rel201 m c a b uv t u f) {g : H} (hg : g = uv ∨ g = t ∨ g = u ∨ g = f)
    {d : H} (hd : d ∈ Subgroup.closure ({c, a, b} : Set H)) :
    g * d * g⁻¹ ∈ Subgroup.closure ({c, a, b} : Set H) := by
  set K := Subgroup.closure ({c, a, b} : Set H)
  have hc : c ∈ K := mem_closure_cab201_c
  have ha : a ∈ K := mem_closure_cab201_a
  have hb : b ∈ K := mem_closure_cab201_b
  rcases hg with rfl | rfl | rfl | rfl
  · refine conj_mem_closure_cab201 h.uv_sq ?_ ?_ ?_ hd
    · rw [h.uv_c]
      exact K.mul_mem (K.mul_mem (K.zpow_mem hc _) (K.zpow_mem ha _)) (K.zpow_mem hb _)
    · rw [h.uv_a]
      exact K.mul_mem (K.mul_mem hc ha) (K.pow_mem hb _)
    · rw [h.uv_b]
      exact K.mul_mem (K.mul_mem hc (K.pow_mem ha _)) hb
  · refine conj_mem_closure_cab201 h.t_sq ?_ ?_ ?_ hd
    · rw [h.t_c]
      exact K.mul_mem hc (K.pow_mem ha _)
    · rw [h.t_a]
      exact K.zpow_mem ha _
    · rw [h.t_b]
      exact K.mul_mem (K.mul_mem (K.zpow_mem hc _) (K.zpow_mem ha _)) (K.zpow_mem hb _)
  · refine conj_mem_closure_cab201 h.u_sq ?_ ?_ ?_ hd
    · rw [h.u_c]
      exact hc
    · rw [h.u_a]
      exact hb
    · rw [h.u_b]
      exact ha
  · refine conj_mem_closure_cab201 h.f_sq ?_ ?_ ?_ hd
    · rw [h.f_c]
      exact K.inv_mem hc
    · rw [h.f_a]
      exact K.mul_mem (K.inv_mem ha) (K.pow_mem ha _)
    · rw [h.f_b]
      exact K.mul_mem (K.inv_mem hb) (K.pow_mem hb _)

theorem mul_f_eq201 (h : Rel201 m c a b uv t u f) {g k : H} (hk : f⁻¹ * g * f = k * g) :
    g * f = (f * k * f⁻¹) * f * g := by
  have : g * f = f * (f⁻¹ * g * f) := by group
  rw [this, hk]
  group

theorem Rel201.mul_mem_normalForm (h : Rel201 m c a b uv t u f) {g x : H}
    (hg : g = c ∨ g = a ∨ g = b ∨ g = uv ∨ g = t ∨ g = u ∨ g = f)
    (hx : x ∈ normalForm201 c a b uv t u f) : g * x ∈ normalForm201 c a b uv t u f := by
  set K := Subgroup.closure ({c, a, b} : Set H)
  obtain ⟨d, hd, δ, α, β, γ, rfl⟩ := hx
  have hcab : g = c ∨ g = a ∨ g = b → g * (d * f ^ (δ : ℕ) * word201 uv t u α β γ) ∈
      normalForm201 c a b uv t u f := by
    intro hg'
    have hgK : g ∈ K := by
      rcases hg' with rfl | rfl | rfl
      · exact mem_closure_cab201_c
      · exact mem_closure_cab201_a
      · exact mem_closure_cab201_b
    exact ⟨g * d, K.mul_mem hgK hd, δ, α, β, γ, by group⟩
  have hfK : ∀ {k : H}, k ∈ K → f * k * f⁻¹ ∈ K := fun hk =>
    h.conj_mem (Or.inr (Or.inr (Or.inr rfl))) hk
  have hfδ : ∀ {g k : H}, f⁻¹ * g * f = k * g → k ∈ K → ∀ δ : Fin 2,
      ∃ d' ∈ K, g * f ^ (δ : ℕ) = d' * f ^ (δ : ℕ) * g := by
    intro g k hk hkK δ
    fin_cases δ
    · exact ⟨1, K.one_mem, by simp⟩
    · refine ⟨f * k * f⁻¹, hfK hkK, ?_⟩
      simpa using mul_f_eq201 h hk
  have hD8 : ∀ {g k : H}, f⁻¹ * g * f = k * g → k ∈ K → (g = uv ∨ g = t ∨ g = u) →
      g * (d * f ^ (δ : ℕ) * word201 uv t u α β γ) ∈ normalForm201 c a b uv t u f := by
    intro g k hk hkK hg'
    obtain ⟨d', hd', hd'eq⟩ := hfδ hk hkK δ
    have hgdK : g * d * g⁻¹ ∈ K := h.conj_mem (by rcases hg' with h' | h' | h' <;> simp [h']) hd
    have key : g * (d * f ^ (δ : ℕ) * word201 uv t u α β γ) =
        (g * d * g⁻¹ * d') * f ^ (δ : ℕ) * (g * word201 uv t u α β γ) := by
      have : g * (d * f ^ (δ : ℕ) * word201 uv t u α β γ) =
          (g * d * g⁻¹) * (g * f ^ (δ : ℕ)) * word201 uv t u α β γ := by group
      rw [this, hd'eq]
      group
    rw [key]
    rcases hg' with rfl | rfl | rfl
    · exact ⟨_, K.mul_mem hgdK hd', δ, α + 1, β, γ, by rw [uv_mul_word201 h]⟩
    · exact ⟨_, K.mul_mem hgdK hd', δ, α, β + 1, γ, by rw [t_mul_word201 h]⟩
    · exact ⟨_, K.mul_mem hgdK hd', δ, α + β, β, γ + 1, by rw [u_mul_word201 h]⟩
  rcases hg with hg | hg | hg | hg | hg | hg | hg
  · exact hcab (Or.inl hg)
  · exact hcab (Or.inr (Or.inl hg))
  · exact hcab (Or.inr (Or.inr hg))
  · subst g
    refine hD8 h.f_uv ?_ (Or.inl rfl)
    exact K.pow_mem (K.mul_mem (K.mul_mem mem_closure_cab201_c mem_closure_cab201_a)
      mem_closure_cab201_b) _
  · subst g
    exact hD8 h.f_t (K.pow_mem (K.inv_mem mem_closure_cab201_a) _) (Or.inr (Or.inl rfl))
  · subst g
    exact hD8 (by rw [h.f_u, one_mul]) K.one_mem (Or.inr (Or.inr rfl))
  · subst g
    have hfdK : f * d * f⁻¹ ∈ K := hfK hd
    fin_cases δ
    · refine ⟨f * d * f⁻¹, hfdK, 1, α, β, γ, ?_⟩
      simp only [Fin.isValue, Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one]
      group
    · refine ⟨f * d * f⁻¹, hfdK, 0, α, β, γ, ?_⟩
      simp only [Fin.isValue, Fin.val_one, pow_one, Fin.val_zero, pow_zero, mul_one]
      calc f * (d * f * word201 uv t u α β γ) = f * d * f⁻¹ * (f * f) * word201 uv t u α β γ := by
            group
        _ = f * d * f⁻¹ * word201 uv t u α β γ := by rw [h.f_sq, mul_one]

theorem Rel201.mem_normalForm201 (h : Rel201 m c a b uv t u f)
    (hgen : Subgroup.closure ({c, a, b, uv, t, u, f} : Set H) = ⊤) (x : H) :
    x ∈ normalForm201 c a b uv t u f := by
  have hx : x ∈ Subgroup.closure ({c, a, b, uv, t, u, f} : Set H) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction_left with
  | one =>
    exact ⟨1, Subgroup.one_mem _, 0, 0, 0, 0, by simp [word201]⟩
  | mul_left g hg y _ hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    exact h.mul_mem_normalForm hg hy
  | inv_mul_cancel g hg y _ hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    set K := Subgroup.closure ({c, a, b} : Set H)
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨d, hd, δ, α, β, γ, rfl⟩ := hy
      exact ⟨g⁻¹ * d, K.mul_mem (K.inv_mem mem_closure_cab201_c) hd, δ, α, β, γ, by group⟩
    · obtain ⟨d, hd, δ, α, β, γ, rfl⟩ := hy
      exact ⟨g⁻¹ * d, K.mul_mem (K.inv_mem mem_closure_cab201_a) hd, δ, α, β, γ, by group⟩
    · obtain ⟨d, hd, δ, α, β, γ, rfl⟩ := hy
      exact ⟨g⁻¹ * d, K.mul_mem (K.inv_mem mem_closure_cab201_b) hd, δ, α, β, γ, by group⟩
    · rw [h.uv_inv]
      exact h.mul_mem_normalForm (by simp) hy
    · rw [h.t_inv]
      exact h.mul_mem_normalForm (by simp) hy
    · rw [h.u_inv]
      exact h.mul_mem_normalForm (by simp) hy
    · rw [h.f_inv]
      exact h.mul_mem_normalForm (by simp) hy

theorem card_le_of_rel201 (h : Rel201 m c a b uv t u f)
    (hgen : Subgroup.closure ({c, a, b, uv, t, u, f} : Set H) = ⊤) :
    Finite H ∧ Nat.card H ≤ 2 ^ (3 * m + 8) := by
  obtain ⟨hfin, hcard⟩ := card_closure_cab_le201 h.c_pow h.a_pow h.b_pow h.ca h.cb h.ab
  let Ψ : Subgroup.closure ({c, a, b} : Set H) × Fin 2 × Fin 2 × Fin 2 × Fin 2 → H :=
    fun p => (p.1 : H) * f ^ (p.2.1 : ℕ) * word201 uv t u p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨d, hd, δ, α, β, γ, rfl⟩ := h.mem_normalForm201 hgen x
    exact ⟨(⟨d, hd⟩, δ, α, β, γ), rfl⟩
  refine ⟨Finite.of_surjective Ψ hsurj, ?_⟩
  calc Nat.card H ≤ Nat.card (Subgroup.closure ({c, a, b} : Set H) × Fin 2 × Fin 2 × Fin 2 ×
        Fin 2) := Nat.card_le_card_of_surjective Ψ hsurj
    _ = Nat.card (Subgroup.closure ({c, a, b} : Set H)) * 16 := by
        simp only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
    _ ≤ 2 ^ (3 * m + 4) * 16 := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (3 * m + 8) := by ring

end NormalForm

inductive Gen201 : Type
  | c | a | b | uv | t | u | f
  deriving DecidableEq

@[expose] def rels201 (m : ℕ) : Set (FreeGroup Gen201) :=
  {r | ∃ p ∈ eqns201 m (FreeGroup.of Gen201.c) (FreeGroup.of Gen201.a) (FreeGroup.of Gen201.b)
    (FreeGroup.of Gen201.uv) (FreeGroup.of Gen201.t) (FreeGroup.of Gen201.u)
    (FreeGroup.of Gen201.f),
    r = p.1 * p.2⁻¹}

abbrev G201 (m : ℕ) : Type := PresentedGroup (rels201 m)

namespace G201

variable {m : ℕ}

theorem rel (m : ℕ) : Rel201 m (PresentedGroup.of (rels := rels201 m) Gen201.c)
    (PresentedGroup.of Gen201.a) (PresentedGroup.of Gen201.b) (PresentedGroup.of Gen201.uv)
    (PresentedGroup.of Gen201.t) (PresentedGroup.of Gen201.u) (PresentedGroup.of Gen201.f) := by
  change Rel201 m (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.c))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.a))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.b))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.uv))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.t))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.u))
    (PresentedGroup.mk (rels201 m) (FreeGroup.of Gen201.f))
  intro p hp
  rw [← eqns201_map, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨q, hq, rfl⟩

theorem closure_gens (m : ℕ) : Subgroup.closure ({PresentedGroup.of (rels := rels201 m) Gen201.c,
    PresentedGroup.of Gen201.a, PresentedGroup.of Gen201.b, PresentedGroup.of Gen201.uv,
    PresentedGroup.of Gen201.t, PresentedGroup.of Gen201.u, PresentedGroup.of Gen201.f} :
      Set (G201 m)) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of]
  apply Subgroup.closure_mono
  rintro _ ⟨x, rfl⟩
  cases x <;> simp

theorem card_le (m : ℕ) : Finite (G201 m) ∧ Nat.card (G201 m) ≤ 2 ^ (3 * m + 8) :=
  card_le_of_rel201 (rel m) (closure_gens m)

@[expose] def genMap {H : Type*} (c a b uv t u f : H) : Gen201 → H
  | .c => c
  | .a => a
  | .b => b
  | .uv => uv
  | .t => t
  | .u => u
  | .f => f

@[expose] def lift {H : Type*} [Group H] {c a b uv t u f : H} (h : Rel201 m c a b uv t u f) :
    G201 m →* H :=
  PresentedGroup.toGroup (f := genMap c a b uv t u f) (by
    rintro r ⟨p, hp, rfl⟩
    rw [map_mul, map_inv, mul_inv_eq_one]
    have hmap := eqns201_map (FreeGroup.lift (genMap c a b uv t u f)) m (FreeGroup.of Gen201.c)
      (FreeGroup.of Gen201.a) (FreeGroup.of Gen201.b) (FreeGroup.of Gen201.uv)
      (FreeGroup.of Gen201.t) (FreeGroup.of Gen201.u) (FreeGroup.of Gen201.f)
    simp only [FreeGroup.lift_apply_of, genMap] at hmap
    exact h (FreeGroup.lift (genMap c a b uv t u f) p.1, FreeGroup.lift (genMap c a b uv t u f) p.2)
      (by rw [← hmap, List.mem_map]; exact ⟨p, hp, rfl⟩))

theorem lift_of {H : Type*} [Group H] {c a b uv t u f : H} (h : Rel201 m c a b uv t u f) :
    lift h (PresentedGroup.of Gen201.c) = c ∧ lift h (PresentedGroup.of Gen201.a) = a ∧
      lift h (PresentedGroup.of Gen201.b) = b ∧ lift h (PresentedGroup.of Gen201.uv) = uv ∧
      lift h (PresentedGroup.of Gen201.t) = t ∧ lift h (PresentedGroup.of Gen201.u) = u ∧
      lift h (PresentedGroup.of Gen201.f) = f := by
  simp [lift, PresentedGroup.toGroup.of, genMap]

theorem lift_surjective {H : Type*} [Group H] {c a b uv t u f : H} (h : Rel201 m c a b uv t u f)
    (hgen : Subgroup.closure ({c, a, b, uv, t, u, f} : Set H) = ⊤) :
    Function.Surjective (lift h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := lift_of h
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, h1⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h3⟩
  · exact ⟨_, h4⟩
  · exact ⟨_, h5⟩
  · exact ⟨_, h6⟩
  · exact ⟨_, h7⟩

end G201

end CFSG.CGT.Stroth77
