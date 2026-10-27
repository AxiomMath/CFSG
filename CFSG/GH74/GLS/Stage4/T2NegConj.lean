module

public import CFSG.GH74.GLS.Stage4.T2NegDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

section TwoGroup

theorem isPGroup_closure_zuw {G : Type} [Group G] {z u w₁ w₂ : G}
    (hzz : z * z = 1) (huu : u * u = 1) (hzu : z * u = u * z)
    (hw₁z : w₁ * z = z * w₁) (hw₂z : w₂ * z = z * w₂)
    (hw₁sq : w₁ * w₁ = z) (hw₂sq : w₂ * w₂ = z)
    (hw₁u : w₁ * u * w₁⁻¹ = u * z) (hw₂u : w₂ * u * w₂⁻¹ = u * z) (hw₁w₂ : w₁ * w₂ = w₂ * w₁) :
    IsPGroup 2 ↥(Subgroup.closure ({z, u, w₁, w₂} : Set G)) := by
  have hw₁u' : w₁ * u = u * w₁ * z := by
    have h1 := hw₁u
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [h1, mul_assoc u z w₁, ← hw₁z, ← mul_assoc]
  have hw₂u' : w₂ * u = u * w₂ * z := by
    have h1 := hw₂u
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [h1, mul_assoc u z w₂, ← hw₂z, ← mul_assoc]
  have huw₁ : u * w₁ = w₁ * u * z := by
    rw [hw₁u', mul_assoc (u * w₁) z z, hzz, mul_one]
  have huw₂ : u * w₂ = w₂ * u * z := by
    rw [hw₂u', mul_assoc (u * w₂) z z, hzz, mul_one]
  have hzc : ∀ x ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G), x * z = z * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : x = z ∨ x = u ∨ x = w₁ ∨ x = w₂ := hx
      rcases hx' with h | h | h | h <;> rw [h]
      · exact hzu.symm
      · exact hw₁z
      · exact hw₂z
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ih => exact (Commute.inv_left (show Commute x z from ih)).eq
  have hNc : ∀ a ∈ Subgroup.zpowers z, ∀ y ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G),
      a * y = y * a := by
    intro a ha y hy
    have h1 : z ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hzc g hy
    have h2 : Subgroup.zpowers z ≤ Subgroup.centralizer ({y} : Set G) :=
      (Subgroup.zpowers_le).2 h1
    exact ((Subgroup.mem_centralizer_iff.1 (h2 ha)) y rfl).symm
  have hNsq : ∀ a ∈ Subgroup.zpowers z, a * a = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hzz, one_zpow]
  have hcomm : ∀ x ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G),
      ∀ y ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G),
      ∃ a ∈ Subgroup.zpowers z, x * y = y * x * a := by
    intro x hx y hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy =>
      have hz : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      have hx' : x = z ∨ x = u ∨ x = w₁ ∨ x = w₂ := hx
      have hy' : y = z ∨ y = u ∨ y = w₁ ∨ y = w₂ := hy
      rcases hx' with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h']
      · exact ⟨1, one_mem _, by simp⟩
      · exact ⟨1, one_mem _, by simpa using hzu⟩
      · exact ⟨1, one_mem _, by simpa using hw₁z.symm⟩
      · exact ⟨1, one_mem _, by simpa using hw₂z.symm⟩
      · exact ⟨1, one_mem _, by simpa using hzu.symm⟩
      · exact ⟨1, one_mem _, by simp⟩
      · exact ⟨z, hz, huw₁⟩
      · exact ⟨z, hz, huw₂⟩
      · exact ⟨1, one_mem _, by simpa using hw₁z⟩
      · exact ⟨z, hz, hw₁u'⟩
      · exact ⟨1, one_mem _, by simp⟩
      · exact ⟨1, one_mem _, by simpa using hw₁w₂⟩
      · exact ⟨1, one_mem _, by simpa using hw₂z⟩
      · exact ⟨z, hz, hw₂u'⟩
      · exact ⟨1, one_mem _, by simpa using hw₁w₂.symm⟩
      · exact ⟨1, one_mem _, by simp⟩
    | one_left x hx => exact ⟨1, one_mem _, by simp⟩
    | one_right x hx => exact ⟨1, one_mem _, by simp⟩
    | mul_left x y w hx hy hw ihx ihy =>
      obtain ⟨a, ha, hxa⟩ := ihx
      obtain ⟨b, hb, hyb⟩ := ihy
      refine ⟨a * b, mul_mem ha hb, ?_⟩
      calc x * y * w = x * (y * w) := mul_assoc _ _ _
        _ = x * (w * y * b) := by rw [hyb]
        _ = (x * w) * y * b := by simp only [mul_assoc]
        _ = w * x * a * y * b := by rw [hxa]
        _ = w * x * (a * y) * b := by simp only [mul_assoc]
        _ = w * x * (y * a) * b := by rw [hNc a ha y hy]
        _ = w * (x * y) * (a * b) := by simp only [mul_assoc]
    | mul_right y w x hy hw hx ihy ihw =>
      obtain ⟨a, ha, hya⟩ := ihy
      obtain ⟨b, hb, hwb⟩ := ihw
      refine ⟨b * a, mul_mem hb ha, ?_⟩
      calc x * (y * w) = (x * y) * w := (mul_assoc _ _ _).symm
        _ = y * x * a * w := by rw [hya]
        _ = y * x * (a * w) := by simp only [mul_assoc]
        _ = y * x * (w * a) := by rw [hNc a ha w hw]
        _ = y * (x * w) * a := by simp only [mul_assoc]
        _ = y * (w * x * b) * a := by rw [hwb]
        _ = (y * w) * x * (b * a) := by simp only [mul_assoc]
    | inv_left x y hx hy ih =>
      obtain ⟨a, ha, hxa⟩ := ih
      refine ⟨a⁻¹, inv_mem ha, ?_⟩
      have hyx : y * x = x * y * a⁻¹ := eq_mul_inv_of_mul_eq hxa.symm
      have hax : a⁻¹ * x⁻¹ = x⁻¹ * a⁻¹ :=
        (Commute.inv_inv (show Commute a x from hNc a ha x hx)).eq
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y * a⁻¹) * x⁻¹ := by rw [hyx]
        _ = y * (a⁻¹ * x⁻¹) := by group
        _ = y * (x⁻¹ * a⁻¹) := by rw [hax]
        _ = y * x⁻¹ * a⁻¹ := by group
    | inv_right x y hx hy ih =>
      obtain ⟨a, ha, hxa⟩ := ih
      refine ⟨a⁻¹, inv_mem ha, ?_⟩
      have hyx : y * x = x * y * a⁻¹ := eq_mul_inv_of_mul_eq hxa.symm
      have hay : y * a⁻¹ = a⁻¹ * y :=
        (Commute.inv_left (show Commute a y from hNc a ha y hy)).eq.symm
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y * a⁻¹) * y⁻¹ := by rw [hyx]
        _ = y⁻¹ * x * (y * a⁻¹) * y⁻¹ := by group
        _ = y⁻¹ * x * (a⁻¹ * y) * y⁻¹ := by rw [hay]
        _ = y⁻¹ * x * a⁻¹ := by group
  have hsq : ∀ x ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G),
      x * x ∈ Subgroup.zpowers z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : x = z ∨ x = u ∨ x = w₁ ∨ x = w₂ := hx
      rcases hx' with h | h | h | h <;> rw [h]
      · rw [hzz]; exact one_mem _
      · rw [huu]; exact one_mem _
      · rw [hw₁sq]; exact Subgroup.mem_zpowers z
      · rw [hw₂sq]; exact Subgroup.mem_zpowers z
    | one => simp
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha, hyx⟩ := hcomm y hy x hx
      have hax : a * y = y * a := hNc a ha y hy
      have h1 : x * y * (x * y) = (x * x) * (y * y) * a := by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y * a) * y := by rw [hyx]
          _ = x * x * y * (a * y) := by group
          _ = x * x * y * (y * a) := by rw [hax]
          _ = (x * x) * (y * y) * a := by group
      rw [h1]
      exact mul_mem (mul_mem ihx ihy) ha
    | inv x _ ih =>
      rw [← mul_inv_rev]
      exact inv_mem ih
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  have h1 := hNsq _ (hsq g.1 g.2)
  show (g : G) ^ 2 ^ 2 = 1
  calc (g : G) ^ 2 ^ 2 = ((g : G) * g) * ((g : G) * g) := by
        rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, sq, sq]
    _ = 1 := h1

end TwoGroup

section Conj

variable {G : Type} [Group G]

theorem t2NegConj_apply (c y : G) : (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := rfl

theorem t2NegConj_mem_map_iff (H : Subgroup G) (c x : G) :
    x ∈ H.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * ((MulAut.conj c).toMonoidHom y) * c = y := by
      rw [t2NegConj_apply]
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨c⁻¹ * x * c, hx, ?_⟩
    rw [t2NegConj_apply]
    group

theorem t2NegConj_injective (c : G) : Function.Injective (MulAut.conj c).toMonoidHom :=
  fun a b hab => by
    rw [t2NegConj_apply, t2NegConj_apply] at hab
    simpa using hab

theorem t2NegConj_map_inf (H K : Subgroup G) (c : G) (hK : ∀ x, c⁻¹ * x * c ∈ K ↔ x ∈ K) :
    H.map (MulAut.conj c).toMonoidHom ⊓ K = (H ⊓ K).map (MulAut.conj c).toMonoidHom := by
  ext x
  rw [Subgroup.mem_inf, t2NegConj_mem_map_iff, t2NegConj_mem_map_iff, Subgroup.mem_inf, hK x]

theorem t2NegConj_mem_sup {K₁ K₂ : Subgroup G} {g : G}
    (h₁ : ∀ x ∈ K₁, g * x * g⁻¹ ∈ K₁) (h₂ : ∀ x ∈ K₂, g * x * g⁻¹ ∈ K₂) :
    ∀ x ∈ K₁ ⊔ K₂, g * x * g⁻¹ ∈ K₁ ⊔ K₂ := by
  have h : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_sup_left (h₁ x hx)))
      (fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_sup_right (h₂ x hx)))
  intro x hx
  exact h hx

end Conj

theorem Ch6NegCfg.conj {G : Type} [Group G] {C₁ : Subgroup G} {q : ℕ} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ c : G} (h : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) (hc : c ∈ C₁) :
    Ch6NegCfg C₁ q z (c * u * c⁻¹) K₁ K₂ (H.map (MulAut.conj c).toMonoidHom) (c * w₁ * c⁻¹)
      (c * w₂ * c⁻¹) := by
  have hci : c⁻¹ ∈ C₁ := inv_mem hc
  have hcz : c * z = z * c := h.C_comm c hc
  have hczc : c * z * c⁻¹ = z := by rw [hcz]; group
  have hczi : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := mul_assoc _ _ _
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  have hK₁ : ∀ x, c⁻¹ * x * c ∈ K₁ ↔ x ∈ K₁ := by
    intro x
    constructor
    · intro hx
      have := h.C_norm₁ c hc _ hx
      rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
    · intro hx
      have := h.C_norm₁ c⁻¹ hci x hx
      rwa [inv_inv] at this
  have hK₂ : ∀ x, c⁻¹ * x * c ∈ K₂ ↔ x ∈ K₂ := by
    intro x
    constructor
    · intro hx
      have := h.C_norm₂ c hc _ hx
      rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
    · intro hx
      have := h.C_norm₂ c⁻¹ hci x hx
      rwa [inv_inv] at this
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := t2NegConj_injective c
  have hI₁ := t2NegConj_map_inf H K₁ c hK₁
  have hI₂ := t2NegConj_map_inf H K₂ c hK₂
  have hsup' : ∀ x ∈ K₁ ⊔ K₂, c⁻¹ * x * c ∈ K₁ ⊔ K₂ := by
    intro x hx
    have := t2NegConj_mem_sup (K₁ := K₁) (K₂ := K₂) (g := c⁻¹) (h.C_norm₁ c⁻¹ hci)
      (h.C_norm₂ c⁻¹ hci) x hx
    rwa [inv_inv] at this
  refine
    { toT2Four1 :=
        { zz := h.zz
          z_ne := h.z_ne
          uu := ?_
          u_ne := ?_
          zu_ne := ?_
          zu_comm := ?_
          K_comm := h.K_comm
          K_inter := h.K_inter
          C_comm := h.C_comm
          K_le_C := h.K_le_C
          C_norm₁ := h.C_norm₁
          C_norm₂ := h.C_norm₂
          C_idx := h.C_idx
          H_comm := ?_
          z_mem_H := ?_
          u_mem_H := ?_
          H_le_C := ?_
          H_not_le_K := ?_
          H₁_iff := ?_
          H₂_iff := ?_
          w₁_mem := h.C_norm₁ c hc w₁ h.w₁_mem
          w₂_mem := h.C_norm₂ c hc w₂ h.w₂_mem
          w₁_sq := ?_
          w₂_sq := ?_
          w₁_u := ?_
          w₂_u := ?_
          w₁_normH := ?_
          w₂_normH := ?_
          w₀_inv := ?_
          w₀_not_mem := ?_ }
      H₁_cyc := ?_
      H₂_cyc := ?_
      H₁_card := ?_
      H₂_card := ?_
      H_idx := ?_
      H₁_cent := ?_
      H₂_cent := ?_ }
  ·
    calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [h.uu]; group
  ·
    intro h1
    apply h.u_ne
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  ·
    intro h1
    apply h.zu_ne
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [hczc, ← h1]
      _ = u := by group
  ·
    calc z * (c * u * c⁻¹) = (c * z * c⁻¹) * (c * u * c⁻¹) := by rw [hczc]
      _ = c * (z * u) * c⁻¹ := by group
      _ = c * (u * z) * c⁻¹ := by rw [h.zu_comm]
      _ = (c * u * c⁻¹) * (c * z * c⁻¹) := by group
      _ = (c * u * c⁻¹) * z := by rw [hczc]
  ·
    intro x hx y hy
    rw [t2NegConj_mem_map_iff] at hx hy
    have hxy := h.H_comm _ hx _ hy
    calc x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by rw [hxy]
      _ = y * x := by group
  ·
    rw [t2NegConj_mem_map_iff, hczi]
    exact h.z_mem_H
  ·
    rw [t2NegConj_mem_map_iff, show c⁻¹ * (c * u * c⁻¹) * c = u by group]
    exact h.u_mem_H
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff] at hx
    have h1 : c * (c⁻¹ * x * c) * c⁻¹ ∈ C₁ := mul_mem (mul_mem hc (h.H_le_C hx)) hci
    rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at h1
  ·
    intro hle
    apply h.H_not_le_K
    intro a ha
    have h1 : c * a * c⁻¹ ∈ H.map (MulAut.conj c).toMonoidHom :=
      (t2NegConj_mem_map_iff H c _).2 (by rw [show c⁻¹ * (c * a * c⁻¹) * c = a by group]; exact ha)
    have h2 := hsup' _ (hle h1)
    rwa [show c⁻¹ * (c * a * c⁻¹) * c = a by group] at h2
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff, h.H₁_iff _ ((hK₁ x).2 hx)]
    constructor
    · intro e
      calc x * (c * u * c⁻¹) = c * ((c⁻¹ * x * c) * u) * c⁻¹ := by group
        _ = c * (u * (c⁻¹ * x * c)) * c⁻¹ := by rw [e]
        _ = (c * u * c⁻¹) * x := by group
    · intro e
      calc (c⁻¹ * x * c) * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [e]
        _ = u * (c⁻¹ * x * c) := by group
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff, h.H₂_iff _ ((hK₂ x).2 hx)]
    constructor
    · intro e
      calc x * (c * u * c⁻¹) = c * ((c⁻¹ * x * c) * u) * c⁻¹ := by group
        _ = c * (u * (c⁻¹ * x * c)) * c⁻¹ := by rw [e]
        _ = (c * u * c⁻¹) * x := by group
    · intro e
      calc (c⁻¹ * x * c) * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [e]
        _ = u * (c⁻¹ * x * c) := by group
  ·
    calc c * w₁ * c⁻¹ * (c * w₁ * c⁻¹) = c * (w₁ * w₁) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [h.w₁_sq]
      _ = z := hczc
  ·
    calc c * w₂ * c⁻¹ * (c * w₂ * c⁻¹) = c * (w₂ * w₂) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [h.w₂_sq]
      _ = z := hczc
  ·
    calc c * w₁ * c⁻¹ * (c * u * c⁻¹) * (c * w₁ * c⁻¹)⁻¹ = c * (w₁ * u * w₁⁻¹) * c⁻¹ := by group
      _ = c * (u * z) * c⁻¹ := by rw [h.w₁_u]
      _ = (c * u * c⁻¹) * (c * z * c⁻¹) := by group
      _ = (c * u * c⁻¹) * z := by rw [hczc]
  ·
    calc c * w₂ * c⁻¹ * (c * u * c⁻¹) * (c * w₂ * c⁻¹)⁻¹ = c * (w₂ * u * w₂⁻¹) * c⁻¹ := by group
      _ = c * (u * z) * c⁻¹ := by rw [h.w₂_u]
      _ = (c * u * c⁻¹) * (c * z * c⁻¹) := by group
      _ = (c * u * c⁻¹) * z := by rw [hczc]
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff] at hx ⊢
    have h1 := h.w₁_normH _ hx
    rwa [show w₁ * (c⁻¹ * x * c) * w₁⁻¹ =
      c⁻¹ * (c * w₁ * c⁻¹ * x * (c * w₁ * c⁻¹)⁻¹) * c by group] at h1
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff] at hx ⊢
    have h1 := h.w₂_normH _ hx
    rwa [show w₂ * (c⁻¹ * x * c) * w₂⁻¹ =
      c⁻¹ * (c * w₂ * c⁻¹ * x * (c * w₂ * c⁻¹)⁻¹) * c by group] at h1
  ·
    intro x hx
    rw [t2NegConj_mem_map_iff] at hx
    have h1 := h.w₀_inv _ hx
    calc c * w₁ * c⁻¹ * (c * w₂ * c⁻¹) * x * (c * w₁ * c⁻¹ * (c * w₂ * c⁻¹))⁻¹
        = c * ((w₁ * w₂) * (c⁻¹ * x * c) * (w₁ * w₂)⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * x * c)⁻¹ * c⁻¹ := by rw [h1]
      _ = x⁻¹ := by group
  ·
    intro hmem
    rw [t2NegConj_mem_map_iff] at hmem
    apply h.w₀_not_mem
    rwa [show c⁻¹ * (c * w₁ * c⁻¹ * (c * w₂ * c⁻¹)) * c = w₁ * w₂ by group] at hmem
  ·
    rw [hI₁]
    exact (Subgroup.equivMapOfInjective (H ⊓ K₁) _ hinj).isCyclic.1 h.H₁_cyc
  ·
    rw [hI₂]
    exact (Subgroup.equivMapOfInjective (H ⊓ K₂) _ hinj).isCyclic.1 h.H₂_cyc
  ·
    rw [hI₁, ← h.H₁_card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (H ⊓ K₁) _ hinj).toEquiv).symm
  ·
    rw [hI₂, ← h.H₂_card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (H ⊓ K₂) _ hinj).toEquiv).symm
  ·
    rw [hI₁, hI₂, ← Subgroup.map_sup, Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact h.H_idx
  ·
    intro y hy hyy d hd hdy
    rw [Subgroup.mem_inf, t2NegConj_mem_map_iff] at hy
    rw [t2NegConj_mem_map_iff]
    refine h.H₁_cent (c⁻¹ * y * c) (Subgroup.mem_inf.2 ⟨hy.1, (hK₁ y).2 hy.2⟩) ?_ (c⁻¹ * d * c)
      ((hK₁ d).2 hd) ?_
    · intro h1
      apply hyy
      calc y * y = c * ((c⁻¹ * y * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · calc c⁻¹ * d * c * (c⁻¹ * y * c) = c⁻¹ * (d * y) * c := by group
        _ = c⁻¹ * (y * d) * c := by rw [hdy]
        _ = c⁻¹ * y * c * (c⁻¹ * d * c) := by group
  ·
    intro y hy hyy d hd hdy
    rw [Subgroup.mem_inf, t2NegConj_mem_map_iff] at hy
    rw [t2NegConj_mem_map_iff]
    refine h.H₂_cent (c⁻¹ * y * c) (Subgroup.mem_inf.2 ⟨hy.1, (hK₂ y).2 hy.2⟩) ?_ (c⁻¹ * d * c)
      ((hK₂ d).2 hd) ?_
    · intro h1
      apply hyy
      calc y * y = c * ((c⁻¹ * y * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · calc c⁻¹ * d * c * (c⁻¹ * y * c) = c⁻¹ * (d * y) * c := by group
        _ = c⁻¹ * (y * d) * c := by rw [hdy]
        _ = c⁻¹ * y * c * (c⁻¹ * d * c) := by group


section Sylow

open scoped Pointwise

theorem exists_cfg_in_sylow {G : Type} [Group G] [Finite G] {C₁ S : Subgroup G} (hSC : S ≤ C₁)
    (hS2 : IsPGroup 2 ↥S) (hSidx : ¬ 2 ∣ S.index) {q : ℕ} {z u : G} {K₁ K₂ H : Subgroup G}
    {w₁ w₂ : G} (h : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) :
    ∃ (u' : G) (H' : Subgroup G) (w₁' w₂' : G), Ch6NegCfg C₁ q z u' K₁ K₂ H' w₁' w₂' ∧
      u' ∈ S ∧ w₁' ∈ S ∧ w₂' ∈ S := by
  have hz_C : z ∈ C₁ := h.H_le_C h.z_mem_H
  have hu_C : u ∈ C₁ := h.H_le_C h.u_mem_H
  have hw₁_C : w₁ ∈ C₁ := h.K_le_C (Subgroup.mem_sup_left h.w₁_mem)
  have hw₂_C : w₂ ∈ C₁ := h.K_le_C (Subgroup.mem_sup_right h.w₂_mem)
  have hPC : Subgroup.closure ({z, u, w₁, w₂} : Set G) ≤ C₁ := by
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : x = z ∨ x = u ∨ x = w₁ ∨ x = w₂ := hx
    rcases hx' with h' | h' | h' | h' <;> rw [h'] <;> assumption
  have hP2 : IsPGroup 2 ↥(Subgroup.closure ({z, u, w₁, w₂} : Set G)) :=
    isPGroup_closure_zuw h.zz h.uu h.zu_comm (h.C_comm w₁ hw₁_C) (h.C_comm w₂ hw₂_C)
      h.w₁_sq h.w₂_sq h.w₁_u h.w₂_u (h.K_comm w₁ h.w₁_mem w₂ h.w₂_mem)
  have hP2' : IsPGroup 2 ↥((Subgroup.closure ({z, u, w₁, w₂} : Set G)).subgroupOf C₁) :=
    hP2.comap_subtype
  obtain ⟨Q, hPQ⟩ := hP2'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥C₁) Q ((hS2.toSylow hSidx).subtype hSC)
  have key : ∀ x ∈ Subgroup.closure ({z, u, w₁, w₂} : Set G), (g : G) * x * (g : G)⁻¹ ∈ S := by
    intro x hx
    have hxQ : (⟨x, hPC hx⟩ : ↥C₁) ∈ (Q : Subgroup ↥C₁) :=
      hPQ (Subgroup.mem_subgroupOf.2 hx)
    have h1 := Subgroup.smul_mem_pointwise_smul (⟨x, hPC hx⟩ : ↥C₁) (MulAut.conj g)
      (Q : Subgroup ↥C₁) hxQ
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  exact ⟨(g : G) * u * (g : G)⁻¹, H.map (MulAut.conj (g : G)).toMonoidHom,
    (g : G) * w₁ * (g : G)⁻¹, (g : G) * w₂ * (g : G)⁻¹, h.conj g.2,
    key u (Subgroup.subset_closure (by simp)), key w₁ (Subgroup.subset_closure (by simp)),
    key w₂ (Subgroup.subset_closure (by simp))⟩

end Sylow

end CFSG.GH74.GLS.Stage4.Rest
