module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.AltStdSec.Wreath

open Subgroup

variable {G : Type} [Group G]

structure WConfig (H : Subgroup G) (z : G) : Prop where
  sq : z * z = 1
  comm : ∀ a ∈ H, ∀ b ∈ H, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a
  inf : ∀ a ∈ H, ∀ b ∈ H, a = z * b * z⁻¹ → a = 1

variable {H : Subgroup G} {z : G}

@[expose] def Phi (z : G) (a b : G) : G := a * (z * b * z⁻¹)

theorem WConfig.Phi_mul (c : WConfig H z) {a b a' b' : G} (ha' : a' ∈ H) (hb : b ∈ H) :
    Phi z a b * Phi z a' b' = Phi z (a * a') (b * b') := by
  unfold Phi
  have h := c.comm a' ha' b hb
  calc a * (z * b * z⁻¹) * (a' * (z * b' * z⁻¹))
      = a * ((z * b * z⁻¹) * a') * (z * b' * z⁻¹) := by group
    _ = a * (a' * (z * b * z⁻¹)) * (z * b' * z⁻¹) := by rw [← h]
    _ = a * a' * (z * (b * b') * z⁻¹) := by group

theorem WConfig.Phi_inv (c : WConfig H z) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    (Phi z a b)⁻¹ = Phi z a⁻¹ b⁻¹ := by
  unfold Phi
  have h := c.comm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
  calc (a * (z * b * z⁻¹))⁻¹ = (z * b⁻¹ * z⁻¹) * a⁻¹ := by group
    _ = a⁻¹ * (z * b⁻¹ * z⁻¹) := h.symm

theorem WConfig.Phi_eq_one (c : WConfig H z) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (h : Phi z a b = 1) : a = 1 ∧ b = 1 := by
  unfold Phi at h
  have h1 : a = z * b⁻¹ * z⁻¹ := by
    have := eq_inv_of_mul_eq_one_left h
    rw [this]; group
  have ha1 : a = 1 := c.inf a ha b⁻¹ (inv_mem hb) h1
  refine ⟨ha1, ?_⟩
  rw [ha1, one_mul] at h
  have h2 : z * b * z⁻¹ = 1 := h
  have h3 : b = z⁻¹ * 1 * z := by
    calc b = z⁻¹ * (z * b * z⁻¹) * z := by group
      _ = z⁻¹ * 1 * z := by rw [h2]
  simpa using h3

theorem WConfig.Phi_inj (c : WConfig H z) {a b a' b' : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha' : a' ∈ H) (hb' : b' ∈ H) (h : Phi z a b = Phi z a' b') : a = a' ∧ b = b' := by
  have h1 : Phi z (a'⁻¹ * a) (b'⁻¹ * b) = 1 := by
    have h2 := c.Phi_mul (a := a'⁻¹) (b := b'⁻¹) (a' := a) (b' := b) ha (inv_mem hb')
    rw [← h2, ← c.Phi_inv ha' hb', h]
    exact inv_mul_cancel _
  obtain ⟨h3, h4⟩ := c.Phi_eq_one (mul_mem (inv_mem ha') ha) (mul_mem (inv_mem hb') hb) h1
  exact ⟨(inv_mul_eq_one.1 h3).symm, (inv_mul_eq_one.1 h4).symm⟩

theorem WConfig.Phi_pow (c : WConfig H z) {a : G} (ha : a ∈ H) (m : ℕ) :
    (Phi z a a) ^ m = Phi z (a ^ m) (a ^ m) := by
  induction m with
  | zero => simp [Phi]
  | succ m ih =>
    rw [pow_succ, ih, c.Phi_mul ha (pow_mem ha m), pow_succ]

theorem WConfig.z_Phi (c : WConfig H z) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    z * Phi z a b * z⁻¹ = Phi z b a := by
  unfold Phi
  have h := c.comm b hb a ha
  have h2 := c.sq
  calc z * (a * (z * b * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * ((z * z) * b * (z * z)⁻¹) := by group
    _ = (z * a * z⁻¹) * b := by rw [h2]; group
    _ = b * (z * a * z⁻¹) := h.symm

@[expose] def prodSub (c : WConfig H z) (T₁ : Subgroup G) (hT : T₁ ≤ H) : Subgroup G where
  carrier := {x | ∃ a ∈ T₁, ∃ b ∈ T₁, x = Phi z a b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', c.Phi_mul (hT ha') (hT hb)⟩
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp [Phi]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, c.Phi_inv (hT ha) (hT hb)⟩

theorem WConfig.z_mem_prodSub (c : WConfig H z) {T₁ : Subgroup G} (hT : T₁ ≤ H) {x : G}
    (hx : x ∈ prodSub c T₁ hT) : z * x * z⁻¹ ∈ prodSub c T₁ hT := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨b, hb, a, ha, c.z_Phi (hT ha) (hT hb)⟩

theorem WConfig.isPGroup_prodSub (c : WConfig H z) {T₁ : Subgroup G} (hT : T₁ ≤ H)
    (h2 : IsPGroup 2 T₁) : IsPGroup 2 (prodSub c T₁ hT) := by
  rintro ⟨x, a, ha, b, hb, rfl⟩
  obtain ⟨i, hi⟩ := h2 ⟨a, ha⟩
  obtain ⟨j, hj⟩ := h2 ⟨b, hb⟩
  have hi' : a ^ 2 ^ i = 1 := congrArg Subtype.val hi
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  refine ⟨max i j, Subtype.ext ?_⟩
  have ha' : a ^ 2 ^ (max i j) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_pow_eq_one hi').trans (pow_dvd_pow 2 (le_max_left i j))
  have hb' : b ^ 2 ^ (max i j) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_pow_eq_one hj').trans (pow_dvd_pow 2 (le_max_right i j))
  have hcomm : Commute a (z * b * z⁻¹) := c.comm a (hT ha) b (hT hb)
  show (Phi z a b) ^ 2 ^ (max i j) = 1
  unfold Phi
  rw [hcomm.mul_pow, conj_pow, ha', hb']
  simp

@[expose] def diagPre (c : WConfig H z) (P : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ H ∧ Phi z a a ∈ P}
  mul_mem' := by
    rintro a a' ⟨ha, hPa⟩ ⟨ha', hPa'⟩
    exact ⟨mul_mem ha ha', by rw [← c.Phi_mul ha' ha]; exact mul_mem hPa hPa'⟩
  one_mem' := ⟨one_mem _, by simp [Phi]⟩
  inv_mem' := by
    rintro a ⟨ha, hPa⟩
    exact ⟨inv_mem ha, by rw [← c.Phi_inv ha ha]; exact inv_mem hPa⟩

theorem diagPre_le (c : WConfig H z) (P : Subgroup G) : diagPre c P ≤ H := fun _ ha => ha.1

theorem WConfig.isPGroup_diagPre (c : WConfig H z) {P : Subgroup G} (hP : IsPGroup 2 P) :
    IsPGroup 2 (diagPre c P) := by
  rintro ⟨a, haH, haP⟩
  obtain ⟨k, hk⟩ := hP ⟨Phi z a a, haP⟩
  have h1 : (Phi z a a) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [c.Phi_pow haH] at h1
  have h2 := (c.Phi_eq_one (pow_mem haH _) (pow_mem haH _) h1).1
  exact ⟨k, Subtype.ext h2⟩

@[expose] def Ssub (z : G) (hz : z * z = 1) (T : Subgroup G) (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) :
    Subgroup G where
  carrier := {x | ∃ t ∈ T, x = t ∨ x = t * z}
  mul_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨t', ht', hy⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨t * t', mul_mem ht ht', Or.inl (by rw [hx, hy])⟩
    · exact ⟨t * t', mul_mem ht ht', Or.inr (by rw [hx, hy]; group)⟩
    · exact ⟨t * (z * t' * z⁻¹), mul_mem ht (hT t' ht'), Or.inr (by rw [hx, hy]; group)⟩
    · refine ⟨t * (z * t' * z⁻¹), mul_mem ht (hT t' ht'), Or.inl ?_⟩
      rw [hx, hy]
      calc t * z * (t' * z) = t * (z * t' * z⁻¹) * (z * z) := by group
        _ = t * (z * t' * z⁻¹) := by rw [hz, mul_one]
  one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
  inv_mem' := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    rintro x ⟨t, ht, hx⟩
    rcases hx with hx | hx
    · exact ⟨t⁻¹, inv_mem ht, Or.inl (by rw [hx])⟩
    · refine ⟨z * t⁻¹ * z⁻¹, hT _ (inv_mem ht), Or.inr ?_⟩
      rw [hx]
      calc (t * z)⁻¹ = z⁻¹ * t⁻¹ := by group
        _ = z * t⁻¹ := by rw [hzi]
        _ = (z * t⁻¹ * z⁻¹) * z := by group

theorem le_Ssub (z : G) (hz : z * z = 1) (T : Subgroup G) (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) :
    T ≤ Ssub z hz T hT := fun t ht => ⟨t, ht, Or.inl rfl⟩

theorem z_mem_Ssub (z : G) (hz : z * z = 1) (T : Subgroup G) (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) :
    z ∈ Ssub z hz T hT := ⟨1, one_mem _, Or.inr (by simp)⟩

theorem Ssub_eq_sup (z : G) (hz : z * z = 1) (T : Subgroup G) (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) :
    Ssub z hz T hT = T ⊔ zpowers z := by
  refine le_antisymm ?_ (sup_le (le_Ssub z hz T hT) (zpowers_le.2 (z_mem_Ssub z hz T hT)))
  rintro x ⟨t, ht, hx | hx⟩
  · rw [hx]; exact mem_sup_left ht
  · rw [hx]; exact mul_mem (mem_sup_left ht) (mem_sup_right (mem_zpowers z))

theorem isPGroup_Ssub (z : G) (hz : z * z = 1) (hz2 : orderOf z = 2) (T : Subgroup G)
    (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) (hP : IsPGroup 2 T) : IsPGroup 2 (Ssub z hz T hT) := by
  rw [Ssub_eq_sup z hz T hT]
  have hzp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  refine hP.to_sup_of_normal_left' hzp ?_
  rw [zpowers_le]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  rw [mem_normalizer_iff]
  intro t
  refine ⟨hT t, fun ht => ?_⟩
  have := hT _ ht
  have h2 : z * (z * t * z⁻¹) * z⁻¹ = t := by
    calc z * (z * t * z⁻¹) * z⁻¹ = (z * z) * t * (z * z)⁻¹ := by group
      _ = t := by rw [hz]; group
  rwa [h2] at this

theorem relIndex_Ssub (z : G) (hz : z * z = 1) (T : Subgroup G)
    (hT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) (hzT : z ∉ T) :
    T.relIndex (Ssub z hz T hT) = 2 := by
  have hdvd : T.relIndex (Ssub z hz T hT) ∣ 2 := by
    rw [relIndex_dvd_two_iff']
    refine ⟨z, z_mem_Ssub z hz T hT, fun b hb => ?_⟩
    obtain ⟨t, ht, hb | hb⟩ := hb
    · exact Or.inr (hb ▸ ht)
    · left
      rw [hb]
      have : z * (t * z) = z * t * z⁻¹ * (z * z) := by group
      rw [this, hz, mul_one]
      exact hT t ht
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exfalso
    exact hzT ((relIndex_eq_one.1 h1) (z_mem_Ssub z hz T hT))
  · exact h2

theorem WConfig.involution_conj (c : WConfig H z) {T₁ : Subgroup G} (hT : T₁ ≤ H) {y : G}
    (hyS : y ∈ Ssub z c.sq (prodSub c T₁ hT) (fun _ hx => c.z_mem_prodSub hT hx))
    (hyT : y ∉ prodSub c T₁ hT) (hy2 : y * y = 1) : ∃ a ∈ T₁, y = a * z * a⁻¹ := by
  obtain ⟨t, ht, hy | hy⟩ := hyS
  · exact absurd (hy ▸ ht) hyT
  · obtain ⟨a, ha, b, hb, rfl⟩ := ht
    have hz := c.sq
    have h1 : Phi z (a * b) (b * a) = 1 := by
      have e1 : y * y = Phi z a b * (z * Phi z a b * z⁻¹) * (z * z) := by
        rw [hy]; group
      rw [hz, mul_one, c.z_Phi (hT ha) (hT hb), c.Phi_mul (hT hb) (hT hb)] at e1
      rw [← e1]; exact hy2
    obtain ⟨h2, h3⟩ := c.Phi_eq_one (mul_mem (hT ha) (hT hb)) (mul_mem (hT hb) (hT ha)) h1
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h2
    refine ⟨a, ha, ?_⟩
    rw [hy, hb']
    unfold Phi
    calc a * (z * a⁻¹ * z⁻¹) * z = a * z * a⁻¹ * (z⁻¹ * z) := by group
      _ = a * z * a⁻¹ := by rw [inv_mul_cancel, mul_one]

end CFSG.OddStandard.AltStdSec.Wreath
