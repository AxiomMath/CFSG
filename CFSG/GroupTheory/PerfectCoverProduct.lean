module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.GroupTheory.PerfectCover

open scoped commutatorElement

section Basic

variable {E : Type*} [Group E]

theorem commutatorElement_mul_mul_of_mem_center {a b z w : E} (hz : z ∈ Subgroup.center E)
    (hw : w ∈ Subgroup.center E) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz1 : ∀ c : E, ⁅z, c⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz c).symm
  have hw1 : ∀ c : E, ⁅c, w⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw c)
  rw [commutatorElement_mul_left_eq_conj_mul, hz1, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, hw1, mul_one, mul_inv_cancel_right]

theorem commute_of_commutator_le_center {H₁ H₂ : Subgroup E}
    (h : ⁅H₁, H₂⁆ ≤ Subgroup.center E) {a b : E} (ha : a ∈ ⁅H₁, H₁⁆) (hb : b ∈ H₂) :
    a * b = b * a := by
  have hc : ∀ K K' : Subgroup E, K ≤ Subgroup.center E → ⁅K, K'⁆ = ⊥ := fun K K' hK =>
    eq_bot_iff.mpr ((Subgroup.commutator_mono_left hK).trans
      (Subgroup.commutator_center_left K').le)
  have h1 : ⁅⁅H₁, H₁⁆, H₂⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · exact hc _ _ h
    · exact hc _ _ (by rwa [Subgroup.commutator_comm])
  have h2 : ⁅H₁, H₁⁆ ≤ Subgroup.centralizer (H₂ : Set E) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  exact (Subgroup.mem_centralizer_iff.mp (h2 ha) b hb).symm

end Basic

section Cover

variable {E X : Type*} [Group E] [Group X] (π : E →* X)

theorem map_commutator_comap {L : Subgroup X} (hπ : Function.Surjective π) (hL : ⁅L, L⁆ = L) :
    (⁅L.comap π, L.comap π⁆).map π = L := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ, hL]

theorem exists_mul_of_mem_comap {L : Subgroup X} (hπ : Function.Surjective π)
    (hL : ⁅L, L⁆ = L) {g : E} (hg : g ∈ L.comap π) :
    ∃ q ∈ ⁅L.comap π, L.comap π⁆, ∃ z ∈ π.ker, g = q * z := by
  have h : π g ∈ (⁅L.comap π, L.comap π⁆).map π := by
    rw [map_commutator_comap π hπ hL]
    exact hg
  obtain ⟨q, hq, hqg⟩ := h
  refine ⟨q, hq, q⁻¹ * g, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hqg, inv_mul_cancel]

theorem isPerfect_commutator_comap (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) {L : Subgroup X} (hL : ⁅L, L⁆ = L) :
    Group.IsPerfect ↥⁅L.comap π, L.comap π⁆ := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨q, hq, z, hz, rfl⟩ := exists_mul_of_mem_comap π hπ hL hg
  obtain ⟨q', hq', z', hz', rfl⟩ := exists_mul_of_mem_comap π hπ hL hg'
  rw [commutatorElement_mul_mul_of_mem_center (hker hz) (hker hz')]
  exact Subgroup.commutator_mem_commutator hq hq'

theorem commute_commutator_comap (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    {L₁ L₂ : Subgroup X} (hc : ⁅L₁, L₂⁆ = ⊥) {a b : E} (ha : a ∈ ⁅L₁.comap π, L₁.comap π⁆)
    (hb : b ∈ ⁅L₂.comap π, L₂.comap π⁆) : a * b = b * a := by
  have hHc : ⁅L₁.comap π, L₂.comap π⁆ ≤ Subgroup.center E := by
    refine le_trans ?_ hker
    rw [← Subgroup.map_eq_bot_iff, Subgroup.map_commutator,
      Subgroup.map_comap_eq_self_of_surjective hπ, Subgroup.map_comap_eq_self_of_surjective hπ]
    exact hc
  exact commute_of_commutator_le_center hHc ha
    (Subgroup.commutator_le_of_le le_rfl le_rfl (hb : b ∈ ⁅L₂.comap π, L₂.comap π⁆))

theorem exists_mul_mul_ker {L₁ L₂ : Subgroup X} (hπ : Function.Surjective π)
    (hL₁ : ⁅L₁, L₁⁆ = L₁) (hL₂ : ⁅L₂, L₂⁆ = L₂) (hX : ∀ x : X, ∃ u ∈ L₁, ∃ v ∈ L₂, x = u * v)
    (x : E) :
    ∃ q₁ ∈ ⁅L₁.comap π, L₁.comap π⁆, ∃ q₂ ∈ ⁅L₂.comap π, L₂.comap π⁆, ∃ w ∈ π.ker,
      x = q₁ * q₂ * w := by
  obtain ⟨u, hu, v, hv, huv⟩ := hX (π x)
  obtain ⟨q₁, hq₁, hq₁u⟩ : u ∈ (⁅L₁.comap π, L₁.comap π⁆).map π := by
    rw [map_commutator_comap π hπ hL₁]
    exact hu
  obtain ⟨q₂, hq₂, hq₂v⟩ : v ∈ (⁅L₂.comap π, L₂.comap π⁆).map π := by
    rw [map_commutator_comap π hπ hL₂]
    exact hv
  refine ⟨q₁, hq₁, q₂, hq₂, (q₁ * q₂)⁻¹ * x, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hq₁u, hq₂v, ← huv, inv_mul_cancel]

theorem exists_eq_mul_commutator_comap (hE : Group.IsPerfect E) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) {L₁ L₂ : Subgroup X} (hL₁ : ⁅L₁, L₁⁆ = L₁)
    (hL₂ : ⁅L₂, L₂⁆ = L₂) (hc : ⁅L₁, L₂⁆ = ⊥) (hX : ∀ x : X, ∃ u ∈ L₁, ∃ v ∈ L₂, x = u * v)
    (y : E) :
    ∃ a₁ ∈ ⁅L₁.comap π, L₁.comap π⁆, ∃ a₂ ∈ ⁅L₂.comap π, L₂.comap π⁆, y = a₁ * a₂ := by
  have hcomm : ∀ (a : ↥⁅L₁.comap π, L₁.comap π⁆) (b : ↥⁅L₂.comap π, L₂.comap π⁆),
      Commute (⁅L₁.comap π, L₁.comap π⁆.subtype a) (⁅L₂.comap π, L₂.comap π⁆.subtype b) :=
    fun a b => commute_commutator_comap π hπ hker hc a.2 b.2
  let P : Subgroup E := (MonoidHom.noncommCoprod _ _ hcomm).range
  have hP₁ : ∀ q ∈ ⁅L₁.comap π, L₁.comap π⁆, q ∈ P := fun q hq => ⟨(⟨q, hq⟩, 1), by simp⟩
  have hP₂ : ∀ q ∈ ⁅L₂.comap π, L₂.comap π⁆, q ∈ P := fun q hq => ⟨(1, ⟨q, hq⟩), by simp⟩
  have htop : ⁅(⊤ : Subgroup E), ⊤⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x _ x' _
    obtain ⟨q₁, hq₁, q₂, hq₂, w, hw, rfl⟩ := exists_mul_mul_ker π hπ hL₁ hL₂ hX x
    obtain ⟨q₁', hq₁', q₂', hq₂', w', hw', rfl⟩ := exists_mul_mul_ker π hπ hL₁ hL₂ hX x'
    rw [commutatorElement_mul_mul_of_mem_center (hker hw) (hker hw')]
    exact Subgroup.commutator_le_of_le (K := P) le_rfl le_rfl
      (Subgroup.commutator_mem_commutator (P.mul_mem (hP₁ _ hq₁) (hP₂ _ hq₂))
        (P.mul_mem (hP₁ _ hq₁') (hP₂ _ hq₂')))
  have hEtop : ⁅(⊤ : Subgroup E), ⊤⁆ = ⊤ := hE.commutator_eq_top
  have hy : y ∈ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ := by
    rw [hEtop]
    exact Subgroup.mem_top y
  obtain ⟨⟨a₁, a₂⟩, hy⟩ : y ∈ P := htop hy
  exact ⟨a₁, a₁.2, a₂, a₂.2, hy.symm⟩

end Cover

section Exponent

theorem pow_eq_one_of_mem_commutator_comap {E X Y : Type} [Group E] [Finite E] [Group X]
    [Group Y] (π : E →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    {L : Subgroup X} (hL : ⁅L, L⁆ = L) (p : X →* Y) (hinj : ∀ x ∈ L, p x = 1 → x = 1)
    (hsurj : ∀ s : Y, ∃ x ∈ L, p x = s) (n : ℕ)
    (h : ∀ (F : Type) [Group F] [Finite F], Group.IsPerfect F → ∀ q : F →* Y,
      Function.Surjective q → q.ker ≤ Subgroup.center F → ∀ y ∈ q.ker, y ^ n = 1)
    {a : E} (ha : a ∈ ⁅L.comap π, L.comap π⁆) (h1 : π a = 1) : a ^ n = 1 := by
  have hQH : ⁅L.comap π, L.comap π⁆ ≤ L.comap π := Subgroup.commutator_le_of_le le_rfl le_rfl
  let f : ↥⁅L.comap π, L.comap π⁆ →* Y := p.comp (π.comp (⁅L.comap π, L.comap π⁆).subtype)
  have hfs : Function.Surjective f := by
    intro s
    obtain ⟨x, hxL, hxs⟩ := hsurj s
    obtain ⟨q, hq, hqx⟩ : x ∈ (⁅L.comap π, L.comap π⁆).map π := by
      rw [map_commutator_comap π hπ hL]
      exact hxL
    exact ⟨⟨q, hq⟩, by rw [← hxs, ← hqx]; rfl⟩
  have hfk : f.ker ≤ Subgroup.center ↥⁅L.comap π, L.comap π⁆ := by
    intro u hu
    have hpu : p (π u) = 1 := hu
    have hu1 : π u = 1 := hinj _ (hQH u.2) hpu
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hu1)) g)
  have h2 := h ↥⁅L.comap π, L.comap π⁆ (isPerfect_commutator_comap π hπ hker hL) f hfs hfk
    ⟨a, ha⟩ (by show p (π a) = 1; rw [h1, map_one])
  exact congrArg Subtype.val h2

end Exponent

theorem exponent_ker_prod_cover {E X₁ X₂ : Type} [Group E] [Finite E] [Group X₁] [Finite X₁]
    [Group X₂] [Finite X₂] (hE : Group.IsPerfect E) (hX₁ : Group.IsPerfect X₁)
    (hX₂ : Group.IsPerfect X₂) (π : E →* X₁ × X₂) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (n : ℕ)
    (h₁ : ∀ (F : Type) [Group F] [Finite F], Group.IsPerfect F → ∀ q : F →* X₁,
      Function.Surjective q → q.ker ≤ Subgroup.center F → ∀ y ∈ q.ker, y ^ n = 1)
    (h₂ : ∀ (F : Type) [Group F] [Finite F], Group.IsPerfect F → ∀ q : F →* X₂,
      Function.Surjective q → q.ker ≤ Subgroup.center F → ∀ y ∈ q.ker, y ^ n = 1) :
    ∀ y ∈ π.ker, y ^ n = 1 := by
  set L₁ : Subgroup (X₁ × X₂) := (⊤ : Subgroup X₁).prod ⊥ with hL₁
  set L₂ : Subgroup (X₁ × X₂) := (⊥ : Subgroup X₁).prod ⊤ with hL₂
  have hS₁ : ⁅(⊤ : Subgroup X₁), (⊤ : Subgroup X₁)⁆ = ⊤ := hX₁.commutator_eq_top
  have hS₂ : ⁅(⊤ : Subgroup X₂), (⊤ : Subgroup X₂)⁆ = ⊤ := hX₂.commutator_eq_top
  have hL₁p : ⁅L₁, L₁⁆ = L₁ := by
    rw [hL₁, Subgroup.commutator_prod_prod, hS₁, Subgroup.commutator_bot_left]
  have hL₂p : ⁅L₂, L₂⁆ = L₂ := by
    rw [hL₂, Subgroup.commutator_prod_prod, hS₂, Subgroup.commutator_bot_left]
  have hc : ⁅L₁, L₂⁆ = ⊥ := by
    rw [hL₁, hL₂, Subgroup.commutator_prod_prod, Subgroup.commutator_bot_right,
      Subgroup.commutator_bot_left, Subgroup.bot_prod_bot]
  have hX : ∀ x : X₁ × X₂, ∃ u ∈ L₁, ∃ v ∈ L₂, x = u * v := fun x =>
    ⟨(x.1, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, (1, x.2),
      ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩, Prod.ext (by simp) (by simp)⟩
  intro y hy
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ :=
    exists_eq_mul_commutator_comap π hE hπ hker hL₁p hL₂p hc hX y
  have hπ₁ : π a₁ ∈ L₁ :=
    (Subgroup.commutator_le_of_le (K := L₁.comap π) le_rfl le_rfl) ha₁
  have hπ₂ : π a₂ ∈ L₂ :=
    (Subgroup.commutator_le_of_le (K := L₂.comap π) le_rfl le_rfl) ha₂
  have hy' : π a₁ * π a₂ = 1 := by rw [← map_mul]; exact hy
  have h1 : π a₁ = 1 := by
    refine Prod.ext ?_ (Subgroup.mem_bot.mp hπ₁.2)
    have := congrArg Prod.fst hy'
    simpa [Subgroup.mem_bot.mp hπ₂.1] using this
  have h2 : π a₂ = 1 := by
    refine Prod.ext (Subgroup.mem_bot.mp hπ₂.1) ?_
    have := congrArg Prod.snd hy'
    simpa [Subgroup.mem_bot.mp hπ₁.2] using this
  have e₁ : a₁ ^ n = 1 :=
    pow_eq_one_of_mem_commutator_comap π hπ hker hL₁p (MonoidHom.fst X₁ X₂)
      (fun x hx hx1 => Prod.ext hx1 (Subgroup.mem_bot.mp hx.2))
      (fun s => ⟨(s, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, rfl⟩) n h₁ ha₁ h1
  have e₂ : a₂ ^ n = 1 :=
    pow_eq_one_of_mem_commutator_comap π hπ hker hL₂p (MonoidHom.snd X₁ X₂)
      (fun x hx hx1 => Prod.ext (Subgroup.mem_bot.mp hx.1) hx1)
      (fun s => ⟨(1, s), ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩, rfl⟩) n h₂ ha₂ h2
  have hcomm : Commute a₁ a₂ := commute_commutator_comap π hπ hker hc ha₁ ha₂
  rw [hcomm.mul_pow, e₁, e₂, mul_one]

end CFSG.GroupTheory.PerfectCover
