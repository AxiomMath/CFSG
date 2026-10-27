module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b

section Comm

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
theorem _root_.CFSG.EvenSporadicStandard.Fin76b.OuterConfig.commutator_mem [Finite G]
    {a b : G} (ha : a ∈ centralizer ({z} : Set G))
    (hb : b ∈ centralizer ({z} : Set G)) : a * b * a⁻¹ * b⁻¹ ∈ A := by
  classical
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hAH : A ≤ centralizer ({z} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A ha)
  have hNn : (A.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).2 h.cent_le
  have hrel : A.relIndex (centralizer ({z} : Set G)) = 2 * 2 := by
    rw [← Subgroup.relIndex_mul_relIndex A (A ⊔ zpowers z) (centralizer ({z} : Set G))
      le_sup_left (sup_le hAH (zpowers_le.2 hzH)), h.A_relIndex_sup, h.index_two]
  have hcard : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
      2 ^ 2 := by
    have : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
        A.relIndex (centralizer ({z} : Set G)) := rfl
    rw [this, hrel]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) :=
    IsPGroup.commGroupOfCardEqPrimeSq hcard
  have key : (QuotientGroup.mk ((⟨a, ha⟩ : centralizer ({z} : Set G)) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ *
      ⟨b, hb⟩⁻¹) : centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm (QuotientGroup.mk (⟨a, ha⟩ : centralizer ({z} : Set G)))
      (QuotientGroup.mk (⟨b, hb⟩ : centralizer ({z} : Set G)))]
    group
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 key)

end Comm

section Abstract

variable {H M : Type*} [Group H] [Group M]

structure ImageSetup (θ : H →* M) (z : H) (N : Subgroup H) : Prop where
  z_sq : z * z = 1
  z_central : ∀ g : H, g * z = z * g
  ker : ∀ g : H, θ g = 1 ↔ g ∈ zpowers z
  zN : z ∉ N
  comm : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N

variable {θ : H →* M} {z : H} {N : Subgroup H} (I : ImageSetup θ z N)

namespace ImageSetup

include I in
theorem eq_one_or_eq_z {g : H} (hg : θ g = 1) : g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ((I.ker g).1 hg)
  have hz2 : z ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact I.z_sq
  have : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    rw [hz2, one_zpow, mul_one]
  rw [this]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> simp [h0]

include I in
theorem comm_eq_one {a b : H} (h : a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = z) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rcases h with h | h
  · exact h
  · exact absurd (h ▸ I.comm a b) I.zN

include I in
theorem eq_of_theta_eq_of_mem {a b : H} (hab : θ a = θ b) (hN : a⁻¹ * b ∈ N) : a = b := by
  have h1 : θ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  rcases I.eq_one_or_eq_z h1 with h | h
  · exact inv_mul_eq_one.1 h
  · exact absurd (h ▸ hN) I.zN

variable {T E : Subgroup H}

include I in
theorem card_image (hzE : z ∈ E) : Nat.card (E.map θ) * 2 = Nat.card E := by
  let θE : E →* M := θ.comp E.subtype
  have hmap : E.map θ = θE.range := by
    ext m
    simp [θE, Subgroup.mem_map, MonoidHom.mem_range]
  have hker : θE.ker = (zpowers z).subgroupOf E := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact I.ker g
  have hcard : Nat.card θE.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 hzE)).toEquiv,
      Nat.card_zpowers]
    have : orderOf z = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (by rw [pow_two]; exact I.z_sq) ?_
      intro h
      exact I.zN (h ▸ N.one_mem)
    exact this
  have h := Subgroup.card_ker_mul_card_range θE
  rw [hcard, ← hmap] at h
  omega

structure NormalElemAb (T E : Subgroup H) (z : H) : Prop where
  le : E ≤ T
  normal : ∀ y ∈ T, ∀ e ∈ E, y * e * y⁻¹ ∈ E
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  sq : ∀ a ∈ E, a * a = 1
  z_mem : z ∈ E
  cent : ∀ y ∈ T, (∀ e ∈ E, y * e = e * y) → y ∈ E

variable (D : NormalElemAb T E z)

include D in
theorem image_le : E.map θ ≤ T.map θ := Subgroup.map_mono D.le

include D in
theorem image_normal : ∀ α ∈ T.map θ, ∀ β ∈ E.map θ, α * β * α⁻¹ ∈ E.map θ := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨e, he, rfl⟩
  exact ⟨y * e * y⁻¹, D.normal y hy e he, by rw [map_mul, map_mul, map_inv]⟩

include D in
theorem image_comm : ∀ α ∈ E.map θ, ∀ β ∈ E.map θ, α * β = β * α := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, D.comm a ha b hb]

include D in
theorem image_sq : ∀ α ∈ E.map θ, α * α = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_mul, D.sq a ha, map_one]

include I in
theorem centralizes_of_image {y : H} (hc : ∀ β ∈ E.map θ, θ y * β = β * θ y) :
    ∀ e ∈ E, y * e = e * y := by
  intro e he
  have h1 : θ (y * e * y⁻¹ * e⁻¹) = 1 := by
    have := hc (θ e) ⟨e, he, rfl⟩
    simp only [map_mul, map_inv]
    rw [this]
    group
  have h2 := I.comm_eq_one (I.eq_one_or_eq_z h1)
  calc y * e = (y * e * y⁻¹ * e⁻¹) * e * y := by group
    _ = e * y := by rw [h2]; group

include I D in
theorem image_cent : ∀ γ ∈ T.map θ, (∀ β ∈ E.map θ, γ * β = β * γ) → γ ∈ E.map θ := by
  rintro _ ⟨y, hy, rfl⟩ hc
  exact ⟨y, D.cent y hy (centralizes_of_image I hc), rfl⟩

include I in
theorem class_ncard [N.Normal] (e : H) :
    {β : M | ∃ α ∈ T.map θ, β = α * θ e * α⁻¹}.ncard =
      {g : H | ∃ y ∈ T, g = y * e * y⁻¹}.ncard := by
  have hset : {β : M | ∃ α ∈ T.map θ, β = α * θ e * α⁻¹} =
      θ '' {g : H | ∃ y ∈ T, g = y * e * y⁻¹} := by
    ext β
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y * e * y⁻¹, ⟨y, hy, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨θ y, ⟨y, hy, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  rw [hset]
  refine Set.InjOn.ncard_image ?_
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hθ
  have h1 : (y * e * y⁻¹)⁻¹ * (y' * e * y'⁻¹) ∈ N := by
    have e1 : (y * e * y⁻¹)⁻¹ * (y' * e * y'⁻¹) =
        e⁻¹ * ((y * e * y⁻¹ * e⁻¹)⁻¹ * (y' * e * y'⁻¹ * e⁻¹)) * e⁻¹⁻¹ := by group
    rw [e1]
    exact (inferInstance : N.Normal).conj_mem _
      (N.mul_mem (N.inv_mem (I.comm y e)) (I.comm y' e)) _
  exact I.eq_of_theta_eq_of_mem hθ h1

end ImageSetup

end Abstract

end CFSG.EvenSporadicStandard.M22Std
