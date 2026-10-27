module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

section Diag

variable {G : Type} [Group G] {E : Subgroup G} {z : G}

@[expose] def diagHom (hc : ∀ a ∈ E, ∀ b ∈ E, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) :
    E →* G where
  toFun a := a * (z * a * z⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h1 := hc b b.2 a a.2
    show (a * b : G) * (z * (a * b) * z⁻¹) = (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹))
    calc (a * b : G) * (z * (a * b) * z⁻¹) = a * b * (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      _ = a * ((z * a * z⁻¹) * b) * (z * b * z⁻¹) := by rw [← h1]; group
      _ = (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹)) := by group

theorem diagHom_injective (hc : ∀ a ∈ E, ∀ b ∈ E, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a)
    (hint : ∀ a ∈ E, z * a * z⁻¹ ∈ E → a = 1) : Function.Injective (diagHom hc) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (a : G) * (z * a * z⁻¹) = 1 := ha
  have h2 : z * (a : G) * z⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : z * (a : G) * z⁻¹ ∈ E := h2 ▸ inv_mem a.2
  exact Subtype.ext (hint a a.2 h3)

end Diag

section Lift

variable {G : Type} [Group G] {E : Subgroup G}

@[expose] def liftSub (δ : E →* G) (S : Subgroup G) : Subgroup G := (S.comap δ).map E.subtype

theorem mem_liftSub {δ : E →* G} {S : Subgroup G} {g : G} :
    g ∈ liftSub δ S ↔ ∃ a : E, δ a ∈ S ∧ (a : G) = g := by
  simp only [liftSub, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]

theorem liftSub_le (δ : E →* G) (S : Subgroup G) : liftSub δ S ≤ E := by
  rintro _ hg
  obtain ⟨a, -, rfl⟩ := mem_liftSub.1 hg
  exact a.2

theorem liftSub_mono (δ : E →* G) {S S' : Subgroup G} (h : S ≤ S') :
    liftSub δ S ≤ liftSub δ S' := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := mem_liftSub.1 hg
  exact mem_liftSub.2 ⟨a, h ha, rfl⟩

theorem card_liftSub {δ : E →* G} (hδ : Function.Injective δ) {S : Subgroup G}
    (hS : S ≤ δ.range) : Nat.card (liftSub δ S) = Nat.card S := by
  unfold liftSub
  rw [Subgroup.card_map_of_injective E.subtype_injective, ← Subgroup.card_map_of_injective hδ,
    Subgroup.map_comap_eq, inf_eq_right.2 hS]

theorem exists_mem_liftSub {δ : E →* G} {S : Subgroup G} (hS : S ≤ δ.range) {s : G} (hs : s ∈ S) :
    ∃ a : E, δ a = s ∧ (a : G) ∈ liftSub δ S := by
  obtain ⟨a, rfl⟩ := hS hs
  exact ⟨a, rfl, mem_liftSub.2 ⟨a, hs, rfl⟩⟩

theorem liftSub_normalizes (δ : E →* G) {S S' : Subgroup G}
    (h : ∀ s ∈ S, ∀ s' ∈ S', s * s' * s⁻¹ ∈ S') :
    ∀ q ∈ liftSub δ S, ∀ x ∈ liftSub δ S', q * x * q⁻¹ ∈ liftSub δ S' := by
  intro q hq x hx
  obtain ⟨a, ha, rfl⟩ := mem_liftSub.1 hq
  obtain ⟨b, hb, rfl⟩ := mem_liftSub.1 hx
  refine mem_liftSub.2 ⟨a * b * a⁻¹, ?_, rfl⟩
  rw [map_mul, map_mul, map_inv]
  exact h _ ha _ hb

theorem liftSub_isPGroup {δ : E →* G} (hδ : Function.Injective δ) {S : Subgroup G}
    (hS : IsPGroup 2 S) : IsPGroup 2 (liftSub δ S) := by
  intro g
  obtain ⟨a, ha, hag⟩ := mem_liftSub.1 g.2
  obtain ⟨k, hk⟩ := hS ⟨δ a, ha⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (δ a) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : a ^ (2 ^ k) = 1 := hδ (by rw [map_pow, h1, map_one])
  have h3 : (a : G) ^ (2 ^ k) = 1 := congrArg Subtype.val h2
  show (g : G) ^ (2 ^ k) = 1
  rw [← hag]
  exact h3

end Lift

section FixCard

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G}

@[expose] noncomputable def conjOn (A : Subgroup G) (b : G) (hb : b ∈ normalizer (A : Set G)) :
    A ≃* A where
  toFun a := ⟨b * a * b⁻¹, (mem_normalizer_iff.1 hb a).1 a.2⟩
  invFun a := ⟨b⁻¹ * a * b, by
    have := (mem_normalizer_iff.1 (inv_mem hb) a).1 a.2
    simpa using this⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a a' := Subtype.ext (by simp [mul_assoc])

theorem card_fix_eq_of_comm (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAB : Nat.card (A ⊓ B : Subgroup G) * 16 = Nat.card A) {b : G}
    (hb : b ∈ normalizer (A : Set G))
    (h1 : ∀ a ∈ A, a * (b * a⁻¹ * b⁻¹) ∈ B)
    (h2 : ∀ c ∈ A ⊓ B, ∃ a ∈ A, c = a * (b * a⁻¹ * b⁻¹)) :
    Nat.card {a : A // b * a * b⁻¹ = a} = 16 := by
  let _ : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun x y => Subtype.ext (hAab x x.2 y y.2) }
  let κ : A →* A := MonoidHom.id A / (conjOn A b hb).toMonoidHom
  have hκ : ∀ a : A, ((κ a : A) : G) = a * (b * (a : G)⁻¹ * b⁻¹) := by
    intro a
    show ((a / (conjOn A b hb a) : A) : G) = _
    rw [div_eq_mul_inv]
    simp [conjOn, mul_assoc]
  have hker : ∀ a : A, a ∈ κ.ker ↔ b * a * b⁻¹ = a := by
    intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      rw [hκ] at h1
      have h2 : b * (a : G)⁻¹ * b⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 := congrArg (fun x => x⁻¹) h2
      simpa [mul_assoc] using h3
    · intro h
      apply Subtype.ext
      rw [hκ]
      show (a : G) * (b * (a : G)⁻¹ * b⁻¹) = 1
      have : b * (a : G)⁻¹ * b⁻¹ = (a : G)⁻¹ := by
        have h3 := congrArg (fun x => x⁻¹) h
        simpa [mul_assoc] using h3
      rw [this, mul_inv_cancel]
  have hrange : κ.range = (A ⊓ B).subgroupOf A := by
    ext a
    constructor
    · rintro ⟨a', rfl⟩
      refine mem_subgroupOf.2 ⟨(κ a').2, ?_⟩
      rw [hκ]
      exact h1 a' a'.2
    · intro ha
      obtain ⟨c, hc, hca⟩ := h2 a (mem_subgroupOf.1 ha)
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      rw [hκ]
      exact hca.symm
  have hcard := Subgroup.card_ker_mul_card_range κ
  rw [hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
    at hcard
  have hk : Nat.card κ.ker = 16 := by
    have hpos : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
    nlinarith
  rw [← hk]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun a => (hker a).symm))

end FixCard

section Half

variable {G : Type} [Group G]

@[expose] def CSideHalf (L A : Subgroup G) (z : G) (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
  (∀ a ∈ E, z * a * z⁻¹ ∈ E → a = 1) ∧
  (∀ a ∈ E, a * (z * a * z⁻¹) ∈ egNL L A) ∧
  Nat.card E * 2 = Nat.card (egNL L A)

end Half

end CFSG.EvenSporadicStandard.M24Std.DRes
