module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

theorem eq_of_comm_eq {G : Type*} [Group G] {X : Subgroup G}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {δ : G} (hδ : ∀ z ∈ X, δ * z * δ⁻¹ ∈ X)
    (hfix : ∀ z ∈ X, δ * z * δ⁻¹ = z → z = 1) {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (h1 : δ * a * δ⁻¹ * a⁻¹ = δ * b * δ⁻¹ * b⁻¹) : a = b := by
  have hcX : δ * a * δ⁻¹ * a⁻¹ ∈ X := X.mul_mem (hδ a ha) (X.inv_mem ha)
  have hw : a * b⁻¹ ∈ X := X.mul_mem ha (X.inv_mem hb)
  set c : G := δ * a * δ⁻¹ * a⁻¹ with hc
  have e1 : δ * a * δ⁻¹ = c * a := by rw [hc]; group
  have e2 : δ * b * δ⁻¹ = c * b := by rw [h1]; group
  have h2 : δ * (a * b⁻¹) * δ⁻¹ = a * b⁻¹ := by
    calc δ * (a * b⁻¹) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹)⁻¹ := by group
      _ = (c * a) * (c * b)⁻¹ := by rw [e1, e2]
      _ = c * (a * b⁻¹) * c⁻¹ := by group
      _ = (a * b⁻¹) * c * c⁻¹ := by rw [hX c hcX _ hw]
      _ = a * b⁻¹ := by group
  exact mul_inv_eq_one.1 (hfix _ hw h2)

theorem exists_eq_commutator_of_fixed_trivial {G : Type*} [Group G] {X : Subgroup G} [Finite X]
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {δ : G} (hδ : ∀ z ∈ X, δ * z * δ⁻¹ ∈ X)
    (hfix : ∀ z ∈ X, δ * z * δ⁻¹ = z → z = 1) {y : G} (hy : y ∈ X) :
    ∃ z ∈ X, y = δ * z * δ⁻¹ * z⁻¹ := by
  let f : X → X := fun z => ⟨δ * (z : G) * δ⁻¹ * (z : G)⁻¹, X.mul_mem (hδ z z.2) (X.inv_mem z.2)⟩
  have hinj : Function.Injective f := by
    intro z z' h
    exact Subtype.ext (eq_of_comm_eq hX hδ hfix z.2 z'.2 (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
  exact ⟨z, z.2, (congrArg Subtype.val hz).symm⟩

theorem orbit_injective {G : Type*} [Group G] {A Y : Subgroup G}
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ y ∈ Y, a⁻¹ * y * a = y → y = 1)
    {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : a⁻¹ * y * a = b⁻¹ * y * b) : a = b := by
  by_contra hne
  have hc : b * a⁻¹ ∈ A := A.mul_mem hb (A.inv_mem ha)
  have hc1 : b * a⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.1 h1).symm
  have key : (b * a⁻¹)⁻¹ * y * (b * a⁻¹) = y := by
    have h' : b⁻¹ * y * b = a⁻¹ * y * a := h.symm
    calc (b * a⁻¹)⁻¹ * y * (b * a⁻¹) = a * (b⁻¹ * y * b) * a⁻¹ := by group
      _ = a * (a⁻¹ * y * a) * a⁻¹ := by rw [h']
      _ = y := by group
  exact hy1 (hfree _ hc hc1 y hy key)

noncomputable def orbitMap {G : Type*} [Group G] {A Y : Subgroup G}
    (hY : ∀ a ∈ A, ∀ y ∈ Y, a⁻¹ * y * a ∈ Y) {y : G} (hy : y ∈ Y) : A ⊕ Unit → Y :=
  Sum.elim (fun a => ⟨(a : G)⁻¹ * y * a, hY a a.2 y hy⟩) (fun _ => 1)

theorem orbitMap_injective {G : Type*} [Group G] {A Y : Subgroup G}
    (hY : ∀ a ∈ A, ∀ y ∈ Y, a⁻¹ * y * a ∈ Y)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ y ∈ Y, a⁻¹ * y * a = y → y = 1)
    {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) : Function.Injective (orbitMap hY hy) := by
  have hne : ∀ a : A, orbitMap hY hy (Sum.inl a) ≠ 1 := by
    intro a h
    have : (a : G)⁻¹ * y * a = 1 := congrArg Subtype.val h
    apply hy1
    calc y = (a : G) * ((a : G)⁻¹ * y * a) * (a : G)⁻¹ := by group
      _ = 1 := by rw [this]; group
  rintro (a | _) (b | _) h
  · have := orbit_injective hfree hy hy1 a.2 b.2 (congrArg Subtype.val h)
    exact congrArg Sum.inl (Subtype.ext this)
  · exact absurd h (hne a)
  · exact absurd h.symm (hne b)
  · rfl

theorem card_add_one_le_of_free {G : Type*} [Group G] [Finite G] {A Y : Subgroup G}
    (hY : ∀ a ∈ A, ∀ y ∈ Y, a⁻¹ * y * a ∈ Y)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ y ∈ Y, a⁻¹ * y * a = y → y = 1)
    {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) : Nat.card A + 1 ≤ Nat.card Y := by
  have := Nat.card_le_card_of_injective _ (orbitMap_injective hY hfree hy hy1)
  rw [Nat.card_sum] at this
  simpa using this

theorem transitive_of_free_of_card {G : Type*} [Group G] [Finite G] {A Y : Subgroup G}
    (hY : ∀ a ∈ A, ∀ y ∈ Y, a⁻¹ * y * a ∈ Y)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ y ∈ Y, a⁻¹ * y * a = y → y = 1)
    (hcard : Nat.card Y = Nat.card A + 1) {z z' : G} (hz : z ∈ Y) (hz1 : z ≠ 1) (hz' : z' ∈ Y)
    (hz1' : z' ≠ 1) : ∃ a ∈ A, a⁻¹ * z * a = z' := by
  have hinj := orbitMap_injective hY hfree hz hz1
  have hbij : Function.Bijective (orbitMap hY hz) := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_sum, hcard]
    simp
  obtain ⟨w, hw⟩ := hbij.2 ⟨z', hz'⟩
  rcases w with a | u
  · exact ⟨a, a.2, congrArg Subtype.val hw⟩
  · exfalso
    apply hz1'
    exact congrArg Subtype.val hw.symm

end CFSG.QuasithinUnique.Lin2
