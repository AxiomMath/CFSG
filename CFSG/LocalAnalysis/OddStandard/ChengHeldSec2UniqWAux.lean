module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup

variable {G : Type} [Group G]

theorem card_le_mul_of_cover [Finite G] {W' W₀ : Subgroup G} (ws : Finset G)
    (hcov : ∀ w ∈ W', ∃ v ∈ ws, w * v⁻¹ ∈ W₀) : Nat.card W' ≤ ws.card * Nat.card W₀ := by
  classical
  let f : G → G := fun w => if h : ∃ v ∈ ws, w * v⁻¹ ∈ W₀ then h.choose else 1
  have hf : ∀ w ∈ W', f w ∈ ws ∧ w * (f w)⁻¹ ∈ W₀ := by
    intro w hw
    have h := hcov w hw
    simp only [f, h, ↓reduceDIte]
    exact h.choose_spec
  let Wfin : Finset G := (Set.toFinite (W' : Set G)).toFinset
  let W0fin : Finset G := (Set.toFinite (W₀ : Set G)).toFinset
  let F : G → Finset G := fun v => Wfin.filter fun w => f w = v
  have hW : Nat.card W' = Wfin.card := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite (W' : Set G)), ← Nat.card_coe_set_eq]
    rfl
  have hW0 : Nat.card W₀ = W0fin.card := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite (W₀ : Set G)), ← Nat.card_coe_set_eq]
    rfl
  have hsub : Wfin ⊆ ws.biUnion F := by
    intro w hw
    have hw' : w ∈ W' := by simpa [Wfin] using hw
    simp only [Finset.mem_biUnion]
    exact ⟨f w, (hf w hw').1, by simp [F, hw]⟩
  have hcardF : ∀ v ∈ ws, (F v).card ≤ Nat.card W₀ := by
    intro v hv
    rw [hW0]
    refine Finset.card_le_card_of_injOn (fun w : G => w * v⁻¹) (fun w hw => ?_) ?_
    · have hw1 := Finset.mem_filter.1 (show w ∈ Wfin.filter (fun w => f w = v) from hw)
      have hw' : w ∈ W' := by simpa [Wfin] using hw1.1
      have := (hf w hw').2
      rw [hw1.2] at this
      simpa [W0fin] using this
    · intro a _ b _ hab
      simpa using hab
  calc Nat.card W' = Wfin.card := hW
    _ ≤ (ws.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ws.card * Nat.card W₀ := Finset.card_biUnion_le_card_mul _ _ _ hcardF

theorem exists_Ewit {W' W V : Subgroup G} (e : ↥W' ≃* ↥W) (hVW : V ≤ W) (hV8 : Nat.card V = 8)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (hWinv : ∀ a ∈ W, a * a = 1 → a ∈ V) (hVc : ∀ w ∈ W, ∀ v ∈ V, w * v = v * w)
    (hsq : ∀ v ∈ V, ∃ w ∈ W, w * w = v) :
    ∃ E : Subgroup G, E ≤ W' ∧ Nat.card E = 8 ∧ (∀ a ∈ E, a * a = 1) ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ x ∈ W', x * x = 1 → x ∈ E) ∧
      (∀ x ∈ W', ∀ a ∈ E, x * a = a * x) ∧ (∀ a ∈ E, ∃ z ∈ W', z * z = a) := by
  classical
  set K : Subgroup ↥W' := (V.subgroupOf W).comap e.toMonoidHom with hKdef
  have hK : ∀ x : ↥W', x ∈ K ↔ ((e x : ↥W) : G) ∈ V := fun x => by
    simp only [hKdef, mem_comap, MulEquiv.coe_toMonoidHom, mem_subgroupOf]
  have hmem : ∀ g : G, g ∈ K.map W'.subtype ↔ ∃ x : ↥W', ((e x : ↥W) : G) ∈ V ∧ (x : G) = g :=
    fun g => by simp only [mem_map, hK, Subgroup.coe_subtype]
  have hcardK : Nat.card K = 8 := by
    have h1 : Nat.card K = Nat.card (K.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective e.injective).symm
    rw [h1, hKdef, Subgroup.map_comap_eq_self_of_surjective e.surjective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv, hV8]
  have hmul1 : ∀ x y : ↥W', ((e (x * y) : ↥W) : G) = (e x : G) * (e y : G) := fun x y => by
    rw [map_mul]; rfl
  refine ⟨K.map W'.subtype, map_subtype_le K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective W'.subtype_injective, hcardK]
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := (hmem a).1 ha
    have h1 : e (x * x) = e 1 := Subtype.ext (by rw [hmul1]; exact (hV2 _ hx).trans (by simp))
    have := e.injective h1
    exact congrArg Subtype.val this
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, hy, rfl⟩ := (hmem b).1 hb
    have h1 : e (x * y) = e (y * x) := Subtype.ext (by
      rw [hmul1, hmul1]; exact hVab _ hx _ hy)
    exact congrArg Subtype.val (e.injective h1)
  · intro x hx hx2
    refine (hmem x).2 ⟨⟨x, hx⟩, ?_, rfl⟩
    refine hWinv _ (e ⟨x, hx⟩).2 ?_
    rw [← hmul1]
    have : (⟨x, hx⟩ : ↥W') * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
    rfl
  · intro x hx a ha
    obtain ⟨y, hy, rfl⟩ := (hmem a).1 ha
    have h1 : e (⟨x, hx⟩ * y) = e (y * ⟨x, hx⟩) := Subtype.ext (by
      rw [hmul1, hmul1]; exact hVc _ (e ⟨x, hx⟩).2 _ hy)
    exact congrArg Subtype.val (e.injective h1)
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := (hmem a).1 ha
    obtain ⟨w, hw, hww⟩ := hsq _ hx
    refine ⟨((e.symm ⟨w, hw⟩ : ↥W') : G), (e.symm ⟨w, hw⟩).2, ?_⟩
    have h1 : e (e.symm ⟨w, hw⟩ * e.symm ⟨w, hw⟩) = e x := Subtype.ext (by
      rw [hmul1, MulEquiv.apply_symm_apply]
      exact hww)
    exact congrArg Subtype.val (e.injective h1)

end CFSG.OddStandard.ChengHeld
