module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Transport

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open Subgroup

variable {J G : Type} [Group J] [Group G]

theorem unique_map (ι : J →* G) (hι : Function.Injective ι) {U T0 : Subgroup J}
    (h : LocalData (⊤ : Subgroup J) U T0) :
    ∀ A : Subgroup G, A ≤ T0.map ι → (∀ a ∈ A, a * a = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → 2 ^ 11 ≤ Nat.card A → A = U.map ι := by
  intro A hA hsq hcomm hcard
  have hAT : A.comap ι ≤ T0 := fun x hx => (mem_map_iff_mem hι).1 (hA hx)
  have hmap : (A.comap ι).map ι = A := map_comap_eq_self (hA.trans (map_le_range ι T0))
  have heq : A.comap ι = U := by
    refine h.unique _ hAT (fun a ha => hι ?_) (fun a ha b hb => hι ?_) ?_
    · rw [map_mul, map_one]
      exact hsq _ ha
    · rw [map_mul, map_mul]
      exact hcomm _ ha _ hb
    · rw [← card_map_of_injective hι, hmap]
      exact hcard
  rw [← hmap, heq]

theorem selfCentralizing_map (ι : J →* G) (hι : Function.Injective ι) {U T0 : Subgroup J}
    (h : LocalData (⊤ : Subgroup J) U T0) :
    ∀ l ∈ ι.range, (∀ u ∈ U.map ι, l * u = u * l) → l ∈ U.map ι := by
  rintro _ ⟨j, rfl⟩ hc
  refine ⟨j, h.selfCentralizing j (mem_top j) fun u hu => hι ?_, rfl⟩
  rw [map_mul, map_mul]
  exact hc (ι u) ⟨u, hu, rfl⟩

theorem orbits_map (ι : J →* G) (hι : Function.Injective ι) {U T0 : Subgroup J}
    (h : LocalData (⊤ : Subgroup J) U T0) :
    ∃ a b : G, a ∈ U.map ι ∧ b ∈ U.map ι ∧ a ≠ 1 ∧ b ≠ 1 ∧ b ∉ hOrbit ι.range (U.map ι) a ∧
      (∀ u ∈ U.map ι, u ≠ 1 → u ∈ hOrbit ι.range (U.map ι) a ∨ u ∈ hOrbit ι.range (U.map ι) b) ∧
      (hOrbit ι.range (U.map ι) a).ncard = 1771 ∧ (hOrbit ι.range (U.map ι) b).ncard = 276 := by
  obtain ⟨a, b, haU, hbU, ha1, hb1, hba, hcov, hca, hcb⟩ := h.orbits
  have hne : ∀ x : J, x ≠ 1 → ι x ≠ 1 := fun x hx e => hx (hι (by rw [e, map_one]))
  refine ⟨ι a, ι b, mem_map_of_mem ι haU, mem_map_of_mem ι hbU, hne a ha1, hne b hb1,
    ?_, ?_, ?_, ?_⟩
  · rw [hOrbit_map ι hι]
    exact fun hb => hba (hι.mem_set_image.1 hb)
  · rintro _ ⟨u, hu, rfl⟩ hu1
    have hu1' : u ≠ 1 := fun e => hu1 (by rw [e, map_one])
    rw [hOrbit_map ι hι, hOrbit_map ι hι]
    rcases hcov u hu hu1' with hua | hub
    · exact Or.inl ⟨u, hua, rfl⟩
    · exact Or.inr ⟨u, hub, rfl⟩
  · rw [hOrbit_map ι hι, Set.ncard_image_of_injective _ hι]
    exact hca
  · rw [hOrbit_map ι hι, Set.ncard_image_of_injective _ hι]
    exact hcb

theorem irred_map (ι : J →* G) (hι : Function.Injective ι) {U T0 : Subgroup J}
    (h : LocalData (⊤ : Subgroup J) U T0) :
    ∀ D : Subgroup G, D ≤ U.map ι → (∀ g ∈ Hloc ι.range (U.map ι), ∀ d ∈ D, g * d * g⁻¹ ∈ D) →
      D = ⊥ ∨ D = U.map ι := by
  intro D hD hinv
  have hmap : (D.comap ι).map ι = D := map_comap_eq_self (hD.trans (map_le_range ι U))
  have hle : D.comap ι ≤ U := fun x hx => (mem_map_iff_mem hι).1 (hD hx)
  have hinv' : ∀ g ∈ Hloc (⊤ : Subgroup J) U, ∀ d ∈ D.comap ι, g * d * g⁻¹ ∈ D.comap ι := by
    intro g hg d hd
    have := hinv (ι g) ((mem_Hloc_map ι hι U).2 ⟨g, hg, rfl⟩) (ι d) hd
    rwa [← map_inv, ← map_mul, ← map_mul] at this
  rcases h.irred _ hle hinv' with h0 | h0
  · left
    rw [← hmap, h0, Subgroup.map_bot]
  · right
    rw [← hmap, h0]

theorem localData_map (ι : J →* G) (hι : Function.Injective ι) {U T0 : Subgroup J}
    (h : LocalData (⊤ : Subgroup J) U T0) :
    LocalData ι.range (U.map ι) (T0.map ι) where
  U_le_T0 := map_mono h.U_le_T0
  T0_le_L := map_le_range ι T0
  T0_pGroup := h.T0_pGroup.map ι
  T0_index_odd := by
    rw [MonoidHom.range_eq_map, relIndex_map_map_of_injective T0 ⊤ hι]
    exact h.T0_index_odd
  U_sq := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, h.U_sq u hu, map_one]
  U_comm := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, h.U_comm u hu v hv]
  card_U := by
    rw [card_map_of_injective hι]
    exact h.card_U
  unique := unique_map ι hι h
  selfCentralizing := selfCentralizing_map ι hι h
  card_H := by
    rw [Hloc_map ι hι, card_map_of_injective hι]
    exact h.card_H
  orbits := orbits_map ι hι h
  irred := irred_map ι hι h

end CFSG.EvenSporadicStandard.J4Std.DataLocal
