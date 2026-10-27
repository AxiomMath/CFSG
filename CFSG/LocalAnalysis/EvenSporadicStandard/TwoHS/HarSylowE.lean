module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

theorem card_sq_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (K : Subgroup G) (x : G) :
    Nat.card {y : K // (y : G) ^ 2 = x} = Nat.card {y : K.map f // (y : H) ^ 2 = f x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Subgroup.equivMapOfInjective K f hf).toEquiv
    fun y => ?_)
  have : ((Subgroup.equivMapOfInjective K f hf y : K.map f) : H) = f y := rfl
  change (y : G) ^ 2 = x ↔ ((Subgroup.equivMapOfInjective K f hf y : K.map f) : H) ^ 2 = f x
  rw [this, ← map_pow]
  exact (hf.eq_iff).symm

@[expose] def CoverMaps.T0 {E : Type} [Group E] (M : CoverMaps E) : Subgroup E :=
  Subgroup.closure {x | x ∈ M.uE}

section Maps

theorem CoverMaps.map_T0 {E : Type} [Group E] (M : CoverMaps E) : M.T0.map M.ρ = harT0 := by
  unfold CoverMaps.T0 harT0 genOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  have h := congrArg (fun L => x ∈ L) M.uE_rho
  simp only [List.mem_map, eq_iff_iff] at h
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_toArray]
  exact h

theorem CoverModel.card_T0 {E : Type} [Group E] (M : CoverModel E) : Nat.card M.T0 = 1024 := by
  rw [← Subgroup.card_map_of_injective M.ρ_inj, M.map_T0]
  exact harT0_card

theorem CoverModel.card_sq_T0_tE {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.T0 // (y : E) ^ 2 = M.tE} = 80 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_T0]
  exact harT0_sq_c M.rep_tE

theorem CoverModel.card_sq_T0_z2E {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.T0 // (y : E) ^ 2 = M.tE * M.z1E} = 48 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_T0, map_mul]
  exact harT0_sq_z2 (Rep.compT M.rep_tE M.rep_z1E)

theorem harCPairs_letters : ∀ p ∈ harCPairs, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3) ∧
    ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ 3 := by
  decide

@[expose] def CoverMaps.cgens {E : Type} [Group E] (M : CoverMaps E) : List E :=
  harCPairs.map fun p => ⁅wordVal M.uE p.1, wordVal M.uE p.2⁆

@[expose] def CoverMaps.T0' {E : Type} [Group E] (M : CoverMaps E) : Subgroup E :=
  Subgroup.closure {x | x ∈ M.cgens}

set_option maxRecDepth 100000 in
theorem CoverMaps.rho_comm_pair {E : Type} [Group E] (M : CoverMaps E) {p : List ℕ × List ℕ}
    (hp : p ∈ harCPairs) :
    M.ρ ⁅wordVal M.uE p.1, wordVal M.uE p.2⁆ = tp 11200 (tComm 11200 (tU p.1) (tU p.2)) := by
  have hl := harCPairs_letters p hp
  have hperm : permOK 11200 (tComm 11200 (tU p.1) (tU p.2)) = true :=
    harCgens_perm _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  rw [map_commutatorElement]
  exact (rep_unique (rep_tp hperm)
    (rep_tComm hn11200 (M.rep_tU p.1 hl.1) (M.rep_tU p.2 hl.2))).symm

theorem CoverMaps.map_T0' {E : Type} [Group E] (M : CoverMaps E) : M.T0'.map M.ρ = harT0' := by
  unfold CoverMaps.T0' harT0' genOf
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_toArray, CoverMaps.cgens, harCgens,
    List.mem_map]
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, (M.rho_comm_pair hp).symm⟩
  · rintro ⟨g, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, M.rho_comm_pair hp⟩

theorem CoverModel.card_T0' {E : Type} [Group E] (M : CoverModel E) : Nat.card M.T0' = 128 := by
  rw [← Subgroup.card_map_of_injective M.ρ_inj, M.map_T0']
  exact harT0'_card

theorem CoverModel.tE_mem_T0' {E : Type} [Group E] (M : CoverModel E) : M.tE ∈ M.T0' := by
  rw [← Subgroup.mem_map_iff_mem M.ρ_inj, M.map_T0']
  exact harC_mem_harT0' M.rep_tE

theorem CoverModel.card_sq_T0'_tE {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.T0' // (y : E) ^ 2 = M.tE} = 16 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_T0']
  exact harT0'_sq_c M.rep_tE

theorem CoverModel.card_sq_T0'_z1E {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.T0' // (y : E) ^ 2 = M.z1E} = 32 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_T0']
  exact harT0'_sq_z1 M.rep_z1E

theorem CoverModel.card_sq_T0'_z2E {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.T0' // (y : E) ^ 2 = M.tE * M.z1E} = 16 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_T0', map_mul]
  exact harT0'_sq_z2 (Rep.compT M.rep_tE M.rep_z1E)

end Maps

section WMaps

@[expose] def CoverMaps.W0 {E : Type} [Group E] (M : CoverMaps E) : Subgroup E :=
  Subgroup.closure ((M.T0' : Set E) ∪ {y | y ∈ M.T0 ∧ y ^ 2 = 1})

theorem CoverModel.map_W0 {E : Type} [Group E] (M : CoverModel E) : M.W0.map M.ρ = harW0 := by
  rw [CoverMaps.W0, MonoidHom.map_closure, Set.image_union, harW0_eq]
  congr 1
  apply congrArg₂ (· ∪ ·)
  · rw [← Subgroup.coe_map, M.map_T0']
  · ext z
    constructor
    · rintro ⟨y, ⟨hyT, hy2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← M.map_T0]
        exact Subgroup.mem_map_of_mem _ hyT
      · rw [← map_pow, hy2, map_one]
    · rintro ⟨hzT, hz2⟩
      rw [← M.map_T0] at hzT
      obtain ⟨y, hyT, rfl⟩ := hzT
      refine ⟨y, ⟨hyT, M.ρ_inj ?_⟩, rfl⟩
      rw [map_pow, hz2, map_one]

theorem CoverModel.card_sq_W0_tE {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.W0 // (y : E) ^ 2 = M.tE} = 48 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_W0]
  exact harW0_sq_c M.rep_tE

theorem CoverModel.card_sq_W0_z2E {E : Type} [Group E] (M : CoverModel E) :
    Nat.card {y : M.W0 // (y : E) ^ 2 = M.tE * M.z1E} = 16 := by
  rw [card_sq_map M.ρ M.ρ_inj, M.map_W0, map_mul]
  exact harW0_sq_z2 (Rep.compT M.rep_tE M.rep_z1E)

end WMaps

end CFSG.EvenSporadicStandard.TwoHS
