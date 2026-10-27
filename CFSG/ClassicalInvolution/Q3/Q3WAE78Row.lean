module

public import CFSG.ClassicalInvolution.Q3.Q3WAE78

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem oddLieType_of_chainE7_3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 1 (CompData.model .POmegaPlus 6) Ω z) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) (U : Fin 7 → Subgroup G) (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨hp, le_rfl, by norm_num⟩
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_E7_3 hadm U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel3_E7 hadm
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E7 0 3 1 hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E7 0 3 1 Nat.prime_three).D
      (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E7 0 3 1 Nat.prime_three).K :=
    rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup ⟨0, by show 0 < 7; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 7; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D,
      R.map Ψ ∈ Ω :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ hΩ.conjInvariant
      (by rw [hR₀]; exact hUΩ _)
  obtain ⟨hsurj, -⟩ := routeD_core3 (le_refl 1) hsc
    (ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) hp trivial hadmY) M hΩ hex hK₀
    hsingle hconn hz hshape hP1 hO3 Ψ hker hΩψ
  have hgen : ⨆ k, U k = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT3_e7 hadm (F := GaloisField 3 1) card_gf3 U hgen
    hcomm hpair
  exact oddLieType_of_model3 hnab hadm hmodel

theorem oddLieType_of_chainE8_3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z) (hshape : LocalShapeC3 1 (CompData.model .E7 0) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (U : Fin 8 → Subgroup G)
    (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E8 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : StatedLieAdmissible .E7 0 3 1 := ⟨hp, le_rfl, rfl⟩
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_E8_3 hadm U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel3_E8 hadm
  have hsc : FundamentalSingleClass .E8 (modelUniv .E8 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E8 0 3 1 hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E8 0 3 1 Nat.prime_three).D
      (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E8 0 3 1 hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E8 0 3 1 Nat.prime_three).K :=
    rankOne (modelUniv .E8 0 3 1 Nat.prime_three).D.rootGroup ⟨0, by show 0 < 8; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 8; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 3 1 Nat.prime_three).D,
      R.map Ψ ∈ Ω :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ hΩ.conjInvariant
      (by rw [hR₀]; exact hUΩ _)
  obtain ⟨hsurj, -⟩ := routeD_core3 (le_refl 1) hsc
    (ModelFacts.finite_modelUniv (t := .E7) (by norm_num) hp trivial hadmY) M hΩ hex hK₀
    hsingle hconn hz hshape hP1 hO3 Ψ hker hΩψ
  have hgen : ⨆ k, U k = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT3_e8 hadm (F := GaloisField 3 1) card_gf3 U hgen
    hcomm hpair
  exact oddLieType_of_model3 hnab hadm hmodel

@[expose] def ChainPiece3E7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .POmegaPlus 6) (conjClass3 K) z →
      ∃ U : Fin 7 → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
        (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j)) ∧
        ∀ i j : Fin 7, edgeE 7 i j →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

@[expose] def ChainPiece3E8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
      ∃ U : Fin 8 → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
        (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j)) ∧
        ∀ i j : Fin 8, edgeE 8 i j →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem piece3E7_of_chain (h3 : OddThreeFreeInput) (h : ChainPiece3E7) : Piece3E7 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainE7_3 hnab hR.inClass hex hK hsingle hconn hR.cls hshape hP1
    (h3 G K z hR) U hUΩ hcomm hpair)

theorem piece3E8_of_chain (h3 : OddThreeFreeInput) (h : ChainPiece3E8) : Piece3E8 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainE8_3 hnab hR.inClass hex hK hsingle hconn hR.cls hshape hP1
    (h3 G K z hR) U hUΩ hcomm hpair)

end CFSG.ClassicalInvolution.Q3.Q3W
