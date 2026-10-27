module

public import CFSG.ClassicalInvolution.Q3.Q3TSModelD5
public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TS

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem oddLieType_of_chainD5_3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 2 (CompData.model .PSL 4) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (U : Fin 5 → Subgroup G)
    (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin 5, i ≠ j → ¬ edgeD 5 i j → ¬ edgeD 5 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 5, edgeD 5 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ 5 := by omega
  have hadm : StatedLieAdmissible .POmegaPlus 5 3 1 := ⟨hp, le_rfl, by show 4 ≤ 5; omega⟩
  have hadmY : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨hp, le_rfl, by show 2 ≤ 4; omega, fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have hfundY : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .PSL := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 5 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ 3 _ _ hfundM hadm (by decide)
      (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField 3 1) hn3) := by
    revert hscT
    rw [e1]
    exact id
  have hfinY : Finite (modelUniv .PSL 4 3 1 hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) hp hfundY hadmY
  obtain ⟨M⟩ := nonempty_extModel3_D5
  obtain ⟨ψ0, hker0, hrange0, hψ0⟩ := exists_psi_of_chain_plus3 hadm U hcomm hpair
  have hΩψ0 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) hn3),
      R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum 5 (GaloisField 3 1) hn3).rootGroup
      (zeroD (n := 5) (by omega))) (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  have hψ : ∃ ψ : (modelUniv .POmegaPlus 5 3 1 hp).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 5 3 1 hp).K ∧
      ψ.range = ⨆ i, U i ∧
      ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 3 1 hp).D,
        R.map ψ ∈ Ω := by
    rw [e1]
    exact ⟨ψ0, hker0, hrange0, hΩψ0⟩
  obtain ⟨ψ, hker, hrange, hΩψ⟩ := hψ
  obtain ⟨hsurj, -⟩ := routeD_core3 (by norm_num) hscT hfinY M hΩ hex hK₀ hsingle hconn hz hshape
    hP1 hO3 ψ hker hΩψ
  have hgen : ⨆ i, U i = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT3_spinPlus hadm hn3 card_gf3 U hgen hcomm hpair
  exact oddLieType_of_model3 hnab hadm hmodel

@[expose] def ChainPiece3TwinSL4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z →
      ∃ U : Fin 5 → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
        (∀ i j : Fin 5, i ≠ j → ¬ edgeD 5 i j → ¬ edgeD 5 j i → Commutes (U i) (U j)) ∧
        ∀ i j : Fin 5, edgeD 5 i j →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem piece3TwinSL4_of_chain (h3 : OddThreeFreeInput) (h : ChainPiece3TwinSL4) :
    Piece3TwinSL4 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainD5_3 hnab hR.inClass hex hK hsingle hconn hR.cls hshape hP1
    (h3 G K z hR) U hUΩ hcomm hpair)

end CFSG.ClassicalInvolution.Q3.Q3TS
