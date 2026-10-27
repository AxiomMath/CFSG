module

public import CFSG.ClassicalInvolution.Q3.Q3TWModelTD
public import CFSG.ClassicalInvolution.Q3.Q3TWRowB

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false


theorem oddLieType_of_chainTD3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {N : ℕ} (hN : 6 ≤ N) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 2 (CompData.model .POmegaMinus (N - 2)) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (hW : WeakCT3MinusMap N)
    (hΘ : LeviEmbed3Minus) (U : Fin (N - 1) → Subgroup G)
    (hU0 : U (twIdx0 (by omega : 3 ≤ N)) ∈ Ω)
    (hcomm : ∀ i j : Fin (N - 1), i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (N - 1), i.val + 1 = j.val → j.val + 2 < N →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (htw : ∀ i j : Fin (N - 1), i.val + 3 = N → j.val + 2 = N →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ N := by omega
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus N 3 1 := ⟨hp, le_rfl, by show 4 ≤ N; omega⟩
  have hadmY : StatedLieAdmissible .POmegaMinus (N - 2) 3 1 :=
    ⟨hp, le_rfl, by show 4 ≤ N - 2; omega⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaMinus := trivial
  have hscT : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus N 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus N 3 1 hp hfundM hadm
      (by decide) (by decide)
  have hscT' : FundamentalSingleClass .POmegaMinus (minusDatum N hirr) := hscT
  have hfinY : Finite (modelUniv .POmegaMinus (N - 2) 3 1 hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) hp hfundM hadmY
  obtain ⟨M⟩ := nonempty_extModel3_minus hN hΘ
  obtain ⟨ψ0, hker0, hψ0⟩ := hW U hcomm hpair htw
  have hk0 : (twIdx0 hn3).val + 1 < N - 1 := by simp only [twIdx0]; omega
  have hΩψ : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum N hirr), R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (minusDatum N hirr).rootGroup (twIdx0 hn3))
      (rankOne_mem_fund_minus hirr hk0) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ hU0
  obtain ⟨hsurj, -⟩ := routeD_core3 (by norm_num) hscT hfinY M hΩ hex hK₀ hsingle hconn hz hshape
    hP1 hO3 ψ0 hker0 hΩψ
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadMinus N (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ⧸
        Subgroup.center (spinGroup (quadMinus N (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) .POmegaMinus N 3 1 :=
    (curtisTitsConclusion_spinMinus.{0} hirr hadm (by rw [card_gf3, pow_one])).1.2.2
  exact oddLieType_of_model3 hnab hadm (lieModel_of_surjective_simple3 hnab ψ0 hsurj hker0 hmodel)

@[expose] def ChainPiece3TwinTD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (N : ℕ) (hN : 6 ≤ N),
      LocalShapeC3 2 (CompData.model .POmegaMinus (N - 2)) (conjClass3 K) z →
      ∃ U : Fin (N - 1) → Subgroup G, U (twIdx0 (by omega : 3 ≤ N)) ∈ conjClass3 K ∧
        (∀ i j : Fin (N - 1), i.val + 1 < j.val → Commutes (U i) (U j)) ∧
        (∀ i j : Fin (N - 1), i.val + 1 = j.val → j.val + 2 < N →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
        ∀ i j : Fin (N - 1), i.val + 3 = N → j.val + 2 = N →
          ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)

theorem piece3TwinTD_of_chain (h3 : OddThreeFreeInput) (hW : ∀ N : ℕ, 6 ≤ N → WeakCT3MinusMap N)
    (hΘ : LeviEmbed3Minus) (h : ChainPiece3TwinTD) : Piece3TwinTD := by
  rintro a t n ⟨rfl, rfl, hn⟩ G _ _ _ hnab K z hR hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeC3 2 (CompData.model .POmegaMinus (n + 2 - 2)) (conjClass3 K) z := by
    rw [hn']
    exact hshape
  obtain ⟨U, hU0, hcomm, hpair, htw⟩ := h G hnab K z hR (n + 2) (by omega) hS'
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainTD3 hnab (N := n + 2) (by omega) hR.inClass hex hK hsingle
    hconn hR.cls hS' hP1 (h3 G K z hR) (hW _ (by omega)) hΘ U hU0 hcomm hpair htw)

end CFSG.ClassicalInvolution.Q3.Q3TW
