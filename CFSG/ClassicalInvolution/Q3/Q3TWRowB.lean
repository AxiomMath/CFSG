module

public import CFSG.ClassicalInvolution.Q3.Q3TWModelB
public import CFSG.ClassicalInvolution.Q3.Q3WAE6Row

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false

theorem lieModel_of_surjective_simple3 {K G : Type} [Group K] [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (ψ : K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {t : StatedLieTag} {n : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) t n 3 1) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t n 3 1 := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hZ' : Subgroup.center G = (Subgroup.center K).map ψ := by
    rw [hZ]
    symm
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨k, hk, rfl⟩
    have h : ψ k ∈ Subgroup.center G := Subgroup.map_center_le_center hsurj ⟨k, hk, rfl⟩
    rw [hZ, Subgroup.mem_bot] at h
    exact h
  exact lieModel_of_mulEquiv (centerQuotientEquivOfSurjective ψ hsurj hker hZ') hmodel


theorem oddLieType_of_chainB3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {N : ℕ} (hN : 5 ≤ N) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 2 (CompData.model .POmegaOdd (N - 2)) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (hW : WeakCT3OddMap N)
    (hΘ : LeviEmbed3Odd) (U : Fin N → Subgroup G)
    (hUΩ : ∀ k : Fin N, k.val + 1 < N → U k ∈ Ω)
    (hcomm : ∀ i j : Fin N, i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin N, i.val + 1 = j.val → j.val + 1 < N →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin N, i.val + 2 = N → j.val + 1 = N →
      ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ N := by omega
  have hn3' : 3 ≤ N - 2 := by omega
  have hadm : StatedLieAdmissible .POmegaOdd N 3 1 := ⟨hp, le_rfl, hn3, by norm_num⟩
  have hadmY : StatedLieAdmissible .POmegaOdd (N - 2) 3 1 := ⟨hp, le_rfl, hn3', by norm_num⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd N 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd N 3 1 hp hfundM hadm
      (by decide) (by decide)
  have hscT' : FundamentalSingleClass .POmegaOdd (oddDatum N (GaloisField 3 1)) := hscT
  have hfinY : Finite (modelUniv .POmegaOdd (N - 2) 3 1 hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) hp hfundM hadmY
  obtain ⟨M⟩ := nonempty_extModel3_odd hN hΘ
  obtain ⟨ψ0, hker0, hψ0⟩ := hW U hcomm hpair hsp
  have hΩψ : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum N (GaloisField 3 1)),
      R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (oddDatum N (GaloisField 3 1)).rootGroup
      (zeroB (n := N) (by omega)))
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (by simp only [zeroB_val]; omega)) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ (hUΩ _ (by simp only [zeroB_val]; omega))
  obtain ⟨hsurj, -⟩ := routeD_core3 (by norm_num) hscT hfinY M hΩ hex hK₀ hsingle hconn hz hshape
    hP1 hO3 ψ0 hker0 hΩψ
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadOdd N (GaloisField 3 1)) ⧸
        Subgroup.center (spinGroup (quadOdd N (GaloisField 3 1)))) .POmegaOdd N 3 1 :=
    (curtisTitsConclusion_spinOdd.{0} hadm (by rw [card_gf3, pow_one])).1.2.2
  exact oddLieType_of_model3 hnab hadm (lieModel_of_surjective_simple3 hnab ψ0 hsurj hker0 hmodel)

@[expose] def ChainPiece3TwinB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ N : ℕ, 5 ≤ N →
      LocalShapeC3 2 (CompData.model .POmegaOdd (N - 2)) (conjClass3 K) z →
      ∃ U : Fin N → Subgroup G, (∀ k : Fin N, k.val + 1 < N → U k ∈ conjClass3 K) ∧
        (∀ i j : Fin N, i.val + 1 < j.val → Commutes (U i) (U j)) ∧
        (∀ i j : Fin N, i.val + 1 = j.val → j.val + 1 < N →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
        ∀ i j : Fin N, i.val + 2 = N → j.val + 1 = N →
          ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem piece3TwinB_of_chain (h3 : OddThreeFreeInput) (hW : ∀ N : ℕ, 5 ≤ N → WeakCT3OddMap N)
    (hΘ : LeviEmbed3Odd) (h : ChainPiece3TwinB) : Piece3TwinB := by
  rintro a t n ⟨rfl, rfl, hn⟩ G _ _ _ hnab K z hR hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeC3 2 (CompData.model .POmegaOdd (n + 2 - 2)) (conjClass3 K) z := by
    rw [hn']
    exact hshape
  obtain ⟨U, hUΩ, hcomm, hpair, hsp⟩ := h G hnab K z hR (n + 2) (by omega) hS'
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainB3 hnab (N := n + 2) (by omega) hR.inClass hex hK hsingle hconn
    hR.cls hS' hP1 (h3 G K z hR) (hW _ (by omega)) hΘ U hUΩ hcomm hpair hsp)

end CFSG.ClassicalInvolution.Q3.Q3TW
