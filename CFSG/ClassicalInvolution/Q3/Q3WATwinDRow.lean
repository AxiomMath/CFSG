module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinD
public import CFSG.ClassicalInvolution.Q3.Q3WAE6Row

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem exists_psi_of_chain_plus3 {N : ℕ} (hadm : StatedLieAdmissible .POmegaPlus N 3 1)
    {G : Type} [Group G] (U : Fin N → Subgroup G)
    (hcomm : ∀ i j : Fin N, i ≠ j → ¬ edgeD N i j → ¬ edgeD N j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin N, edgeD N i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ ψ : spinGroup (quadPlus N (GaloisField 3 1)) →* G, ψ.ker ≤ Subgroup.center _ ∧
      ψ.range = ⨆ i, U i ∧
      ∀ k : Fin N, (rankOne (plusDatum N (GaloisField 3 1)
        (by have := hadm.2.2; omega)).rootGroup k).map ψ = U k := by
  have hn3 : 3 ≤ N := by have := hadm.2.2; omega
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  obtain ⟨Ψ, hsurj, hker, -, -, -, hnodes⟩ := weakCT3_spinPlus hadm hn3 card_gf3
    (X := ↥Gs) (fun i => (U i).subgroupOf Gs) (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 a ha b hb => Subtype.ext (hcomm i j hij h1 h2 a.1
      (Subgroup.mem_subgroupOf.mp ha) b.1 (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := hpair i j hij
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ, ?_, ?_, fun k => ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle k)]


theorem oddLieType_of_chainD3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {N : ℕ} (hN : 6 ≤ N) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 2 (CompData.model .POmegaPlus (N - 2)) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (U : Fin N → Subgroup G)
    (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin N, i ≠ j → ¬ edgeD N i j → ¬ edgeD N j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin N, edgeD N i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ N := by omega
  have hn3' : 3 ≤ N - 2 := by omega
  have hadm : StatedLieAdmissible .POmegaPlus N 3 1 := ⟨hp, le_rfl, by show 4 ≤ N; omega⟩
  have hadmY : StatedLieAdmissible .POmegaPlus (N - 2) 3 1 :=
    ⟨hp, le_rfl, by show 4 ≤ N - 2; omega⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have e2 := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3'
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus N 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ 3 _ _ hfundM hadm (by decide)
      (by decide)
  have hscY : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus (N - 2) 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ 3 _ _ hfundM hadmY (by decide)
      (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum N (GaloisField 3 1) hn3) := by
    revert hscT
    rw [e1]
    exact id
  have hscY' : FundamentalSingleClass .POmegaPlus (plusDatum (N - 2) (GaloisField 3 1) hn3') := by
    revert hscY
    rw [e2]
    exact id
  have hfinY : Finite (modelUniv .POmegaPlus (N - 2) 3 1 hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) hp hfundM hadmY
  have hM : Nonempty (ExtModel3 .POmegaPlus N .POmegaPlus (N - 2) 2) := by
    show Nonempty (ExtModel3U .POmegaPlus .POmegaPlus (modelUniv .POmegaPlus N 3 1 hp)
      (modelUniv .POmegaPlus (N - 2) 3 1 hp) 2)
    rw [e1, e2]
    exact nonempty_extModel3U_plus hN hscT' hscY' hadmY
  obtain ⟨M⟩ := hM
  obtain ⟨ψ0, hker0, hrange0, hψ0⟩ := exists_psi_of_chain_plus3 hadm U hcomm hpair
  have hΩψ0 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum N (GaloisField 3 1) hn3),
      R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum N (GaloisField 3 1) hn3).rootGroup
      (zeroD (n := N) (by omega))) (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  have hψ : ∃ ψ : (modelUniv .POmegaPlus N 3 1 hp).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus N 3 1 hp).K ∧
      ψ.range = ⨆ i, U i ∧
      ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus N 3 1 hp).D, R.map ψ ∈ Ω := by
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

@[expose] def ChainPiece3TwinD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ N : ℕ, 6 ≤ N →
      LocalShapeC3 2 (CompData.model .POmegaPlus (N - 2)) (conjClass3 K) z →
      ∃ U : Fin N → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
        (∀ i j : Fin N, i ≠ j → ¬ edgeD N i j → ¬ edgeD N j i → Commutes (U i) (U j)) ∧
        ∀ i j : Fin N, edgeD N i j →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem piece3TwinD_of_chain (h3 : OddThreeFreeInput) (h : ChainPiece3TwinD) : Piece3TwinD := by
  rintro a t n ⟨rfl, rfl, hn⟩ G _ _ _ hnab K z hR hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeC3 2 (CompData.model .POmegaPlus (n + 2 - 2)) (conjClass3 K) z := by
    rw [hn']
    exact hshape
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z hR (n + 2) (by omega) hS'
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainD3 hnab (N := n + 2) (by omega) hR.inClass hex hK hsingle hconn
    hR.cls hS' hP1 (h3 G K z hR) U hUΩ hcomm hpair)

end CFSG.ClassicalInvolution.Q3.Q3W
