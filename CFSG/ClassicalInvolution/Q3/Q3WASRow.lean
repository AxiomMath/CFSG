module

public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3WAE6Row

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem oddLieType_of_chain_E6_3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    (hO3 : LocalOddThreeFree3 (conjClass3 K) z)
    (hshape : LocalShapeC3 1 (CompData.model .PSL 6) (conjClass3 K) z)
    (U : Fin 6 → Subgroup G) (hUΩ : ∀ i, U i ∈ conjClass3 K)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E6 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 6 3 1 :=
    ⟨hp, le_rfl, by norm_num, by simp, by simp⟩
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_E6_3 hadm U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel3_E6 hadm
  have hsc : FundamentalSingleClass .E6 (modelUniv .E6 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E6 0 3 1 hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E6 0 3 1 Nat.prime_three).D
      (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E6 0 3 1 hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E6 0 3 1 Nat.prime_three).K :=
    rankOne (modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup ⟨0, by show 0 < 6; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 6; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Nat.prime_three).D,
      R.map Ψ ∈ conjClass3 K :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ
      hR.inClass.conjInvariant (by rw [hR₀]; exact hUΩ _)
  obtain ⟨hsurj, -⟩ := routeD_core3 (le_refl 1) hsc
    (ModelFacts.finite_modelUniv (t := .PSL) (by norm_num) hp trivial hadmY) M hR.inClass hex hK
    hsingle hconn hR.cls hshape hP1 hO3 Ψ hker hΩψ
  have hgen : ⨆ k, U k = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT3_e6 hadm (F := GaloisField 3 1) card_gf3 U hgen
    hcomm hpair
  exact oddLieType_of_model3 hnab hadm hmodel

theorem piece3SL6_proved (h3 : OddThreeFreeInput) : Piece3SL6 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hshape' := hshape
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (m := 5) (by norm_num) hR.inClass hK hR.cls hshape
  let c : ACtx3 5 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨ι, -, D, -⟩ := hshape'
  obtain ⟨β, hβ, hadp⟩ := c.adapted_partner (RouteD.Gaps.fundNoncentral 3) D hsingle nd
  obtain ⟨wβ, hwβ⟩ := hβ.cl
  rcases c.commutes_or_stdpair_end nd hsingle hβ hwβ (hadp wβ hwβ) with h3' | h3'
  ·
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_A7 nd hβ h3'
    obtain ⟨ψ, -, -, -, -, hmodel⟩ := c.toACore3.typeA_of_chain hsingle hconn U hUΩ hcomm hpair
    exact Or.inl (oddLieType_of_psl_model3 hnab (by norm_num) hmodel)
  ·
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_E6 nd hβ h3'
    exact Or.inl (oddLieType_of_chain_E6_3 hnab hR (h3 G K z hR) hshape U hUΩ hcomm hpair)

end CFSG.ClassicalInvolution.Q3.Q3W
