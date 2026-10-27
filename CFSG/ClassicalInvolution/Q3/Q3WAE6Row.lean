module

public import CFSG.ClassicalInvolution.Q3.Q3WAE6
public import CFSG.ClassicalInvolution.Q3.Q3WAFive
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3WExc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem oddLieType_of_model3 {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {t : StatedLieTag} {n : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1)
    (hmodel : CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t n 3 1) :
    CFSG.Blueprint.OddLieType G := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨t, n, 3, 1, Nat.prime_three, by norm_num, hadm,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩

section Chain

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.chain_E6_mid (c : ACtx3 5 Ω K z) (nd : Nodes3 c) {β : Subgroup G}
    (hβ : IsMidPartnerE3 c nd β) (h1 : Commutes β (nd.j 1)) :
    ∃ U : Fin 6 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 6, edgeE 6 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) := by
  have hD : ∀ a b : ℕ, a < 5 → b < 5 → a ≠ b → ¬ b = a + 1 → ¬ a = b + 1 →
      Commutes (nd.j a) (nd.j b) := by
    intro a b ha hb hab h1' h2'
    have : a + 2 ≤ b ∨ b + 2 ≤ a := by omega
    rcases this with h | h
    · exact nd.far a ha b hb h
    · exact (nd.far b hb a ha h).symm
  obtain ⟨W₂, hW₂⟩ := hβ.p2
  have b0 := hβ.zero
  have b3 := hβ.three
  have b4 := hβ.four
  refine ⟨![nd.j 0, β, nd.j 1, nd.j 2, nd.j 3, nd.j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (nd.mem 0 (by norm_num)).1
    · exact hβ.mem
    all_goals exact (nd.mem _ (by norm_num)).1
  · intro i k hik h1' h2'
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1' h2' ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact h1 | exact h1.symm | exact b3 | exact b3.symm
      | exact b4 | exact b4.symm
      | exact hD _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact ⟨W₂, hW₂⟩
      | exact nd.pair 0 (by norm_num) | exact nd.pair 1 (by norm_num)
      | exact nd.pair 2 (by norm_num) | exact nd.pair 3 (by norm_num)

@[expose] def EndDichotomyE3 (c : ACtx3 5 Ω K z) : Prop :=
  ∀ nd : Nodes3 c, ∀ β₁ β₂ : Subgroup G, IsPartnerE3 c nd β₁ → IsMidPartnerE3 c nd β₂ →
    Commutes β₁ (nd.j 3) ∨ Commutes β₂ (nd.j 1)

end Chain


theorem exists_psi_E6_3 (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E6 0 3 1)
    {X : Type} [Group X] (U : Fin 6 → Subgroup X)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E6 0 3 1 Nat.prime_three).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := weakCT3_e6 hadm (F := GaloisField 3 1) card_gf3
    (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k)) (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 3 1)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

@[expose] def EndDichotomy3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → ∀ c : ACtx3 5 (conjClass3 K) K z, EndDichotomyE3 c

theorem piece3SL6_of_dich (h3 : OddThreeFreeInput) (hd : EndDichotomy3Input) : Piece3SL6 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (m := 5) (by norm_num) hR.inClass hK hR.cls hshape
  let c : ACtx3 5 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β₁, hβ₁⟩ := c.exists_partnerE nd hsingle
  obtain ⟨β₂, hβ₂⟩ := c.exists_partnerMidE nd hsingle
  rcases hd G K z hR c nd β₁ β₂ hβ₁ hβ₂ with h3' | h1
  ·
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_A7 nd hβ₁ h3'
    obtain ⟨ψ, -, -, -, -, hmodel⟩ := c.toACore3.typeA_of_chain hsingle hconn U hUΩ hcomm hpair
    exact Or.inl (oddLieType_of_psl_model3 hnab (by norm_num) hmodel)
  ·
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_E6_mid nd hβ₂ h1
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
      hsingle hconn hR.cls hshape hP1 (h3 G K z hR) Ψ hker hΩψ
    have hgen : ⨆ k, U k = ⊤ := by
      rw [← hrange]
      exact MonoidHom.range_eq_top.mpr hsurj
    obtain ⟨-, -, -, -, -, hmodel, -⟩ := weakCT3_e6 hadm (F := GaloisField 3 1) card_gf3 U hgen
      hcomm hpair
    exact Or.inl (oddLieType_of_model3 hnab hadm hmodel)

end CFSG.ClassicalInvolution.Q3.Q3W
