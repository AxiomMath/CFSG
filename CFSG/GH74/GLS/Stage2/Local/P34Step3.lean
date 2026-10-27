module

public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Two
public import CFSG.GH74.GLS.Stage2.Local.P34Lift
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34Qarg
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def RankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (k = Kind.g2 ∨ k = Kind.m12) → pRank 2 G = 3

theorem step23_of (hSch : GHSchreier) (hrank : RankThree) : Step23 := by
  intro G _ _ z k S hctx H hne hCH hV h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : fittingSubgroup (HBar H) = ⊥ :=
    fitting_eq_bot_of_cores (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two) hV
  have hGH : Uniqueness.SU.SU0.GHGroup (HBar H) :=
    Uniqueness.SU.SU0.GHGroup.of_kgh_quotient hctx.std.kgh hne (pPrimeCore 2 ↥H)
  have hOut : ∀ K : Subgroup (HBar H), IsComponent K → Group.IsSolvable (Outer ↥K) :=
    fun K hK => outer_solvable_of_component hSch hGH hF hK
  obtain ⟨x, -, hx2, -, -⟩ := h2
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (HBar H), IsComponent A := by
    by_contra hno
    push Not at hno
    have hlayer : layer (HBar H) = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hno
    have hFs : generalizedFitting (HBar H) = ⊥ := by
      rw [generalizedFitting_eq_layer hF, hlayer]
    have hcen := centralizer_generalizedFitting_le (HBar H)
    rw [hFs] at hcen
    have hmem : x ∈ Subgroup.centralizer (((⊥ : Subgroup (HBar H)) : Subgroup (HBar H)) : Set (HBar H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      subst hh
      simp
    exact hx1 (Subgroup.mem_bot.1 (hcen hmem))
  by_cases hone : ∀ K : Subgroup (HBar H), IsComponent K → K = A
  ·
    have hFA : generalizedFitting (HBar H) = A := by
      rw [generalizedFitting_eq_layer hF]
      exact le_antisymm (sSup_le fun L hL => (hone L hL).le)
        (CFSG.LocalCores.component_le_layer hA)
    obtain ⟨hs, hnab⟩ := generalizedFitting_simple_of_unique hF hA hone
    refine ⟨hs, hnab, ?_⟩
    intro P hPH hPperf
    have hP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hPperf
    have h1 := commutator_barIn H hPH hP
    have h3 := perfect_le_of_unique hF hA hone (hOut A hA) h1
    rwa [hFA]
  · exfalso
    push Not at hone
    obtain ⟨B, hB, hBA⟩ := hone
    have hrk := hctx.std.rank.2
    have hH4 := open_pRank_hbar_le H
    by_cases hthree : ∃ D : Subgroup (HBar H), IsComponent D ∧ D ≠ A ∧ D ≠ B
    · obtain ⟨D, hD, hDA, hDB⟩ := hthree
      have h6 := rank_triple_le hF hA hB hD hBA.symm hDA.symm hDB.symm
      omega
    · push Not at hthree
      have hall : ∀ K : Subgroup (HBar H), IsComponent K → K = A ∨ K = B := fun K hK => by
        by_cases hKA : K = A
        · exact Or.inl hKA
        · exact Or.inr (hthree K hK hKA)
      obtain ⟨hsum, hA2, hB2⟩ := rank_pair_le hF hA hB hBA.symm
      by_cases hg : k = Kind.g2 ∨ k = Kind.m12
      · have h3 := hrank G z k S hctx hg
        omega
      · push Not at hg
        obtain ⟨Q, c, hQperf, hc2, hQ1, hQ2⟩ := qData_of_ctx hctx hg
        obtain ⟨P, f, -, hPperf, hfsurj, hfodd⟩ := exists_lift_hbar H hCH hQperf
        have hPAB : P ≤ A ⊔ B :=
          perfect_le_sup_of_two hF hA hB hBA.symm hall (hOut A hA) (hOut B hB) hPperf
        obtain ⟨hcomm, hinf⟩ := components_commute_inf hF hA hB hBA.symm
        have hA2' : Open.pRank 2 (⊤ : Subgroup ↥A) ≤ 2 := by omega
        have hB2' : Open.pRank 2 (⊤ : Subgroup ↥B) ≤ 2 := by omega
        exact q_argument hcomm hinf hA2' hB2' hPAB f hfsurj hfodd hc2 hQ1 hQ2

end CFSG.GH74.GLS.Stage2.Local.P34
