module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpH1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

section LongPumpUp

variable {G : Type} [Group G] [Finite G]

theorem reflTransGen_pumpUpLT_self {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (h1 : pRank 2 ↥(CxK x K) ≤ 1) {c : G × Subgroup G}
    (h : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) (x, K) c) :
    c = (x, K) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [ih] at hstep
    obtain ⟨h1', h2'⟩ := pumpUpLT_self hpair h1 hstep
    exact Prod.ext h1' h2'

theorem isTwoTerminal_of_pRank_le_one {x : G} {K : Subgroup G} (hILo : IsILo 2 x K)
    (h1 : pRank 2 ↥(CxK x K) ≤ 1) : IsTwoTerminal x K := by
  have hpair : IsIL2Pair x K := ⟨hILo.1, hILo.2.2⟩
  refine ⟨hILo, ?_, ?_⟩
  · intro x' K' hpump
    have ht := (pumpUpLT_self hpair h1 hpump).1
    rw [ht] at hpump
    exact isTrivialPumpupAt_self hpair h1 K' hpump
  · intro Q hQ x' K' hpump _ _
    obtain ⟨rfl, rfl⟩ := pumpUpLT_self hpair h1 hpump
    exact hQ

end LongPumpUp

end CFSG.GH74.GLS.C3.Layer1.PumpH1

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.PumpH1

@[expose] def B_ig_6_10_h2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x : G) (K : Subgroup G), IsILo 2 x K → 2 ≤ pRank 2 ↥(CxK x K) →
      ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsTwoTerminal x' K'

theorem b_ig_6_10_of_h2 (h : B_ig_6_10_h2) : B_ig_6_10 := by
  intro G _ _ hG h3 x K hILo
  by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
  · exact h G hG h3 x K hILo h2
  · exact ⟨x, K, ⟨hILo, Relation.ReflTransGen.refl⟩, isTwoTerminal_of_pRank_le_one hILo (by omega)⟩

@[expose] def B_ivk_7_20_h2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G),
    IsIL2Pair x K → InU2 (kBar K) → ¬ InC2 (kBar K) → 2 ≤ pRank 2 ↥(CxK x K) →
      LongPumpUp 2 x K x' K' → InU2 (kBar K') ∧ ¬ InC2 (kBar K')

theorem b_ivk_7_20_of_h2 (h : B_ivk_7_20_h2) : B_ivk_7_20 := by
  intro G _ _ hG x K x' K' hpair hU2 hnC2 hlong
  by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
  · exact h G hG x K x' K' hpair hU2 hnC2 h2 hlong
  · have hc := reflTransGen_pumpUpLT_self hpair (by omega) hlong.2
    have e := Prod.mk.inj hc
    rw [e.2]
    exact ⟨hU2, hnC2⟩

end CFSG.GH74.GLS
