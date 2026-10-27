module

public import CFSG.GH74.Generic.S45.LBridge
public import CFSG.GH74.Generic.S45.LEvenOrth
public import CFSG.GH74.Generic.S45.LEvenRee
public import CFSG.GH74.Generic.S45.LEvenExc

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem concl_of_outcome {K : Type} [Group K] [Finite K]
    {y : MulAut K} {L : Subgroup K} (hyp : Hyp1310 K y L)
    {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    (hL5 : HasL2Model ↥L (fun x => x = 5)) (hout : yb ∉ inner (K ⧸ Subgroup.center K))
    (hS : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2 ∨
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 2 2 ∨
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 4) : Concl1310 K y L := by
  refine ⟨hL5, ?_, fun _ => ?_⟩
  · rcases hS with h | h | h
    · exact Or.inl (Or.inl ⟨by decide, h⟩)
    · exact Or.inr (Or.inl (Or.inl ⟨by decide, h⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have hKq : IsQuasisimple K := ⟨hyp.1.1.1, hyp.1.1.2.1, hyp.1.1.2.2⟩
      have hz2 : IsPGroup 2 ↥(Subgroup.center K) := by
        have := hyp.data
        exact this.2.1
      have hLie : LieModel (K ⧸ Subgroup.center K) .PSL 2 2 4 := Or.inl ⟨by decide, h⟩
      have hZ : Subgroup.center K = ⊥ :=
        CFSG.GH74.KGroups.noTwoCover_even (K ⧸ Subgroup.center K) (Or.inr (Or.inl hLie)) K hKq hz2
          ⟨MulEquiv.refl _⟩
      let e : K ⧸ Subgroup.center K ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      exact CFSG.GH74.lieModel_of_mulEquiv e hLie
  · rintro ⟨k, hk⟩
    exact LAlt.not_inner_of_not_inner y yb hyb (fun s h => hout ⟨s, h.symm⟩) k hk.symm

theorem b_1310_even
    : B_1310_even := by
  intro K _ _ y L hyp hLie
  obtain ⟨yb, Lb, q, hyb, hQ, hmodelL⟩ := hyp.quot_data
  have hSs : IsSimpleGroup (K ⧸ Subgroup.center K) := hyp.1.1.2.1
  have hSnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := hyp.1.1.2.2
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := center_eq_bot_of_simple_nonab hSs hSnab
  rcases hLie with ⟨t, n, f, hmodel⟩ | ⟨t, f, ht, hmodel⟩ | ⟨t, f, ht, hmodel⟩ | ⟨f, hmodel⟩
  · by_cases htc : t = .PSL ∨ t = .PSU ∨ t = .PSp
    · obtain ⟨hq5, hout, hS⟩ := classical_outcome hSs hSnab htc hmodel hQ
      exact concl_of_outcome hyp hyb (hmodelL _ hq5) hout hS
    · exfalso
      cases t
      · exact htc (Or.inl rfl)
      · exact htc (Or.inr (Or.inl rfl))
      · exact htc (Or.inr (Or.inr rfl))
      · exact hmodel.1.2.2.2 rfl
      · exact orthogonal_false hSs hSnab (Or.inl rfl) hmodel hQ
      · exact orthogonal_false hSs hSnab (Or.inr rfl) hmodel hQ
      all_goals exact hmodel.2
  · exact (even_exc_false hmodel hQ).elim
  · have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      simpa [reeTitsTags] using ht
    rcases ht' with rfl | rfl | rfl
    · exact absurd hmodel.1.2.2.2.1 (by norm_num)
    · exact (even_twistedF4_false hSs hSnab hmodel hQ).elim
    · exact (even_tits_false hSs hSnab hmodel hQ).elim
  · exact (suzuki_false hmodel hZ hQ).elim

end CFSG.GH74.Generic.S45
