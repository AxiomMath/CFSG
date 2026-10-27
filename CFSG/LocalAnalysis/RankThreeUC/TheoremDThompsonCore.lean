module

public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeUC.ModuleRank
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
import CFSG.LocalAnalysis.RankThreeUC.TheoremDThompson

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

@[expose] def thompsonCore (M T : Subgroup G) : Subgroup G :=
  ⨆ m : M, (thompsonSubgroup T).map (MulAut.conj (m : G)).toMonoidHom

omit [Finite G] in
theorem thompsonSubgroup_le_thompsonCore (M T : Subgroup G) :
    thompsonSubgroup T ≤ thompsonCore M T := fun x hx =>
  mem_iSup_of_mem (1 : M) ⟨x, hx, by simp⟩

omit [Finite G] in
theorem le_normalizer_thompsonCore (M T : Subgroup G) :
    M ≤ normalizer (thompsonCore M T : Set G) :=
  le_normalizer_iSup_conj M _

omit [Finite G] in
theorem thompsonCore_le {M T : Subgroup G} (hTM : T ≤ M) : thompsonCore M T ≤ M :=
  iSup_le fun m => by
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hTM (thompsonSubgroup_le' T hx))) (M.inv_mem m.2)

theorem le_sup_normalizer_thompsonSubgroup {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    M ≤ thompsonCore M T ⊔ (M ⊓ normalizer (thompsonSubgroup T : Set G)) := by
  have hLM := thompsonCore_le hT.le
  have hn := le_normalizer_thompsonCore M T
  have hS := hT.inf_of_le_normalizer hLM hn
  have hJ : thompsonSubgroup (T ⊓ thompsonCore M T) = thompsonSubgroup T :=
    thompsonSubgroup_eq_of_le inf_le_left
      (le_inf (thompsonSubgroup_le' T) (thompsonSubgroup_le_thompsonCore M T))
  refine (le_sup_inf_normalizer_of_isSylowOf hLM hn hS).trans
    (sup_le_sup_left (inf_le_inf_left M ?_) _)
  rw [← hJ]
  exact normalizer_le_normalizer_thompsonSubgroup _

namespace IsWitnessGen

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem two_le_pRank_normalizer_thompson_or_core (hS : StandingGen G)
    (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (thompsonSubgroup T : Set G)) ∨
      2 ≤ CFSG.Open.pRank p (thompsonCore M T) :=
  (two_le_pRank_or_of_le_sup hp.prime hp.odd (thompsonCore_le hT.le)
    (le_normalizer_thompsonCore M T) inf_le_left (le_sup_normalizer_thompsonSubgroup hT)
    (hw.three_le_pRank hp)).symm

theorem normalizer_le_of_pRank_thompsonCore_le_one (hS : StandingGen G)
    (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (h : CFSG.Open.pRank p (thompsonCore M T) ≤ 1) : normalizer (T : Set G) ≤ M := by
  have h2 := (hw.two_le_pRank_normalizer_thompson_or_core hS hp hT).resolve_right (by omega)
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  exact hw.normalizer_le_of_normalizer_le hT.isPGroup (thompsonSubgroup_le' T)
    (thompsonSubgroup_ne_bot hT1) (normalizer_le_normalizer_thompsonSubgroup T) h2

end IsWitnessGen

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_le_of_pRank_thompsonCore_le_one (hS : Standing G)
    (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (h : CFSG.Open.pRank p (thompsonCore M T) ≤ 1) : normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_pRank_thompsonCore_le_one hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hT h

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
