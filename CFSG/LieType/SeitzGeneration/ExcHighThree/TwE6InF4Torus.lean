module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLM2
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.Open

set_option linter.unusedSectionVars false


def rhoE6' : Equiv.Perm (Fin (Tag.rank .E6)) := TwistTag.E6.perm

def branchDelta : Fin (Tag.rank .E6) → ℤ := ![2, 3, 4, 6, 4, 2]

theorem iform_branchDelta (l : Fin (Tag.rank .E6)) :
    CFSG.LieType.Steinberg.Adjoint.iform branchDelta (Pi.single l 1) =
      if l = CFSG.RankThree.E6.e6Index 3 then 1 else 0 := by
  rw [CFSG.SeitzReduction.E6Pilot.iform_single_right_E6]
  fin_cases l <;> decide

theorem corootTuple_branch_apply {k : Type} [Field k] (ω : kˣ) (l : Fin (Tag.rank .E6)) :
    CFSG.SeitzReduction.E6Pilot.corootTuple branchDelta ω l =
      if l = e6Index 3 then ω else 1 := by
  rw [CFSG.SeitzReduction.E6Pilot.corootTuple, iform_branchDelta]
  split_ifs <;> simp

theorem zSplit_twE6_good (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (ω : kˣ) :
    ∃ z : twistedFixedGroup TwistTag.E6 k (RingHom.id k), e6FixedF4EquivAll k z = zSplit k ω ∧
      ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) → ∀ d : K,
        Commute (baseChangeGL (algebraMap k K) (z : ModGL TwistTag.E6.tag k)) (xUnit Tag.E6 K i d) ∧
        Commute (baseChangeGL (algebraMap k K) (z : ModGL TwistTag.E6.tag k)) (yUnit Tag.E6 K i d) := by
  classical
  set a := CFSG.SeitzReduction.E6Pilot.corootTuple branchDelta ω with ha_def
  have ha_val : ∀ l : Fin (Tag.rank .E6), a l = if l = e6Index 3 then ω else 1 :=
    corootTuple_branch_apply ω
  have hperm3 : rhoE6' (e6Index 3) = e6Index 3 := rfl
  have ha_rho : ∀ i : Fin (Tag.rank .E6), a (rhoE6' i) = a i := by
    intro i
    rw [ha_val, ha_val]
    by_cases hi : i = e6Index 3
    · rw [hi, hperm3]
    · have hne : rhoE6' i ≠ e6Index 3 := by
        intro h
        apply hi
        rw [← hperm3] at h
        exact rhoE6'.injective h
      rw [if_neg hi, if_neg hne]
  have hmem : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 a ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨
      CFSG.SeitzReduction.E6Pilot.rootDiagUnit_corootTuple_mem_adjointGroup branchDelta ω,
      twistHom_rootDiagUnit (t := TwistTag.E6) (σ := RingHom.id k) ?_⟩
    intro i
    exact (ha_rho i).trans (Units.ext rfl)
  set z : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 a, hmem⟩ with hz
  have hF4 : e6FixedF4EquivAll k z = zSplit k ω := by
    apply Subtype.ext
    rw [coe_e6FixedF4EquivAll]
    have h : e6FixedToF4 k z = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.F4 (fun j => a (f4IndexRep j)) :=
      CFSG.SeitzReduction.F4Pilot.e6FixedToF4_rootDiagUnit ha_rho hmem
    rw [h]
    show (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.F4 (fun j => a (f4IndexRep j)) : ModGL Tag.F4 k) =
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) : ModGL Tag.F4 k)
    congr 2
    have hiff : ∀ j : Fin Tag.F4.rank, (f4IndexRep j = e6Index 3) ↔ (j = 1) := by decide
    funext j
    rw [ha_val, Pi.mulSingle_apply]
    simp only [hiff j]
  refine ⟨z, hF4, ?_⟩
  intro i hi d
  have hJ : a i = 1 := by
    rw [ha_val, if_neg]
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hbc : baseChangeGL (algebraMap k K) (z : ModGL TwistTag.E6.tag k) =
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 (fun l => Units.map (algebraMap k K).toMonoidHom (a l)) : ModGL Tag.E6 K) := by
    show baseChangeGL (algebraMap k K) (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 a : ModGL Tag.E6 k) = _
    rw [baseChangeGL_rootDiagUnit (algebraMap k K) a]
  have hval : ((Units.map (algebraMap k K).toMonoidHom (a i)) : K) = 1 := by
    rw [hJ]
    simp
  have hx := (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.root_diagonal_conjugation Tag.E6 K
    (fun l => Units.map (algebraMap k K).toMonoidHom (a l))).1 i d
  have hy := (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.root_diagonal_conjugation Tag.E6 K
    (fun l => Units.map (algebraMap k K).toMonoidHom (a l))).2.1 i d
  simp only [hval, Units.val_inv_eq_inv_val, inv_one, one_mul] at hx hy
  rw [hbc]
  have hcx : Commute (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 (fun l => Units.map (algebraMap k K).toMonoidHom (a l)))
      (xUnit Tag.E6 K i d) := mul_inv_eq_iff_eq_mul.1 hx
  have hcy : Commute (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 (fun l => Units.map (algebraMap k K).toMonoidHom (a l)))
      (yUnit Tag.E6 K i d) := mul_inv_eq_iff_eq_mul.1 hy
  exact ⟨hcx, hcy⟩

end CFSG.LieType.SeitzGeneration.ExcHighThree
