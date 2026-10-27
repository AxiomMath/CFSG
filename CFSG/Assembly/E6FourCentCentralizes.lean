module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private lemma e6Four_isRoot_of_mem_rationalRoots {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 5) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) : IsRoot Tag.E6 γ := by
  obtain ⟨k, δ, hδ, hγeq⟩ := hγ
  have hδroot : IsRoot Tag.E6 δ := hδ.1.1
  rw [hγeq]
  clear hγeq hδ
  induction k with
  | zero => simpa using hδroot
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (S.frob.isRoot_iff _).2 ih

theorem e6Four_rootDiag_commute {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1)
    {x : ModGL Tag.E6 L} (hx : x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    Commute (rootDiagUnit Tag.E6 b) x := by
  have hspan : rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) ≤
      Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)) := by
    refine iSup_le fun γ => iSup_le fun hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    change pinnedX Tag.E6 L γ c ∈ Subgroup.centralizer {rootDiagUnit Tag.E6 b}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hγroot : IsRoot Tag.E6 γ := e6Four_isRoot_of_mem_rationalRoots S i hγ
    have hconj := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (K := L) b hγroot c
    rw [hb γ hγ, Units.val_one, one_mul] at hconj
    have hcomm : rootDiagUnit Tag.E6 b * pinnedX Tag.E6 L γ c =
        pinnedX Tag.E6 L γ c * rootDiagUnit Tag.E6 b := by
      have h := congrArg (· * rootDiagUnit Tag.E6 b) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    exact hcomm.symm
  have hle : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [rationalSpan]
    exact inf_le_left
  have hcomp : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)) :=
    (Subgroup.commutator_le_of_le hle hle).trans hspan
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcomp hx)).symm

end CFSG.Assembly

end
