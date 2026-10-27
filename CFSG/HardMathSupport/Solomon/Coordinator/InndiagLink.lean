module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {F : Type} [Field F]

theorem isInnDiagPSL_three_iff_isConjByGL {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) (α : MulAut Y) :
    IsInnDiagPSL 3 e α ↔
      LocalBalance.Lemma54Ns.IsConjByGL (CFSG.Open.StatedSL 3 F) (MulAut.congr e α) :=
  ⟨fun ⟨g, hg⟩ => ⟨g, mem_normalizer_statedSL g, hg⟩, fun ⟨g, _, hg⟩ => ⟨g, hg⟩⟩

theorem isInnDiagPSL_three_iff {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) (α : MulAut Y) :
    IsInnDiagPSL 3 e α ↔ α ∈ ((stdPinnedPSL 3 F).comap (e.trans (psiO F))).inndiag := by
  rw [isInnDiagPSL_three_iff_isConjByGL, PinnedAut.mem_comap_inndiag, stdPinnedPSL_inndiag,
    congr_trans]
  refine ⟨LocalBalance.AutL3.congr_psiO_mem_linearAutGroup, fun h => ?_⟩
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 h
  exact isConjByGL_of_congr_eq_conjAut F _ A hA.symm

theorem isInnDiagPSL_three_iff_mem_innAutDerived [Finite F] {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) (α : MulAut Y) :
    IsInnDiagPSL 3 e α ↔ α ∈ innAutDerived Y := by
  rw [isInnDiagPSL_three_iff, comap_stdPinnedPSL_three_inndiag_eq]

section Unitary

variable {p f : ℕ}

theorem mem_unitaryIsom3_iff_pow (hF : UnitaryFieldData p f F) {g : GL (Fin 3) F} :
    g ∈ unitaryIsom3 hF ↔
      ((g : Matrix (Fin 3) (Fin 3) F).map (· ^ p ^ f))ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
  Iff.rfl

theorem isInnDiagPSU_three_iff (hF : UnitaryFieldData p f F) {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) (α : MulAut Y) :
    IsInnDiagPSU 3 (p ^ f) e α ↔
      α ∈ ((stdPinnedPSU3 hF).comap (e.trans (psuO hF).symm)).inndiag := by
  rw [PinnedAut.mem_comap_inndiag]
  change _ ↔ ∃ A, psuConj hF A = _
  have key : ∀ s : unitarySU p f F 3,
      MulAut.congr (e.trans (psuO hF).symm) α (unitaryProj hF 3 s) =
        (psuO hF).symm (e (α (e.symm (psuO hF (unitaryProj hF 3 s))))) := by
    intro s
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm]
  constructor
  · rintro ⟨g, hgU, hg⟩
    set A : unitaryIsom3 hF := ⟨g, (mem_unitaryIsom3_iff_pow hF).2 hgU⟩
    refine ⟨A, ?_⟩
    ext x
    obtain ⟨s, rfl⟩ := unitaryProj_surjective hF 3 x
    rw [key s]
    have h1 : psuO hF (unitaryProj hF 3 s) =
        (QuotientGroup.mk (⟨s.1, s.2⟩ : CFSG.Open.StatedSU 3 (p ^ f) F) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) :=
      psuO_proj hF s
    have h2 : psuO hF (unitaryProj hF 3 (suConj hF A s)) =
        (QuotientGroup.mk (⟨(suConj hF A s).1, (suConj hF A s).2⟩ :
          CFSG.Open.StatedSU 3 (p ^ f) F) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) :=
      psuO_proj hF _
    rw [h1, hg ⟨s.1, s.2⟩ ⟨(suConj hF A s).1, (suConj hF A s).2⟩ (coe_suConj A s), ← h2,
      MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨A, hA⟩
    refine ⟨A, (mem_unitaryIsom3_iff_pow hF).1 A.2, fun s s' hs => ?_⟩
    set t : unitarySU p f F 3 := ⟨s.1, s.2⟩ with ht
    obtain rfl : s' = ⟨(suConj hF A t).1, (suConj hF A t).2⟩ :=
      Subtype.ext (hs.trans (coe_suConj A t).symm)
    have h1 : psuO hF (unitaryProj hF 3 t) =
        (QuotientGroup.mk s : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) :=
      psuO_proj hF t
    have h2 : psuO hF (unitaryProj hF 3 (suConj hF A t)) =
        (QuotientGroup.mk (⟨(suConj hF A t).1, (suConj hF A t).2⟩ :
          CFSG.Open.StatedSU 3 (p ^ f) F) :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) :=
      psuO_proj hF _
    have h3 := key t
    rw [← hA, h1] at h3
    have h4 : e (α (e.symm (QuotientGroup.mk s))) =
        psuO hF (psuConj hF A (unitaryProj hF 3 t)) := by
      rw [h3, MulEquiv.apply_symm_apply]
    rw [h4, ← h2]
    rfl

theorem isInnDiagPSU_three_iff_mem_innAutDerived (hF : UnitaryFieldData p f F) (hq : 2 < p ^ f)
    {Y : Type} [Group Y] (e : Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F))
    (α : MulAut Y) : IsInnDiagPSU 3 (p ^ f) e α ↔ α ∈ innAutDerived Y := by
  rw [isInnDiagPSU_three_iff hF, comap_stdPinnedPSU3_inndiag_eq hF hq]

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator
