module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT1
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFam

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

private lemma pCoreOf_le_self {Y : Type*} [Group Y] (H : Subgroup Y) (q : ℕ) :
    pCoreOf q H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

private lemma isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hcomm, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hcomm] at hle
  haveI := hsimple
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

private lemma noInnerInduced_mono {Y : Type*} [Group Y] {W W' A : Subgroup Y} (hWW : W' ≤ W)
    (h : NoInnerInduced W A) : NoInnerInduced W' A := by
  unfold NoInnerInduced at *
  have hle : inducedAutGroup W' A ≤ inducedAutGroup W A := by
    unfold inducedAutGroup
    exact Subgroup.map_mono fun x hx => hWW (Subgroup.mem_subgroupOf.1 hx)
  exact eq_bot_iff.2 ((inf_le_inf_right _ hle).trans (eq_bot_iff.1 h))

theorem chev_hyp28One (h : IvSetting m p M D L) (h1 : Input19_20_2)
    (hch : IsChevTwo (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)))
    (hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) :
    Hyp28One (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M) := by
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ :=
    isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hNI : NoInnerInduced (sigmaFam (tl M D) (Hfam M D)) (tl M L) :=
    (h1 (Mt M) p hp hp2 (tl M L) hcomp hch (tl M D) (Hfam M D) (hfam_family h)).2.2
  have hle : tl M (gammaD D) ≤ sigmaFam (tl M D) (Hfam M D) :=
    (tl_gammaD_le_pCore h).trans (pCoreOf_le_self _ 2)
  refine ⟨⟨isQuasisimple_of_open hcomp.2.2, hch⟩, fun hA => hAlt hA.2, noInnerInduced_mono hle hNI⟩

theorem chev_fpf (h : IvSetting m p M D L) (h2 : Input19_20_3)
    (hch : IsChevTwo (↥(tl M L) ⧸ Subgroup.center ↥(tl M L))) (n : ℕ) (ε : Bool) (hn : 1 ≤ n)
    (hΩ : IsOmegaTwo ε (n + 1) ↥(tl M L)) : HasFixedPointFreeOrder ε n p := by
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ :=
    isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hnc : ¬ sigmaFam (tl M D) (Hfam M D) ≤ Subgroup.centralizer (↑(tl M L) : Set (Mt M)) := by
    intro hle
    exact not_tl_gammaD_le_centralizer h
      ((tl_gammaD_le_pCore h).trans ((pCoreOf_le_self _ 2).trans hle))
  exact (h2 (Mt M) p hp hp2 (tl M L) hcomp hch (tl M D) (Hfam M D) (hfam_family h) n ε hn hΩ
    hnc).2

theorem chev_beta_module {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h)) (e : ↥(tl M L) ≃* ↥(StatedOmega Q))
    (hmod : ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
      ChiefFactorIso L U V (e.toMonoidHom.comp (toTl M L h.hL.1))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v)) :
    ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
      ChiefFactorIso L U V
        (((MulEquiv.ofBijective (psiL h) hψ).symm.trans e).toMonoidHom.comp (barMap p h.hL.1))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v) := by
  have key : ((MulEquiv.ofBijective (psiL h) hψ).symm.trans e).toMonoidHom.comp (barMap p h.hL.1)
      = e.toMonoidHom.comp (toTl M L h.hL.1) := by
    rw [← psiL_comp_toTl h, ← MonoidHom.comp_assoc]
    congr 1
    refine MonoidHom.ext fun x => ?_
    exact congrArg e ((MulEquiv.ofBijective (psiL h) hψ).symm_apply_apply x)
  intro V U hVU
  rw [key]
  exact hmod V U hVU

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
