module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428NonInnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll
public import CFSG.GroupTheory.PLayer.UniqueComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428NonInn

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem t1428NonInn_exists_D4 {i : TauCeti.CFSGIndex} (hi : isD4any i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D m q =>
      rcases m with _ | _ | _ | _ | _ | m
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact ⟨q, hv, hi, rfl⟩
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

set_option linter.unusedSectionVars false


variable {Ω : Type} [Group Ω] [Finite Ω]

theorem t1428NonInn_of_r2Prop {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup Ω} {y : Ω}
    (hK : GLAPComponent p ⊤ K) (hchev : IsChevSimple 2 (PSimple p K)) (hyp : y ^ p = 1)
    (hR2 : R2Prop p y K) {J₁ J₂ : Subgroup Ω}
    (h₁ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₁)
    (h₂ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₂) : J₁ = J₂ := by
  have hI : Ipart p K y ≠ ⊥ := by
    intro h
    apply CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' h₁
    have hle : J₁ ≤ Ipart p K y := le_sSup h₁
    rw [h] at hle
    exact le_bot_iff.1 hle
  obtain ⟨hcomp, -⟩ := FR.i91CompAt_holds (G := Ω) hp hp2 ⊤ K y hK hchev hyp hR2 hI
  rw [CFSG.glaPComponent_eq_of_glaPLayer hcomp rfl h₁, CFSG.glaPComponent_eq_of_glaPLayer hcomp rfl h₂]

theorem t1428NonInn_of_d4 {K : Subgroup Ω} {y : Ω} (hK : GLAPComponent 3 ⊤ K)
    (hchev : IsChevSimple 2 (PSimple 3 K)) (hD4 : catalogIs (PSimple 3 K) isD4any) (hy3 : y ^ 3 = 1)
    (hnon : NonInnDiag 3 y K) {J₁ J₂ : Subgroup Ω}
    (h₁ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₁)
    (h₂ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₂) : J₁ = J₂ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hyN : y ∈ Subgroup.normalizer (K : Set Ω) := hnon.1
  have hap : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy3
  have hβ3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  have hβout : chevAut 3 K ⟨y, hyN⟩ ∉ inner (PSimple 3 K) := fun hin =>
    hnon.2 (MI.inner_innDiag_holds hp3 hK hchev hyN ((chevAut_mem_inner_iff hp3 hK hyN).1 hin))
  obtain ⟨i, hi, ⟨e⟩⟩ := hD4
  obtain ⟨q, hv, hq2, rfl⟩ := t1428NonInn_exists_D4 hi
  have hm := CFSG.Models.lieModel_D 4 q hv e
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hm.statedClassicalModel (by decide)
  rw [hq2] at hF
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : PSimple 3 K ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  have hα3 : MulAut.congr e₂ (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hout : ∀ h : ↥(adjointGroup Tag.D4 F),
      MulAut.conj h ≠ MulAut.congr e₂ (chevAut 3 K ⟨y, hyN⟩) := by
    intro h hh
    apply hβout
    refine ⟨e₂.symm h, ?_⟩
    ext x
    have h1 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 F) => e₂.symm (φ (e₂ x))) hh
    simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, map_mul, map_inv] at h1
    rw [MulAut.conj_apply]
    exact h1
  have hcore : NonInnCore ↥(fixSubgroup (chevAut 3 K ⟨y, hyN⟩)) :=
    (nonInnCore_d4 (MulAut.congr e₂ (chevAut 3 K ⟨y, hyN⟩)) hα3 hout).of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e₂ _)
  exact eq_of_chevTransfer_eq hp3 hyN hap h₁ h₂
    (hcore.pComponent_eq (glaPComponent_chevTransfer hp3 hyN hap h₁)
      (glaPComponent_chevTransfer hp3 hyN hap h₂))

theorem t1428NonInnFact_holds : CFSG.LocalAnalysis.GLTheoremA.T1428.T1428NonInnFact := by
  intro p hp hp2 Ω' _ _ _ K y hK hchev hyp hnon J₁ J₂ h₁ h₂
  rcases i91_holds Ω' p hp hp2 ⊤ K y hK hchev hnon.1 hyp hnon with hF | ⟨rfl, hD4 | hTD4⟩
  · exact t1428NonInn_of_r2Prop hp hp2 hK hchev hyp (Or.inl hF) h₁ h₂
  · exact t1428NonInn_of_d4 hK hchev hD4 hyp hnon h₁ h₂
  · have hNI : NonInner 3 y K :=
      ⟨hnon.1, fun hin => hnon.2 (MI.inner_innDiag_holds hp hK hchev hnon.1 hin)⟩
    exact t1428NonInn_of_r2Prop hp hp2 hK hchev hyp (Or.inr ⟨rfl, hTD4, hNI⟩) h₁ h₂

end CFSG.LocalAnalysis.GLTheoremA.T1428NonInn

end
