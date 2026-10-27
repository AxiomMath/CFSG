module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open Subgroup CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag

theorem congr_mem_commutator {Q M : Type*} [Group Q] [Group M] (e : Q ≃* M) {τ : MulAut Q}
    (h : τ ∈ commutator (MulAut Q)) : MulAut.congr e τ ∈ commutator (MulAut M) := by
  have : MulAut.congr e τ ∈ (commutator (MulAut Q)).map (MulAut.congr e).toMonoidHom :=
    ⟨_, h, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at this
  exact Subgroup.commutator_mono le_top le_top this

theorem mem_commutator_of_congr {Q M : Type*} [Group Q] [Group M] (e : Q ≃* M) {τ : MulAut Q}
    (h : MulAut.congr e τ ∈ commutator (MulAut M)) : τ ∈ commutator (MulAut Q) := by
  have h2 := congr_mem_commutator e.symm h
  have h1 : MulAut.congr e.symm (MulAut.congr e τ) = τ := by
    ext q
    simp [MulAut.congr_apply]
  rwa [h1] at h2

theorem centerDescend_mem_commutator {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {α : MulAut Y} (hα : IsInnDiagThree α) :
    centerDescend Y α ∈ commutator (MulAut (Y ⧸ center Y)) := by
  rcases hα with hL | hU
  · obtain ⟨F, _, _, e, hmem⟩ := AutL3.inndiagPSL3_data hL
    exact mem_commutator_of_congr e ((goodPinned_psl F).up hmem)
  · obtain ⟨p, f, F, _, hF, e, hmem⟩ := AutL3.inndiagPSU3_data hY hU
    have hq := two_lt_pow_of_quasisimple hY hF e
    exact mem_commutator_of_congr e ((goodPinned_psu hF hq).up hmem)

theorem comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian p B) : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have := hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
  simpa using congrArg Subtype.val this

theorem three_dvd_card_units {F : Type} [Field F] [Finite F] (h : Nat.card F % 3 = 1) :
    3 ∣ Nat.card Fˣ := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [Nat.card_eq_fintype_card] at h
  omega

theorem innDiagRankTwo_holds : InnDiagRankTwo := by
  intro K _ _ hK hL E hE hin
  have hinj : Function.Injective (centerDescend K) := by
    rw [injective_iff_map_eq_one]
    intro α hα
    exact eq_one_of_centerDescend_eq_one hK hα
  let Eb : Subgroup (MulAut (K ⧸ center K)) := E.map (centerDescend K)
  have hcard : Nat.card E = Nat.card Eb := (Subgroup.card_map_of_injective hinj).symm
  have hEb : CFSG.Open.IsElemAbelian 3 Eb := CFSG.SectionRank.isElemAbelian_map hE _
  have hcomm : ∀ x ∈ Eb, x ∈ commutator (MulAut (K ⧸ center K)) := by
    rintro _ ⟨α, hα, rfl⟩
    exact centerDescend_mem_commutator hK (hin α hα)
  rw [hcard]
  rcases hL with ⟨F, _, _, hF3, ⟨θ⟩⟩ | ⟨F, _, _, q, hFq, hq3, ⟨θ⟩⟩
  · let e : (K ⧸ center K) ≃* projectiveSL 3 F := θ.trans (psiO F)
    let B : Subgroup (MulAut (projectiveSL 3 F)) := Eb.map (MulAut.congr e).toMonoidHom
    have hBD : B ≤ linearAutGroup 3 F := by
      rintro _ ⟨x, hx, rfl⟩
      exact (goodPinned_psl F).down (congr_mem_commutator e (hcomm x hx))
    have hB : CFSG.Open.IsElemAbelian 3 B := CFSG.SectionRank.isElemAbelian_map hEb _
    have hK3 : 3 ∣ Nat.card F - 1 := by
      have : 0 < Nat.card F := Nat.card_pos
      omega
    have h9 := CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.card_le_nine_of_le_linearAutGroup hK3
      B hBD (comm_of_isElemAbelian hB) (fun x hx => hB.2 x hx)
    rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h9
  · obtain ⟨p, f, hqpf, ⟨hF⟩⟩ := exists_unitaryFieldData hFq
    subst hqpf
    let e : (K ⧸ center K) ≃* unitaryPSU hF 3 := θ.trans (psuO hF).symm
    have hq2 : 2 < p ^ f := two_lt_pow_of_quasisimple hK hF e
    let B : Subgroup (MulAut (unitaryPSU hF 3)) := Eb.map (MulAut.congr e).toMonoidHom
    have hBR : B ≤ (psuConj hF).range := by
      rintro _ ⟨x, hx, rfl⟩
      exact (goodPinned_psu hF hq2).down (congr_mem_commutator e (hcomm x hx))
    have hB : CFSG.Open.IsElemAbelian 3 B := CFSG.SectionRank.isElemAbelian_map hEb _
    have hmod : Nat.card F % 3 = 1 := by
      have h := Nat.pow_mod (p ^ f) 2 3
      rw [hq3] at h
      rw [hFq]
      norm_num at h
      exact h
    have hker : ∀ A : unitaryIsom3 hF, psuConj hF A = 1 ↔
        (A : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
      intro A
      have hc : CFSG.Open.StatedScalars (Fin 3) F = Subgroup.center (GL (Fin 3) F) := by
        rw [CFSG.Open.StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      rw [CFSG.RankThree.PartTwo.Sec4.psuConj_eq_one_iff A, hc]
    have h9 := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
      Nat.prime_three (by norm_num) (three_dvd_card_units hmod) (by norm_num)
      (unitaryIsom3 hF) (psuConj hF) hker B hBR hB
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h9
    simpa using h9

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
