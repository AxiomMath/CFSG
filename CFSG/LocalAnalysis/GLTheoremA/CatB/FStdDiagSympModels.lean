module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSympOrd
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel
  (exists_statedClassicalModel_quotCenter_orthDerived)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_centralQuotient_mulEquiv)

theorem fstdSymp_quot_equiv {S : Type} [Group S] {I : Subgroup S} {X : Type} [Group X]
    (hXp : commutator X = ⊤) (g : X →* ↥I) (hg : Function.Surjective g)
    (hk : g.ker ≤ Subgroup.center X) :
    Nonempty (↥I ⧸ Subgroup.center ↥I ≃* X ⧸ Subgroup.center X) :=
  (nonempty_centralQuotient_mulEquiv hXp g hg hk).map MulEquiv.symm

theorem fstdSymp_sl_false {S : Type} [Group S] {I : Subgroup S} (hord : SmallOrd I) {X : Type}
    [Group X] (hQ : Nonempty (↥I ⧸ Subgroup.center ↥I ≃* X ⧸ Subgroup.center X)) {m k : ℕ}
    {E : Type} [Field E] [Finite E] (hm : 2 ≤ m) (hk : 1 ≤ k) (hE : Nat.card E = 2 ^ k)
    (hm4 : m = 2 → 4 ≤ Nat.card E) (eX : X ≃* Matrix.SpecialLinearGroup (Fin m) E) : False := by
  obtain ⟨e1⟩ := hQ
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m eX
  have h2 : (m, 2 ^ k) ≠ (2, 2) := by
    intro h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    have := hm4 rfl
    omega
  have h3 : (m, 2 ^ k) ≠ (2, 3) := by
    intro h
    obtain ⟨rfl, h3⟩ := Prod.mk.inj h
    have := hm4 rfl
    omega
  have hmodel : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSL m 2 k :=
    ⟨⟨Nat.prime_two, hk, hm, h2, h3⟩, E, inferInstance, inferInstance, hE, ⟨e1.trans e2⟩⟩
  obtain ⟨h, -⟩ := fstdSymp_classical_order hmodel (Or.inl rfl) hord.symm
  exact StatedLieTag.noConfusion h

theorem fstdSymp_sp_false {S : Type} [Group S] {I : Subgroup S} (hord : SmallOrd I) {X : Type}
    [Group X] (hQ : Nonempty (↥I ⧸ Subgroup.center ↥I ≃* X ⧸ Subgroup.center X)) {s k : ℕ}
    {K : Type} [Field K] [Finite K] (hs : 2 ≤ s) (hk : 1 ≤ k) (hK : Nat.card K = 2 ^ k)
    (hne : ¬(s = 2 ∧ Nat.card K = 2)) (eX : X ≃* ↥(StatedSp s K)) : False := by
  obtain ⟨e1⟩ := hQ
  have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp hs hne
    hchar eX
  have h2 : (s, 2 ^ k) ≠ (2, 2) := by
    intro h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    exact hne ⟨rfl, hK.trans h2⟩
  have hmodel : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSp s 2 k :=
    ⟨⟨Nat.prime_two, hk, hs, h2⟩, K, inferInstance, inferInstance, hK, ⟨e1.trans e2⟩⟩
  obtain ⟨h, -⟩ := fstdSymp_classical_order hmodel (Or.inr (Or.inr (Or.inl rfl))) hord.symm
  exact StatedLieTag.noConfusion h

theorem fstdSymp_omega_false {S : Type} [Group S] {I : Subgroup S} (hord : SmallOrd I) {X : Type}
    [Group X] (hQ : Nonempty (↥I ⧸ Subgroup.center ↥I ≃* X ⧸ Subgroup.center X)) {f : ℕ}
    {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hK : Nat.card K = 2 ^ f)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (eX : X ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q)) : False := by
  obtain ⟨e1⟩ := hQ
  obtain ⟨s, hs⟩ := exists_statedClassicalModel_quotCenter_orthDerived hK hnd hd hT eX
  have hcen : ∀ {t : StatedLieTag},
      StatedClassicalModel (X ⧸ Subgroup.center X) t s 2 f →
      StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) t s 2 f :=
    fun h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e1.symm h
  rcases hs with hs | hs
  · obtain ⟨h, -⟩ := fstdSymp_classical_order (hcen hs)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hord.symm
    exact StatedLieTag.noConfusion h
  · obtain ⟨h, -⟩ := fstdSymp_classical_order (hcen hs)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hord.symm
    exact StatedLieTag.noConfusion h

theorem fstdSymp_su_case {S : Type} [Group S] {I : Subgroup S} (hord : SmallOrd I) {X : Type}
    [Group X] (hQ : Nonempty (↥I ⧸ Subgroup.center ↥I ≃* X ⧸ Subgroup.center X)) {m k : ℕ}
    {E : Type} [Field E] [Finite E] (hm : 3 ≤ m) (hk : 1 ≤ k) (hmq : (m, 2 ^ k) ≠ (3, 2))
    (hE : Nat.card E = (2 ^ k) ^ 2) (eX : X ≃* ↥(StatedSU m (2 ^ k) E)) :
    m = 4 ∧ k = 1 ∧ Nat.card (↥I ⧸ Subgroup.center ↥I) = 25920 ∧ Subgroup.center X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := k) hE hm hmq
  obtain ⟨e1⟩ := hQ
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eX
  let e3 : (↥(StatedSU m (2 ^ k) E) ⧸ Subgroup.center ↥(StatedSU m (2 ^ k) E)) ≃*
      StatedProj (StatedSU m (2 ^ k) E) := QuotientGroup.quotientMulEquivOfEq hZ
  have hmodel : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSU m 2 k :=
    ⟨⟨Nat.prime_two, hk, hm, hmq⟩, E, inferInstance, inferInstance, hE,
      ⟨e1.trans (e2.trans e3)⟩⟩
  obtain ⟨-, rfl, rfl, hc⟩ := fstdSymp_classical_order hmodel (Or.inr (Or.inl rfl)) hord.symm
  refine ⟨rfl, rfl, hc, ?_⟩
  have hker := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hE (n := 4)
    (by norm_num)).2.2
  rw [← hZ] at hker
  have h1 : Nat.card (Subgroup.center ↥(StatedSU 4 (2 ^ 1) E)) = 1 := by
    rw [hker]
    decide +kernel
  have h2 := Subgroup.eq_bot_of_card_eq _ h1
  rw [← Subgroup.map_center_eq eX] at h2
  exact Subgroup.map_injective eX.injective (by rw [h2, Subgroup.map_bot])

theorem fstdSymp_commutator_sp_four_equiv {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nonempty (↥(commutator (StatedSp 2 k)) ≃* ↥(commutator
      CFSG.ComponentClassification.PresentationLocal.sympFour)) := by
  let e : StatedSp 2 k ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (CFSG.Monster.Existence.Compat.statedProjEquivOfBot (StatedSp 2 k)
      (CFSG.Monster.Existence.Compat.statedScalars_eq_bot hk)).symm.trans
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hk)
  have hmap : (commutator (StatedSp 2 k)).map e.toMonoidHom =
      commutator CFSG.ComponentClassification.PresentationLocal.sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  exact ⟨(e.subgroupMap (commutator (StatedSp 2 k))).trans (MulEquiv.subgroupCongr hmap)⟩

theorem fstdSymp_a6_case {S : Type} [Group S] {I : Subgroup S} {X : Type} [Group X]
    (hXp : commutator X = ⊤) (g : X →* ↥I) (hg : Function.Surjective g)
    (hk : g.ker ≤ Subgroup.center X) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (eX : X ≃* ↥(commutator (StatedSp 2 K))) :
    Subgroup.center ↥I = ⊥ ∧ Nonempty (↥I ⧸ Subgroup.center ↥I ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eC⟩ := fstdSymp_commutator_sp_four_equiv hK
  let eA : X ≃* alternatingGroup (Fin 6) :=
    (eX.trans eC).trans CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating
  haveI : IsSimpleGroup ↥(commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
    CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
  haveI : Group.IsPerfect ↥(commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
    CFSG.ComponentClassification.PresentationLocal.isPerfect_commutator_sympFour
  haveI : IsSimpleGroup X := (eX.trans eC).isSimpleGroup
  haveI : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := (eX.trans eC).symm.toMonoidHom)
      (eX.trans eC).symm.surjective
  have hcen : Subgroup.center X = ⊥ := by
    rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.1 h) (Group.IsPerfect.not_isMulCommutative _)
  have hZ : Subgroup.center ↥I = ⊥ := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective hXp g hg hk,
      hcen, Subgroup.map_bot]
  refine ⟨hZ, ?_⟩
  obtain ⟨e1⟩ := fstdSymp_quot_equiv hXp g hg hk
  exact ⟨e1.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientBot.trans eA))⟩

theorem fstdSymp_threeFree_top {S P : Type} [Group S] [Group P] (e : S ≃* P)
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* P) → ¬ 3 ∣ Nat.card (Subgroup.center Y)) :
    ThreeFreeMult ↥(⊤ : Subgroup S) := by
  intro M _ _ hM ⟨eM⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    (hP M hM ⟨eM.trans (Subgroup.topEquiv.trans e)⟩)

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
