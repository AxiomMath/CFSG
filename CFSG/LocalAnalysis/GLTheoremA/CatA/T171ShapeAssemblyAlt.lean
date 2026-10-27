module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssembly
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
public import CFSG.RankThree.PartOne.FOC.AltFamily
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompAlt
import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Sec66T
open CFSG.Quasithin.A318P
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem not_dvd_outer_alt_small {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
  haveI : Finite (alternatingGroup (Fin n)) := by
    rcases hn with rfl | rfl | rfl | rfl <;> infer_instance
  rcases hn with rfl | rfl | rfl | rfl
  · exact not_dvd_outer_alternating (Or.inl rfl) (MulEquiv.refl _) hp hp2
  · exact not_dvd_outer_alternating_six (MulEquiv.refl _) hp hp2
  · exact not_dvd_outer_alternating (Or.inr le_rfl) (MulEquiv.refl _) hp hp2
  · exact not_dvd_outer_alternating (Or.inr (by norm_num)) (MulEquiv.refl _) hp hp2

theorem exists_conj_eq_of_alt_small {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut (alternatingGroup (Fin n))} (hβ : β ^ p = 1) :
    ∃ x : alternatingGroup (Fin n), MulAut.conj x = β := by
  have hmem : β ∈ innerAut (alternatingGroup (Fin n)) :=
    mem_innerAut_of_not_dvd_outer hp (not_dvd_outer_alt_small hn hp hp2) hβ
  exact hmem


section Certificates


theorem alt_transfer_of_setup {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) (h : Setup p L J A d b)
    (e : PSimple p L ≃* alternatingGroup (Fin n)) :
    ∃ (xd : alternatingGroup (Fin n)) (Jstar : Subgroup (PSimple p L)),
      MulAut.conj xd = MulAut.congr e (chevAut p L ⟨d,
        S171.normalizer_of_innerDiagMarking h.idiag h.d_mem⟩) ∧
      xd ^ p = 1 ∧
      GLAPComponent p (Subgroup.centralizer ({xd} : Set (alternatingGroup (Fin n))))
        (Jstar.map (e : PSimple p L →* alternatingGroup (Fin n))) ∧
      Jstar.map (e : PSimple p L →* alternatingGroup (Fin n)) = altFix (xd : Equiv.Perm (Fin n)) ∧
      5 ≤ n - (xd : Equiv.Perm (Fin n)).support.card ∧
      GLAPComponent p (fixSubgroup (chevAut p L ⟨d,
        S171.normalizer_of_innerDiagMarking h.idiag h.d_mem⟩)) Jstar ∧
      Jstar = chevTransfer p L J := by
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking h.idiag h.d_mem
  have hp := h.prime
  have hp2 := h.odd
  have hdp : d ^ p = 1 := h.elem.2 d h.d_mem
  set β : MulAut (alternatingGroup (Fin n)) :=
    MulAut.congr e (chevAut p L ⟨d, hdN⟩) with hβ
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow, chevAut_pow_eq_one p L hdN hdp, map_one]
  have hn4 : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by
    rcases hn with rfl | rfl | rfl <;> simp
  obtain ⟨xd, hxd⟩ := exists_conj_eq_of_alt_small hn4 hp hp2 hβp
  have hxdp : xd ^ p = 1 := by
    have h1 : MulAut.conj (xd ^ p) = 1 := by
      rw [map_pow, hxd, hβp]
    have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
      rcases hn with rfl | rfl | rfl <;>
        exact alternatingGroup.center_eq_bot (by norm_num)
    exact CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ
      (by rw [h1, map_one])
  set Jstar : Subgroup (PSimple p L) := chevTransfer p L J with hJstar_def
  have hdP : IsPGroup p (Subgroup.zpowers d) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hx : ((x : G) ^ p) = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
    simpa using hx
  have hJstar : GLAPComponent p (fixSubgroup (chevAut p L ⟨d, hdN⟩)) Jstar :=
    glaPComponent_chevTransfer hp hdN hdP h.pcomp
  have hker_e : (e : PSimple p L →* alternatingGroup (Fin n)).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact e.injective
  have hEmap : GLAPComponent p
      ((fixSubgroup (chevAut p L ⟨d, hdN⟩)).map
        (e : PSimple p L →* alternatingGroup (Fin n)))
      (Jstar.map (e : PSimple p L →* alternatingGroup (Fin n))) := by
    refine CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp
      (e : PSimple p L →* alternatingGroup (Fin n)) ?_ hJstar
    rw [hker_e, inf_bot_eq]
    simp
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e
    (chevAut p L ⟨d, hdN⟩)] at hEmap
  rw [show (MulAut.congr e) (chevAut p L ⟨d, hdN⟩) = MulAut.conj xd from hxd.symm,
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj] at hEmap
  obtain ⟨hEeq, h5⟩ := altFix_unique_of_component hp hp2 hxdp hEmap
  exact ⟨xd, Jstar, hxd, hxdp, hEmap, hEeq, h5, hJstar, rfl⟩

theorem ambiguousAltFalse : AmbiguousAltFalse := by
  intro G _ _ p L J A d b n hn hf168 hSetup hcat
  obtain ⟨i, rfl, ⟨e⟩⟩ := hcat
  haveI : Finite (alternatingGroup (Fin n)) := by
    rcases hf168 with rfl | rfl | rfl <;> infer_instance
  obtain ⟨xd, Jstar, hxd, hxdp, hEmap, hEeq, h5, hJstar, hJstarEq⟩ :=
    alt_transfer_of_setup hf168 hSetup e
  have hp := hSetup.prime
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hSetup.idiag hSetup.d_mem
  have hdp : d ^ p = 1 := hSetup.elem.2 d hSetup.d_mem
  have hdP : IsPGroup p (Subgroup.zpowers d) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hx : ((x : G) ^ p) = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
    simpa using hx
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = (xd : Equiv.Perm (Fin n)).support.card := ⟨_, rfl⟩
  let f : ℕ := n - s
  have h5' : 5 ≤ n - s := by simpa [hs] using h5
  have hfn : f ≤ n := by dsimp [f]; exact Nat.sub_le n s
  have hff' : n - s = 5 ∨ n - s = 6 ∨ n - s = 7 ∨ n - s = 8 := by
    have hle : n - s ≤ n := Nat.sub_le n s
    have h5'' : 5 ≤ n - s := h5'
    rcases hf168 with h | h | h <;> omega
  have hff : f = 5 ∨ f = 6 ∨ f = 7 ∨ f = 8 := hff'
  obtain ⟨eAlt⟩ := nonempty_altFix_equiv (xd : Equiv.Perm (Fin n)) (m := f)
    (by show n - (xd : Equiv.Perm (Fin n)).support.card = n - s; rw [← hs])
  have hEeq' : Jstar.map (e : PSimple p L →* alternatingGroup (Fin n)) =
      altFix (xd : Equiv.Perm (Fin n)) := hEeq
  let eJE : ↥Jstar ≃* ↥(altFix (xd : Equiv.Perm (Fin n))) :=
    (Jstar.equivMapOfInjective (e : PSimple p L →* alternatingGroup (Fin n)) e.injective).trans
      (MulEquiv.subgroupCongr hEeq')
  let eA : ↥Jstar ≃* ↥(alternatingGroup (Fin f)) := eJE.trans eAlt
  have hfs : 5 ≤ f := h5'
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin f)) :=
    alternatingGroup.isSimpleGroup (by simpa using hfs)
  haveI : IsSimpleGroup ↥(altFix (xd : Equiv.Perm (Fin n))) := eAlt.isSimpleGroup
  haveI : IsSimpleGroup ↥Jstar := eJE.isSimpleGroup
  haveI : IsSimpleGroup (PSimple p Jstar) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hJstar).2
  haveI : Nontrivial (PSimple p Jstar) := inferInstance
  obtain ⟨a0, b0, hab⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.exists_ne_comm_alternatingGroup
      (by omega : 4 ≤ f)
  have hpair : ∃ a b : ↥Jstar, a * b ≠ b * a := by
    refine ⟨eA.symm a0, eA.symm b0, fun h => hab ?_⟩
    exact (by simpa using congrArg eA h)
  have hJq : CFSG.Open.IsQuasisimple ↥Jstar :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥Jstar).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Jstar).mpr
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hpair).1)
  have hZJ : Subgroup.center ↥Jstar = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hpair).2
  let ePJ : PSimple p Jstar ≃* ↥Jstar :=
    (S171.chevIso' hp hJstar hJq).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZJ).trans (QuotientGroup.quotientBot (G := ↥Jstar)))
  obtain ⟨eJJstar⟩ := nonempty_pSimple_equiv_chevTransfer hp hdN hdP hSetup.pcomp
  let psi : PSimple p J ≃* ↥(alternatingGroup (Fin f)) :=
    eJJstar.trans (hJstarEq.symm ▸ (ePJ.trans eA))
  have hbp : b ^ p = 1 := hSetup.elem.2 b hSetup.b_mem
  have hβp : (MulAut.congr psi (chevAut p J ⟨b, hSetup.b_norm⟩)) ^ p = 1 := by
    rw [← map_pow, chevAut_pow_eq_one p J hSetup.b_norm hbp, map_one]
  obtain ⟨x, hx⟩ := exists_conj_eq_of_alt_small hff hp hSetup.odd hβp
  have hinner' : CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (MulAut.congr psi (chevAut p J ⟨b, hSetup.b_norm⟩)) := ⟨x, hx⟩
  have hinner : chevAut p J ⟨b, hSetup.b_norm⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) :=
    (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr psi _).1 hinner'
  have hInd : InducesInnerMod p J b :=
    (chevAut_mem_inner_iff hp hSetup.pcomp hSetup.b_norm).1 hinner
  exact hSetup.nonID
    (CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hp hSetup.pcomp hSetup.chevJ
      hSetup.b_norm hInd)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
