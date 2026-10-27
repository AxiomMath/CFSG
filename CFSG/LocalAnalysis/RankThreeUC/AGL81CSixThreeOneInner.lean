module

public import CFSG.Open.StatedDefs
public import CFSG.Foundations.Basic
public import Certificates.Certificate1022
public import Certificates.Certificate7059
public import Certificates.Certificate7023
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate110
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9
import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
import CFSG.GH74.GLS.LU.Local.SL2Aut2
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Quasithin.EmptyFaithful.S152VR1
import CFSG.LieType.SteinbergBRSmallAltSylow
import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelInputsBase
import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
import CFSG.GH74.BNPair.Defs
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
import CFSG.GH74.GLS.IVK.L2.Lemma19c
import CFSG.GH74.GLS.IVK.L2.SylowAux
import CFSG.GH74.GLS.IVK.L2.Torus
import CFSG.GH74.GLS.IVK.L2.TorusGeneral
import CFSG.GH74.GLS.IVK.Prod.Basic
import CFSG.GH74.Statements
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

private theorem exists_conj_of_mulAut_congr {L S : Type*} [Group L] [Group S] (e : L ≃* S)
    (α : MulAut L) (h : ∃ y : S, MulAut.congr e α = MulAut.conj y) :
    ∃ y : L, α = MulAut.conj y := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [hy, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]

private theorem exists_conj_of_pow_eq_one_of_isPGroup_outer {X : Type*} [Group X]
    (hOut : IsPGroup 2 (Outer X)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (α : MulAut X) (hα : α ^ r = 1) : ∃ y : X, α = MulAut.conj y := by
  let q : Outer X := QuotientGroup.mk' (inner X) α
  have hq : q ^ r = 1 := by
    dsimp only [q]
    rw [← map_pow, hα, map_one]
  have hq1 : q = 1 := by
    by_contra hne
    have h2 : 2 ∣ orderOf q := IsPGroup.dvd_orderOf hOut hne
    have hdvd : orderOf q ∣ r := orderOf_dvd_of_pow_eq_one hq
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
    · exact hne (orderOf_eq_one_iff.mp h1)
    · rw [h1] at h2
      exact hr2 (((Nat.dvd_prime hr).1 h2).resolve_left (by norm_num)).symm
  have hq' : (QuotientGroup.mk α : Outer X) = 1 := by
    simpa only [q, QuotientGroup.mk'_apply] using hq1
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff α).1 hq'
  exact ⟨y, hy.symm⟩

private theorem inducedAut_conj {X Γ : Type*} [Group X] [Group Γ]
    (ψ : X ⧸ Subgroup.center X ≃* Γ) (y : X) :
    CFSG.Quasithin.S152V.inducedAut ψ (MulAut.conj y) =
      MulAut.conj (ψ (QuotientGroup.mk y)) := by
  apply MulEquiv.ext
  intro w
  obtain ⟨x, rfl⟩ := ψ.surjective w
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center X) x
  simp only [CFSG.Quasithin.S152V.inducedAut_apply, MulAut.conj_apply,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]

theorem exists_conj_of_centerQuotient_a7 {X : Type*} [Group X]
    (hperf : Group.IsPerfect X) (ψ : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7))
    (α : MulAut X) (hα : α ^ 7 = 1) : ∃ y : X, α = MulAut.conj y := by
  let a : MulAut (alternatingGroup (Fin 7)) := CFSG.Quasithin.S152V.inducedAut ψ α
  have ha : a ^ 7 = 1 := by
    dsimp only [a]
    rw [← map_pow, hα, map_one]
  obtain ⟨ybar, hybar⟩ := exists_conj_of_pow_eq_one_of_isPGroup_outer
    CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_seven (r := 7)
    (by norm_num) (by norm_num) a ha
  obtain ⟨x, hx⟩ := ψ.surjective ybar
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center X) x
  refine ⟨y, ?_⟩
  have hconj : CFSG.Quasithin.S152V.inducedAut ψ (MulAut.conj y) = a := by
    rw [inducedAut_conj, hx]
    exact hybar.symm
  let β : MulAut X := (MulAut.conj y)⁻¹ * α
  have hβ : CFSG.Quasithin.S152V.inducedAut ψ β = 1 := by
    dsimp only [β]
    rw [map_mul, map_inv, hconj]
    exact inv_mul_cancel a
  have hcent : ∀ x : X, x⁻¹ * β x ∈ Subgroup.center X := by
    intro x
    apply (QuotientGroup.eq_one_iff (x⁻¹ * β x)).1
    apply ψ.injective
    rw [map_one]
    calc ψ (QuotientGroup.mk (x⁻¹ * β x))
        = (ψ (QuotientGroup.mk x))⁻¹ * ψ (QuotientGroup.mk (β x)) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      _ = (ψ (QuotientGroup.mk x))⁻¹ *
            (CFSG.Quasithin.S152V.inducedAut ψ β) (ψ (QuotientGroup.mk x)) := by
          rw [← CFSG.Quasithin.S152V.inducedAut_apply]
      _ = (ψ (QuotientGroup.mk x))⁻¹ * ψ (QuotientGroup.mk x) := by rw [hβ]; rfl
      _ = 1 := inv_mul_cancel _
  have hβ1 : β = 1 := CFSG.Quasithin.S152V.mulAut_eq_one_of_central hperf β hcent
  dsimp only [β] at hβ1
  have := congrArg (fun t : MulAut X => MulAut.conj y * t) hβ1
  simpa using this

private theorem exists_conj_of_mulEquiv_sl2 {L : Type*} {F : Type} [Group L] [Field F] [Finite F]
    {q f r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hF : Nat.card F = q ^ f)
    (h3 : 3 < q ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrf : ¬ r ∣ f)
    (e : L ≃* SL(2, F)) (α : MulAut L) (hα : α ^ r = 1) :
    ∃ y : L, α = MulAut.conj y := by
  apply exists_conj_of_mulAut_congr e α
  have hα' : (MulAut.congr e α) ^ r = 1 := by rw [← map_pow, hα, map_one]
  exact CFSG.GH74.GLS.LU.Local.sl2_aut_inner_of_prime hq hF hq2 h3 hr hr2 hrf _ hα'

section Certificates


theorem exists_conj_of_pow_eq_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {L : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hLS : L ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hq : CFSG.IsQuasisimple ↥L) (α : MulAut ↥L) (hα : α ^ p = 1) :
    (∃ y : ↥L, α = MulAut.conj y) ∨
      Nat.card ↥L = Nat.card ↥(CFSG.Open.StatedSp 2 (ZMod p)) := by
  have hp2 : p ≠ 2 := by omega
  have hp : p.Prime := Fact.out
  rcases CFSG.RankThree.SubgroupLists.mitchell_quasisimple_sp4_of
    CFSG.RankThree.SubgroupLists.mitchellPartThree_holds
    CFSG.RankThree.SubgroupLists.fischerSpClique
    CFSG.RankThree.SubgroupLists.fischerOrthClique
    CFSG.RankThree.SubgroupLists.fischerSpCard
    CFSG.RankThree.SubgroupLists.fischerOrthCard
    CFSG.RankThree.SubgroupLists.fischerUnitaryCard
    CFSG.RankThree.SubgroupLists.fischerReflectionCard hp2 hLS hq with
    hSp4 | hSLp2 | hSLp | hSL5 | hSL9 | hA7
  ·
    obtain ⟨e⟩ := hSp4
    exact Or.inr (Nat.card_congr e.toEquiv)
  ·
    obtain ⟨e⟩ := hSLp2
    exact Or.inl (exists_conj_of_mulEquiv_sl2 (L := ↥L) (F := GaloisField p 2)
      (q := p) (f := 2) (r := p) hp hp2
      (GaloisField.card p 2 (by norm_num)) (by nlinarith)
      hp hp2 (by rw [Nat.dvd_prime Nat.prime_two]; omega) e α hα)
  ·
    obtain ⟨e⟩ := hSLp
    exact Or.inl (exists_conj_of_mulEquiv_sl2 (L := ↥L) (F := ZMod p)
      (q := p) (f := 1) (r := p) hp hp2
      (by rw [Nat.card_zmod, pow_one]) (by simpa using (by omega : 3 < p))
      hp hp2 (by rw [Nat.dvd_one]; omega) e α hα)
  ·
    obtain ⟨e⟩ := hSL5
    letI : Field (ZMod 5) := @ZMod.instField 5 ⟨by norm_num⟩
    exact Or.inl (exists_conj_of_mulEquiv_sl2 (L := ↥L) (F := ZMod 5) (q := 5) (f := 1) (r := p)
      (show Nat.Prime 5 by norm_num) (by norm_num)
      (by rw [Nat.card_zmod]; norm_num) (by norm_num)
      hp hp2 (by rw [Nat.dvd_one]; omega) e α hα)
  ·
    obtain ⟨e⟩ := hSL9
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Field (GaloisField 3 2) := instFieldGaloisField 3 2
    exact Or.inl (exists_conj_of_mulEquiv_sl2 (L := ↥L) (F := GaloisField 3 2)
      (q := 3) (f := 2) (r := p)
      (show Nat.Prime 3 by norm_num) (by norm_num)
      (GaloisField.card 3 2 (by norm_num)) (by norm_num)
      hp hp2 (by rw [Nat.dvd_prime Nat.prime_two]; omega) e α hα)
  ·
    obtain ⟨hp7, -, ⟨ψ⟩⟩ := hA7
    subst hp7
    exact Or.inl (exists_conj_of_centerQuotient_a7 hq.1 ψ α hα)

end Certificates

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
