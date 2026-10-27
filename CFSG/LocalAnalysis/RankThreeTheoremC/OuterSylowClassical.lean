module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBULinearUnitaryOuterExtraspecial
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalOuter
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSmallKernelFiltrations

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GorensteinLyons
open CFSG.Assembly.LowTwoRank

theorem sylow_normal_outer_A1 {p : ℕ} [Fact p.Prime] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)).Normal := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
  refine sylow_normal_of_comm fun a b => (equivalence e).injective ?_
  rw [map_mul, map_mul]
  exact OuterDerived.outer_psl2_mul_comm _ _ _

theorem sylow_normal_outer_A2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group)).Normal := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ≃*
      LinearFlag.projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group := Finite.of_equiv _ e.symm.toEquiv
  haveI := finite_outer (LinearFlag.projectiveSL 3 (GaloisField q.p q.exponent))
  obtain ⟨N, hN, -, hcard, hab, -⟩ :=
    LinearUnitaryOuter.linear_outer_filtration (K := GaloisField q.p q.exponent) (n := 3) le_rfl
  haveI := hN
  refine sylow_normal_outer_of_mulEquiv e (sylow_normal_of_quotient N ?_ (sylow_normal_of_comm hab))
  have h2 := (Fact.out : p.Prime).two_le
  have h3 := Nat.le_of_dvd (by norm_num) (hcard.trans (Nat.gcd_dvd_left 3 _))
  omega

theorem sylow_normal_outer_twistedA2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)).Normal := by
  obtain ⟨⟨hp, hf, -, h32⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
      (G := (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) (MulEquiv.refl _)
  have hU : UnitaryFieldData q.p q.exponent K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(2 + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨_, h2⟩ => h32 (by rw [h2])
  obtain ⟨⟨eT⟩, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order hU (n := 2 + 1) le_rfl hq
  let E := (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm).trans
    eT.symm
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group :=
    Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨N, hN, -, hcard, hQ⟩ :=
    LinearUnitaryOuter.unitary_outer_filtration hU (n := 2 + 1) le_rfl hq
  haveI := hN
  haveI := hQ
  haveI := Finite.of_equiv _ E.toEquiv
  haveI := finite_outer
    (UnitaryHigher.primeFormP hU ((1 : GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K))
  refine sylow_normal_outer_of_mulEquiv E
    (sylow_normal_of_quotient N ?_ fun S => sylow_normal_of_isCyclic S)
  have h2 := (Fact.out : p.Prime).two_le
  have h3 := Nat.le_of_dvd (by norm_num) (hcard.trans (Nat.gcd_dvd_left 3 _))
  omega

theorem sylow_normal_outer_spFour {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsSpFourIndex p d) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie d).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie d).Group)).Normal := by
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KlingenSpFour.nonempty_mulEquiv_psp4 hp2
    (CFSG.AGLEmbedding.KlingenSpFour.statedClassicalModel_of_spFourIndex d hd (MulEquiv.refl _))
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.symm.toEquiv
  haveI := finite_outer (CFSG.AGLEmbedding.KlingenSpFour.PSp4 p)
  refine sylow_normal_outer_of_mulEquiv e (sylow_normal_of_not_dvd fun h => hp2 ?_)
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    (h.trans (KFactProofs.card_outer_psp4_dvd_two p hp2))

theorem sylow_normal_outer_B2_eight (q : TauCeti.PrimePower) (h2 : q.p = 2) (h3 : q.exponent = 3)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) :
    ∀ S : Sylow 3 (Outer (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group)).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv
    (G := (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) (MulEquiv.refl _)
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := Finite.of_equiv _ e.symm.toEquiv
  haveI := finite_outer (StatedProj (StatedSp 2 K))
  have hO := (SymplecticHigher.outer_card_dvd (r := 2) q.prime_p q.exponent_pos hK le_rfl).1
  rw [h2, h3] at hO
  refine sylow_normal_outer_of_mulEquiv e
    (sylow_normal_of_card_dvd (a := 1) (m := 2) (hO.trans ?_) (by norm_num) (by norm_num))
  norm_num

theorem sylow_normal_outer_B3_two {p : ℕ} [Fact p.Prime] (q : TauCeti.PrimePower) (h2 : q.p = 2)
    (h1 : q.exponent = 1) (hv : (TauCeti.LieTypeIndex.B 3 q).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group)).Normal := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even
    3 q hv h2 le_rfl (G := (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) (MulEquiv.refl _)
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := Finite.of_equiv _ e.symm.toEquiv
  haveI := finite_outer (StatedProj (StatedSp 3 K))
  have hO :=
    (SymplecticHigher.outer_card_dvd (r := 3) q.prime_p q.exponent_pos hK (by norm_num)).2 le_rfl
  rw [h2, h1] at hO
  refine sylow_normal_outer_of_mulEquiv e (sylow_normal_of_not_dvd fun h => ?_)
  have h1' : p ∣ 1 := h.trans (hO.trans (by norm_num))
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1')

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
