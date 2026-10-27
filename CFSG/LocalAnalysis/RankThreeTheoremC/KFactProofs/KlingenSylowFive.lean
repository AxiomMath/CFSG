module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43
import CFSG.LieType.Multipliers.U42Bridge
import Certificates.Certificate10010

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.Open Subgroup

namespace KlingenSylowFive

section Exponent

variable {p : ℕ} [Fact p.Prime]

theorem matrix_pow_card_eq_zero {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {N : Matrix ι ι K} (hN : IsNilpotent N) : N ^ Fintype.card ι = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h2 : N.charpoly = Polynomial.X ^ Fintype.card ι := sub_eq_zero.mp h.eq_zero
  have h3 := Matrix.aeval_self_charpoly N
  rwa [h2, map_pow, Polynomial.aeval_X] at h3

theorem matrix_pow_prime_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : Fintype.card ι ≤ p) {h : Matrix ι ι (ZMod p)} {k : ℕ} (hk : h ^ p ^ k = 1) :
    h ^ p = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  have hN : IsNilpotent (h - 1) :=
    ⟨p ^ k, by rw [sub_pow_char_pow_of_commute p k (Commute.one_right h), hk, one_pow, sub_self]⟩
  have hN0 := matrix_pow_card_eq_zero hN
  have hNp : (h - 1) ^ p = 0 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hp
    calc (h - 1) ^ p = (h - 1) ^ (Fintype.card ι + m) := congrArg (fun n => (h - 1) ^ n) hm
      _ = 0 := by rw [pow_add, hN0, zero_mul]
  have h1 := add_pow_char_of_commute (R := Matrix ι ι (ZMod p)) p (x := h - 1) (y := 1)
    (Commute.one_right _)
  rwa [sub_add_cancel, hNp, one_pow, zero_add] at h1

theorem eq_one_of_pow_coprime {G : Type*} [Group G] {y : G} {m n : ℕ} (hm : y ^ m = 1)
    (hn : y ^ n = 1) (hc : Nat.Coprime m n) : y = 1 := by
  have h1 : orderOf y ∣ Nat.gcd m n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
  rw [hc] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem coprime_pred_prime_pow (k : ℕ) : Nat.Coprime (p - 1) (p ^ k) := by
  refine Nat.Coprime.pow_right k ?_
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [hm, Nat.add_sub_cancel]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)

theorem pow_prime_eq_one_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    (hp : Fintype.card ι ≤ p) (H : Subgroup (GL ι (ZMod p))) {x : StatedProj H} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hx0 := hx
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hc1 : c ^ (p - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact ZMod.pow_card_sub_one_eq_one c.ne_zero
  rw [Subgroup.coe_pow] at hc
  have hg1 : (((g ^ (p - 1)) ^ p ^ k : H) : GL ι (ZMod p)) = 1 := by
    rw [Subgroup.coe_pow, Subgroup.coe_pow, pow_right_comm, ← hc, ← map_pow, hc1, map_one]
  have hM : ((((g ^ (p - 1) : H) : GL ι (ZMod p)) : Matrix ι ι (ZMod p))) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hg1, Units.val_one]
  have hM1 := matrix_pow_prime_eq_one hp hM
  have hg2 : (g ^ (p - 1)) ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hM1]
    rfl
  have hy1 : ((g : StatedProj H) ^ p) ^ (p - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hg2]
    rfl
  have hy2 : ((g : StatedProj H) ^ p) ^ p ^ k = 1 := by
    rw [pow_right_comm, hx0, one_pow]
  exact eq_one_of_pow_coprime hy1 hy2 (coprime_pred_prime_pow k)

end Exponent

theorem card_le_of_forall_pow_eq_one {K : Type*} [Group K] {N : Subgroup K} (hc : IsCyclic N)
    {p : ℕ} (hp : 0 < p) (h : ∀ y ∈ N, y ^ p = 1) : Nat.card N ≤ p := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hg3 : g ^ p = 1 := Subtype.ext (h g g.2)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_le_of_pow_eq_one hp hg3

end KlingenSylowFive

theorem kFactKlingenSylowNormalCyclic_of_five_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsKlingenIndex p d) (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* CatGroup d)) (T : Sylow p K) (N : Subgroup K)
    (hN : N ≤ (T : Subgroup K)) (_hT : (T : Subgroup K) ≤ normalizer (N : Set K))
    (hc : IsCyclic N) : Nat.card N ≤ p := by
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := hK
  have hd' : IsSpFourIndex p d := hd.resolve_right fun h => by omega
  obtain ⟨eK⟩ := KlingenSpFour.nonempty_mulEquiv_psp4 (p := p) (by omega)
    (KlingenSpFour.statedClassicalModel_of_spFourIndex d hd' e)
  refine KlingenSylowFive.card_le_of_forall_pow_eq_one hc hp.pos fun y hy => ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (Sylow.isPGroup' T) ⟨y, hN hy⟩
  have hk' : orderOf y = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h1 : (eK y) ^ p ^ k = 1 := by
    rw [← map_pow, ← hk', pow_orderOf_eq_one, map_one]
  have h2 := KlingenSylowFive.pow_prime_eq_one_statedProj (ι := Fin 2 ⊕ Fin 2)
    (by simpa using hp5.trans' (by omega)) (StatedSp 2 (ZMod p)) h1
  exact eK.injective (by rw [map_pow, h2, map_one])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
