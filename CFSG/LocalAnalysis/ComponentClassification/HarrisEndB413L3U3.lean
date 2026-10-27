module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3Z
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3K
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3J
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL3U3
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.Goldschmidt75.WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGroups
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelAction
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.Walter.J1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.GrSLit

theorem EndB.isSylowTwoIn_inf {G : Type*} [Group G] [Finite G] {U K C : Subgroup G}
    (hU : IsSylowOf 2 U C) (hKC : K ≤ C) (hKs : (K.subgroupOf C).IsSubnormal) :
    IsSylowTwoIn (U ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU' : IsSylowOf 2 (U.subgroupOf C) ⊤ := by
    rw [← isSylowOf_map_subtype_iff C, subgroupOf_map_subtype, inf_of_le_left hU.le,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hU
  have key : ∀ {H : Subgroup ↥C}, H.IsSubnormal → IsSylowOf 2 (U.subgroupOf C ⊓ H) H := by
    intro H hH
    induction hH with
    | top => simpa using hU'
    | step H K' hHK _ hN ih =>
      have h1 := ih.inf_of_le_normalizer hHK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
      rwa [inf_assoc, inf_eq_right.mpr hHK] at h1
  have h2 := key hKs
  rw [← isSylowOf_map_subtype_iff C, Subgroup.map_inf_eq _ _ _ C.subtype_injective,
    subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hU.le,
    inf_of_le_left hKC] at h2
  obtain ⟨Q₀, hQ₀⟩ := h2.exists_sylow_eq_subgroupOf
  exact ⟨inf_le_right, Q₀, hQ₀⟩

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem false_of_L3U3 [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hGA : TBLit.GriessMultipliersOdd)
    (h219 : Harris82Lemma219Input) (h35 : Harris81Lemma35Step)
    (hC8 : AlternatingCoverInvolutionFact) (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 p
        (f / 2) ∨
      Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSU 3 p
        (f / 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hs.prime_p
  have hp2 := hs.p_ne_two
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hzK
  have hzE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hz2 : orderOf (QuotientGroup.mk ⟨z, hzM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
    have hz2' : z ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one z
      rwa [hs.setup.z_order] at h1
    have hsq : (⟨z, hzM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2
        = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2')
    refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]) ?_
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, hs.setup.z_order] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
  obtain ⟨Y, hYle, hYsub, hYsl, hzY⟩ := EndB.l3u3InvolutionSL2Fact
    (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) p (f / 2) hp hp2 hs.one_le_half hY _
    hzE hz2
  have hs5 : 5 ≤ p ^ (f / 2) := by
    have h16 := hs.sixteen_dvd
    have hr3 : 3 ≤ p ^ (f / 2) := le_trans (hp.two_le.lt_of_ne (Ne.symm hp2))
      (Nat.le_self_pow (by have := hs.one_le_half; omega) p)
    by_contra hlt
    have hr : p ^ (f / 2) = 3 ∨ p ^ (f / 2) = 4 := by omega
    rw [show p ^ (2 * (f / 2)) = (p ^ (f / 2)) ^ 2 by rw [← pow_mul, mul_comm]] at h16
    rcases hr with hr | hr <;> rw [hr] at h16 <;> norm_num at h16
  obtain ⟨J, hJ, hM, hzJ, hJsl⟩ := hs.setup.exists_J_of_sl2 hGA i j hzM hs.one_le_half hs5 hYle
    hYsub hYsl hzY
  obtain ⟨K, hKc, hJeq, hKβ, hq, -, hL, hsl7⟩ := hs.setup.lemma35_L3U3 hnab hK hcat hSch hFC hKC
    hI h219 h35 hC8 i j hJ hM hzJ hs.one_le_half hs5 hJsl
  have hKK : ⁅K, K⁆ = K := Lemma47.commutator_self_eq_of_isPerfect hKc.2.2.1
  obtain ⟨eZ⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥K
  have hL' : IsL34Type (↥K ⧸ Open.fusionZStar ↥K) := GSThmB.OddQuot.lieModel_of_equiv eZ.symm hL
  have hβN := Lemma47.mem_normalizer_of_map_conj_eq hKβ
  have hβ2 : w ^ (orderOf w / 2) * t ^ i * z ^ j * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 1 := by
    rw [← sq]
    exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hJperf : ⁅J, J⁆ = J := Lemma47.commutator_self_eq_of_isPerfect hJ.2.2.1
  have hJq : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 336 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hsl7
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, hF]
    norm_num
  have hJcard : Nat.card ↥J = 336 * Nat.card ↥(pPrimeCore 2 ↥J) := by
    rw [← hJq, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hOodd : Nat.card ↥(pPrimeCore 2 ↥J) % 2 = 1 :=
    Nat.odd_iff.mp (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hJeven : 2 ∣ Nat.card ↥J := by rw [hJcard]; exact Dvd.dvd.mul_right (by norm_num) _
  have hJ64 : ¬ 64 ∣ Nat.card ↥J := by rw [hJcard]; omega
  rw [hJeq] at hJperf hJeven hJ64
  have hβK := EndB.not_mem_withKernel hL' hq hβN hβ2 hJperf hJeven hJ64
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  obtain ⟨U, hU, hWU, hUβ, h4⟩ := hs.exists_U hKC h412 hW hUW
  have hP := EndB.isSylowTwoIn_inf hU hKc.1 hKc.2.1
  have h8 := EndB.eight_mul_card_inf_le hKK hL' hP hβN hβ2 hβK
  have hPC : U ⊓ K ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) = W ⊓ K := by
    rw [inf_right_comm, hUβ]
  rw [hPC] at h8
  have hcount := EndB.card_inf_le_of_card_le (K := K) hWU h4
  have hpos : 0 < Nat.card ↥(W ⊓ K) := Nat.card_pos
  omega

end Setting46e

namespace EndB

theorem harris413_L3U3
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hGA : TBLit.GriessMultipliersOdd)
    (h219 : Harris82Lemma219Input) (h35 : Harris81Lemma35Step)
    (hC8 : AlternatingCoverInvolutionFact) :
    Harris413L3U3Case := by
  intro X _ _ _ hnab hK hcat t L p f S w z V i j hhyp
  obtain ⟨hs, h412, -, hsimple, -⟩ := hhyp
  exact ⟨fun hY => hs.false_of_L3U3 hnab hK hcat hSch hFC hKC hI hGA h219 h35 hC8 h412
    (Or.inl hY), fun hY => hs.false_of_L3U3 hnab hK hcat hSch hFC hKC hI hGA h219 h35 hC8
    h412 (Or.inr hY)⟩

end EndB

end CFSG.ComponentClassification.HarrisLit
