module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupCases
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2168
public import Certificates.Certificate2170
public import Certificates.Certificate2171
public import Certificates.Certificate2172
public import Certificates.Certificate2173
public import Certificates.Certificate2174
public import Certificates.Certificate2176
public import Certificates.Certificate2177
public import Certificates.Certificate2178
public import Certificates.Certificate2179
public import Certificates.Certificate2180
public import Certificates.Certificate2181
public import Certificates.Certificate2182
public import Certificates.Certificate2183
public import Certificates.Certificate2218
public import Certificates.Certificate2219
public import Certificates.Certificate2240
public import Certificates.Certificate2241
public import Certificates.Certificate2242
public import Certificates.Certificate2243
public import Certificates.Certificate2244
public import Certificates.Certificate2245
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate2272
public import Certificates.Certificate2274
public import Certificates.Certificate2284
public import Certificates.Certificate2285
public import Certificates.Certificate2288
public import Certificates.Certificate3017
public import Certificates.Certificate3084
public import Certificates.Certificate3170
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8129
public import Certificates.Certificate9123
public import Certificates.Certificate9125
public import Certificates.Certificate9126
public import Certificates.Certificate9212
public import Certificates.Certificate9215
public import Certificates.Certificate9216
public import Certificates.Certificate9357
public import Certificates.Certificate9530
public import Certificates.Certificate10095
public import Certificates.Certificate12601
public import Certificates.Certificate12602
public import Certificates.Certificate12603
public import Certificates.Certificate12605
public import Certificates.Certificate19761
public import Certificates.Certificate19765
public import Certificates.Certificate19766
public import Certificates.Certificate41721
public import Certificates.Certificate41722
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigJ4
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigMcL
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSz
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTits
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialAlt
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J4SEleven
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate10095Base
import CFSG.Foundations
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.Sporadic.J4.QT2LocCntProof
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Certificates.Data.HSFiveCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC Subgroup

section Bridge

variable {X : Type} [Group X] {K : Subgroup X} [K.Normal]

private theorem conjNormal_eq_one_iff {x : X} :
    (MulAut.conjNormal x : MulAut K) = 1 ↔ x ∈ centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx k hk
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = x * k * x⁻¹ * x := by rw [h1]
      _ = x * k := by group
  · intro hx
    ext k
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    calc x * (k : X) * x⁻¹ = (k : X) * x * x⁻¹ := by rw [← hx k k.2]
      _ = k := by group

private theorem conjNormal_mem {b : X} (hb : b ∈ K) :
    (MulAut.conjNormal b : MulAut K) = MulAut.conj (⟨b, hb⟩ : K) :=
  MulAut.conjNormal_val (h := ⟨b, hb⟩)

private theorem card_map_conjNormal {B : Subgroup X} (hBC : B ⊓ centralizer (K : Set X) = ⊥) :
    Nat.card (B.map (MulAut.conjNormal : X →* MulAut K)) = Nat.card B := by
  have hinj : Set.InjOn (MulAut.conjNormal : X →* MulAut K) (B : Set X) := by
    intro a ha b hb hab
    have h1 : (MulAut.conjNormal (a⁻¹ * b) : MulAut K) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ B ⊓ centralizer (K : Set X) :=
      ⟨B.mul_mem (B.inv_mem ha) hb, conjNormal_eq_one_iff.1 h1⟩
    rw [hBC, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  exact (Nat.card_congr (Equiv.Set.imageOfInjOn _ _ hinj)).symm

private theorem coprime_card_map [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Subgroup X} (hT : IsPGroup 2 T) :
    p.Coprime (Nat.card (T.map (MulAut.conjNormal : X →* MulAut K))) := by
  obtain ⟨k, hk⟩ := (hT.map (MulAut.conjNormal : X →* MulAut K)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem commutator_le_centralizer_of_signalizerAutAt [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {i : TauCeti.CFSGIndex} (h : SignalizerAutAt p i)
    (hK : Nonempty (↥K ≃* i.Group)) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) (hBC : B ⊓ centralizer (K : Set X) = ⊥)
    (hin : B ≤ K ∨ GL83OuterType24 p i)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hBT : B ≤ normalizer (T : Set X)) :
    ⁅B, T⁆ ≤ centralizer (K : Set X) := by
  set θ : X →* MulAut K := MulAut.conjNormal
  have hnorm : B.map θ ≤ normalizer ((T.map θ : Subgroup (MulAut K)) : Set (MulAut K)) :=
    (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map θ)
  have hin' : B.map θ ≤ (MulAut.conj : K →* MulAut K).range ∨ GL83OuterType24 p i := by
    rcases hin with hBK | hout
    · refine Or.inl ?_
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b, hBK hb⟩, (conjNormal_mem (hBK hb)).symm⟩
    · exact Or.inr hout
  have hcent := h K hK (B.map θ) (T.map θ) (hB.map θ) ((card_map_conjNormal hBC).trans hBc)
    (coprime_card_map hp hp2 hT) hnorm hin'
  rw [Subgroup.commutator_le]
  intro b hb t ht
  rw [← conjNormal_eq_one_iff (K := K), map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_map_of_mem θ hb)) (θ t)
    (Subgroup.mem_map_of_mem θ ht)).symm

theorem twoSignalizerOn_of_exists_signalizerAutAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {C : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Prop}
    (hC : ∀ (X : Type) [Group X] (K B : Subgroup X), C X K B → ∃ i : TauCeti.CFSGIndex,
      SignalizerAutAt p i ∧ Nonempty (↥K ≃* i.Group) ∧ (B ≤ K ∨ GL83OuterType24 p i)) :
    TwoSignalizerOn p C := by
  intro X _ _ K hKn _ _ B hB hBc hBC hCB T hT hBT
  haveI := hKn
  obtain ⟨i, h, hK, hin⟩ := hC X K B hCB
  exact commutator_le_centralizer_of_signalizerAutAt hp hp2 h hK hB hBc hBC hin hT hBT

theorem twoSignalizerOn_of_signalizerAutAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : TauCeti.CFSGIndex} (h : SignalizerAutAt p i)
    {C : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Prop}
    (hC : ∀ (X : Type) [Group X] (K B : Subgroup X), C X K B →
      Nonempty (↥K ≃* i.Group) ∧ (B ≤ K ∨ GL83OuterType24 p i)) :
    TwoSignalizerOn p C :=
  twoSignalizerOn_of_exists_signalizerAutAt hp hp2 fun X _ K B hCB =>
    ⟨i, h, (hC X K B hCB).1, (hC X K B hCB).2⟩

end Bridge

section Cases

theorem twoSignalizerJ4_holds :
    TwoSignalizerJ4 :=
  twoSignalizerOn_of_signalizerAutAt (by norm_num) (by norm_num) (signalizerAutAt_jFour rfl)
    fun _ _ _ _ ⟨e, hBK⟩ => ⟨e, Or.inl hBK⟩

theorem twoSignalizerSz32_holds :
    TwoSignalizerSz32 := by
  refine twoSignalizerOn_of_exists_signalizerAutAt (by norm_num) (by norm_num) ?_
  rintro X _ K B ⟨hv, ⟨e⟩⟩
  exact ⟨.lie ⟨.suzuki 2, hv⟩, signalizerAutAt_suzuki rfl rfl, ⟨e⟩,
    Or.inr ⟨⟨.suzuki 2, hv⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem twoSignalizerL28_of
    (h : ∀ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsLinTwoIndex 2 3 d →
      SignalizerAutAt 3 (.lie d)) : TwoSignalizerL28 := by
  refine twoSignalizerOn_of_exists_signalizerAutAt Nat.prime_three (by norm_num) ?_
  rintro X _ K B ⟨hv, ⟨e⟩⟩
  have hd : CFSG.AGLEmbedding.IsLinTwoIndex 2 3 ⟨_, hv⟩ :=
    ⟨⟨2, 3, by norm_num, by norm_num⟩, rfl, rfl, rfl⟩
  exact ⟨.lie ⟨_, hv⟩, h _ hd, ⟨e⟩, Or.inr ⟨⟨_, hv⟩, rfl, Or.inl ⟨rfl, hd⟩⟩⟩

end Cases

section Alt

private theorem not_pow_three_dvd_factorial {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ¬ p ^ 3 ∣ (2 * p).factorial := by
  have hlog : Nat.log p (2 * p) < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    nlinarith
  rw [hp.pow_dvd_factorial_iff hlog]
  have h1 : 2 * p / p = 2 := Nat.mul_div_cancel _ hp.pos
  simp [h1]

theorem twoSignalizerAlt_holds : TwoSignalizerAlt := by
  intro p hp hp5 X _ _ K hKn _ _ B hB hBc _ ⟨⟨e⟩, hBK⟩ T hT hBT
  haveI := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  set θ : X →* MulAut K := MulAut.conjNormal
  have hB'card : Nat.card (B.subgroupOf K) = p ^ 2 := by
    have h := Subgroup.card_map_of_injective (K := B.subgroupOf K) K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBK] at h
    rw [← h, hBc]
  have hB'p : IsPGroup p (B.subgroupOf K) := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hB.2 g.1.1 g.2
  obtain ⟨P, hBP⟩ := hB'p.exists_le_sylow
  have hKcard : ¬ p ^ 3 ∣ Nat.card K := by
    intro hdvd
    haveI : Nontrivial (Fin (2 * p)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    apply not_pow_three_dvd_factorial hp (by omega)
    have hA : 2 * Nat.card (alternatingGroup (Fin (2 * p))) = (2 * p).factorial := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    rw [← hA, ← Nat.card_congr e.toEquiv]
    exact Dvd.dvd.mul_left hdvd 2
  have hPcard : Nat.card (P : Subgroup K) ≤ p ^ 2 := by
    rw [Sylow.card_eq_multiplicity]
    refine Nat.pow_le_pow_right hp.pos ?_
    by_contra hlt
    exact hKcard ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 (by omega))
  have hBP' : B.subgroupOf K = P :=
    Subgroup.eq_of_le_of_card_ge hBP (by rw [hB'card]; exact hPcard)
  have hbot : T.map θ = ⊥ := by
    refine SignalizerTrivial.signalizerTrivialAlt_holds p hp hp5 K ⟨e⟩ P (T.map θ)
      (coprime_card_map hp (by omega) hT) ?_
    intro g hg w hw
    rw [← hBP'] at hg
    have hgB : (g : X) ∈ B := hg
    obtain ⟨t, ht, rfl⟩ := hw
    have h1 : (MulAut.conj g : MulAut K) = θ g := (conjNormal_mem g.2).symm
    rw [h1, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, (Subgroup.mem_normalizer_iff.1 (hBT hgB) t).1 ht, rfl⟩
  rw [Subgroup.commutator_le]
  intro b hb t ht
  rw [← conjNormal_eq_one_iff (K := K), map_commutatorElement]
  have h2 : θ t = 1 := by
    have : θ t ∈ T.map θ := Subgroup.mem_map_of_mem θ ht
    rwa [hbot, Subgroup.mem_bot] at this
  rw [h2, commutatorElement_one_right]

end Alt

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
