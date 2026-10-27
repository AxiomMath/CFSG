module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Graph
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Lemma47

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {K : Subgroup G} {t : G}
    (hK : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hK]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hK] at hy
    obtain ⟨k, hk, hky⟩ := hy
    have : k = y := (MulAut.conj t).injective hky
    rwa [← this]

theorem component_data {G : Type} [Group G] [Finite G] {Kb : Subgroup G} (hKb : IsComponent Kb)
    (hO : pPrimeCore 2 G = ⊥) {Q : Type} [Group Q] (e : ↥Kb ≃* Q) :
    Nonempty (↥Kb ⧸ Open.fusionZStar ↥Kb ≃* Q ⧸ center Q) ∧
      Nat.card ↥(GrSLit.zStarIn Kb) = Nat.card ↥(center Q) * Nat.card ↥(GrSLit.oddIn Kb) ∧
      ⁅Kb, Kb⁆ = Kb := by
  have hOK : pPrimeCore 2 ↥Kb = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hKb.2
  have hZ := fusionZStar_eq_center_of_pPrimeCore_eq_bot hOK
  have hZmap := OuterAutomorphisms.center_map_equiv e
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.congr (center ↥Kb) (center Q) e hZmap)⟩, ?_,
    commutator_self_eq_of_isPerfect hKb.1.1⟩
  have h1 : Nat.card ↥(GrSLit.zStarIn Kb) = Nat.card ↥(center Q) := by
    unfold GrSLit.zStarIn
    rw [Subgroup.card_map_of_injective Kb.subtype_injective, hZ, ← hZmap,
      Subgroup.card_map_of_injective e.injective]
  have h2 : Nat.card ↥(GrSLit.oddIn Kb) = 1 := by
    unfold GrSLit.oddIn
    rw [hOK, Subgroup.map_bot, card_bot]
  rw [h1, h2, mul_one]

end Lemma47

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

omit [Finite X] in
theorem t_mem_centralizer_z (hσ : Setup42 h hS w z) : t ∈ centralizer ({z} : Set X) := by
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzH).symm

theorem lemma35_data [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (_hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (h219 : Harris82Lemma219Input) (h35 : Harris81Lemma35Step)
    (hC8 : AlternatingCoverInvolutionFact) (hσ : Setup42 h hS w z) (i j : ℕ) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
      centralizer {z})) (hM : IsMTypeSchur p ↥J) (hzJ : z ∈ J) {k : ℕ} (hk : 1 ≤ k)
    (hs5 : 5 ≤ p ^ k) (hJsl : IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J)) :
    ∃ K : Subgroup X, IsTwoComponentIn K (centralizer {z}) ∧
      J = GSThmB.layerIn (K ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      K.map (MulAut.conj t).toMonoidHom = K ∧ IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
      GrSLit.IsL34Type ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
  have hp : p.Prime := h.config.prime
  have hp2 : p ≠ 2 := h.config.ne_two
  have hβ2 := hσ.orderOf_beta i j
  have hzβ := hσ.z_mem_centralizer_beta hFC hKC i j
  have hz1 : z ≠ 1 := fun h1 => by
    have := hσ.z_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hW := Lemma47.fourGroup_closure_pair hβ2 hσ.z_order (hσ.z_ne_beta i j)
    (mem_centralizer_singleton_iff.mp hzβ).symm
  have hCW := Lemma47.centralizer_closure_pair (w ^ (orderOf w / 2) * t ^ i * z ^ j) z
  have hJW : IsTwoComponentIn J (centralizer ((closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} :
      Subgroup X) : Set X)) := by
    rw [hCW]; exact hJ
  have hzW : z ∈ (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :=
    subset_closure (Set.mem_insert _ _)
  have hβz : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ zpowers z := by
    intro h1
    rcases eq_one_or_eq_of_mem_zpowers_two hσ.z_order h1 with h1 | h1
    · rw [h1, orderOf_one] at hβ2; exact absurd hβ2 (by norm_num)
    · exact hσ.z_ne_beta i j h1.symm
  have hJW' : J ⊓ (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) ≠ ⊥ := by
    intro hb
    have : z ∈ (⊥ : Subgroup X) := hb ▸ ⟨hzJ, hzW⟩
    exact hz1 (mem_bot.mp this)
  obtain ⟨-, -, hKc, -, hJeq, hcases⟩ :=
    h35 X hnonab hK hcat p hp hp2 _ hW.1 hW.2 J hJW hM k hk hs5 hJsl hJW' z ⟨hzJ, hzW⟩ hz1 _
      hβW hβz _ rfl
  set K := GSThmB.conjClosure J (GSThmB.layerIn (centralizer {z}))
  have h44z := (hσ.isPGroup_quot_centralizer_z hI).1
  have htz := hσ.t_mem_centralizer_z
  have hKt := map_conj_eq_of_isTwoComponentIn h219 h.config.orderOf_eq htz h44z hKc
  have hCK := isPGroup_quot_inf_centralizer h44z hKc.1
  have htN := Lemma47.mem_normalizer_of_map_conj_eq hKt
  have ht2 : t * t = 1 := by rw [← sq, ← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hKK : ⁅K, K⁆ = K := Lemma47.commutator_self_eq_of_isPerfect hKc.2.2.1
  obtain ⟨eZ⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥K
  refine ⟨K, hKc, hJeq, hKt, ?_⟩
  rcases hcases with ⟨-, -, hq, h16, hL⟩ | ⟨-, -, n, hn, -, -, ⟨e⟩⟩ | ⟨-, -, n, hn, -, -, ⟨e⟩⟩
  · exact ⟨hq, h16, hL⟩
  · exact absurd hCK (hC8 X K t (2 * n + 1) (by omega) hKK ⟨eZ.trans e⟩ htN ht2)
  · exact absurd hCK (hC8 X K t (2 * n) (by omega) hKK ⟨eZ.trans e⟩ htN ht2)

theorem false_of_graph [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKG : AutPSL2SylowInput)
    (hGA : TBLit.GriessMultipliersOdd) (h219 : Harris82Lemma219Input)
    (h35 : Harris81Lemma35Step) (hC5 : L34CoverInvolutionFact)
    (hC8 : AlternatingCoverInvolutionFact) (hσ : Setup42 h hS w z) (i j : ℕ) {k : ℕ}
    (hk : 1 ≤ k) (hs5 : 5 ≤ p ^ k)
    (hgraph : ∀ w' ∈ GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {hσ.tBar i j}), orderOf w' = 2 →
      ∃ X₁ X₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), X₁ ≠ X₂ ∧
        X₁ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
        X₂ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
        (X₁.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {w'})).IsSubnormal ∧
        (X₂.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {w'})).IsSubnormal ∧
        X₁ ≤ centralizer (X₂ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
        X₁ ⊓ X₂ = zpowers w' ∧ IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J₁, J₂, hne, ⟨hJ₁, hM₁, hz₁, hsl₁⟩, ⟨hJ₂, hM₂, hz₂, hsl₂⟩⟩ :=
    hσ.exists_two_components hnonab hK hSch hFC hKC hGA i j hk hs5 hgraph
  obtain ⟨K₁, hK₁c, hJ₁eq, hK₁t, -, h16₁, hL₁⟩ :=
    hσ.lemma35_data hnonab hK hcat hSch hFC hKC hI h219 h35 hC8 i j hJ₁ hM₁ hz₁ hk hs5 hsl₁
  obtain ⟨K₂, hK₂c, hJ₂eq, hK₂t, -, h16₂, hL₂⟩ :=
    hσ.lemma35_data hnonab hK hcat hSch hFC hKC hI h219 h35 hC8 i j hJ₂ hM₂ hz₂ hk hs5 hsl₂
  have hK12 : K₁ ≠ K₂ := fun h12 => hne (by rw [hJ₁eq, hJ₂eq, h12])
  have h44z := (hσ.isPGroup_quot_centralizer_z hI).1
  have htz := hσ.t_mem_centralizer_z
  obtain ⟨hKb₁, ⟨e₁⟩, hN₁, hC₁⟩ := Lemma47.fbar_component htz h.config.orderOf_eq h44z hK₁c hK₁t
  obtain ⟨hKb₂, ⟨e₂⟩, hN₂, hC₂⟩ := Lemma47.fbar_component htz h.config.orderOf_eq h44z hK₂c hK₂t
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hKb12 : (K₁.subgroupOf (centralizer {z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) ≠
      (K₂.subgroupOf (centralizer {z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) := by
    intro heq
    obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))
      (QuotientGroup.mk'_surjective _)
      (GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥(centralizer ({z} : Set X))))
    have h1 := hbij.injOn ((isTwoComponentIn_iff hK₁c.1).mp hK₁c)
      ((isTwoComponentIn_iff hK₂c.1).mp hK₂c) heq
    apply hK12
    rw [← inf_eq_left.mpr hK₁c.1, ← inf_eq_left.mpr hK₂c.1, ← subgroupOf_map_subtype,
      ← subgroupOf_map_subtype, h1]
  have ht2 : (QuotientGroup.mk ⟨t, htz⟩ : MBar z) * QuotientGroup.mk ⟨t, htz⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨t, htz⟩ : ↥(centralizer ({z} : Set X))) * ⟨t, htz⟩ = 1 :=
      Subtype.ext (by
        change t * t = 1
        rw [← sq, ← h.config.orderOf_eq, pow_orderOf_eq_one])
    rw [this, QuotientGroup.mk_one]
  obtain ⟨⟨eZ₁⟩, hc₁, hKK₁⟩ := Lemma47.component_data hKb₁ hO e₁
  obtain ⟨⟨eZ₂⟩, hc₂, hKK₂⟩ := Lemma47.component_data hKb₂ hO e₂
  obtain ⟨E₁, hE₁le, hE₁, hE₁Z, hE₁c⟩ := hC5 (MBar z) _ _ hKK₁
    (GSThmB.OddQuot.lieModel_of_equiv eZ₁.symm hL₁) (by rw [hc₁, h16₁]) hN₁ ht2 hC₁
  obtain ⟨E₂, hE₂le, hE₂, -, hE₂c⟩ := hC5 (MBar z) _ _ hKK₂
    (GSThmB.OddQuot.lieModel_of_equiv eZ₂.symm hL₂) (by rw [hc₂, h16₂]) hN₂ ht2 hC₂
  obtain ⟨E, hEt, hE, hE16⟩ := Lemma47.exists_elemTwo_gt_sixteen hKb₁ hKb₂ hKb12 ht2 hE₁le hE₂le
    hE₁ hE₂ hE₁Z hE₁c hE₂c
  have hle := h.card_le_sixteen_of_le_centralizer_bar hKG htz hEt hE
  exact lt_irrefl _ (hE16.trans_le hle)

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
