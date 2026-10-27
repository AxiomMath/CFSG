module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexW
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineOddInnWPerm
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
public import Certificates.Certificate43
public import Certificates.Certificate7067
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineOddInnWSmall
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTypes
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveInner
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLie
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.RankThree.OddKernel.FailureReduction
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeAt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartTwo.Sec18.Transport
import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime Subgroup Equiv
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open scoped commutatorElement

@[expose] def KFactCompParabFieldIndexWAt (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → L.Normal →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) → p ∣ Nat.card (wPre P) →
    Open.pRank p (wPre P) ≤ 1 → ∀ a : Y, IsPGroup p (Subgroup.zpowers a) →
    a ∈ Subgroup.normalizer (P : Set Y) →
    (¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) →
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p

theorem oddInnW_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (h : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g) : OddInnW X := by
  intro α _
  obtain ⟨g, rfl⟩ := h α
  haveI hWn : (wSup X).Normal := ⟨fun n hn c => by
    rw [← map_wSup_eq (MulAut.conj c)]
    exact ⟨n, hn, rfl⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (wSup X) with hW | hW
  · refine ⟨1, one_mem _, fun x hx => ?_⟩
    rw [hW, mem_bot] at hx
    simp [hx]
  · exact ⟨g, hW ▸ mem_top g, fun x _ => rfl⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem pCore_eq_bot_of_mulEquiv_quotient {J : Subgroup Y} {X : Type} [Group X]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* X) : CFSG.pCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.pCore_map_iso 2 e, CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot,
    Subgroup.map_bot]

theorem pRank_wSup_le_pRank_wPre (J : Subgroup Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Open.pRank p (wSup (↥J ⧸ CFSG.pCore 2 ↥J)) ≤ Open.pRank p (wPre J) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  set C := (wSup (↥J ⧸ CFSG.pCore 2 ↥J)).comap mk
  have h1 : Open.pRank p (C.map mk) ≤ Open.pRank p C :=
    TenElevenOneLie.pRank_map_le hp mk (by
      rw [QuotientGroup.ker_mk']
      exact not_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup hp hp2) C
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
  have h2 : Open.pRank p C ≤ Open.pRank p (C.map J.subtype) :=
    CFSG.RankThree.OddKernel.pRank_le_map_of_not_dvd hp _ C (by
      rw [Subgroup.ker_subtype, Subgroup.card_bot]
      exact hp.not_dvd_one)
  exact h1.trans h2

theorem odd_orderOf_of_isPGroup {a : Y} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : IsPGroup p (Subgroup.zpowers a)) : Odd (orderOf a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp ha ⟨a, mem_zpowers a⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem oddInnW_sp_two {k : ℕ} {d : TauCeti.ValidLieTypeIndex} (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) :
    OddInnW (TauCeti.CFSGIndex.lie d).Group := by
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := (kFactSpTwoSimple_holds k d hk hd).1
  refine oddInnW_of_isSimpleGroup ?_
  obtain ⟨d₁, hv⟩ := d
  obtain ⟨q, hq, hd₁⟩ := hd
  change d₁ = .B k q at hd₁
  subst hd₁
  have hp2 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hp : q.p = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).1 hp2).1
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hp hk
    (G := TauCeti.ValidLieTypeIndex.Group ⟨.B k q, hv⟩) (MulEquiv.refl _)
  rw [hp] at h
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; rw [hp] at hp2; exact hp2
  intro α
  obtain ⟨g, hg⟩ := inn_statedProj_sp_two hk hK2 (MulAut.congr e' α)
  refine ⟨e'.symm g, MulEquiv.ext fun x => e'.injective ?_⟩
  have h1 := congrArg (fun β : MulAut _ => β (e' x)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [← h1]
  simp [MulAut.conj_apply]

theorem pCore_two_perm_two_prod_ne_bot (X : Type) [Group X] :
    CFSG.pCore 2 (Perm (Fin 2) × X) ≠ ⊥ := by
  set N0 : Subgroup (Perm (Fin 2) × X) := (⊤ : Subgroup (Perm (Fin 2))).prod ⊥
  have hN0 : N0.Normal := Subgroup.prod_normal ⊤ ⊥
  have hsq : ∀ σ : Perm (Fin 2), σ ^ 2 = 1 := by decide
  have hN0p : IsPGroup 2 N0 := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simpa using hsq x.1
    · have : x.2 = 1 := (Subgroup.mem_prod.mp hx).2
      simp [this]
  have hle : N0 ≤ CFSG.pCore 2 (Perm (Fin 2) × X) := le_sSup ⟨hN0, hN0p⟩
  intro hbot
  have hmem : ((Equiv.swap (0 : Fin 2) 1 : Perm (Fin 2)), (1 : X)) ∈ N0 :=
    Subgroup.mem_prod.mpr ⟨mem_top _, one_mem _⟩
  have h1 := hle hmem
  rw [hbot, mem_bot, Prod.ext_iff] at h1
  have hs : (Equiv.swap (0 : Fin 2) 1 : Perm (Fin 2)) ≠ 1 := by decide
  exact hs h1.1

theorem nineThreeTwo_of_not_inner_wPre {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G} (hyps : BlockL28Hyps M S L)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3)
    (hdvd : p ∣ Nat.card (wPre (blockPL M S L))) (hrk : Open.pRank p (wPre (blockPL M S L)) ≤ 1)
    {a : ↥M ⧸ CFSG.pCore 2 ↥M} (ha : IsPGroup p (Subgroup.zpowers a))
    (hN : a ∈ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hout : ¬ ∃ v ∈ wPre (blockPL M S L), ∀ w ∈ wPre (blockPL M S L),
      ⁅a * v, w⁆ ∈ pCoreOf 2 (blockPL M S L)) : NineThreeTwo M S L := by
  obtain ⟨hK, hA, hL, h93, hX, hS⟩ := id hyps
  set J := blockPL M S L with hJdef
  have hJL : J ≤ barM M L := fun x ⟨y, hy, hyx⟩ => ⟨y, (Subgroup.mem_inf.1 hy).2, hyx⟩
  have hodd := odd_orderOf_of_isPGroup hp hp2 ha
  have hinn : ∀ {X : Type} [Group X], (↥J ⧸ CFSG.pCore 2 ↥J ≃* X) → OddInnW X → False :=
    fun e h => hout (exists_inner_wPre_of_oddInnW (h.of_mulEquiv e) hN hodd)
  have hsolv : Nat.card J ∣ 72 → False := by
    intro h72
    have h1 : p ∣ 2 ^ 3 * 3 ^ 2 := hdvd.trans ((Subgroup.card_dvd_of_le (wPre_le J)).trans h72)
    have hp3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    subst hp3
    exact hinn (MulEquiv.refl _) (oddInnW_of_card_dvd_seventyTwo
      ((Subgroup.card_quotient_dvd_card _).trans h72)
      (pCore_eq_bot_of_mulEquiv_quotient (MulEquiv.refl _))
      ((pRank_wSup_le_pRank_wPre J hp hp2).trans hrk))
  rcases h93 with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact h2
  · exfalso
    rcases citedBlockTransvectionPL_of_type
        CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
        G M S L hK hA hL hX hS h3' with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
    · exact hinn e (oddInnW_sp_two hk hd)
    · exact hinn e (oddInnW_perm (pCore_eq_bot_of_mulEquiv_quotient e))
  · exfalso
    obtain ⟨-, hZ3, -, -, ⟨e⟩⟩ := h4
    set Z := Subgroup.center ↥(barM M L)
    set I : Subgroup (↥(barM M L) ⧸ Z) :=
      ((blockPL M S L).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
    set φ : ↥J →* ↥(barM M L) ⧸ Z := (QuotientGroup.mk' Z).comp (Subgroup.inclusion hJL)
    have hrange : φ.range ≤ I := by
      rintro _ ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hJL x, x.2, rfl⟩
    have hcen : ∀ x : φ.ker, Subgroup.inclusion hJL (x : ↥J) ∈ Z := fun x =>
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 x.2)
    have hker : Nat.card φ.ker ∣ 3 := by
      have h1 : Nat.card (φ.ker.map (Subgroup.inclusion hJL)) = Nat.card φ.ker :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJL)
      have h2 : φ.ker.map (Subgroup.inclusion hJL) ≤ Z := by
        rintro _ ⟨x, hx, rfl⟩
        exact hcen ⟨x, hx⟩
      rw [← h1, ← hZ3]
      exact Subgroup.card_dvd_of_le h2
    have hran : Nat.card φ.range ∣ 24 := by
      have h1 : Nat.card I = 24 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
        rfl
      rw [← h1]
      exact Subgroup.card_dvd_of_le hrange
    have h72 : Nat.card J ∣ 72 := by
      rw [← Subgroup.card_ker_mul_card_range φ]
      exact Nat.mul_dvd_mul hker hran
    exact hsolv h72
  · exfalso
    have h72 := citedBlockAltSevenPL_holds G M S L hK hA hL hX hS h5
    exact hsolv h72
  · exfalso
    obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact hinn e (oddInnW_perm (pCore_eq_bot_of_mulEquiv_quotient e))
  · exfalso
    obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact hinn e (oddInnW_perm (pCore_eq_bot_of_mulEquiv_quotient e))
  · exfalso
    obtain ⟨-, N, r, hN, h2r, h0, h2, h4', ⟨ψ⟩, φ, -⟩ := h8
    have hm6 : 6 ≤ N - 2 * r := by
      obtain ⟨t, ht⟩ := hN
      omega
    have hN11 : N ≤ 11 := by
      by_contra hN12
      have h1 := div_three_le_pRank_of_alt ψ
      have h2' := hrank 3 Nat.prime_three (by norm_num)
      omega
    have hO := pCore_eq_bot_of_mulEquiv_quotient φ
    rcases Nat.lt_or_ge r 2 with hr | hr
    · haveI : Subsingleton (Fin r) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hr)
      let e2 : (Perm (Fin r) × Perm (Fin (N - 2 * r))) ≃* Perm (Fin (N - 2 * r)) :=
        MulEquiv.ofBijective (MonoidHom.snd _ _)
          ⟨fun x y h => Prod.ext (Subsingleton.elim _ _) h, fun y => ⟨(1, y), rfl⟩⟩
      exact hinn (φ.trans e2) (oddInnW_perm (pCore_eq_bot_of_mulEquiv_quotient (φ.trans e2)))
    · obtain rfl : r = 2 := by omega
      exact pCore_two_perm_two_prod_ne_bot _ hO

theorem kFactBlockFieldIndexWAt_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : KFactCompParabFieldIndexWAt p) :
    KFactBlockFieldIndexWAt p := by
  intro G _ _ M S L hyps hQS hLn hrank hdvd hrk a ha hN hout
  exact hC _ _ _ (KFactProofs.compParab_of_blockHyps hyps
      (nineThreeTwo_of_not_inner_wPre hp hp2 hyps hrank hdvd hrk ha hN hout))
    (hLn.map _ (QuotientGroup.mk'_surjective _)) hrank hdvd hrk a ha hN hout

end CFSG.LocalAnalysis.RankThreeTheoremC
