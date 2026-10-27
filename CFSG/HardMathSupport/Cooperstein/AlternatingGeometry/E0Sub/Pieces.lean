module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Defs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Assembly
import CFSG.Quasithin.Vol2.Ch11SecA11Comp

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def ThetaSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a)

@[expose] def NormSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      L₁ ≤ L ∧ ⁅L₁, L₁⁆ = L₁ ∧ S ≤ Subgroup.normalizer (L₁ : Set G)

@[expose] def CardSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 360

@[expose] def AltQuotSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* alternatingGroup (Fin 6))

@[expose] def NotNormSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      ¬ L₁ ≤ Subgroup.normalizer (S : Set G)

@[expose] def SQTKSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      S ≤ Subgroup.normalizer (L₁ : Set G) →
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* alternatingGroup (Fin 6)) →
      IsSQTKIn (L₁ ⊔ S)

@[expose] def MS2SubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      S ≤ Subgroup.normalizer (L₁ : Set G) →
      ∃ H' : Subgroup G, H' < L₁ ⊔ S ∧ ¬ 2 ∣ H'.relIndex (L₁ ⊔ S) ∧ S = pCoreOf 2 H'

@[expose] def MSPairSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      S ≤ Subgroup.normalizer (L₁ : Set G) →
      IsMSPair (L₁ ⊔ S) S ∧ L₁ ∈ cComp (L₁ ⊔ S) ∧
        ((L₁ ⊔ S : Subgroup G) : Set G) = (L₁ : Set G) * (S : Set G)

@[expose] def ShortCommSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      S ≤ Subgroup.normalizer (L₁ : Set G) →
      IsShort2 L₁ → ⁅pCoreOf 2 (L ⊔ S), L₁⁆ ≤ blockV S L

@[expose] def NormalClosureSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      ⁅pCoreOf 2 (L ⊔ S), L₁⁆ ≤ blockV S L → ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L

@[expose] def NotShortSubLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
    E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
    ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
      (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a) →
      S ≤ Subgroup.normalizer (L₁ : Set G) →
      ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L → ¬ IsShort2 L₁

theorem cardSubLStmt_of_altQuot (h : AltQuotSubLStmt) : CardSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
  obtain ⟨e⟩ := h G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

section Bridges

variable {G : Type} [Group G] [Finite G]

theorem charTwo_sup_of_le {X S L L₁ : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hL₁ : L₁ ≤ L) : CharTwo (L₁ ⊔ S) := by
  have hA' := CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bHyp_sup hA hL hSL
  have hLS : L₁ ⊔ S ≤ L ⊔ S := sup_le_sup_right hL₁ S
  have hQG : pCoreOf 2 (L ⊔ S) ≤ L₁ ⊔ S := hA'.twoCore_le.trans le_sup_right
  have hQ : pCoreOf 2 (L ⊔ S) ≤ pCoreOf 2 (L₁ ⊔ S) := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQG ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQG]
    exact hLS.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S))
  rintro g ⟨hg, hgC⟩
  exact hQ (hA'.charTwo ⟨hLS hg, Subgroup.centralizer_le hQ hgC⟩)

theorem ms3_of_not_le_normalizer {X S L L₁ : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hL₁ : L₁ ≤ L)
    (hnot : ¬ L₁ ≤ Subgroup.normalizer (S : Set G)) :
    ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ L₁ ⊔ S ≤ Subgroup.normalizer (C : Set G) := by
  intro C hCS hC1 hchar hN
  apply hnot
  intro g hg
  have h1 : X ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn X S :=
    le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))
  rw [hA.cgs] at h1
  exact (h1 ⟨hL.le (hL₁ hg), hN (Subgroup.mem_sup_left hg)⟩).2

theorem center_eq_bot_of_alt {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 6)) :
    Subgroup.center Y = ⊥ := by
  have h := Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (by simp)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem isRankTwoLie2Derived_of_alt {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 6)) :
    IsRankTwoLie2Derived (Y ⧸ Subgroup.center Y) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_⟩))))
  exact (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_alt e)).trans
    (QuotientGroup.quotientBot.trans e)

theorem isQuasisimple_of_alt {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 6)) :
    CFSG.IsQuasisimple Y := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hp : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hpY : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have f : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_alt e)).trans
      (QuotientGroup.quotientBot.trans e)
  have hnc : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have h1 : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => hcon a b⟩⟩
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp h1
    simp at this
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨hpY, f.isSimpleGroup, f.symm a, f.symm b, fun h => hab ?_⟩
  simpa using congrArg f h

end Bridges

theorem ccompSubLStmt_holds :
    ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
      (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)),
      E0NS X S L N θ Δ₀ P ω → ∀ a, a ∉ Δ₀ →
      ∀ L₁ : Subgroup G, L₁ = subL S L θ (omegaOne Δ₀ ω a) →
        S ≤ Subgroup.normalizer (L₁ : Set G) →
        Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* alternatingGroup (Fin 6)) →
        L₁ ∈ cComp (L₁ ⊔ S) := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hN ⟨e⟩
  have hperf : ⁅L₁, L₁⁆ = L₁ := hL₁ ▸ subL_perfect S L θ _
  have hne : L₁ ≠ ⊥ := by
    intro h
    have h1 : Nontrivial (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) :=
      (Equiv.nontrivial_congr e.toEquiv).mpr inferInstance
    have h2 : Nontrivial ↥L₁ := (QuotientGroup.mk_surjective (s := CFSG.pCore 2 ↥L₁)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L₁).mp h2 h
  have hsub : IsSubnormal L₁ (L₁ ⊔ S) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hN))
  exact CFSG.Quasithin.Vol2.Ch11.SecA.mem_cComp_of_quasisimple hne hperf
    (isQuasisimple_of_alt e) hsub

theorem msPairSubLStmt_of_pieces (hAlt : AltQuotSubLStmt) (hNot : NotNormSubLStmt)
    (hsqtk : SQTKSubLStmt) (hms2 : MS2SubLStmt) : MSPairSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN
  have hLle : L₁ ≤ L := hL₁ ▸ subL_le S L θ _
  obtain ⟨e⟩ := hAlt G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
  have hc := ccompSubLStmt_holds G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hN ⟨e⟩
  have hprod : ((L₁ ⊔ S : Subgroup G) : Set G) = (L₁ : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L₁ S hN
  refine ⟨⟨⟨hsqtk G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hN ⟨e⟩,
      charTwo_sup_of_le hE.asc hE.block.toIsTwoPrimeComponent hE.normalizes hLle, L₁, hc, hprod,
      isRankTwoLie2Derived_of_alt e⟩,
    Or.inl (hms2 G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN),
    ms3_of_not_le_normalizer hE.asc hE.block.toIsTwoPrimeComponent hLle
      (hNot G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁)⟩, hc, hprod⟩

theorem notShortSubLStmt_of_pieces (hshort : ShortCommSubLStmt) (hclos : NormalClosureSubLStmt) :
    NotShortSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN hQL hs
  exact hQL (hclos G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
    (hshort G X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN hs))

theorem e0SubConfigStatement_of_pieces (h1 : ThetaSubLStmt) (h2 : NormSubLStmt)
    (h3 : CardSubLStmt) (h4 : MSPairSubLStmt) (h5 : NotShortSubLStmt) : E0SubConfigStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ hωfree hθ
    hshort
  have hE : E0NS X S L N θ Δ₀ P ω :=
    { six_le := hN, card_Δ₀ := hΔ₀, card_P := hPc, P_sq := hPsq, P_fix := hPfix,
      P_trans := hPtrans, ω_invol := hωω, ω_fix := hωΔ, ω_free := hωfree, asc := hA, block := hL,
      normalizes := hSL, natural := hNS, ker_le := hθS, image_S := hθ }
  obtain ⟨a, ha⟩ := hE.toE0Data.exists_not_mem
  have hθ₁ := h1 G X S L N θ Δ₀ P ω hE a ha _ rfl
  obtain ⟨hle, hperf, hnorm⟩ := h2 G X S L N θ Δ₀ P ω hE a ha _ rfl
  obtain ⟨hMS, hcomp, hprod⟩ := h4 G X S L N θ Δ₀ P ω hE a ha _ rfl hθ₁ hnorm
  exact ⟨_, hle, hperf, hnorm, hMS, hcomp, hprod, h3 G X S L N θ Δ₀ P ω hE a ha _ rfl hθ₁,
    h5 G X S L N θ Δ₀ P ω hE a ha _ rfl hθ₁ hnorm hshort⟩

theorem e0SubConfigStatement_of_fine_pieces (h1 : ThetaSubLStmt) (h2 : NormSubLStmt)
    (h3 : AltQuotSubLStmt) (h4 : NotNormSubLStmt) (h5 : SQTKSubLStmt) (h6 : MS2SubLStmt)
    (h7 : ShortCommSubLStmt) (h8 : NormalClosureSubLStmt) : E0SubConfigStatement :=
  e0SubConfigStatement_of_pieces h1 h2 (cardSubLStmt_of_altQuot h3)
    (msPairSubLStmt_of_pieces h3 h4 h5 h6) (notShortSubLStmt_of_pieces h7 h8)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
