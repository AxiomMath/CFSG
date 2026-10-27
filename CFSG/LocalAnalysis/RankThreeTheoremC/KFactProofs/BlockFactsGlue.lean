module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Shapes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduce
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.Quasithin.Background.F6ResL28
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce

@[expose] def KFactCompParabPerfectCoreThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → PerfectCoreThree ↥P

@[expose] def KFactCompParabSylowThreeAut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    Group.IsSolvable ↥P → ¬ 3 ∣ (P.subgroupOf L).index → ¬ 27 ∣ Nat.card (MulAut ↥L)

@[expose] def KFactCompParabL28Rank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ∀ N : Subgroup Y, N ≤ P → P ≤ Subgroup.normalizer (N : Set Y) →
    ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥N →* CatGroup d), IsCaseTwoIndex 3 d →
      Function.Surjective ψ →
      ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
        E ⊓ Subgroup.centralizer (L : Set Y) = ⊥

@[expose] def KFactCompParabL28TwoRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ∀ N : Subgroup Y, N ≤ P → P ≤ Subgroup.normalizer (N : Set Y) →
    ∀ (d₁ d₂ : TauCeti.ValidLieTypeIndex) (ψ : ↥N →* CatGroup d₁ × CatGroup d₂),
      IsCaseTwoIndex 3 d₁ → IsCaseTwoIndex 3 d₂ → Function.Surjective ψ →
      3 ≤ Open.pRank 7 L

@[expose] def KFactCompParabPerfectCoreThreeOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → PerfectCoreThree ↥P

variable {G : Type} [Group G] [Finite G]

theorem compParab_of_blockHyps {M S L : Subgroup G} (h : BlockL28Hyps M S L)
    (h2 : NineThreeTwo M S L) : CompParab (barM M L) (blockPL M S L) :=
  LeviBlock.compParab_of_nineThreeTwo h.2.1 h.2.2.1 h.2.2.2.2.2 h2

theorem exists_normal_section_blockPL {M S L T : Subgroup G} (h : BlockL28Hyps M S L)
    (hT : T ≤ Subgroup.normalizer (S : Set G) ⊓ L)
    (hN : Subgroup.normalizer (S : Set G) ⊓ L ≤ Subgroup.normalizer (T : Set G))
    {U : Type} [Group U] [Finite U] [IsSimpleGroup U] (h3 : 3 ∣ Nat.card U)
    (ψ : ↥T →* U) (hψ : Function.Surjective ψ) :
    ∃ T' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), T' ≤ blockPL M S L ∧
      blockPL M S L ≤ Subgroup.normalizer (T' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∃ ψ' : ↥T' →* U, Function.Surjective ψ' := by
  have hLM : L ≤ M := h.2.2.1.le
  have hTM : T ≤ M := (hT.trans inf_le_right).trans hLM
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_surj_barM h3 hTM ψ hψ
  exact ⟨barM M T, barM_mono hT, barM_le_normalizer_barM hN, ψ', hψ'⟩

theorem exists_normal_section_blockPL₂ {M S L T : Subgroup G} (h : BlockL28Hyps M S L)
    (hT : T ≤ Subgroup.normalizer (S : Set G) ⊓ L)
    (hN : Subgroup.normalizer (S : Set G) ⊓ L ≤ Subgroup.normalizer (T : Set G))
    {U₁ U₂ : Type} [Group U₁] [Group U₂] [Finite U₁] [Finite U₂] [IsSimpleGroup U₁]
    [IsSimpleGroup U₂] (h₁ : 3 ∣ Nat.card U₁) (h₂ : 3 ∣ Nat.card U₂)
    (ψ : ↥T →* U₁ × U₂) (hψ : Function.Surjective ψ) :
    ∃ T' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), T' ≤ blockPL M S L ∧
      blockPL M S L ≤ Subgroup.normalizer (T' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∃ ψ' : ↥T' →* U₁ × U₂, Function.Surjective ψ' := by
  have hLM : L ≤ M := h.2.2.1.le
  have hTM : T ≤ M := (hT.trans inf_le_right).trans hLM
  have hs₁ : Function.Surjective ((MonoidHom.fst U₁ U₂).comp ψ) := by
    intro a
    obtain ⟨x, hx⟩ := hψ (a, (1 : U₂))
    exact ⟨x, by simp [hx]⟩
  have hs₂ : Function.Surjective ((MonoidHom.snd U₁ U₂).comp ψ) := by
    intro b
    obtain ⟨x, hx⟩ := hψ ((1 : U₁), b)
    exact ⟨x, by simp [hx]⟩
  have hker : (LeviBlock.toBarM hTM).ker ≤ ψ.ker := by
    intro x hx
    have hK2 := LeviBlock.isPGroup_ker_toBarM hTM
    have a1 := LeviBlock.le_ker_of_isPGroup_two h₁ ((MonoidHom.fst U₁ U₂).comp ψ) hs₁
      (K := (LeviBlock.toBarM hTM).ker) hK2 hx
    have a2 := LeviBlock.le_ker_of_isPGroup_two h₂ ((MonoidHom.snd U₁ U₂).comp ψ) hs₂
      (K := (LeviBlock.toBarM hTM).ker) hK2 hx
    exact Prod.ext a1 a2
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_factor (LeviBlock.toBarM hTM)
    (LeviBlock.toBarM_surjective hTM) ψ hψ hker
  exact ⟨barM M T, barM_mono hT, barM_le_normalizer_barM hN, ψ', hψ'⟩

theorem perfectCoreThree_of_perfect {Q : Type*} [Group Q] [Finite Q]
    (hQ : commutator Q = ⊤) (h3 : 3 ∣ Nat.card Q) : PerfectCoreThree Q := by
  intro k hk
  have hall : ∀ n, derivedSeries Q n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero Q
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact hQ
  right
  rw [hall k, Subgroup.card_top]
  exact h3

theorem kFactBlockPerfectCoreThree_of (hC : KFactCompParabPerfectCoreThree) :
    KFactBlockPerfectCoreThree := by
  intro G _ _ M S L hyps hcases
  obtain ⟨hK, hA, hL, h93, hX, hS⟩ := id hyps
  rcases hcases with h2 | h3 | h5
  · exact hC _ _ _ (compParab_of_blockHyps hyps h2)
  · rcases citedBlockTransvectionPL_of_type
        CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
        G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      refine perfectCoreThree_of_pCore_quotient e (perfectCoreThree_of_perfect
        (kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd) ?_)
      obtain ⟨E, -, hE⟩ := hasE9_sp hk hd
      have h9 := Subgroup.card_subgroup_dvd_card E
      rw [hE] at h9
      exact (dvd_pow_self 3 (by norm_num)).trans h9
    · exact perfectCoreThree_of_pCore_quotient e (perfectCoreThree_perm n)
  · haveI := isSolvable_of_card_dvd_seventyTwo
      (citedBlockAltSevenPL_holds G M S L hK hA hL hX hS h5)
    exact PerfectCoreThree.of_isSolvable

theorem perfectCoreThree_of_hasLeviBlocks {Q P : Type} [Group Q] [Finite Q] [Group P]
    {𝒯 : Set ℕ} (hQ : HasLeviBlocks Q 𝒯) (h3 : ∀ n ∈ 𝒯, 1 < n → 3 ∣ n) (π : Q →* P)
    (hπ : Function.Surjective π) : PerfectCoreThree P := by
  haveI : Finite P := Finite.of_surjective π hπ
  intro k hk
  by_cases hbot : derivedSeries P k = ⊥
  · exact Or.inl hbot
  right
  set D := derivedSeries P k with hD
  have hDD : ⁅D, D⁆ = D := by rw [hD, ← derivedSeries_succ]; exact hk
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hbot
  haveI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDD
  obtain ⟨M, hMn, -, hsimple⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.exists_normal_isSimpleGroup_quotient ↥D
  haveI : M.Normal := hMn
  have hnab : ∃ a b : ↥D ⧸ M, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : Group.IsPerfect (↥D ⧸ M) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
    have : IsMulCommutative (↥D ⧸ M) := ⟨⟨fun a b => hcomm a b⟩⟩
    have : Nontrivial (↥D ⧸ M) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative (↥D ⧸ M) inferInstance
  haveI hNn : (D.comap π).Normal := Subgroup.Normal.comap inferInstance π
  let f : ↥(D.comap π) →* ↥D ⧸ M := (QuotientGroup.mk' M).comp (π.subgroupComap D)
  have hf : Function.Surjective f := by
    refine (QuotientGroup.mk'_surjective M).comp ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hmem := card_mem_of_hasLeviBlocks hQ (N := D.comap π) hnab f hf
  haveI : Nontrivial (↥D ⧸ M) := hsimple.toNontrivial
  exact (h3 _ hmem Finite.one_lt_card).trans (Subgroup.card_quotient_dvd_card M)

theorem perfectCoreThree_of_cover {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L) {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    {𝒯 : Set ℕ} (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯)
    (h3 : ∀ n ∈ 𝒯, 1 < n → 3 ∣ n) : PerfectCoreThree ↥P := by
  let π₁ : ↥((P.subgroupOf L).comap ρ) →* ↥(P.subgroupOf L) := ρ.subgroupComap (P.subgroupOf L)
  have hπ₁ : Function.Surjective π₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hs : Function.Surjective
      ((Subgroup.subgroupOfEquivOfLe hPL).toMonoidHom.comp π₁) := by
    intro y
    obtain ⟨x, hx⟩ := hπ₁ ((Subgroup.subgroupOfEquivOfLe hPL).symm y)
    exact ⟨x, by simp [hx]⟩
  exact perfectCoreThree_of_hasLeviBlocks hQ h3 _ hs

theorem card_mulAut_alternatingGroup_eq {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  have h := Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6))
  rw [← h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem kFactBlockSylowThreeAut_of (hC : KFactCompParabSylowThreeAut) :
    KFactBlockSylowThreeAut := by
  intro G _ _ M S L hyps hQS hcases hsolv hidx
  obtain ⟨hK, hA, hL, h93, hX, hS⟩ := id hyps
  have hLM : L ≤ M := hL.le
  have hPsolv : Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :=
    isSolvable_barM (inf_le_right.trans hLM) hsolv
  have hPidx := not_dvd_index_barM hLM hidx
  rcases hcases with h2 | h3 | h5
  · exact hC _ _ _ (compParab_of_blockHyps hyps h2) hPsolv hPidx
  · obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ :=
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
        G M S L hK hA hL hX hS h3
    have hns : ∀ {X : Type} [Group X] (φ : ↥(blockPL M S L) →* X), Function.Surjective φ →
        commutator X = ⊤ → Nontrivial X → False := by
      intro X _ φ hφ hX1 hnt
      have hs : Group.IsSolvable X := Group.isSolvable_of_surjective hφ
      have : Group.IsPerfect X := ⟨hX1⟩
      exact Group.IsPerfect.not_isSolvable X hs
    have hsix : Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 6)) → False := by
      rintro ⟨e6⟩
      have := le_four_of_isSolvable_perm (Group.isSolvable_of_surjective
        (f := e6.toMonoidHom) e6.surjective)
      omega
    have hsp : ∀ (m : ℕ) (d' : TauCeti.ValidLieTypeIndex), 4 ≤ m →
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) →
        Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃*
          (TauCeti.CFSGIndex.lie d').Group) → False := by
      rintro m d' hm hd' ⟨φ⟩
      exact hns (φ.toMonoidHom.comp (QuotientGroup.mk' _))
        (φ.surjective.comp (QuotientGroup.mk'_surjective _))
        (kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds (m - 1) d' (by omega) hd')
        (kFactSpTwoSimple_holds (m - 1) d' (by omega) hd').1.toNontrivial
    have hval : ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
        (d.1 = .D m q ∨ d.1 = .twistedD m q) → 4 ≤ m := by
      intro m d q hd
      have h := d.2
      rcases hd with hd | hd <;> rw [hd] at h <;>
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        exact (hsp m d' (hval m d q (Or.inl hd)) hd' hφ).elim
      · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        exact (hsp m d' (hval m d q (Or.inr hd)) hd' hφ).elim
      · exact (hsix (hU4 d ⟨q, hq, hd⟩ ⟨e⟩)).elim
    · rcases hn with rfl | rfl | rfl
      · rw [Nat.card_congr (MulAut.congr e).toEquiv,
          card_mulAut_alternatingGroup_eq (by norm_num) (by norm_num)]
        decide
      · exfalso
        obtain ⟨e4⟩ := hA6 ⟨e⟩
        have h24 : Nat.card ↥(blockPL M S L) = 24 := by
          rw [Nat.card_congr e4.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
            Fintype.card_fin]; decide
        have h360 : Nat.card ↥(barM M L) = 360 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
            Fintype.card_fin]; decide
        have hmul : Nat.card ↥((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
            (barM M L)) * ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
            (barM M L)).index = Nat.card ↥(barM M L) := Subgroup.card_mul_index _
        have hc : Nat.card ↥((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
            (barM M L)) = 24 := (card_subgroupOf_barM inf_le_right).trans h24
        rw [hc, h360] at hmul
        exact hPidx ⟨5, by omega⟩
      · exact (hsix (hA8 ⟨e⟩)).elim
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      card_mulAut_alternatingGroup_eq (by norm_num) (by norm_num)]
    decide

theorem card_of_isCaseTwoGroup_three {L : Type} [Group L] (hL : IsCaseTwoGroup 3 L) :
    Nat.card L = 504 := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hK
    let e₃ : L ≃* CFSG.Quasithin.F6.L28Res.G8 :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂)
    rw [Nat.card_congr e₃.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]
  · omega

theorem kFactBlockL28Rank_of (hC : KFactCompParabL28Rank) : KFactBlockL28Rank := by
  intro G _ _ M S L hyps h2 hq
  obtain ⟨T, hT, hN, d, ψ, hd, hψ⟩ := hq
  have hcase : IsCaseTwoGroup 3 (CatGroup d) := ⟨d, hd, ⟨MulEquiv.refl _⟩⟩
  have : IsSimpleGroup (CatGroup d) := isSimpleGroup_of_isCaseTwoGroup_three hcase
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have h3 : 3 ∣ Nat.card (CatGroup d) := by
    rw [card_of_isCaseTwoGroup_three hcase]; norm_num
  obtain ⟨T', hT'P, hPT', ψ', hψ'⟩ := exists_normal_section_blockPL hyps hT hN h3 ψ hψ
  exact hC _ _ _ (compParab_of_blockHyps hyps h2) T' hT'P hPT' d ψ' hd hψ'

theorem kFactBlockL28TwoRank_of (hC : KFactCompParabL28TwoRank) : KFactBlockL28TwoRank := by
  intro G _ _ M S L hyps h2 hq
  obtain ⟨T, hT, hN, d₁, d₂, ψ, hd₁, hd₂, hψ⟩ := hq
  have hc₁ : IsCaseTwoGroup 3 (CatGroup d₁) := ⟨d₁, hd₁, ⟨MulEquiv.refl _⟩⟩
  have hc₂ : IsCaseTwoGroup 3 (CatGroup d₂) := ⟨d₂, hd₂, ⟨MulEquiv.refl _⟩⟩
  have : IsSimpleGroup (CatGroup d₁) := isSimpleGroup_of_isCaseTwoGroup_three hc₁
  have : IsSimpleGroup (CatGroup d₂) := isSimpleGroup_of_isCaseTwoGroup_three hc₂
  have : Finite (CatGroup d₁ × CatGroup d₂) := Finite.of_surjective ψ hψ
  have : Finite (CatGroup d₁) :=
    Finite.of_surjective (Prod.fst : CatGroup d₁ × CatGroup d₂ → CatGroup d₁)
      (fun a => ⟨(a, (1 : CatGroup d₂)), rfl⟩)
  have : Finite (CatGroup d₂) :=
    Finite.of_surjective (Prod.snd : CatGroup d₁ × CatGroup d₂ → CatGroup d₂)
      (fun b => ⟨((1 : CatGroup d₁), b), rfl⟩)
  obtain ⟨T', hT'P, hPT', ψ', hψ'⟩ := exists_normal_section_blockPL₂ hyps hT hN
    (by rw [card_of_isCaseTwoGroup_three hc₁]; norm_num)
    (by rw [card_of_isCaseTwoGroup_three hc₂]; norm_num) ψ hψ
  exact hC _ _ _ (compParab_of_blockHyps hyps h2) T' hT'P hPT' d₁ d₂ ψ' hd₁ hd₂ hψ'

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
