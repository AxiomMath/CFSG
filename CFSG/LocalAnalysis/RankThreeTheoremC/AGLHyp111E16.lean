module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaFirst
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3D
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.QuasiDihedralFusion CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem isComponent_of_openComponent {Y : Type*} [Group Y] {L : Subgroup Y}
    (h : CFSG.Open.IsComponentOf L ⊤) : CFSG.IsComponent L := by
  obtain ⟨-, hsub, hperf, hsimple⟩ := h
  have hP : Group.IsPerfect ↥L := ⟨hperf⟩
  refine ⟨⟨hP, hsimple, ?_⟩, ?_⟩
  · by_contra hcon
    have : IsMulCommutative (↥L ⧸ Subgroup.center ↥L) :=
      isMulCommutative_iff.2 fun a b => by_contra fun hne => hcon ⟨a, b, hne⟩
    exact Group.IsPerfect.not_isMulCommutative (↥L ⧸ Subgroup.center ↥L) this
  · have key : ∀ H K : Subgroup Y, CFSG.Open.IsSubnormal H K → K = ⊤ → H.IsSubnormal := by
      intro H K h
      induction h with
      | refl H => rintro rfl; exact Subgroup.IsSubnormal.top
      | step hHM hN _ ih => intro hK; exact Subgroup.IsSubnormal.step _ _ hHM (ih hK) hN
    exact key L ⊤ hsub rfl

theorem not_hasPrimeConstraint_of_component {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {L : Subgroup (X ⧸ primeComplementCore (G := X) p)}
    (hL : CFSG.Open.IsComponentOf L ⊤) : ¬ HasPrimeConstraint (G := X) p := by
  rintro ⟨N, hNn, hNp, hC⟩
  have hc := isComponent_of_openComponent hL
  have hLN : L ≤ N := by
    rcases CFSG.LocalCores.component_normal_subgroup hc hNn with h | h
    · exact h
    · refine le_trans ?_ hC
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h
  obtain ⟨-, -, hperf, hsimple⟩ := hL
  have hLp : IsPGroup p L := hNp.to_le hLN
  have hP : Group.IsPerfect ↥L := ⟨hperf⟩
  have : Nontrivial ↥L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
    exact hsimple.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
      hab (Subsingleton.elim _ _)
  have : Group.IsNilpotent ↥L := hLp.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥L inferInstance

theorem exists_sylow_of_maximal {p : ℕ} [Fact p.Prime] {N T : Subgroup G} (hTN : T ≤ N)
    (hT : IsPGroup p T) (hmax : ∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) :
    ∃ S : Sylow p N, (S : Subgroup N).map N.subtype = T := by
  obtain ⟨S, hS⟩ := (hT.comap_subtype (K := N)).exists_le_sylow
  refine ⟨S, hmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) fun t ht => ?_⟩
  exact ⟨⟨t, hTN ht⟩, hS ht, rfl⟩

theorem exists_sylowBase {p : ℕ} {P : Sylow p G} {M H₁ R₁ B H₀ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) (hB : IsAGLQ p M B) (hBH : B ≤ H₀) :
    ∃ Q₀ : Subgroup G, B ≤ Q₀ ∧ Q₀ ≤ H₀ ∧ IsAGLQ p M Q₀ ∧
      ∃ S : Sylow p H₀, (S : Subgroup H₀).map H₀.subtype = Q₀ := by
  have : Fact p.Prime := ⟨he.prime⟩
  have hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M := fun U hBU hUM hU =>
    normalizer_le_of_isAGLQ_of_escape he (isAGLQ_of_le hB hBU hUM hU)
  obtain ⟨T, hBT, hTN, hTM, hT, hmaxN⟩ :=
    exists_maxPSubgroup_of_normalizer_le hB.2.1 hBH hB.1 hNorm
  have hmax : ∀ V : Subgroup G, V ≤ H₀ → IsPGroup p V → T ≤ V → V = T := hmaxN
  exact ⟨T, hBT, hTN, isAGLQ_of_le hB hBT hTM hT, exists_sylow_of_maximal hTN hT hmax⟩

theorem sylowK_of_sylow {p : ℕ} [Fact p.Prime] {H₀ Q₀ : Subgroup G}
    {K : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) p)} [K.Normal] (S : Sylow p H₀)
    (hS : (S : Subgroup H₀).map H₀.subtype = Q₀) :
    ∃ S' : Sylow p K, (S' : Subgroup K).map K.subtype =
      (Q₀.subgroupOf H₀).map (QuotientGroup.mk' (primeComplementCore (G := H₀) p)) ⊓ K := by
  have hQS : Q₀.subgroupOf H₀ = S := by
    rw [← hS]
    exact Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective _
  have h := CFSG.HardMathSupport.Solomon.Coordinator.exists_sylow_inf_normal
    (S.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := H₀) p))) K
  rw [Sylow.coe_mapSurjective, ← hQS] at h
  exact h

theorem card_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    Nat.card K = 20160 := by
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk

variable (G) in
@[expose] def AGL81TenOneExists : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    ∀ H₀ Q₀ : Subgroup G, IsAGLQ p M Q₀ → Q₀ ≤ H₀ → GLBIsMaxTwoLocal H₀ → ¬ H₀ ≤ M →
    (∃ S : Sylow p (d1KBar p M H₀), (S : Subgroup (d1KBar p M H₀)).map (d1KBar p M H₀).subtype =
      (Q₀.subgroupOf H₀).map (QuotientGroup.mk' (primeComplementCore (G := H₀) p)) ⊓
        d1KBar p M H₀) →
    Hyp111B3 p H₀ Q₀ (d1KBar p M H₀) →
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H₀) L

@[expose] def KFactNineThreeComponentL34 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K L : Subgroup Y), NineThreeListGroup 3 K →
    IsComponentOf L ⊤ → L ≤ K →
    (IsLinThreeFour L ∨ IsSLThreeFour L ∨ Nonempty (L ≃* alternatingGroup (Fin 11))) →
    IsLinThreeFour K

@[expose] def KFactNineThreeRankOne : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (A : Type) [Group A],
    NineThreeListGroup p K → NineThreeListGroup p A → Open.pRank p K ≤ 1 → Involves K A →
    Nat.card A = Nat.card K

omit [Finite G] in
theorem d1KBar_ne_bot {p : ℕ} {M H : Subgroup G}
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) : d1KBar p M H ≠ ⊥ := by
  obtain ⟨L, hL, hLX⟩ := hK
  intro h
  have hle := le_d1KBar hL hLX
  rw [h, le_bot_iff] at hle
  exact hLX (hle ▸ bot_le)

theorem card_d1KBar_of_isAltTwoP {p : ℕ} {M H : Subgroup G} (h : IsAltTwoP 3 (d1KBar p M H)) :
    d1Kappa p M H = 360 := by
  obtain ⟨e⟩ := h
  unfold d1Kappa
  rw [Nat.card_congr e.toEquiv]
  exact card_alternatingGroup_six

theorem exists_l34_step_of_ascent_of_list (hKA : KFactNineThreeInvolvedA6L34)
    {M H H₀ : Subgroup G} (hc : Relation.TransGen (AGLAscentStep 3 M) H H₀)
    (hA : IsAltTwoP 3 (d1KBar 3 M H)) (hL : IsLinThreeFour (d1KBar 3 M H₀))
    (hlist : ∀ H₁ : Subgroup G, AGLAscentStep 3 M H H₁ → NineThreeListGroup 3 (d1KBar 3 M H₁)) :
    ∃ H₁ : Subgroup G, AGLAscentStep 3 M H H₁ ∧ IsLinThreeFour (d1KBar 3 M H₁) := by
  obtain ⟨H₁, hs, -, hinv₀⟩ := exists_first_step_of_ascent hc
  obtain ⟨e⟩ := hA
  have hcard : Nat.card (d1KBar 3 M H) = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_alternatingGroup_six
  obtain ⟨-, -, -, -, -, -, -, hlt, -⟩ := id hs
  have hlt' : 360 < Nat.card (d1KBar 3 M H₁) := by
    have : d1Kappa 3 M H < d1Kappa 3 M H₁ := hlt
    unfold d1Kappa at this
    omega
  rcases hKA _ _ (Or.inr hL) (hlist H₁ hs) hinv₀ with hA₁ | hL₁
  · obtain ⟨e₁⟩ := hA₁
    have : Nat.card (d1KBar 3 M H₁) = 360 := by
      rw [Nat.card_congr e₁.toEquiv]
      exact card_alternatingGroup_six
    omega
  · exact ⟨H₁, hs, hL₁⟩

theorem e16_of_base (h9 : AGL81NineCompetitorQ G) (h98 : AGL81NineEightTwo G)
    (h984 : AGL81NineEightFour G) (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G)
    (hKR : KFactNineThreeRankOne) (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) (hS : Setting G) {p : ℕ}
    {P : Sylow p G}
    {M H₁ R₁ H B : Subgroup G}
    (hpσ : p ∈ rankThreeSigmaA G)
    (he : D1Escape p P M H₁ R₁) (hH : GLBIsMaxTwoLocal H) (hHM : ¬ H ≤ M)
    (hB : IsAGLQ p M B) (hBH : B ≤ H) (h3 : 3 ≤ Open.pRank p H)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) :
    p = 3 ∧ (IsLinThreeFour (d1KBar p M H) ∨
      (IsAltTwoP 3 (d1KBar p M H) ∧
        ((∃ Q₀ : Subgroup G, AGL81ElevenData p P M H Q₀ (d1KBar p M H)) ∨
          ∃ H₂ : Subgroup G, AGLAscentStep p M H H₂ ∧ IsLinThreeFour (d1KBar p M H₂)))) := by
  have hg := aglGlobal_of_setting hS
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hμ := muAt_of_escape he
  obtain ⟨H₀, hc, hH₀, hH₀M, hK₀, ⟨B₀, hB₀, hBH₀⟩, -, hinv, hfac⟩ :=
    exists_sizeMax_of_ascent h9 hg hμ hH hHM hK ⟨B, hB, hBH⟩
  have hat₀ := (h9 hg p P M H₀ hμ hH₀ hH₀M hK₀ B₀ H₀ hB₀ hBH₀ hH₀ hH₀M hBH₀
    (aglCovers_self H₀ _)).1
  have hatH := (h9 hg p P M H hμ hH hHM hK B H hB hBH hH hHM hBH (aglCovers_self H _)).1
  haveI := hat₀.nineThree.normal
  obtain ⟨Q₀, -, hQH₀, hQ₀, S, hS₀⟩ := exists_sylowBase he hB₀ hBH₀
  have hsyl := sylowK_of_sylow (K := d1KBar p M H₀) S hS₀
  have listH := hatH.list (d1KBar_ne_bot hK)
  have list₀ := hat₀.list (d1KBar_ne_bot hK₀)
  have key : p = 3 ∧ ((IsAltTwoP 3 (d1KBar p M H₀) ∧ AGL81ElevenData p P M H₀ Q₀ (d1KBar p M H₀)) ∨
      IsLinThreeFour (d1KBar p M H₀)) := by
    rcases h98 hS p P M H₁ R₁ he H₀ Q₀ hQ₀ hQH₀ hH₀ hH₀M hsyl with hb3 | ⟨hp3, L, hL, hLX, hLt⟩
    · obtain ⟨-, hOH, hHM⟩ := h984 hS p P M H₁ R₁ he H₀ Q₀ hQ₀ hQH₀ hH₀ hH₀M hsyl hb3
      have hpair := hyp111Pair_of_competitorFactor h9 hg hμ hH₀ hH₀M hK₀ hQ₀ hQH₀ hfac hOH hHM
      have hdata : AGL81ElevenData p P M H₀ Q₀ (d1KBar p M H₀) :=
        ⟨⟨H₁, R₁, he⟩, hH₀, hpair, rfl, hb3, hsyl,
          fun R' hR' hR1 => star_of_pair hp he.ne_two hpair hb3 hR' hR1⟩
      have hnc : ¬ HasPrimeConstraint (G := H₀) p := by
        obtain ⟨L, hL, -⟩ := hK₀
        exact not_hasPrimeConstraint_of_component hL
      have hrank : Open.pRank p (d1KBar p M H₀) ≤ 1 → 3 ≤ Open.pRank p H₀ := by
        intro h1
        have hcard := hKR p _ _ _ list₀ listH h1 hinv
        have hH : H₀ = H := eq_of_ascent_of_kappa_le hc (by unfold d1Kappa; omega)
        exact hH ▸ h3
      obtain ⟨L, hL⟩ := h101 hS p P M H₁ R₁ he H₀ Q₀ hQ₀ hQH₀ hH₀ hH₀M hsyl hb3
      obtain ⟨hp3, -, hA | ⟨hL34, -⟩⟩ := h115 hS p P M H₀ Q₀ _ hpσ hdata hnc hrank L hL
      · exact ⟨hp3, Or.inl ⟨hA.1, hdata⟩⟩
      · exact ⟨hp3, Or.inr hL34⟩
    · subst hp3
      exact ⟨rfl, Or.inr (hKC _ _ _ list₀ hL (le_d1KBar hL hLX) hLt)⟩
  obtain ⟨hp3, hcase⟩ := key
  subst hp3
  have hKH : IsAltTwoP 3 (d1KBar 3 M H) ∨ IsLinThreeFour (d1KBar 3 M H) :=
    hKA _ _ (hcase.imp And.left id) listH hinv
  refine ⟨rfl, ?_⟩
  rcases hKH with hA | hL
  · refine Or.inr ⟨hA, ?_⟩
    rcases hcase with ⟨hA₀, hdata⟩ | hL₀
    · have hH : H₀ = H := eq_of_ascent_of_kappa_le hc
        (by rw [card_d1KBar_of_isAltTwoP hA₀, card_d1KBar_of_isAltTwoP hA])
      subst hH
      exact Or.inl ⟨Q₀, hdata⟩
    · rcases hc with rfl | hc
      · exfalso
        have h1 := card_d1KBar_of_isAltTwoP hA
        unfold d1Kappa at h1
        rw [card_of_isLinThreeFour hL₀] at h1
        omega
      · refine Or.inr (exists_l34_step_of_ascent_of_list hKA hc hA hL₀ fun H₁ hs => ?_)
        obtain ⟨B', hB', hB'H, hH₁, hH₁M, hB'H₁, hcov, hlt, -⟩ := hs
        refine (h9 hg 3 P M H hμ hH hHM hK B' H₁ hB' hB'H hH₁ hH₁M hB'H₁ hcov).1.list ?_
        intro h1
        have hk : d1Kappa 3 M H < d1Kappa 3 M H₁ := hlt
        unfold d1Kappa at hk
        rw [h1, Subgroup.card_bot] at hk
        have := Nat.card_pos (α := ↥(d1KBar 3 M H))
        omega
  · exact Or.inl hL

theorem e16_of_escape (h9 : AGL81NineCompetitorQ G) (h98 : AGL81NineEightTwo G)
    (h984 : AGL81NineEightFour G) (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G)
    (hKR : KFactNineThreeRankOne) (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G}
    (hpσ : p ∈ rankThreeSigmaA G)
    (he : D1Escape p P M H R)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) :
    p = 3 ∧ (IsLinThreeFour (d1KBar p M H) ∨
      (IsAltTwoP 3 (d1KBar p M H) ∧
        ((∃ Q₀ : Subgroup G, AGL81ElevenData p P M H Q₀ (d1KBar p M H)) ∨
          ∃ H₂ : Subgroup G, AGLAscentStep p M H H₂ ∧ IsLinThreeFour (d1KBar p M H₂)))) :=
  e16_of_base h9 h98 h984 h101 h115 hKR hKA hKC hS hpσ he he.maxTwoLocal_H he.not_le
    (isAGLQ_of_escape he) he.le_H
    (he.three_le_pRank.trans (CFSG.SectionRank.pRank_mono he.prime.one_lt he.le_H)) hK

theorem isSubnormal_inf {Y : Type*} [Group Y] {H T : Subgroup Y} (h : IsSubnormal H T)
    (K : Subgroup Y) : IsSubnormal (H ⊓ K) (T ⊓ K) := by
  induction h with
  | refl H => exact IsSubnormal.refl _
  | @step H M T hHM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right K hHM) ⟨fun x hx g => ?_⟩ ih
    have hxH : (x : Y) ∈ H := hx.1
    have hxK : (x : Y) ∈ K := hx.2
    have hgM : (g : Y) ∈ M := g.2.1
    have hgK : (g : Y) ∈ K := g.2.2
    refine ⟨?_, ?_⟩
    · have := hn.conj_mem ⟨x, hHM hxH⟩ hxH ⟨g, hgM⟩
      exact this
    · exact K.mul_mem (K.mul_mem hgK hxK) (K.inv_mem hgK)

theorem eq_of_isSubnormal_of_isSimpleGroup {Y : Type*} [Group Y] {L K : Subgroup Y}
    (h : IsSubnormal L K) (hK : IsSimpleGroup K) (hL : L ≠ ⊥) : L = K := by
  induction h with
  | refl H => rfl
  | @step H M K hHM hn hMK ih =>
    have hM : M = K := ih hK (fun hb => hL (le_bot_iff.mp (hb ▸ hHM)))
    subst hM
    haveI := hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf M) with h | h
    · exact absurd (((Subgroup.subgroupOf_eq_bot).mp h).eq_bot_of_le hHM) hL
    · exact le_antisymm hHM ((Subgroup.subgroupOf_eq_top).mp h)

theorem isSimpleGroup_of_isLinThreeFour' {K : Type} [Group K] (h : IsLinThreeFour K) :
    IsSimpleGroup K := by
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have : IsSimpleGroup (ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.isSimpleGroup_projectiveSL_four hk
  exact e.isSimpleGroup

theorem isComponentOf_d1KBar {p : ℕ} {M H : Subgroup G}
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) (hs : IsSimpleGroup (d1KBar p M H)) :
    IsComponentOf (d1KBar p M H) ⊤ := by
  obtain ⟨L, hL, hLX⟩ := hK
  have hle := le_d1KBar hL hLX
  have hsub := isSubnormal_inf hL.2.1 (d1KBar p M H)
  rw [inf_eq_left.mpr hle, top_inf_eq] at hsub
  have hne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, -, hsimple⟩ := hL
    have : Subsingleton (↥(⊥ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⧸
        Subgroup.center ↥(⊥ : Subgroup (H ⧸ primeComplementCore (G := H) p))) := inferInstance
    exact hsimple.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
      hab (Subsingleton.elim _ _)
  rw [← eq_of_isSubnormal_of_isSimpleGroup hsub hs hne]
  exact hL

theorem isComponentOf_d1KBar_of_isLinThreeFour {p : ℕ} {M H : Subgroup G}
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) (hL : IsLinThreeFour (d1KBar p M H)) :
    IsComponentOf (d1KBar p M H) ⊤ :=
  isComponentOf_d1KBar hK (isSimpleGroup_of_isLinThreeFour' hL)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
