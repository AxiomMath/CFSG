module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Core

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactU62OmegaMinusThreeCent : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex),
    (IsUSixTwoIndex d ∨ ∃ m, 5 ≤ m ∧ IsOmegaMinusTwoIndex m d) → Nonempty (L ≃* CatGroup d) →
    ∀ x : L, orderOf x = 3 →
      (∃ E : Subgroup L, E ≤ Subgroup.centralizer {x} ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 4) ∧
      ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5

@[expose] def KFactU62ThreeCent : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex),
    IsUSixTwoIndex d → Nonempty (L ≃* CatGroup d) →
    ∀ x : L, orderOf x = 3 →
      (∃ E : Subgroup L, E ≤ Subgroup.centralizer {x} ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 4) ∧
      ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5

@[expose] def KFactOmegaMinusFiveThreeCent : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex),
    (∃ m, 5 ≤ m ∧ IsOmegaMinusTwoIndex m d) → Nonempty (L ≃* CatGroup d) →
    ∀ x : L, orderOf x = 3 →
      (∃ E : Subgroup L, E ≤ Subgroup.centralizer {x} ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 4) ∧
      ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5

theorem kFactU62OmegaMinusThreeCent_of (h1 : KFactU62ThreeCent)
    (h2 : KFactOmegaMinusFiveThreeCent) : KFactU62OmegaMinusThreeCent := by
  intro L _ _ d hd he x hx
  rcases hd with hd | hd
  · exact h1 L d hd he x hx
  · exact h2 L d hd he x hx

@[expose] def KFactBlockLeviU42Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), CFSG.Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → BlockInnerHyp M S L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      (barM M V ⊔ O).relIndex (blockParabolic M S L) ≤ 2 →
      ⁅V, V⁆ = V → ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* CatGroup d),
        IsUFourTwoIndex d → Function.Surjective ψ → Nat.Coprime 3 (Nat.card ψ.ker) →
        (∀ Q : Sylow 3 (blockParabolic M S L),
          Nat.card (Q : Subgroup (blockParabolic M S L)) = 3 ^ 4) →
        ¬ 3 ∣ Nat.card (Subgroup.center (barM M L)) →
        (∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
          IsEmpty (barM M L ≃* CatGroup d')) →
        ∀ x ∈ blockParabolic M S L, orderOf x = 3 →
          (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
            E ≤ barM M L ⊓ Subgroup.centralizer ({x} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
            IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) ∧
          ∃ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
            Y ≤ barM M L ⊓ Subgroup.centralizer ({x} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
            IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5

theorem kFactBlockLeviU42Cent_of (hLevi : KFactBlockLeviU42)
    (hC : KFactU62OmegaMinusThreeCent) : KFactBlockLeviU42Cent := by
  intro G _ _ M S L hK hA hW hN hX hS hB O V hVM hO hV hPO hOc hPVO hrel hVV d ψ hd hψ hker
    hQ hZ h4 x hx hx3
  have hxL : x ∈ barM M L := Subgroup.map_mono (Subgroup.comap_mono inf_le_right) hx
  have hcase : ∃ d' : TauCeti.ValidLieTypeIndex,
      (IsUSixTwoIndex d' ∨ ∃ m, 5 ≤ m ∧ IsOmegaMinusTwoIndex m d') ∧
        Nonempty (barM M L ≃* CatGroup d') := by
    rcases hLevi G M S L hK hA hW hN hX hS hB O V hVM hO hV hPO hOc hPVO hrel hVV d ψ hd hψ
      hker hQ hZ with ⟨d', hd', he, -⟩ | ⟨m, d', hm, hd', he, -⟩
    · exact ⟨d', Or.inl hd', he⟩
    · rcases Nat.eq_or_lt_of_le hm with rfl | hm5
      · exact ((h4 d' hd').false he.some).elim
      · exact ⟨d', Or.inr ⟨m, hm5, hd'⟩, he⟩
  obtain ⟨d', hd', he⟩ := hcase
  have hx3' : orderOf (⟨x, hxL⟩ : barM M L) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  obtain ⟨⟨E, hE, hEe, hEc⟩, Y, hY, hYp, hYc⟩ := hC (barM M L) d' hd' he ⟨x, hxL⟩ hx3'
  have hcen : ∀ T : Subgroup (barM M L), T ≤ Subgroup.centralizer {⟨x, hxL⟩} →
      T.map (barM M L).subtype ≤
        barM M L ⊓ Subgroup.centralizer ({x} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro T hT _ ⟨t, ht, rfl⟩
    refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hT ht))
    simpa using this
  refine ⟨⟨E.map (barM M L).subtype, hcen E hE, elementary_abelian_map 3 hEe _, ?_⟩,
    Y.map (barM M L).subtype, hcen Y hY, hYp.map _, ?_⟩
  · rw [Subgroup.card_map_of_injective (barM M L).subtype_injective, hEc]
  · rw [Subgroup.card_map_of_injective (barM M L).subtype_injective, hYc]

theorem Sp62Block.exists_isPGroup_map_eq_of_le_centralizer {Y : Type*} [Group Y] [Finite Y]
    (O : Subgroup Y) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) {e : Y}
    (he : IsPGroup 3 (Subgroup.zpowers e)) {A : Subgroup (Y ⧸ O)} (hA : IsPGroup 3 A)
    (hAC : A ≤ Subgroup.centralizer ({QuotientGroup.mk' O e} : Set (Y ⧸ O))) :
    ∃ T : Subgroup Y, T ≤ Subgroup.centralizer ({e} : Set Y) ∧ IsPGroup 3 T ∧
      T.map (QuotientGroup.mk' O) = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({e} : Set Y) with hC
  set f : C →* Y ⧸ O := (QuotientGroup.mk' O).comp C.subtype with hf
  set W := A.comap f with hW
  set g : W →* A := (f.comp W.subtype).codRestrict A (fun w => w.2) with hg
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨y, hy, hya⟩ := exists_mem_centralizer_mk_eq Nat.prime_three O hO he (hAC a.2)
    have hyW : (⟨y, hy⟩ : C) ∈ W := by
      show f ⟨y, hy⟩ ∈ A
      simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [hya]; exact a.2
    exact ⟨⟨⟨y, hy⟩, hyW⟩, Subtype.ext (by simpa [hg, hf] using hya)⟩
  have hA' : IsPGroup 3 (⊤ : Subgroup A) := fun a => by
    obtain ⟨k, hk⟩ := hA a.1
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨Q, hQ, hQg⟩ := exists_isPGroup_map_eq' hgs hA'
  refine ⟨(Q.map W.subtype).map C.subtype, Subgroup.map_subtype_le _,
    (hQ.map _).map _, ?_⟩
  ext a
  constructor
  · rintro ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    exact (q : W).2
  · intro ha
    have hmem : (⟨a, ha⟩ : A) ∈ Q.map g := hQg ▸ Subgroup.mem_top _
    obtain ⟨q, hq, hqa⟩ := hmem
    refine ⟨((q : W) : C), ⟨(q : W), ⟨q, hq, rfl⟩, rfl⟩, ?_⟩
    have := congrArg Subtype.val hqa
    simpa [hg, hf] using this

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V L : Subgroup G}

theorem D1Sp62Data.exists_cent (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hLC : KFactBlockLeviU42Cent)
    (hLs : Sp62BlockShape M H R L)
    (h4 : ∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
      IsEmpty (barM M L ≃* CatGroup d'))
    {x : G} (hxR : x ∈ R) (hx3 : orderOf x = 3) :
    (∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4) ∧
    ∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 3 Y ∧
      3 ^ 5 ≤ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  have hL := hLs.1
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  obtain ⟨hVV, -, -, hKVN, -, ⟨d, ψ, hd, hψ, hker⟩, -, -⟩ := h.piece
  have hO3 := h.pCore_eq_bot h84 hD2
  have hLn := h.barM_normal h84 h86 hD2 hB3 hb hL
  set N := GLBPrimeCore 3 H with hN
  set Pi := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hPi
  have hVPi := h.le_Pi hB3 hL
  have hPiK : Pi ≤ H ⊓ M := inf_le_left
  have hPiH : Pi ≤ H := hPiK.trans inf_le_left
  have hPiM : Pi ≤ M := hPiK.trans inf_le_right
  have hPiPL : barM M Pi ≤ blockParabolic M (pCoreOf 2 H) L :=
    h.barM_le h84 h86 hD2 hB3 hb hL le_rfl
  have hPLPi := blockParabolic_le_barM hKeq hL.le (le_rfl : Pi ≤ Pi)
  have hPiNPi : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ N : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_glbPrimeCore 3 H (hPiH hx)⟩
  have hPiNV : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ (V ⊔ N) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      hKVN (hPiK hx)⟩
  have hPLnorm : ∀ Y : Subgroup G, (∀ x ∈ Pi, x ∈ Subgroup.normalizer (Y : Set G)) →
      blockParabolic M (pCoreOf 2 H) L ≤
        Subgroup.normalizer (barM M Y : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Y hY
    refine hPLPi.trans ?_
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact mem_normalizer_barM hxM (hY x (Subgroup.mem_subgroupOf.mp hx))
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hxM : x ∈ M := h3.le_M hxR
  have hRPL : barM M R ≤ blockParabolic M (pCoreOf 2 H) L :=
    (Subgroup.map_mono (Subgroup.comap_mono (h.R_le_Pi hB3 hL))).trans hPiPL
  have hxP : mk ⟨x, hxM⟩ ∈ blockParabolic M (pCoreOf 2 H) L :=
    hRPL (Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hxR))
  have hxo : orderOf (mk ⟨x, hxM⟩) = 3 := by
    have hdvd : orderOf (mk ⟨x, hxM⟩) ∣ 3 := by
      rw [← hx3, ← Subgroup.orderOf_mk x hxM]
      exact orderOf_map_dvd _ _
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exfalso
      have hxQ : x ∈ pCoreOf 2 M :=
        coe_mem_pCoreOf_two_of_mk_eq_one (⟨x, hxM⟩ : M) (orderOf_eq_one_iff.mp h1)
      obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) ⟨x, hxQ⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h32 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hk'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
    · exact h1
  obtain ⟨⟨Eb, hEb, hEbe, hEbc⟩, Yb, hYb, hYb3, hYbc⟩ :=
    hLC G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    (fun l hl hcond => hb h3 h84 h86 hD2 hL l hl hcond) (barM M (Pi ⊓ N)) V
    (hVPi.trans hPiM) ((Subgroup.map_mono (Subgroup.comap_mono inf_le_left)).trans hPiPL)
    ((Subgroup.map_mono (Subgroup.comap_mono hVPi)).trans hPiPL) (hPLnorm _ hPiNPi)
    (Nat.Coprime.coprime_dvd_right ((card_barM_dvd (inf_le_left.trans hPiM)).trans
      (Subgroup.card_dvd_of_le inf_le_right)) (glbPrimeCore_coprime 3 H))
    (by rw [barM_sup_eq hVPi hPiH hPiM]; exact hPLnorm _ hPiNV)
    (h.relIndex_le h84 h86 hD2 hB3 hb hL) hVV d ψ hd hψ hker
    (h.card_sylow h84 h86 hD2 hB3 hb hL)
    (@not_dvd_card_center_of_normal _ _ _ 3 ⟨Nat.prime_three⟩ _ hLn hO3) h4 _ hxP hxo
  have hO : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  have he : IsPGroup 3 (Subgroup.zpowers (⟨x, hxM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo', pow_one])
  have hCx : ∀ T : Subgroup M, T ≤ Subgroup.centralizer ({(⟨x, hxM⟩ : M)} : Set M) →
      T.map M.subtype ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro T hT _ ⟨t, ht, rfl⟩
    refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hT ht))
    simpa using this
  obtain ⟨T₁, hT₁C, hT₁, hT₁map⟩ :=
    Sp62Block.exists_isPGroup_map_eq_of_le_centralizer _ hO he hYb3 (hYb.trans inf_le_right)
  have hEb3 : IsPGroup 3 Eb := fun e => ⟨1, Subtype.ext (by simpa using hEbe.2 e e.2)⟩
  obtain ⟨T₂, hT₂C, hT₂, hT₂map⟩ :=
    Sp62Block.exists_isPGroup_map_eq_of_le_centralizer _ hO he hEb3 (hEb.trans inf_le_right)
  obtain ⟨E₁, hE₁T, -, hE₁, hE₁c⟩ := exists_isElemAbelian_lift Nat.prime_three _ hO hT₂ hEbe
    hT₂map.ge
  refine ⟨⟨E₁.map M.subtype, hCx E₁ (hE₁T.trans hT₂C), elementary_abelian_map 3 hE₁ _, ?_⟩,
    T₁.map M.subtype, hCx T₁ hT₁C, hT₁.map _, ?_⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hE₁c, hEbc]
  · rw [Subgroup.card_map_of_injective M.subtype_injective, ← hYbc, ← hT₁map]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

theorem D1Extremal.twoCore_centralizer_eq_bot (hext : D1Extremal 3 P M H R) {x : G}
    (hxH : ¬ Subgroup.centralizer ({x} : Set G) ⊓ H ≤ M) {Y : Subgroup G}
    (hYC : Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G)) (hY3 : IsPGroup 3 Y)
    (hYR : Nat.card R < Nat.card Y) (hYr : 3 ≤ CFSG.Open.pRank 3 Y) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  by_contra hne
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 C : Set G)) :=
    ⟨pCoreOf 2 C, hne, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 C, rfl⟩
  have hCN : C ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 C
  have hle := hext.le_of_card_lt (hYC.trans inf_le_left) hY3 hYr hYR hloc
    ((hYC.trans inf_le_right).trans hCN)
  exact hxH (inf_le_left.trans (hCN.trans hle))

theorem Sp62Block.exists_large_of_elem {x : G} {E Y : Subgroup G}
    (hEC : E ≤ M ⊓ Subgroup.centralizer ({x} : Set G)) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 4) (hYC : Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G))
    (hY3 : IsPGroup 3 Y) :
    ∃ Z : Subgroup G, Z ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 3 Z ∧
      Nat.card Y ≤ Nat.card Z ∧ 4 ≤ CFSG.Open.pRank 3 Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := M ⊓ Subgroup.centralizer ({x} : Set G) with hD
  have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  obtain ⟨T, hT⟩ := (hE3.comap_subtype (K := D)).exists_le_sylow
  have hET : E ≤ (T : Subgroup D).map D.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEC]
    exact Subgroup.map_mono hT
  refine ⟨(T : Subgroup D).map D.subtype, Subgroup.map_subtype_le _, T.isPGroup'.map _,
    card_le_card_map_sylow T hY3 hYC, ?_⟩
  exact CFSG.SectionRank.le_pRank (by norm_num) hET hE hEc

end CFSG.AGLEmbedding
