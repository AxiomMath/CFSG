module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvThree
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Perm
import CFSG.GroupTheory.ABGLocalTools.RelativeStability

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable (G : Type) [Group G] [Finite G] in
@[expose] def AGL81TenThreeThreeCasesNCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ b ∈ H ⊓ M, b ∈ Subgroup.normalizer (L : Set G) → Odd (orderOf b) →
      (∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
        (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
          IsParabolicTwo (barM M L) (barM M (H ⊓ L)) ∧
          ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (barM M (H ⊓ L))) (barM M L))

namespace TenThreeThree

variable {G : Type} [Group G] [Finite G]

theorem bar_action_of_mem_normalizer {M H L : Subgroup G} (hLM : L ≤ M) {b : G}
    (hb : b ∈ H ⊓ M) (hbL : b ∈ normalizer (L : Set G)) (hbo : Odd (orderOf b))
    (hbJ : ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) :
    Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ ∈ normalizer (barM M L : Set _) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ ∈ normalizer (barM M (H ⊓ L) : Set _) ∧
      ∀ w (hw : w ∈ barM M (H ⊓ L)), QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (H ⊓ L))) ⟨w, hw⟩ ∈
          wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ * w *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩)⁻¹ * w⁻¹ ∈
            pCoreOf 2 (barM M (H ⊓ L)) := by
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  have hbM : b ∈ M := hb.2
  have hbX : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := (mem_normalizer_iff.mp (le_normalizer hb.1 : b ∈ normalizer (H : Set G)) x)
    have h2 := mem_normalizer_iff.mp hbL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  refine ⟨hbo.of_dvd_nat
    ((orderOf_map_dvd _ _).trans (Subgroup.orderOf_coe (⟨b, hbM⟩ : ↥M)).symm.dvd),
    mem_normalizer_barM hbM hbL, mem_normalizer_barM hbM hbX,
    fun w hw hwW => commutator_mem_of_wSup hXM hbM hbX hbJ hw hwW⟩

theorem card_pCore_perm_four_dvd_four : Nat.card (CFSG.pCore 2 (Equiv.Perm (Fin 4))) ∣ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.pCore 2 (Equiv.Perm (Fin 4)) ≤ alternatingGroup (Fin 4) := fun σ hσ =>
    CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.mem_alternatingGroup_of_mem_pCore_perm_four
      hσ
  have h12 : Nat.card (CFSG.pCore 2 (Equiv.Perm (Fin 4))) ∣ 12 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [nat_card_alternatingGroup, Nat.card_fin] at h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2)
    (G := Equiv.Perm (Fin 4))))
  rw [hk] at h12 ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h
    have := h8.trans h12
    norm_num at this
  exact pow_dvd_pow 2 hk2

theorem not_isSylowTwoOf_pCoreOf_of_hom {X : Type} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (h8 : 8 ∣ Nat.card Y) (f : ↥P →* Equiv.Perm (Fin 4))
    (hfs : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 P) Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, -, hodd⟩
  have hmap : (CFSG.pCore 2 ↥P).map f ≤ CFSG.pCore 2 (Equiv.Perm (Fin 4)) :=
    CFSG.ABGLocalTools.map_pCore_le_of_surjective f hfs
  have hinj : Function.Injective (f.comp (CFSG.pCore 2 ↥P).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hfx
    have hxk : x ∈ f.ker := hfx
    obtain ⟨i, hi⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) ⟨x, hx⟩
    have hxi : x ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hxo : orderOf x ∣ Nat.card f.ker := by
      rw [← Subgroup.orderOf_mk x hxk]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ i) (Nat.card f.ker) :=
      Nat.Coprime.pow_left i (Nat.coprime_two_left.mpr hker)
    have h1 : orderOf x = 1 :=
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxi) hcop).eq_one_of_dvd hxo
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hcard : Nat.card (CFSG.pCore 2 ↥P) ∣ 4 := by
    have h1 : Nat.card (CFSG.pCore 2 ↥P) ∣ Nat.card (CFSG.pCore 2 (Equiv.Perm (Fin 4))) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact hmap ⟨(x : ↥P), x.2, rfl⟩
    exact h1.trans card_pCore_perm_four_dvd_four
  have hcard' : Nat.card (pCoreOf 2 P) ∣ 4 := by
    rwa [pCoreOf, Subgroup.card_map_of_injective P.subtype_injective]
  set T := pCoreOf 2 P with hT
  have hTY : T ≤ Y := (Subgroup.map_subtype_le _).trans hPY
  have hmul := (T.subgroupOf Y).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv] at hmul
  have h8T : 8 ∣ Nat.card T * (T.subgroupOf Y).index := hmul ▸ h8
  have hco : Nat.Coprime 8 (T.subgroupOf Y).index :=
    Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have h8' : 8 ∣ Nat.card T := hco.dvd_of_dvd_mul_right h8T
  have := Nat.le_of_dvd (by norm_num) (h8'.trans hcard')
  norm_num at this

theorem not_isSylowTwoOf_pCoreOf_threeASix {X : Type} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (hZ : Nat.card (Subgroup.center ↥Y) = 3)
    (hA6 : Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 6)))
    (hS4 : Nonempty (↥((P.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) ≃*
      Equiv.Perm (Fin 4))) :
    ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 P) Y := by
  obtain ⟨e6⟩ := hA6
  obtain ⟨e4⟩ := hS4
  set Z := Subgroup.center ↥Y
  set π : ↥Y →* ↥Y ⧸ Z := QuotientGroup.mk' Z
  set R := (P.subgroupOf Y).map π
  let f₀ : ↥P →* ↥R := (π.comp (Subgroup.inclusion hPY)).codRestrict R (fun x =>
    ⟨⟨(x : X), hPY x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨(y : X), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩
  let f : ↥P →* Equiv.Perm (Fin 4) := e4.toMonoidHom.comp f₀
  have hfs : Function.Surjective f := e4.surjective.comp hf₀
  have hY8 : 8 ∣ Nat.card Y := by
    have h := Z.card_mul_index
    have hi : Z.index = 360 := by
      rw [Subgroup.index, Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [hZ, hi] at h
    omega
  have hker : Odd (Nat.card f.ker) := by
    let g : ↥f.ker →* ↥Z := {
      toFun := fun x => ⟨Subgroup.inclusion hPY x.1, by
        have h1 : f x.1 = 1 := x.2
        have h2 : f₀ x.1 = 1 := (map_eq_one_iff _ e4.injective).mp h1
        have h3 : π (Subgroup.inclusion hPY x.1) = 1 := congrArg Subtype.val h2
        exact (QuotientGroup.eq_one_iff _).mp h3⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥Z => ((z : ↥Y) : X)) h
      exact this
    have hdvd : Nat.card f.ker ∣ 3 := by
      rw [← hZ, Nat.card_congr (MonoidHom.ofInjective hg).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> decide
  exact not_isSylowTwoOf_pCoreOf_of_hom hPY hY8 f hfs hker

end TenThreeThree

variable {G : Type} [Group G] [Finite G]

theorem agl81TenThreeThreeCasesNCfg_of_three (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) (hKT : TenThreeThree.KFactTransvectionW3)
    (hAlt : TenThreeThree.Asc81bAltBlockAutNX) (hA7 : AGL81TenNineOneCfg G)
    (hZ : AGL81TenOneSixCenterCfg G) : AGL81TenThreeThreeCasesNCfg G := by
  intro hS p P M H Q K hd L hL b hb hbL hbo hbJ
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun x hx => by
    rw [mem_subgroupOf] at hx ⊢
    exact hx.2
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hNX hL).1
  have hrk := TenThreeThree.pRank_three_barM_le hS hT.maxTwoLocal_M.1 L
  obtain ⟨hbbo, hbLbar, hbP, hW⟩ :=
    TenThreeThree.bar_action_of_mem_normalizer hLM hb hbL hbo hbJ
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  ·
    refine Or.inr ⟨h2.1, ?_, ?_⟩
    · have := h2.2.1
      rwa [hNS] at this
    · have hsyl := (hT.nineThree_not_one hK h85 hNX hL).2 h2
      have heq := h2.2.2
      rw [hNS] at heq
      rwa [← heq]
  ·
    have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ :=
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds G M
        (pCoreOf 2 H) L hK hA hL hX hSy h3
    have hPP : barM M (H ⊓ L) = blockPL M (pCoreOf 2 H) L := by rw [blockPL, hNS]
    set eP := MulEquiv.subgroupCongr hPP
    have tr : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
        Nonempty (↥(barM M (H ⊓ L)) ≃* T) := fun ⟨e⟩ => ⟨eP.trans e⟩
    have trq : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ⧸
        CFSG.pCore 2 ↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
        Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃* T) := by
      rintro T _ ⟨e⟩
      obtain ⟨e'⟩ := nonempty_quotient_pCore_mulEquiv eP
      exact ⟨e'.trans e⟩
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inl hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar
            hbP hW))
      · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inr hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar
            hbP hW))
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inl ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩,
            tr (hU4 d ⟨q, hq, hd⟩ ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
    · rcases hn with rfl | rfl | rfl
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inr ⟨⟨e⟩, tr (hA5 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
      ·
        obtain ⟨e4⟩ := tr (hA6 ⟨e⟩)
        have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
          (by norm_num : 4 ≤ 6) e
        refine Or.inr ⟨TenThreeThree.isClassicalTwoOrG2_of_altSix
          (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e),
          TenThreeThree.isParabolicTwo_altSix hPY e e4, ?_⟩
        have h8 : 8 ∣ Nat.card (barM M L) := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        refine TenThreeThree.not_isSylowTwoOf_pCoreOf_of_hom hPY h8 e4.toMonoidHom
          e4.surjective ?_
        have hk : e4.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e4.injective
        rw [hk, Subgroup.card_bot]
        decide
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inr ⟨e⟩, tr (hA8 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
  ·
    have hZP := hZ hS p P M H Q K hd L hL h4
    obtain ⟨-, hZc, hA6, -, hS4⟩ := h4
    rw [hNS] at hS4
    refine Or.inr ⟨TenThreeThree.isClassicalTwoOrG2_of_altSix hA6.some,
      TenThreeThree.isParabolicTwo_threeASix hPY hZc hA6 hS4 hZP, ?_⟩
    exact TenThreeThree.not_isSylowTwoOf_pCoreOf_threeASix hPY hZc hA6 hS4
  · exact ((hA7 hS p P M H Q K hd L hL).false h5.2.1.some).elim
  all_goals
    left
    have hbS : b ∈ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact hb.1
    refine TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2 ?_
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inl h6) (H ⊓ L) hNS b hb.2 hbS hbo hbL hW
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inr (Or.inl h7)) (H ⊓ L) hNS b hb.2 hbS hbo
      hbL hW
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inr (Or.inr h8)) (H ⊓ L) hNS b hb.2 hbS hbo
      hbL hW

end CFSG.LocalAnalysis.RankThreeTheoremC
