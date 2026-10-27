module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem relIndex_sup_centralizer_dvd_card_outer {Y : Type*} [Group Y] [Finite Y]
    {L U : Subgroup Y} (hU : U ≤ Subgroup.normalizer (L : Set Y)) :
    (U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))).relIndex U ∣ Nat.card (Outer L) := by
  set φ : U →* Outer L := (QuotientGroup.mk' (inner L)).comp
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hU)) with hφ
  have hker : φ.ker ≤ (U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))).subgroupOf U := by
    intro u hu
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hu
    obtain ⟨l, hl⟩ := hu
    rw [Subgroup.mem_subgroupOf]
    refine ⟨u.2, ?_⟩
    have hcent : (l : Y)⁻¹ * (u : Y) ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
      change (l : Y) * y * (l : Y)⁻¹ = (u : Y) * y * (u : Y)⁻¹ at h1
      calc y * ((l : Y)⁻¹ * u) = (l : Y)⁻¹ * ((l : Y) * y * (l : Y)⁻¹) * u := by group
        _ = (l : Y)⁻¹ * ((u : Y) * y * (u : Y)⁻¹) * u := by rw [h1]
        _ = (l : Y)⁻¹ * u * y := by group
    rw [show (u : Y) = (l : Y) * ((l : Y)⁻¹ * u) by group]
    exact Subgroup.mul_mem_sup l.2 hcent
  have h1 : (U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))).relIndex U ∣ φ.ker.index :=
    Subgroup.index_dvd_of_le hker
  have h2 : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have h3 : Nat.card φ.range ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card _
  exact h1.trans (h2 ▸ h3)

theorem relIndex_sup_centralizer_le_three {Y : Type*} [Group Y] [Finite Y] {L U : Subgroup Y}
    (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U)
    (h9 : ¬ 9 ∣ Nat.card (Outer L)) :
    (U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))).relIndex U ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := relIndex_sup_centralizer_dvd_card_outer hU
  obtain ⟨k, hk⟩ := hU3.exists_card_eq
  have hdU : (U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))).relIndex U ∣ 3 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdU
  rw [hjk] at hdvd ⊢
  by_contra hlt
  have hj2 : 2 ≤ j := by
    by_contra hj1
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp at hlt
  exact h9 ((pow_dvd_pow 3 hj2).trans hdvd)

theorem exists_sylowTwo_parabolic_of_nineThreeTwo {G : Type} [Group G] [Finite G]
    {M S L : Subgroup G} (h2 : NineThreeTwo M S L)
    (hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) :
    ∃ T₁ : Subgroup ↥(barM M L), IsSylowTwoOf T₁ ⊤ ∧
      Subgroup.normalizer (T₁ : Set ↥(barM M L)) ≤
        (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) ∧
      (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) ≠
        Subgroup.normalizer (T₁ : Set ↥(barM M L)) := by
  obtain ⟨-, ⟨hJL, T, hT, hNT⟩, hO⟩ := h2
  set Lb := barM M L
  set Jb := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hT₁ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hN : Subgroup.normalizer ((T.subgroupOf Lb : Subgroup ↥Lb) : Set ↥Lb) ≤
      Jb.subgroupOf Lb := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hNT ⟨z.2, coe_mem_normalizer_of_subgroupOf hT.1 hz⟩)
  refine ⟨T.subgroupOf Lb, hT₁, hN, ?_⟩
  intro heq
  have hJN : Jb ≤ Subgroup.normalizer (T : Set _) := fun j hj => by
    refine coe_mem_normalizer_of_subgroupOf (x := ⟨j, hJL hj⟩) hT.1 ?_
    rw [← heq]
    exact Subgroup.mem_subgroupOf.mpr hj
  have hTJ : T ≤ Jb := fun t ht => hNT ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hTO : T ≤ barM M (S ⊓ L) := by
    rw [hO]
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 T Jb hTJ
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hJN) hT.2.1
  refine hns ⟨barM_mono inf_le_right,
    by rw [hO]; exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Jb,
    fun hd => hT.2.2 ?_⟩
  exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hTO)

@[expose] def KFactOutNineParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
    Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) →
    (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
    ¬ 9 ∣ Nat.card (Outer Y)

theorem not_nine_dvd_of_not_three_dvd {n : ℕ} (h : ¬ 3 ∣ n) : ¬ 9 ∣ n := fun h9 =>
  h ((show 3 ∣ 9 by norm_num).trans h9)

theorem not_nine_dvd_card_outer_orthTwo (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ (m = 3 ∧ d.1 = .twistedA 3 q))) :
    ¬ 9 ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, q, hq, hd⟩ := hd
  have hq2 : q.p = 2 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq
    exact Nat.prime_two.pow_eq_iff.mp hq
  rcases hd with rfl | rfl | ⟨rfl, rfl⟩
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    obtain ⟨a, k, hak, ha0, ha2, hk0, hk3⟩ := exists_card_outer_eq_mul_of_omegaPlus_two hmod
    change ¬ 9 ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.D m q, hv⟩))
    rw [hak]
    intro hdvd
    have := Nat.le_of_dvd (Nat.mul_pos ha0 hk0) hdvd
    nlinarith
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    have h2 := card_outer_le_two_of_omegaMinus_two hmod
    change ¬ 9 ∣ Nat.card (Outer (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD m q, hv⟩))
    intro hdvd
    have := Nat.le_of_dvd h2.1 hdvd
    omega
  · have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
      (MulEquiv.refl _)
    rw [hq2.1, hq2.2] at hmod
    exact not_nine_dvd_of_not_three_dvd
      (not_dvd_card_outer_of_psu_four_two hmod Nat.prime_three (by norm_num))

theorem not_nine_dvd_card_outer_alt {n : ℕ} (hn : 5 ≤ n) :
    ¬ 9 ∣ Nat.card (Outer (alternatingGroup (Fin n))) :=
  not_nine_dvd_of_not_three_dvd
    (not_dvd_card_outer_alternatingGroup n hn 3 Nat.prime_three (by norm_num))

theorem not_nine_dvd_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ¬ 9 ∣ Nat.card (Outer X')) : ¬ 9 ∣ Nat.card (Outer X) := by
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]

theorem not_nine_dvd_of_center_alt {X : Type*} [Group X] [Group.IsPerfect X]
    [Nontrivial (X ⧸ Subgroup.center X)] {n : ℕ}
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) : ¬ 9 ∣ Nat.card (Outer X) := by
  intro h9
  exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt
    (five_le_of_isPerfect_mulEquiv_alternatingGroup e))
    (h9.trans (card_outer_dvd_card_outer_centerQuotient X))

theorem kFactBlockThreeOut_of_parabolic (h : KFactOutNineParabolic) : KFactBlockThreeOut := by
  intro G _ _ M S L hK hA hL h93 hX hS hperf U hUS hUL hU3
  refine relIndex_sup_centralizer_le_three hUL hU3 ?_
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := Group.isPerfect_def.mpr hq.1
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2.toNontrivial
  have : Nontrivial ↥(barM M L) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
      hS (isSylowTwoOf_inf_of_barM hL.le hA.twoCore_le hA.twoRadical.isPGroup hsyl)
    obtain ⟨T₁, hT₁, hN, hne⟩ := exists_sylowTwo_parabolic_of_nineThreeTwo h2 hns
    refine h ↥(barM M L) hq h2.1 T₁ _ hT₁ hN hne ?_
    intro W hW hWp
    have h1 := hperf (W.map (barM M L).subtype) (fun x hx => by
        obtain ⟨u, hu, rfl⟩ := hx
        exact Subgroup.mem_subgroupOf.mp (hW hu))
      (by rw [← Subgroup.map_commutator, hWp])
    rwa [Subgroup.card_map_of_injective (barM M L).subtype_injective] at h1
  · rcases h3.2.1 with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_orthTwo d hd)
    · exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt (by omega))
  · obtain ⟨-, -, ⟨e⟩, -⟩ := h4
    exact not_nine_dvd_of_center_alt e
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt (by norm_num))
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h6
    exact not_nine_dvd_of_center_alt e
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt
      (five_le_of_isPerfect_mulEquiv_alternatingGroup e))
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt
      (five_le_of_isPerfect_mulEquiv_alternatingGroup e))

end CFSG.AGLEmbedding
