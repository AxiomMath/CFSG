module

public import CFSG.ClassicalInvolution.Q3.TL3TwistStep
public import CFSG.ClassicalInvolution.Q3.TL3EndB3
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem isSimpleGroup_of_quasisimple_of_center_eq_bot {K : Type} [Group K]
    (hK : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hK' : IsSimpleGroup K := e.symm.isSimpleGroup
  refine ⟨hK', ?_⟩
  by_contra hab
  push Not at hab
  have hcomm : commutator K = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  obtain ⟨x, y, hxy⟩ := exists_pair_ne K
  have h1 : ∀ z : K, z = 1 := by
    intro z
    have : z ∈ commutator K := by
      rw [hK.1]
      exact Subgroup.mem_top z
    rw [hcomm, Subgroup.mem_bot] at this
    exact this
  exact hxy ((h1 x).trans (h1 y).symm)

theorem exists_central_involution_of_center_ne_bot {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y = ⊥) (hZ : Subgroup.center Y ≠ ⊥) :
    ∃ c ∈ Subgroup.center Y, orderOf c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : 2 ∣ Nat.card ↥(Subgroup.center Y) := by
    by_contra hodd
    apply hZ
    have hle : Subgroup.center Y ≤ classicalInvolutionOddCore Y :=
      le_sSup ⟨inferInstance, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)⟩
    rw [hO] at hle
    exact le_bot_iff.mp hle
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hev
  exact ⟨c, c.2, by rw [Subgroup.orderOf_coe]; exact hc⟩

theorem TightDatum.genFittingFitting_le_center {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) : genFittingFitting Y ≤ Subgroup.center Y := by
  have hFn : (genFittingFitting Y).Normal := genFittingFitting_normal
  have hF2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hc.2.2
  exact hd.le_center_of_normal_two hc hFn hF2 fun h => hE2 ⟨_, hFn, hF2, h⟩

theorem TightDatum.center_genFittingFStar_le {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) :
    (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype ≤
      Subgroup.center Y := by
  set F : Subgroup Y := genFittingFStar Y with hF
  have hFn : F.Normal := genFittingFStar_normal Y
  set Z : Subgroup Y := (Subgroup.center ↥F).map F.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz y => ?_⟩
    obtain ⟨c, hc'', rfl⟩ := hz
    have hc' : c ∈ Subgroup.center ↥F := hc''
    refine ⟨⟨y * c * y⁻¹, hFn.conj_mem _ c.2 y⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro f
    apply Subtype.ext
    have hf : y⁻¹ * (f : Y) * y ∈ F := by simpa using hFn.conj_mem _ f.2 y⁻¹
    have h' : y⁻¹ * (f : Y) * y * (c : Y) = (c : Y) * (y⁻¹ * (f : Y) * y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨_, hf⟩)
    show (f : Y) * (y * c * y⁻¹) = y * c * y⁻¹ * f
    calc (f : Y) * (y * c * y⁻¹) = y * ((y⁻¹ * f * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * f * y)) * y⁻¹ := by rw [h']
      _ = y * c * y⁻¹ * f := by group
  have hZcomm : ∀ a b : ↥Z, a * b = b * a := by
    rintro ⟨a, c₁, hc₁, rfl⟩ ⟨b, c₂, hc₂, rfl⟩
    apply Subtype.ext
    show (c₁ : Y) * c₂ = c₂ * c₁
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₁ c₂).symm
  have hZnil : Group.IsNilpotent ↥Z := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥Z →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hZcomm w z
  exact (le_sSup ⟨hZn, hZnil⟩ : Z ≤ genFittingFitting Y).trans
    (hd.genFittingFitting_le_center hc hE2)

section Cit3


theorem tightStep_of_parts₄ (htw : ∀ n, TightTwistAllTwin n) (h1 : TightSmallBase)
    (h2 : ∀ n, TightLargeEdgeS n) (h3 : ∀ n, TightLargeLift n) : ∀ n, TightStep n := by
  intro n hA hb Y _ _ hn R S t hd hc
  by_cases hE2 : TightInO2 t
  · exact Or.inl (Or.inl hE2)
  rcases (tightDichotomy_holds n Y hn R S t hd hc).resolve_left hE2 with hQ | htw'
  swap
  · exact tightTwistStep_of_allTwin htw n hA hb Y hn R S t hd hc hE2 htw'
  by_cases hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact h1 Y (by rw [hn]; exact hA) R S t hd hc hE2 hQ hsmall
  by_cases hZ : Subgroup.center Y = ⊥
  ·
    have hZF : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
      have h := hd.center_genFittingFStar_le hc hE2
      rw [hZ, le_bot_iff,
        Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h
      exact h
    obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hQ hZF
    exact Or.inr (h3 n hA hb Y hn R S t hd hc hE2 hQ hsmall
      (h2 n hA hb Y hn hnab R S t hd hc hE2 hsmall))
  · obtain ⟨c, hcZ, hc2⟩ := exists_central_involution_of_center_ne_bot hc.2.2 hZ
    by_cases htwin : ∃ y : Y, y * t * y⁻¹ = t * c
    · obtain ⟨y, hy⟩ := htwin
      have hc1 : c ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      exact Or.inr (h3 n hA hb Y hn R S t hd hc hE2 hQ hsmall
        (hd.not_edgeless_of_twin hcZ hc1 hy))
    · push Not at htwin
      exact tightExOrGood_of_central hb hn hd hc hE2 hcZ hc2 htwin

end Cit3

theorem tightTopRestrictS :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
        Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) →
        ∃ (H : Subgroup G) (R' : Subgroup H) (S' : Sylow 2 R') (t' : H),
          TightDatum R' S' t' ∧ TightCls H R' S' t' ∧ ¬ TightInO2 t' ∧
          IsSimpleGroup ↥(genFittingFStar H) ∧ (∃ a b : genFittingFStar H, a * b ≠ b * a) ∧
          ¬ TwoSubgroupsFourGenerated (genFittingFStar H) ∧
          ((∃ L : Subgroup H, IsClassicalMember3 L t') →
            ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z) := by
  intro G _ _ _ hnab hlarge R S t hd hq8
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  have htK : t ∈ tightCore R := Subgroup.subset_closure ⟨hd.mem_right, ht2⟩
  have hK0ne : tightCore R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htK
    have := hd.order
    rw [htK, orderOf_one] at this
    norm_num at this
  have hSK : (S : Subgroup R).map R.subtype ≤ tightCore R := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.subset_closure ⟨s.2, ?_⟩
    have h1 : IsPGroup 2 ↥(Subgroup.zpowers s) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hs)
    have h2 : IsPGroup 2 ↥((Subgroup.zpowers s).map R.subtype) := h1.map _
    rw [MonoidHom.map_zpowers] at h2
    exact h2
  set H := subnormalClosure (tightCore R) with hH
  have hHsub : IsSubnormal H ⊤ := isSubnormal_subnormalClosure _
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hFH : genFittingFStar G ≤ H :=
    le_subnormalClosure_of_isComponentOf (isComponentOf_top_of_normal_simple _ hnab) hC hK0ne
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hSK.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := hd.restrict hSH
  have hord : orderOf (⟨t, hSH hd.mem⟩ : H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hd.order
  obtain ⟨eF⟩ := nonempty_equiv_genFittingFStar_subgroup hnab hFH
  refine ⟨H, R.subgroupOf H, S', ⟨t, hSH hd.mem⟩, hd', ⟨⟨eS.trans hq8.some⟩, ?_, ?_⟩, ?_,
    eF.isSimpleGroup, ?_, ?_, ?_⟩
  · unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  · exact CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hHsub
  · exact not_inO2_of_fstar_le hnab hFH hord
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  · exact not_twoSubgroupsFourGenerated_subgroup hnab hlarge hFH
  · rintro ⟨L, hL⟩
    exact ⟨_, _, isClassicalMember3_map_subnormal hHsub hL⟩

section Top


theorem tightHasMember3LargeBelow_of_inductive₂ (hI : ∀ N, TightInductive N)
    (hE : ∀ n, TightLargeEdgeS n) (hR4 : TightR4) : Q3T.MFS.TightHasMember3LargeBelow := by
  intro n hn G _ _ _ hlt hnab hlarge R S hS t ht hto hRC hRn h2
  have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
  obtain ⟨H, R', S', t', hd', hcls, hE2, hFs, hnabH, hlargeH, hmem⟩ :=
    tightTopRestrictS G hnab hlarge R S t hd (hR4 n hn G hlt hnab hlarge R S t hd)
  have hHn : Nat.card H < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_injective _ H.subtype_injective) hlt
  have hbelow : TightBelow (Nat.card H) := fun Y _ _ hlt' R S t hd hc =>
    hI n hn Y (lt_trans hlt' hHn) R S t hd hc
  have hedge := hE (Nat.card H) (CIT3Below.mono hHn.le hn) hbelow H rfl hnabH R' S' t' hd' hcls
    hE2 hlargeH
  rcases hI n hn H hHn R' S' t' hd' hcls with
    (hex | ⟨hedgeless, -⟩ | ⟨hedgeless, -⟩ | h4) | hgood
  · exact absurd hex hE2
  · exact absurd hedgeless hedge
  · exact absurd hedgeless hedge
  ·
    have := hFs
    have hZ : Subgroup.center ↥H = ⊥ :=
      le_bot_iff.mp ((centralizer_fstar_eq_bot_and_oddCore_eq_bot hnabH).1 ▸
        Subgroup.center_le_centralizer _)
    exact absurd h4 (hd'.not_tightE4 hcls hE2 hZ)
  · obtain ⟨L, -, hL⟩ := tightHasLift_of_good hd' hgood
    exact hmem ⟨L, hL⟩

end Top

section Leaves


theorem tightHasMember3LargeBelow_of_leaves
    (hF1 : TightF1S fun m => CIT3Below m ∧ TightBelow m)
    (hEnd : TightEndGameOdd fun m => CIT3Below m ∧ TightBelow m)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase) (hlift : ∀ n, TightLargeLift n)
    (hR4 : TightR4) : Q3T.MFS.TightHasMember3LargeBelow := by
  have h11b :=
    tightC19_11bS_of_F1_endgame hF1 (tightEndGameS_of_solv (tightEndGameSolv_of_odd hEnd))
  have hE := tightLargeEdgeS_of_core h11b
  exact tightHasMember3LargeBelow_of_inductive₂
    (tightInductive_of_step (tightStep_of_parts₄ htw hsmall hE hlift)) hE hR4

end Leaves

end CFSG.ClassicalInvolution.Q3
