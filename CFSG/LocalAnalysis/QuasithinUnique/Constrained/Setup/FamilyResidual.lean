module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem isPGroup_quotient_of_sup_eq_top {X : Type*} [Group X] (N T : Subgroup X) [N.Normal]
    (hT : IsPGroup 2 T) (h : N ⊔ T = ⊤) : IsPGroup 2 (X ⧸ N) := by
  have hmap : T.map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : (N ⊔ T).map (QuotientGroup.mk' N) = ⊤ := by
      rw [h, Subgroup.map_top, QuotientGroup.range_mk']
    rw [Subgroup.map_sup, (QuotientGroup.map_mk'_self N), bot_sup_eq] at h1
    exact h1
  refine hT.of_surjective ((QuotientGroup.mk' N).comp T.subtype) fun q => ?_
  have : q ∈ T.map (QuotientGroup.mk' N) := by rw [hmap]; trivial
  obtain ⟨t, ht, rfl⟩ := this
  exact ⟨⟨t, ht⟩, rfl⟩

theorem subgroupOf_sup_eq_top {G : Type*} [Group G] {H L T : Subgroup G} (hLH : L ≤ H)
    (hTH : T ≤ H) (h : H = L ⊔ T) : L.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_subgroupOf_eq_of_le hTH,
    Subgroup.map_top, Subgroup.range_subtype]
  exact h.symm

theorem isSolvable_inf_centralizer {G : Type*} [Group G] {H L : Subgroup G}
    [Finite G] [(L.subgroupOf H).Normal] (h2 : IsPGroup 2 (↥H ⧸ L.subgroupOf H)) :
    Group.IsSolvable ↥(H ⊓ Subgroup.centralizer (L : Set G)) := by
  set C := H ⊓ Subgroup.centralizer (L : Set G) with hC
  let φ : ↥C →* ↥H ⧸ L.subgroupOf H :=
    (QuotientGroup.mk' (L.subgroupOf H)).comp (Subgroup.inclusion (inf_le_left : C ≤ H))
  have hmem : ∀ a : ↥φ.ker, ((a : ↥C) : G) ∈ L := by
    intro a
    have : φ a = 1 := a.2
    exact (QuotientGroup.eq_one_iff (N := L.subgroupOf H) _).1 this
  have hcomm : ∀ a b : ↥φ.ker, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (b : ↥C).2.2 _ (hmem a)
    exact this
  have h1 : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_comm hcomm
  have h3 : Group.IsNilpotent (↥H ⧸ L.subgroupOf H) := h2.isNilpotent
  have h4 : Group.IsSolvable (↥H ⧸ L.subgroupOf H) := inferInstance
  exact Group.isSolvable_of_ker_le_range (φ.ker.subtype) φ (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem normal_inf_centralizer {G : Type*} [Group G] {H L : Subgroup G} (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) :
    ((H ⊓ Subgroup.centralizer (L : Set G)).subgroupOf H).Normal := by
  refine ⟨fun c hc h => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hc ⊢
  refine ⟨(h * c * h⁻¹ : ↥H).2, ?_⟩
  show _ ∈ Subgroup.centralizer (L : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : (h : G)⁻¹ * l * (h : G) ∈ L := by
    have := (Subgroup.normal_subgroupOf_iff hLH).1 hLn l (h : G)⁻¹ hl (inv_mem h.2)
    simpa using this
  have hc2 := Subgroup.mem_centralizer_iff.1 hc.2 _ hl'
  calc l * ((h * c * h⁻¹ : ↥H) : G)
      = (h : G) * (((h : G)⁻¹ * l * (h : G)) * c) * (h : G)⁻¹ := by simp [mul_assoc]
    _ = (h : G) * (c * ((h : G)⁻¹ * l * (h : G))) * (h : G)⁻¹ := by rw [hc2]
    _ = _ := by simp [mul_assoc]

theorem isSolvable_subgroupOf_of_le {G : Type*} [Group G] (H C : Subgroup G) (hCH : C ≤ H)
    [Group.IsSolvable ↥C] : Group.IsSolvable ↥(C.subgroupOf H) :=
  Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hCH).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hCH).injective

theorem le_radIn_of_normal_solvable {G : Type} [Group G] {H C : Subgroup G} (hCH : C ≤ H)
    (hn : (C.subgroupOf H).Normal) [Group.IsSolvable ↥C] : C ≤ radIn H := by
  have hmem : C.subgroupOf H ≤ CFSG.solvableRadical ↥H := by
    unfold CFSG.solvableRadical
    exact le_sSup ⟨hn, isSolvable_subgroupOf_of_le H C hCH⟩
  intro c hc
  exact ⟨⟨c, hCH hc⟩, hmem hc, rfl⟩

theorem map_conj_eq_of_normal {G : Type*} [Group G] {H L : Subgroup G} (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) {t : G} (ht : t ∈ H) :
    L.map (MulAut.conj t).toMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hLH).1 hLn l t hl ht
  · intro hx
    refine ⟨t⁻¹ * x * t, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.normal_subgroupOf_iff hLH).1 hLn x t⁻¹ hx (inv_mem ht)
    simpa using this

theorem map_center_subtype_eq_centerIn {G : Type} [Group G] (L : Subgroup G) :
    (Subgroup.center ↥L).map L.subtype = centerIn L := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun l hl => by
      have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
      exact congrArg Subtype.val this
  · rintro ⟨hxL, hxc⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)

theorem card_centerIn_eq {G : Type} [Group G] (L : Subgroup G) :
    Nat.card (centerIn L) = Nat.card (Subgroup.center ↥L) := by
  rw [← map_center_subtype_eq_centerIn, Subgroup.card_map_of_injective L.subtype_injective]

theorem isPGroup_subgroupOf_of_isSylowTwoOf {G : Type} [Group G] {H T : Subgroup G}
    (hT : IsSylowTwoOf T H) : IsPGroup 2 (T.subgroupOf H) := by
  have : IsPGroup 2 ↥T := hT.2.1
  exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm

theorem coreIn_le {G : Type} [Group G] (H M : Subgroup G) : coreIn H M ≤ M := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.normalCore_le _ hx : x ∈ M.subgroupOf H)

theorem two_le_pRank_three_of_alternating_six {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 6)) : 2 ≤ CFSG.pRank 3 S := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt (n := 6) le_rfl)
    (CFSG.SectionRank.card_sylowThreeAlt (n := 6) le_rfl)

theorem ResidualFamily.false_of_oddRankLeOne (hq1 : OddRankOneOddClassicalProp)
    (hq2 : OddRankOneEvenClassicalProp) (hq3 : OddRankOneChevalleyProp)
    (hq4 : OddRankOneReeTitsProp) (hq5 : TrialityTwoHasRankTwoProp) {S : Type} [Group S]
    [Finite S] (hS : OddRankLeOne S) (h : ResidualFamily S) : False := by
  have h3 : CFSG.pRank 3 S ≤ 1 := hS 3 Nat.prime_three (by norm_num)
  rcases h with he | h | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hodd, hf3, h⟩ | h
  · obtain ⟨e⟩ := he
    have := two_le_pRank_three_of_alternating_six e
    omega
  · have := hq1 S hS 3 Nat.prime_three (by norm_num) .PSU 3 1 h
    simp at this
  · rcases h with h | h | h
    · rcases hq2 S hS .PSL 3 f h with ⟨-, h2, -⟩ | ⟨-, -, h1⟩ <;> omega
    · rcases hq2 S hS .PSU 3 f h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp at h1
    · rcases hq2 S hS .PSp 2 f h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp at h1
  · have := hq3 S hS .G2 2 f (by simp [chevalleyExceptionalTags]) h
    simp at this
  · obtain ⟨-, -, hf1⟩ := hq3 S hS .trialityD4 2 f (by simp [chevalleyExceptionalTags]) h
    subst hf1
    have := hq5 S h
    omega
  · exact hq4 S hS .twistedF4 2 f (by simp [reeTitsTags]) h
  · exact hq4 S hS .Tits 2 1 (by simp [reeTitsTags]) h

theorem oneQuasisimpleResidual (hlayer : ActorLayerProp) (hfam : FamilyRestrictionProp)
    (hnorm : ComponentOddRankTwoNormalProp) (hq1 : OddRankOneOddClassicalProp)
    (hq2 : OddRankOneEvenClassicalProp) (hq3 : OddRankOneChevalleyProp)
    (hq4 : OddRankOneReeTitsProp) (hq5 : TrialityTwoHasRankTwoProp) :
    OneQuasisimpleResidualProp := by
  intro V _ _ H T M E hFF hns hSQTK hnoSL2
  have hLay : ActorLayer V H T M := hlayer V H T M E hFF hns
  have hTH : T ≤ H := hFF.sylow.1
  have hcomp_norm : ∀ L : Subgroup (MulAut V), IsComp L H → (L.subgroupOf H).Normal := by
    intro L hL
    by_contra hnn
    have hrank : OddRankLeOne (CQ L) := by
      intro r hr hr2
      by_contra hgt
      exact hnn (hnorm (MulAut V) H L hSQTK hL r hr hr2 (by omega))
    obtain ⟨hres, -, -⟩ := hfam V H T M E hFF hns hSQTK hnoSL2 L hL
    exact ResidualFamily.false_of_oddRankLeOne hq1 hq2 hq3 hq4 hq5 hrank hres
  obtain ⟨L, hL⟩ := hLay.exists_component
  have hLH : L ≤ H := hL.1
  have hLn : (L.subgroupOf H).Normal := hcomp_norm L hL
  have huniq : ∀ L' : Subgroup (MulAut V), IsComp L' H → L' = L := by
    intro L' hL'
    obtain ⟨t, htT, ht⟩ := hLay.components_transitive L L' hL hL'
    rw [ht]
    exact map_conj_eq_of_normal hLH hLn (hTH htT)
  have hKeq : oddOrderSubgroup H = L := by
    rw [← hLay.components_generate]
    exact le_antisymm (le_iSup₂ (f := fun (L' : Subgroup (MulAut V)) (_ : IsComp L' H) => L') L hL)
      (iSup₂_le fun L' hL' => (huniq L' hL').le) |>.symm
  have hHeq : H = L ⊔ T := hKeq ▸ hLay.eq_K_sup_T
  have hquot : IsPGroup 2 (↥H ⧸ L.subgroupOf H) :=
    have := hLn
    isPGroup_quotient_of_sup_eq_top (L.subgroupOf H) (T.subgroupOf H)
      (isPGroup_subgroupOf_of_isSylowTwoOf hFF.sylow) (subgroupOf_sup_eq_top hLH hTH hHeq)
  have hcent : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) = radIn H := by
    apply le_antisymm
    · have := hLn
      have := isSolvable_inf_centralizer (H := H) (L := L) hquot
      exact le_radIn_of_normal_solvable inf_le_left (normal_inf_centralizer hLH hLn)
    · rw [hLay.rad_eq_fitting, hLay.fitting_eq_center, hKeq]
      exact fun x hx => ⟨hLH hx.1, hx.2⟩
  have hfitting : fittingIn H = centerIn L := by rw [hLay.fitting_eq_center, hKeq]
  obtain ⟨-, hZ, -⟩ := hfam V H T M E hFF hns hSQTK hnoSL2 L hL
  have hZ' : Nat.card (centerIn L) = 1 ∨ Nat.card (centerIn L) = 3 := by
    rw [card_centerIn_eq]; exact hZ
  have hC : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) = centerIn L :=
    hcent.trans (hLay.rad_eq_fitting.trans hfitting)
  have hcore : centerIn L ≤ M := by
    rw [← hC, hcent, ← hLay.core_eq_rad]
    exact coreIn_le H M
  refine ⟨L, ⟨hL, huniq, hLn, hKeq, hKeq.symm.trans hLay.K_eq_layer, hLay.layer_eq_genFitting,
    hHeq, hquot, hcent, hLay.rad_eq_fitting, hfitting, hZ', ?_⟩⟩
  exact exists_residual_action hLH hLn (isQuasisimple_of_isComp hL) hC hZ' hFF.sylow
    hFF.not_normal hFF.max hcore

end CFSG.QuasithinUnique.Setup.Family
