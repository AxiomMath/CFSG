module

public import CFSG.LieType.ChevTwo.LayeredOps
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.LocalComponents

variable {W W' : Type}

@[expose] def compOrdSet (W : Type) [Group W] (N : ℕ) : Set (Subgroup W) :=
  {K | CFSG.Open.IsComponentOf K ⊤ ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = N}

@[expose] def IsChevTwoLayeredBy (W : Type) [Group W] (o : List ℕ) : Prop :=
  IsChevTwoLayered W ∧ ∀ N : ℕ, (compOrdSet W N).ncard ≤ o.count N

theorem compOrdSet_finite [Group W] [Finite W] (N : ℕ) : (compOrdSet W N).Finite :=
  Set.finite_univ.subset (Set.subset_univ _)

theorem mem_compOrdSet {W : Type} [Group W] {K : Subgroup W} {N : ℕ} :
    K ∈ compOrdSet W N ↔
      CFSG.Open.IsComponentOf K ⊤ ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = N :=
  Iff.rfl

theorem compOrdSet_map_iff [Group W] [Group W'] (e : W ≃* W') {K : Subgroup W} {N : ℕ} :
    K.map (e : W →* W') ∈ compOrdSet W' N ↔ K ∈ compOrdSet W N := by
  constructor
  · intro h
    rw [mem_compOrdSet] at h ⊢
    refine ⟨(LocalComponents.equiv_iff e K).mp h.1, ?_⟩
    rw [← h.2]
    exact Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
      (Subgroup.equivMapOfInjective K (e : W →* W') e.injective))
  · intro h
    rw [mem_compOrdSet] at h ⊢
    refine ⟨(LocalComponents.equiv_iff e K).mpr h.1, ?_⟩
    rw [← h.2]
    exact (Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
      (Subgroup.equivMapOfInjective K (e : W →* W') e.injective))).symm

theorem ncard_compOrdSet_map [Group W] [Group W'] (e : W ≃* W') (N : ℕ) :
    (compOrdSet W N).ncard = (compOrdSet W' N).ncard := by
  refine Set.ncard_congr (fun K _ => K.map (e : W →* W')) ?_ ?_ ?_
  · intro K hK
    exact (compOrdSet_map_iff e).mpr hK
  · intro K₁ K₂ _ _ h
    exact Subgroup.map_injective e.injective h
  · intro K' hK'
    refine ⟨K'.map (e.symm : W' →* W), ?_, ?_⟩
    · exact (compOrdSet_map_iff e.symm).mpr hK'
    · rw [Subgroup.map_map]
      have hcomp : (e : W →* W').comp (e.symm : W' →* W) = MonoidHom.id W' := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]

theorem IsChevTwoLayeredBy.of_mulEquiv [Group W] [Group W'] {o : List ℕ} (e : W ≃* W')
    (h : IsChevTwoLayeredBy W' o) : IsChevTwoLayeredBy W o :=
  ⟨h.1.of_mulEquiv e, fun N => (ncard_compOrdSet_map e N).le.trans (h.2 N)⟩

theorem IsChevTwoLayeredBy.mulEquiv_iff [Group W] [Group W'] {o : List ℕ} (e : W ≃* W') :
    IsChevTwoLayeredBy W o ↔ IsChevTwoLayeredBy W' o :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isChevTwoLayeredBy_of_isSolvable [Group W] [Finite W] (h : Group.IsSolvable W)
    (o : List ℕ) : IsChevTwoLayeredBy W o := by
  haveI : Group.IsSolvable W := h
  refine ⟨isChevTwoLayered_of_isSolvable h, fun N => ?_⟩
  have hempty : compOrdSet W N = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro K hK
    rw [mem_compOrdSet] at hK
    haveI : Group.IsPerfect ↥K := ⟨hK.1.2.2.1⟩
    haveI : Nontrivial ↥K := Quasisimple.nontrivial hK.1.2.2
    haveI : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  rw [hempty, Set.ncard_empty]
  exact Nat.zero_le _

theorem isChevTwoLayeredBy_of_isQuasisimple [Group W] (hW : CFSG.Open.IsQuasisimple W)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (W ⧸ Subgroup.center W)) :
    IsChevTwoLayeredBy W [Nat.card (W ⧸ Subgroup.center W)] := by
  refine ⟨isChevTwoLayered_of_isQuasisimple hW h, fun N => ?_⟩
  have htop : CFSG.Open.IsComponentOf (⊤ : Subgroup W) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := W)) hW⟩
  have hcomp_top : ∀ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ → K = ⊤ := by
    intro K hK
    haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
    rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hW K hK.2.1 with hbot | htop'
    · exfalso
      haveI : Nontrivial ↥K := Quasisimple.nontrivial hK.2.2
      exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hbot
    · exact htop'
  have hnat : Nat.card (↥(⊤ : Subgroup W) ⧸ Subgroup.center ↥(⊤ : Subgroup W)) =
      Nat.card (W ⧸ Subgroup.center W) :=
    Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
      (Subgroup.topEquiv (G := W)))
  by_cases hN : Nat.card (W ⧸ Subgroup.center W) = N
  · have hset : compOrdSet W N = {⊤} := by
      ext K
      constructor
      · intro hK
        rw [mem_compOrdSet] at hK
        have hKtop : K = ⊤ := hcomp_top K hK.1
        rw [hKtop]
        exact Set.mem_singleton _
      · intro hK
        rw [Set.mem_singleton_iff] at hK
        subst hK
        rw [mem_compOrdSet]
        exact ⟨htop, by rw [hnat, hN]⟩
    rw [hset, Set.ncard_singleton, List.count_singleton]
    have hbeq : (Nat.card (W ⧸ Subgroup.center W) == N) = true := by
      rw [beq_iff_eq]
      exact hN
    rw [hbeq]
    simp
  · have hset : compOrdSet W N = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro K hK
      rw [mem_compOrdSet] at hK
      have hKtop : K = ⊤ := hcomp_top K hK.1
      rw [hKtop] at hK
      exact hN (hnat.symm.trans hK.2)
    rw [hset, Set.ncard_empty]
    exact Nat.zero_le _

theorem IsChevTwoLayeredBy.of_normal_of_solvable_quotient [Group W] [Finite W] (N : Subgroup W)
    [N.Normal] {o : List ℕ} (hN : IsChevTwoLayeredBy ↥N o)
    (hq : Group.IsSolvable (W ⧸ N)) : IsChevTwoLayeredBy W o := by
  haveI : Group.IsSolvable (W ⧸ N) := hq
  refine ⟨IsChevTwoLayered.of_normal_of_solvable_quotient N hN.1 hq, fun n => ?_⟩
  have hbound : (compOrdSet W n).ncard ≤ (compOrdSet ↥N n).ncard := by
    have hinj : Set.InjOn (fun K : Subgroup W => K.subgroupOf N) (compOrdSet W n) := by
      intro K₁ hK₁ K₂ hK₂ heq
      have hK₁N : K₁ ≤ N :=
        Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient
          (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top
            (mem_compOrdSet.mp hK₁).1.2.2.1)
      have hK₂N : K₂ ≤ N :=
        Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient
          (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top
            (mem_compOrdSet.mp hK₂).1.2.2.1)
      calc K₁ = (K₁.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hK₁N).symm
        _ = (K₂.subgroupOf N).map N.subtype := by
          rw [show K₁.subgroupOf N = K₂.subgroupOf N from heq]
        _ = K₂ := Subgroup.map_subgroupOf_eq_of_le hK₂N
    have himage : (fun K : Subgroup W => K.subgroupOf N) '' (compOrdSet W n) ⊆
        compOrdSet ↥N n := by
      rintro L ⟨K, hK, rfl⟩
      rw [mem_compOrdSet] at hK ⊢
      have hKN : K ≤ N :=
        Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient
          (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.1.2.2.1)
      refine ⟨LocalComponents.of_overgroup hK.1 hKN, ?_⟩
      rw [← hK.2]
      exact Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.subgroupOfEquivOfLe hKN))
    calc (compOrdSet W n).ncard
        = ((fun K : Subgroup W => K.subgroupOf N) '' (compOrdSet W n)).ncard :=
          (Set.ncard_image_iff (compOrdSet_finite n)).mpr hinj |>.symm
      _ ≤ (compOrdSet ↥N n).ncard := Set.ncard_le_ncard himage (compOrdSet_finite n)
  exact hbound.trans (hN.2 n)

private theorem exists_component_quotient [Group W] [Finite W] (T : Subgroup W) [T.Normal]
    (hT : Group.IsSolvable ↥T)
    (hE : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.Open.GLALayer (⊤ : Subgroup W))
    {Kbar : Subgroup (W ⧸ T)} (hKbar : CFSG.Open.IsComponentOf Kbar ⊤) :
    ∃ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ ∧ Kbar = K.map (QuotientGroup.mk' T) ∧
      Nat.card (↥K ⧸ Subgroup.center ↥K) =
        Nat.card (↥Kbar ⧸ Subgroup.center ↥Kbar) := by
  haveI : Group.IsSolvable ↥T := hT
  have hTsub : CFSG.Open.IsSubnormal T ⊤ := by
    have h' : (T.subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf ‹T.Normal› ⊤
    exact CFSG.Open.IsSubnormal.step le_top h' (CFSG.Open.IsSubnormal.refl ⊤)
  have hcompImage : ∀ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ →
      K.map (QuotientGroup.mk' T) = ⊥ ∨
        CFSG.Open.IsComponentOf (K.map (QuotientGroup.mk' T)) ⊤ := by
    intro K hK
    by_cases hKT : K ≤ T
    · left
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hKT
    · right
      exact LocalComponents.image hK (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
        (by rwa [QuotientGroup.ker_mk'])
  have hLayerMap : (CFSG.Open.GLALayer (⊤ : Subgroup W)).map (QuotientGroup.mk' T) ≤
      CFSG.Open.GLALayer (⊤ : Subgroup (W ⧸ T)) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    rcases hcompImage K hK with hbot | hcomp
    · rw [hbot]
      exact bot_le
    · exact CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hcomp
  have hLift : ∀ Pbar : Subgroup (W ⧸ T), ⁅Pbar, Pbar⁆ = Pbar →
      ∃ L : Subgroup W, ⁅L, L⁆ = L ∧ L ≤ CFSG.Open.GLALayer (⊤ : Subgroup W) ∧
        L.map (QuotientGroup.mk' T) = Pbar := by
    intro Pbar hPbar
    let M : Subgroup W := Pbar.comap (QuotientGroup.mk' T)
    let φ : ↥M →* ↥Pbar :=
      { toFun := fun x => ⟨QuotientGroup.mk' T x.1, Subgroup.mem_comap.mp x.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ a.1 b.1) }
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective T y.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [Subgroup.mem_comap, hx]
      exact y.2
    haveI : Group.IsPerfect ↥(⊤ : Subgroup ↥Pbar) :=
      Group.IsPerfect.top_iff.mpr
        (Group.isPerfect_def.mpr
          (CFSG.LocalAnalysis.GLTheoremA.I142N.commutator_top_of_comm_self_eq hPbar))
    obtain ⟨L, -, hLmap, hLcomm, -⟩ :=
      CFSG.ComponentClassification.Components.perfect_subnormal_lift φ hφ ⊤
        Subgroup.IsSubnormal.top
    have hLperf : ⁅L.map M.subtype, L.map M.subtype⁆ = L.map M.subtype := by
      have h1 : ⁅L, L⁆ = L :=
        CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hLcomm
      have h2 := congrArg (Subgroup.map M.subtype) h1
      simpa only [Subgroup.map_commutator] using h2
    exact ⟨L.map M.subtype, hLperf, hE _ hLperf, by
      have hcomp : ((QuotientGroup.mk' T).comp M.subtype) = Pbar.subtype.comp φ := by
        ext x
        rfl
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hLmap,
        CFSG.LocalAnalysis.GLTheoremA.I142N.map_subtype_top]⟩
  have hKbarPerf : ⁅Kbar, Kbar⁆ = Kbar :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hKbar.2.2.1
  have hexists : ∃ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ ∧
      Kbar = K.map (QuotientGroup.mk' T) := by
    obtain ⟨L, hLperf, hLle, hLmap⟩ := hLift Kbar hKbarPerf
    have hLle' : L ≤ sSup {K : Subgroup W | CFSG.Open.IsComponentOf K ⊤} := by
      rw [← CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_eq_sSup]
      exact hLle
    have hKbar_le : Kbar ≤ sSup ((fun K : Subgroup W => K.map (QuotientGroup.mk' T)) ''
        {K : Subgroup W | CFSG.Open.IsComponentOf K ⊤}) := by
      rw [← hLmap]
      refine (Subgroup.map_mono hLle').trans ?_
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun K hK => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (Set.mem_image_of_mem _ hK)
    by_contra hcon
    have hne : ∀ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ →
        Kbar ≠ K.map (QuotientGroup.mk' T) := by
      intro K hK heq
      exact hcon ⟨K, hK, heq⟩
    have hcommAll : ∀ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ →
        ⁅K.map (QuotientGroup.mk' T), Kbar⁆ = ⊥ := by
      intro K hK
      rcases hcompImage K hK with hbot | hcomp
      · rw [hbot, Subgroup.commutator_bot_left]
      · exact LocalComponents.commute_of_ne (K.map (QuotientGroup.mk' T)) Kbar hcomp hKbar
          (Ne.symm (hne K hK))
    have hle_cen : sSup ((fun K : Subgroup W => K.map (QuotientGroup.mk' T)) ''
        {K : Subgroup W | CFSG.Open.IsComponentOf K ⊤}) ≤
        Subgroup.centralizer (Kbar : Set (W ⧸ T)) := by
      refine sSup_le fun N hN => ?_
      obtain ⟨K, hK, rfl⟩ := hN
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommAll K hK)
    have habel : ⁅Kbar, Kbar⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKbar_le.trans hle_cen)
    have hbot : Kbar = ⊥ := by rw [← hKbarPerf, habel]
    exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot Kbar).mp
      (Quasisimple.nontrivial hKbar.2.2))
  obtain ⟨K, hK, hKeq⟩ := hexists
  refine ⟨K, hK, hKeq, ?_⟩
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr
    (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
  let f : ↥K →* ↥Kbar :=
    { toFun := fun x => ⟨QuotientGroup.mk' T x.1, hKeq ▸ Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a.1 b.1) }
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : W ⧸ T) ∈ K.map (QuotientGroup.mk' T) := hKeq ▸ y.2
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hfker : f.ker ≤ Subgroup.center ↥K := by
    have hcommKT : ⁅K, T⁆ = ⊥ :=
      LocalComponents.commutes_with_solvable_subnormal K T hK hTsub
    have hcen : K ≤ Subgroup.centralizer (T : Set W) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKT
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxT : (x : W) ∈ T := by
      have h1 : QuotientGroup.mk' T (x : W) = 1 := congrArg Subtype.val hx
      rw [QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff (x : W)).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := hcen y.2
    rw [Subgroup.mem_centralizer_iff] at hy
    exact Subtype.ext (hy (x : W) hxT).symm
  obtain ⟨e⟩ := nonempty_quotCenter_equiv_of_surjective f hfsurj hfker
  exact Nat.card_congr e

theorem IsChevTwoLayeredBy.quotient [Group W] [Finite W] {o : List ℕ}
    (h : IsChevTwoLayeredBy W o) (T : Subgroup W) [T.Normal] (hT : Group.IsSolvable ↥T) :
    IsChevTwoLayeredBy (W ⧸ T) o := by
  refine ⟨h.1.quotient T hT, fun N => ?_⟩
  have hsub : compOrdSet (W ⧸ T) N ⊆
      (fun K : Subgroup W => K.map (QuotientGroup.mk' T)) '' compOrdSet W N := by
    intro Kbar hKbar
    rw [mem_compOrdSet] at hKbar
    obtain ⟨K, hK, hKeq, hcard⟩ := exists_component_quotient T hT h.1.1 hKbar.1
    refine ⟨K, ?_, hKeq.symm⟩
    rw [mem_compOrdSet]
    exact ⟨hK, by rw [hcard, hKbar.2]⟩
  calc (compOrdSet (W ⧸ T) N).ncard
      ≤ ((fun K : Subgroup W => K.map (QuotientGroup.mk' T)) '' compOrdSet W N).ncard :=
        Set.ncard_le_ncard hsub ((compOrdSet_finite N).image _)
    _ ≤ (compOrdSet W N).ncard := Set.ncard_image_le (compOrdSet_finite N)
    _ ≤ o.count N := h.2 N

theorem IsChevTwoLayeredBy.of_surjective [Group W] [Group W'] [Finite W] {o : List ℕ}
    (φ : W →* W') (hφ : Function.Surjective φ) (hker : Group.IsSolvable ↥φ.ker)
    (h : IsChevTwoLayeredBy W o) : IsChevTwoLayeredBy W' o :=
  (h.quotient φ.ker hker).of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm

theorem IsChevTwoLayeredBy.of_commute_sup [Group W] [Finite W] (K₁ K₂ : Subgroup W)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b) (hsup : K₁ ⊔ K₂ = ⊤) {o₁ o₂ : List ℕ}
    (h₁ : IsChevTwoLayeredBy ↥K₁ o₁) (h₂ : IsChevTwoLayeredBy ↥K₂ o₂) :
    IsChevTwoLayeredBy W (o₁ ++ o₂) := by
  refine ⟨IsChevTwoLayered.of_commute_sup K₁ K₂ hc hsup h₁.1 h₂.1, fun N => ?_⟩
  have hK₁n : K₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hconj : b * a * b⁻¹ = a := by
      calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [(hc a ha b hb).eq]
        _ = a := by simp
    rwa [hconj]
  have hK₂n : K₂.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hconj : b * a * b⁻¹ = a := by
      calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [(hc b hb a ha).eq]
        _ = a := by simp
    rwa [hconj]
  haveI := hK₁n
  haveI := hK₂n
  have hcen : (K₁ ⊓ K₂ : Subgroup W) ≤ Subgroup.center W := by
    have h1 : (K₁ ⊓ K₂ : Subgroup W) ≤ Subgroup.centralizer (K₁ : Set W) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc y hy x hx.2).eq
    have h2 : (K₁ ⊓ K₂ : Subgroup W) ≤ Subgroup.centralizer (K₂ : Set W) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc x hx.1 y hy).eq.symm
    have hjoin := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers h1 h2
    rw [hsup] at hjoin
    rw [← Subgroup.centralizer_univ]
    exact hjoin
  have hcover : compOrdSet W N ⊆
      ((fun K : Subgroup ↥K₁ => K.map K₁.subtype) '' compOrdSet ↥K₁ N) ∪
        ((fun K : Subgroup ↥K₂ => K.map K₂.subtype) '' compOrdSet ↥K₂ N) := by
    intro K hK
    rw [mem_compOrdSet] at hK
    rcases LocalComponents.normal_contains_or_commutes K K₁ hK.1 with hle₁ | hcom₁
    · left
      refine ⟨K.subgroupOf K₁, ?_, Subgroup.map_subgroupOf_eq_of_le hle₁⟩
      rw [mem_compOrdSet]
      refine ⟨LocalComponents.of_overgroup hK.1 hle₁, ?_⟩
      rw [← hK.2]
      exact Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.subgroupOfEquivOfLe hle₁))
    · rcases LocalComponents.normal_contains_or_commutes K K₂ hK.1 with hle₂ | hcom₂
      · right
        refine ⟨K.subgroupOf K₂, ?_, Subgroup.map_subgroupOf_eq_of_le hle₂⟩
        rw [mem_compOrdSet]
        refine ⟨LocalComponents.of_overgroup hK.1 hle₂, ?_⟩
        rw [← hK.2]
        exact Nat.card_congr (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
          (Subgroup.subgroupOfEquivOfLe hle₂))
      · exfalso
        have hKc₁ : K ≤ Subgroup.centralizer (K₁ : Set W) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom₁
        have hKc₂ : K ≤ Subgroup.centralizer (K₂ : Set W) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom₂
        have hcenter : K ≤ Subgroup.center W := by
          have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hKc₁ hKc₂
          rw [hsup] at h
          rw [← Subgroup.centralizer_univ]
          exact h
        have hperf : ⁅K, K⁆ = K :=
          CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.1.2.2.1
        have hcomm : ⁅K, K⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y _
          exact Subgroup.mem_center_iff.mp (hcenter hx) y
        have hbot : K = ⊥ := by rw [← hperf, hcomm]
        exact (Subgroup.nontrivial_iff_ne_bot K).mp (Quasisimple.nontrivial hK.1.2.2) hbot
  calc (compOrdSet W N).ncard
      ≤ (((fun K : Subgroup ↥K₁ => K.map K₁.subtype) '' compOrdSet ↥K₁ N) ∪
          ((fun K : Subgroup ↥K₂ => K.map K₂.subtype) '' compOrdSet ↥K₂ N)).ncard :=
        Set.ncard_le_ncard hcover
          (((compOrdSet_finite (W := ↥K₁) N).image _).union
            ((compOrdSet_finite (W := ↥K₂) N).image _))
    _ ≤ ((fun K : Subgroup ↥K₁ => K.map K₁.subtype) '' compOrdSet ↥K₁ N).ncard +
          ((fun K : Subgroup ↥K₂ => K.map K₂.subtype) '' compOrdSet ↥K₂ N).ncard :=
        Set.ncard_union_le _ _
    _ ≤ o₁.count N + o₂.count N :=
        Nat.add_le_add
          ((Set.ncard_image_le (compOrdSet_finite (W := ↥K₁) N)).trans (h₁.2 N))
          ((Set.ncard_image_le (compOrdSet_finite (W := ↥K₂) N)).trans (h₂.2 N))
    _ = (o₁ ++ o₂).count N := (List.count_append).symm

theorem IsChevTwoLayeredBy.quotient_of_sup_eq_top [Group W] [Finite W] {L Q : Subgroup W}
    [Q.Normal] {o : List ℕ} (hQ : Group.IsSolvable ↥Q) (hsup : L ⊔ Q = ⊤)
    (hL : IsChevTwoLayeredBy ↥L o) : IsChevTwoLayeredBy (W ⧸ Q) o := by
  let φ : ↥L →* W ⧸ Q := (QuotientGroup.mk' Q).comp L.subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Q x
    have hw : w ∈ L ⊔ Q := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨l, hl, q, hq, hlq⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    refine ⟨⟨l, hl⟩, ?_⟩
    have hq1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).2 hq
    calc φ ⟨l, hl⟩ = QuotientGroup.mk' Q l * QuotientGroup.mk' Q q := by
          simp [φ, hq1]
      _ = QuotientGroup.mk' Q (l * q) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' Q w := by rw [hlq]
  let ψ : ↥φ.ker →* ↥Q :=
    { toFun := fun x =>
        ⟨(x.1 : W), (QuotientGroup.eq_one_iff (x.1 : W)).1 (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h : (a.1 : W) = (b.1 : W) := congrArg (fun z : ↥Q => (z : W)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : Group.IsSolvable ↥Q := hQ
  have hker_solv : Group.IsSolvable ↥φ.ker :=
    Group.isSolvable_of_isSolvable_injective (f := ψ) hψ
  exact IsChevTwoLayeredBy.of_surjective φ hφ hker_solv hL

end CFSG.LieType.ChevTwo
