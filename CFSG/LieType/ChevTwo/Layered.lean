module

public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.LocalComponents
open scoped commutatorElement

variable {W W' : Type}

theorem isChevSimple_of_mulEquiv {r : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple r B) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple r A := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem nonempty_quotCenter_equiv_of_surjective {A B : Type} [Group A] [Group B]
    [Group.IsPerfect A] (f : A →* B) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center A) :
    Nonempty ((A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B)) := by
  have hZ : Subgroup.map f (Subgroup.center A) = Subgroup.center B :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel f hf hk
  let g : A →* B ⧸ Subgroup.center B := (QuotientGroup.mk' (Subgroup.center B)).comp f
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center B) y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, rfl⟩
  have hker : Subgroup.center A = g.ker := by
    ext a
    constructor
    · intro ha
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk (f a) : B ⧸ Subgroup.center B) = 1
      rw [QuotientGroup.eq_one_iff, ← hZ]
      exact Subgroup.mem_map_of_mem f ha
    · intro ha
      rw [MonoidHom.mem_ker] at ha
      have h1 : f a ∈ Subgroup.map f (Subgroup.center A) := by
        rw [hZ]
        exact (QuotientGroup.eq_one_iff (f a)).mp ha
      obtain ⟨z, hz, hfz⟩ := h1
      have h2 : z⁻¹ * a ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfz]
        simp
      have h3 : z⁻¹ * a ∈ Subgroup.center A := hk h2
      simpa using (Subgroup.center A).mul_mem hz h3
  exact ⟨QuotientGroup.liftEquiv (Subgroup.center A) hg hker⟩

@[expose] def IsChevTwoLayered (W : Type) [Group W] : Prop :=
  (∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.Open.GLALayer ⊤) ∧
    ∀ K : Subgroup W, CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)

namespace IsChevTwoLayered

variable [Group W] [Group W']

theorem of_mulEquiv (e : W ≃* W') (h : IsChevTwoLayered W') : IsChevTwoLayered W := by
  have hker : ∀ g : W, (e : W →* W') g = 1 → g ∈ Subgroup.center W := by
    intro g hg
    have hg1 : g = 1 := (MulEquiv.map_eq_one_iff e).mp hg
    rw [hg1]
    exact Subgroup.one_mem _
  have hker' : ∀ g : W', (e.symm : W' →* W) g = 1 → g ∈ Subgroup.center W' := by
    intro g hg
    have hg1 : g = 1 := (MulEquiv.map_eq_one_iff e.symm).mp hg
    rw [hg1]
    exact Subgroup.one_mem _
  constructor
  · intro P hP
    have hP' : ⁅P.map (e : W →* W'), P.map (e : W →* W')⁆ = P.map (e : W →* W') := by
      rw [← Subgroup.map_commutator, hP]
    have hle := h.1 (P.map (e : W →* W')) hP'
    have hback : (CFSG.Open.GLALayer (⊤ : Subgroup W')).map (e.symm : W' →* W) ≤
        CFSG.Open.GLALayer (⊤ : Subgroup W) := by
      have h := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_map_le (e.symm : W' →* W) hker'
        (⊤ : Subgroup W')
      rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h
    have hcomp : (e.symm : W' →* W).comp (e : W →* W') = MonoidHom.id W := by
      ext x
      simp
    calc P = (P.map (e : W →* W')).map (e.symm : W' →* W) := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ ≤ _ := Subgroup.map_mono hle
      _ ≤ CFSG.Open.GLALayer (⊤ : Subgroup W) := hback
  · intro K hK
    have hK' : CFSG.Open.IsComponentOf (K.map (e : W →* W')) ⊤ :=
      (LocalComponents.equiv_iff e K).mpr hK
    have hq := h.2 (K.map (e : W →* W')) hK'
    exact isChevSimple_of_mulEquiv
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.equivMapOfInjective K (e : W →* W') e.injective)) hq

theorem mulEquiv_iff (e : W ≃* W') : IsChevTwoLayered W ↔ IsChevTwoLayered W' :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end IsChevTwoLayered

theorem isChevTwoLayered_of_isSolvable [Group W] [Finite W] (h : Group.IsSolvable W) :
    IsChevTwoLayered W := by
  haveI : Group.IsSolvable W := h
  constructor
  · intro P hP
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
    haveI : Group.IsSolvable ↥P :=
      Group.isSolvable_of_isSolvable_injective (f := P.subtype) P.subtype_injective
    haveI : Subsingleton ↥P := by
      by_contra hne
      haveI : Nontrivial ↥P := not_subsingleton_iff_nontrivial.mp hne
      exact Group.IsPerfect.not_isSolvable ↥P inferInstance
    rw [Subgroup.eq_bot_of_subsingleton P]
    exact bot_le
  · intro K hK
    haveI : Group.IsPerfect ↥K :=
      Subgroup.isPerfect_iff.mpr
        (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
    haveI : Nontrivial ↥K := Quasisimple.nontrivial hK.2.2
    haveI : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective
    exact (Group.IsPerfect.not_isSolvable ↥K inferInstance).elim

theorem isChevTwoLayered_of_isQuasisimple [Group W] (hW : CFSG.Open.IsQuasisimple W)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (W ⧸ Subgroup.center W)) :
    IsChevTwoLayered W := by
  have htop : CFSG.Open.IsComponentOf (⊤ : Subgroup W) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := W)) hW⟩
  have hlayer : CFSG.Open.GLALayer (⊤ : Subgroup W) = ⊤ :=
    le_antisymm (CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le ⊤)
      (CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer htop)
  constructor
  · intro P _
    rw [hlayer]
    exact le_top
  · intro K hK
    haveI : Group.IsPerfect ↥K :=
      Subgroup.isPerfect_iff.mpr
        (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
    haveI : Nontrivial ↥K := Quasisimple.nontrivial hK.2.2
    rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hW K hK.2.1 with hbot | htop'
    · exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
    · rw [htop']
      exact isChevSimple_of_mulEquiv
        (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
          (Subgroup.topEquiv (G := W))) h

theorem IsChevTwoLayered.of_normal_of_solvable_quotient [Group W] [Finite W] (N : Subgroup W)
    [N.Normal] (hN : IsChevTwoLayered ↥N) (hq : Group.IsSolvable (W ⧸ N)) :
    IsChevTwoLayered W := by
  haveI : Group.IsSolvable (W ⧸ N) := hq
  have hNsub : CFSG.Open.IsSubnormal N ⊤ := by
    have h : (N.subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf ‹N.Normal› ⊤
    exact CFSG.Open.IsSubnormal.step le_top h (CFSG.Open.IsSubnormal.refl ⊤)
  have key : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ N := by
    intro P hP
    have hP' : ⁅P.map (QuotientGroup.mk' N), P.map (QuotientGroup.mk' N)⁆ =
        P.map (QuotientGroup.mk' N) := by
      rw [← Subgroup.map_commutator, hP]
    haveI : Group.IsPerfect ↥(P.map (QuotientGroup.mk' N)) := Subgroup.isPerfect_iff.mpr hP'
    haveI : Group.IsSolvable ↥(P.map (QuotientGroup.mk' N)) :=
      Group.isSolvable_of_isSolvable_injective (f := (P.map (QuotientGroup.mk' N)).subtype)
        (P.map (QuotientGroup.mk' N)).subtype_injective
    haveI : Subsingleton ↥(P.map (QuotientGroup.mk' N)) := by
      by_contra hne
      haveI : Nontrivial ↥(P.map (QuotientGroup.mk' N)) :=
        not_subsingleton_iff_nontrivial.mp hne
      exact Group.IsPerfect.not_isSolvable ↥(P.map (QuotientGroup.mk' N)) inferInstance
    have hbot : P.map (QuotientGroup.mk' N) = ⊥ :=
      Subgroup.eq_bot_of_subsingleton (P.map (QuotientGroup.mk' N))
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  have hmapLayer : (CFSG.Open.GLALayer (⊤ : Subgroup ↥N)).map N.subtype ≤
      CFSG.Open.GLALayer (⊤ : Subgroup W) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : ∀ g : ↥N, N.subtype g = 1 → g ∈ Subgroup.center ↥N := by
      intro g hg
      have hg1 : g = 1 := Subtype.ext hg
      rw [hg1]
      exact Subgroup.one_mem _
    have h1 := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map N.subtype hker hK
    rw [CFSG.LocalAnalysis.GLTheoremA.I142N.map_subtype_top] at h1
    exact CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer
      (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans h1 hNsub)
  constructor
  · intro P hP
    have hPN : P ≤ N := key P hP
    have hPsub : ⁅P.subgroupOf N, P.subgroupOf N⁆ = P.subgroupOf N := by
      apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
      simp only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPN, hP]
    calc P = (P.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hPN).symm
      _ ≤ (CFSG.Open.GLALayer (⊤ : Subgroup ↥N)).map N.subtype :=
          Subgroup.map_mono (hN.1 (P.subgroupOf N) hPsub)
      _ ≤ CFSG.Open.GLALayer (⊤ : Subgroup W) := hmapLayer
  · intro K hK
    have hKN : K ≤ N := key K
      (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
    have hKsub : CFSG.Open.IsComponentOf (K.subgroupOf N) (⊤ : Subgroup ↥N) :=
      LocalComponents.of_overgroup hK hKN
    have hq' := hN.2 (K.subgroupOf N) hKsub
    exact isChevSimple_of_mulEquiv
      (CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv
        (Subgroup.subgroupOfEquivOfLe hKN).symm) hq'

theorem IsChevTwoLayered.quotient [Group W] [Finite W] (h : IsChevTwoLayered W) (T : Subgroup W)
    [T.Normal] (hT : Group.IsSolvable ↥T) : IsChevTwoLayered (W ⧸ T) := by
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
    exact ⟨L.map M.subtype, hLperf, h.1 _ hLperf, by
      have hcomp : ((QuotientGroup.mk' T).comp M.subtype) = Pbar.subtype.comp φ := by
        ext x
        rfl
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hLmap,
        CFSG.LocalAnalysis.GLTheoremA.I142N.map_subtype_top]⟩
  constructor
  · intro Pbar hPbar
    obtain ⟨L, hLperf, hLle, hLmap⟩ := hLift Pbar hPbar
    calc Pbar = L.map (QuotientGroup.mk' T) := hLmap.symm
      _ ≤ (CFSG.Open.GLALayer (⊤ : Subgroup W)).map (QuotientGroup.mk' T) :=
          Subgroup.map_mono hLle
      _ ≤ CFSG.Open.GLALayer (⊤ : Subgroup (W ⧸ T)) := hLayerMap
  · intro Kbar hKbar
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
    haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr
      (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
    have hq := h.2 K hK
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
    exact isChevSimple_of_mulEquiv e.symm hq

theorem IsChevTwoLayered.prod [Group W] [Group W'] [Finite W] [Finite W']
    (h : IsChevTwoLayered W) (h' : IsChevTwoLayered W') : IsChevTwoLayered (W × W') := by
  let N₁ : Subgroup (W × W') := (⊤ : Subgroup W).prod ⊥
  let N₂ : Subgroup (W × W') := (⊥ : Subgroup W).prod ⊤
  haveI hN₁ : N₁.Normal := by
    change ((⊤ : Subgroup W).prod (⊥ : Subgroup W')).Normal
    exact Subgroup.prod_normal ⊤ ⊥
  haveI hN₂ : N₂.Normal := by
    change ((⊥ : Subgroup W).prod (⊤ : Subgroup W')).Normal
    exact Subgroup.prod_normal ⊥ ⊤
  have hinl_top : Subgroup.map (MonoidHom.inl W W') (⊤ : Subgroup W) = N₁ := by
    ext p
    rw [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    · rintro ⟨-, hp2⟩
      exact ⟨p.1, Subgroup.mem_top p.1, Prod.ext rfl (Subgroup.mem_bot.mp hp2).symm⟩
  have hinr_top : Subgroup.map (MonoidHom.inr W W') (⊤ : Subgroup W') = N₂ := by
    ext p
    rw [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
    · rintro ⟨hp1, -⟩
      exact ⟨p.2, Subgroup.mem_top p.2, Prod.ext (Subgroup.mem_bot.mp hp1).symm rfl⟩
  have hN₁sub : CFSG.Open.IsSubnormal N₁ ⊤ := by
    have h' : (N₁.subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf ‹N₁.Normal› ⊤
    exact CFSG.Open.IsSubnormal.step le_top h' (CFSG.Open.IsSubnormal.refl ⊤)
  have hN₂sub : CFSG.Open.IsSubnormal N₂ ⊤ := by
    have h' : (N₂.subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf ‹N₂.Normal› ⊤
    exact CFSG.Open.IsSubnormal.step le_top h' (CFSG.Open.IsSubnormal.refl ⊤)
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h1 : (a, 1) ∈ N₁ :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    have h2 : (1, b) ∈ N₂ :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
    have hmul : (a, 1) * (1, b) ∈ N₁ ⊔ N₂ :=
      (N₁ ⊔ N₂).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    simpa using hmul
  have hE₁ : (CFSG.Open.GLALayer (⊤ : Subgroup W)).map (MonoidHom.inl W W') ≤
      CFSG.Open.GLALayer (⊤ : Subgroup (W × W')) := by
    have hker : ∀ g : W, (MonoidHom.inl W W') g = 1 → g ∈ Subgroup.center W := by
      intro g hg
      have hg1 : g = 1 := by simpa using congrArg Prod.fst hg
      rw [hg1]
      exact Subgroup.one_mem _
    have h1 := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_map_le (MonoidHom.inl W W') hker
      (⊤ : Subgroup W)
    rw [hinl_top] at h1
    exact h1.trans (CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_mono_of_isSubnormal hN₁sub)
  have hE₂ : (CFSG.Open.GLALayer (⊤ : Subgroup W')).map (MonoidHom.inr W W') ≤
      CFSG.Open.GLALayer (⊤ : Subgroup (W × W')) := by
    have hker : ∀ g : W', (MonoidHom.inr W W') g = 1 → g ∈ Subgroup.center W' := by
      intro g hg
      have hg1 : g = 1 := by simpa using congrArg Prod.snd hg
      rw [hg1]
      exact Subgroup.one_mem _
    have h1 := CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_map_le (MonoidHom.inr W W') hker
      (⊤ : Subgroup W')
    rw [hinr_top] at h1
    exact h1.trans (CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_mono_of_isSubnormal hN₂sub)
  constructor
  · intro P hP
    have hP₁ : ⁅P.map (MonoidHom.fst W W'), P.map (MonoidHom.fst W W')⁆ =
        P.map (MonoidHom.fst W W') := by
      rw [← Subgroup.map_commutator, hP]
    have hP₂ : ⁅P.map (MonoidHom.snd W W'), P.map (MonoidHom.snd W W')⁆ =
        P.map (MonoidHom.snd W W') := by
      rw [← Subgroup.map_commutator, hP]
    have h1 := h.1 (P.map (MonoidHom.fst W W')) hP₁
    have h2 := h'.1 (P.map (MonoidHom.snd W W')) hP₂
    intro p hp
    have hp1 : p.1 ∈ CFSG.Open.GLALayer (⊤ : Subgroup W) :=
      h1 (Subgroup.mem_map_of_mem (MonoidHom.fst W W') hp)
    have hp2 : p.2 ∈ CFSG.Open.GLALayer (⊤ : Subgroup W') :=
      h2 (Subgroup.mem_map_of_mem (MonoidHom.snd W W') hp)
    have hmem1 : (MonoidHom.inl W W') p.1 ∈ CFSG.Open.GLALayer (⊤ : Subgroup (W × W')) :=
      hE₁ (Subgroup.mem_map_of_mem _ hp1)
    have hmem2 : (MonoidHom.inr W W') p.2 ∈ CFSG.Open.GLALayer (⊤ : Subgroup (W × W')) :=
      hE₂ (Subgroup.mem_map_of_mem _ hp2)
    have heq : p = (MonoidHom.inl W W') p.1 * (MonoidHom.inr W W') p.2 := by
      ext <;> simp
    rw [heq]
    exact (CFSG.Open.GLALayer (⊤ : Subgroup (W × W'))).mul_mem hmem1 hmem2
  · intro K hK
    have hcontra : ¬ K ≤ N₁ → ¬ K ≤ N₂ → CFSG.Open.IsQuasisimple ↥K → False := by
      intro h1 h2 _
      have hc1 : ⁅K, N₁⁆ = ⊥ :=
        (LocalComponents.normal_contains_or_commutes K N₁ hK).resolve_left h1
      have hc2 : ⁅K, N₂⁆ = ⊥ :=
        (LocalComponents.normal_contains_or_commutes K N₂ hK).resolve_left h2
      have hcen1 : K ≤ Subgroup.centralizer (N₁ : Set (W × W')) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1
      have hcen2 : K ≤ Subgroup.centralizer (N₂ : Set (W × W')) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2
      have hjoin : K ≤ Subgroup.centralizer (Set.univ : Set (W × W')) := by
        have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hcen1 hcen2
        rw [hsup] at h
        simpa only [Subgroup.coe_top] using h
      have habel : ⁅K, K⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hjoin.trans (Subgroup.centralizer_le (Set.subset_univ (K : Set (W × W')))))
      have hperf : ⁅K, K⁆ = K :=
        CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1
      have hbot : K = ⊥ := by rw [← hperf, habel]
      exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot K).mp (Quasisimple.nontrivial hK.2.2))
    by_cases hKN₁ : K ≤ N₁
    ·
      let f : ↥K →* ↥(K.map (MonoidHom.fst W W')) :=
        { toFun := fun x => ⟨(MonoidHom.fst W W') x.1, Subgroup.mem_map_of_mem _ x.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ a.1 b.1) }
      have hfsurj : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
      have hfker : ∀ x : ↥K, f x = 1 → x ∈ Subgroup.center ↥K := by
        intro x hx
        have hx1 : x.1.1 = 1 := congrArg Subtype.val hx
        have hx2 : x.1.2 = 1 :=
          Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hKN₁ x.2)).2
        have hxeq : x.1 = 1 := Prod.ext hx1 hx2
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (by simp only [Subgroup.coe_mul, hxeq, mul_one, one_mul])
      have hfker' : f.ker ≤ Subgroup.center ↥K := by
        intro x hx
        exact hfker x (MonoidHom.mem_ker.mp hx)
      haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr
        (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
      have hKfst : CFSG.Open.IsComponentOf (K.map (MonoidHom.fst W W')) ⊤ := by
        refine ⟨le_top, ?_, CFSG.LocalAnalysis.GLTheoremA.I142N.isQuasisimple_of_surjective f
          hfsurj hfker hK.2.2⟩
        have hsub := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_map
          (MonoidHom.fst W W') hK.2.1
        rwa [Subgroup.map_top_of_surjective _ (fun x => ⟨(x, 1), rfl⟩)] at hsub
      have hq := h.2 (K.map (MonoidHom.fst W W')) hKfst
      obtain ⟨e⟩ := nonempty_quotCenter_equiv_of_surjective f hfsurj hfker'
      exact isChevSimple_of_mulEquiv e hq
    · by_cases hKN₂ : K ≤ N₂
      · let f : ↥K →* ↥(K.map (MonoidHom.snd W W')) :=
          { toFun := fun x => ⟨(MonoidHom.snd W W') x.1, Subgroup.mem_map_of_mem _ x.2⟩
            map_one' := Subtype.ext (map_one _)
            map_mul' := fun a b => Subtype.ext (map_mul _ a.1 b.1) }
        have hfsurj : Function.Surjective f := by
          rintro ⟨y, hy⟩
          obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
          exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
        have hfker : ∀ x : ↥K, f x = 1 → x ∈ Subgroup.center ↥K := by
          intro x hx
          have hx2 : x.1.2 = 1 := congrArg Subtype.val hx
          have hx1 : x.1.1 = 1 :=
            Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hKN₂ x.2)).1
          have hxeq : x.1 = 1 := Prod.ext hx1 hx2
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (by simp only [Subgroup.coe_mul, hxeq, mul_one, one_mul])
        have hfker' : f.ker ≤ Subgroup.center ↥K := by
          intro x hx
          exact hfker x (MonoidHom.mem_ker.mp hx)
        haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr
          (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hK.2.2.1)
        have hKsnd : CFSG.Open.IsComponentOf (K.map (MonoidHom.snd W W')) ⊤ := by
          refine ⟨le_top, ?_, CFSG.LocalAnalysis.GLTheoremA.I142N.isQuasisimple_of_surjective f
            hfsurj hfker hK.2.2⟩
          have hsub := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_map
            (MonoidHom.snd W W') hK.2.1
          rwa [Subgroup.map_top_of_surjective _ (fun x => ⟨(1, x), rfl⟩)] at hsub
        have hq := h'.2 (K.map (MonoidHom.snd W W')) hKsnd
        obtain ⟨e⟩ := nonempty_quotCenter_equiv_of_surjective f hfsurj hfker'
        exact isChevSimple_of_mulEquiv e hq
      · exact (hcontra hKN₁ hKN₂ hK.2.2).elim

end CFSG.LieType.ChevTwo
