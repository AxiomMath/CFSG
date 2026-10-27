module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeSetup
public import CFSG.ClassicalInvolution.RouteD.TypeCLayers

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv suppGroup coords pairPlanes
  pairPlaneSubgroup form IsAdaptedShortIn)
open CFSG.ClassicalInvolution.WeakCT (diagTorus2)
open scoped MatrixGroups commutatorElement

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

section Basic

variable (Fr : Frame p f m Ω K z)

theorem zf_mem_MfW (S : CSetupW p f m Ω K z) {i j : Fin (m + 1)} (k : Fin (m + 1))
    (hk : k = i ∨ k = j) : Fr.zf k ∈ Mf Fr i j :=
  Kf_le_Mf Fr k hk (Frame.zf_memW S k)


theorem Mf_perfectW (S : CSetupW p f m Ω K z) (i j : Fin (m + 1)) :
    ⁅Mf Fr i j, Mf Fr i j⁆ = Mf Fr i j := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) (iSup_le fun L => ?_)
  · rw [commutatorElement_def]
    exact (Mf Fr i j).mul_mem ((Mf Fr i j).mul_mem ((Mf Fr i j).mul_mem h₁ h₂)
      ((Mf Fr i j).inv_mem h₁)) ((Mf Fr i j).inv_mem h₂)
  obtain ⟨z', hz'⟩ := S.inClass.classical L L.2.1
  calc (L : Subgroup G) = ⁅(L : Subgroup G), (L : Subgroup G)⁆ :=
        (commutator_eq_of_isClassicalMember hz').symm
    _ ≤ ⁅Mf Fr i j, Mf Fr i j⁆ := Subgroup.commutator_mono (le_Mf Fr L.2) (le_Mf Fr L.2)

end Basic

section Local

variable [Finite G] {Fr : Frame p f m Ω K z} {l : Fin (m + 1)}

theorem LocalFrame.orth_of_commutesW (S : CSetupW p f m Ω K z) (LF : LocalFrame Fr l)
    {P : Submodule (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)}
    (hP : IsHyperbolicPlane P) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {Fr.zf l})
    (hLP : locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ) {k : Fin m}
    (hc : Commutes L (Fr.Kf (l.succAbove k))) : ∀ u ∈ P, ∀ v ∈ stdPlane (GaloisField p f) m k,
      form u v = 0 := by
  have hKk : Fr.Kf (l.succAbove k) ∈ centralizingMembers Ω {Fr.zf l} := Fr.mem_centW S _ l
  have himg := LF.locImg_Kf k
  refine orth_of_commute_map S.two_ne_zero S.hex LF.d.ψ LF.d.ker_le hP
    (isHyperbolicPlane_stdPlane k) ?_ ?_
  · intro h
    have := locImg_injOn S.inClass (Fr.p1W S l) hL hKk (by rw [hLP, himg, h])
    rw [this] at hc
    exact not_commutes_self_of_isClassicalMember (Fr.clsW S _) hc
  · rw [← hLP, ← himg]
    exact commutes_locImg_of_commutes hc

omit [Finite G] in
theorem LocalFrame.mem_cent_of_memW (S : CSetupW p f m Ω K z) {a b : Fin m} {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) :
    L ∈ centralizingMembers Ω {Fr.zf l} :=
  ⟨hL.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
    (hL.2 l (Fin.succAbove_ne l a).symm (Fin.succAbove_ne l b).symm y hy _ (Frame.zf_memW S l))⟩

omit [Finite G] in
theorem LocalFrame.ne_Kf_of_memW (S : CSetupW p f m Ω K z) {a b : Fin m} {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) : L ≠ Fr.Kf l := by
  rintro rfl
  exact not_commutes_self_of_isClassicalMember (Fr.clsW S l)
    (hL.2 l (Fin.succAbove_ne l a).symm (Fin.succAbove_ne l b).symm)

theorem LocalFrame.exists_plane_of_memW (S : CSetupW p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) :
    ∃ P ∈ pairPlanes (GaloisField p f) m a b,
      locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ := by
  have hcent := LocalFrame.mem_cent_of_memW S hL
  obtain ⟨P, hP, hLP⟩ := typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem l)
    (Fr.clsW S l) (Fr.p1W S l) LF.d hcent (LocalFrame.ne_Kf_of_memW S hL)
  refine ⟨P, ⟨hP, fun u hu => ?_⟩, hLP⟩
  refine mem_sup_stdPlane_of_orth hab (fun c hca hcb v hv => ?_)
  exact LF.orth_of_commutesW S hP hcent hLP
    (hL.2 _ (fun h => hca (Fin.succAbove_right_injective h))
      (fun h => hcb (Fin.succAbove_right_injective h))) u hu v hv

theorem LocalFrame.exists_mem_of_planeW (S : CSetupW p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b)
    {P : Submodule (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)}
    (hP : P ∈ pairPlanes (GaloisField p f) m a b) :
    ∃ L ∈ memberSet Fr (l.succAbove a) (l.succAbove b),
      locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ := by
  obtain ⟨L, hLc, hLK, hLimg⟩ := typeC_exists_member_of_plane S.two_le S.five S.inClass
    (Fr.mem l) (Fr.clsW S l) (Fr.p1W S l) LF.d hP.1
  refine ⟨L, ⟨hLc.1, fun k hki hkj => ?_⟩, hLimg⟩
  by_cases hkl : k = l
  · subst hkl
    exact (typeC_commutes_K_of_ne S.two_le S.five S.inClass S.exact (Fr.mem k) (Fr.clsW S k)
      (Fr.p1W S k) LF.d hLc hLK).symm
  · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hkl
    have hca : c ≠ a := fun h => hki (by rw [h])
    have hcb : c ≠ b := fun h => hkj (by rw [h])
    refine commutes_of_commutes_locImg S.inClass (Fr.p1W S l) hLc (Fr.mem_centW S _ l) ?_
    rw [hLimg, LF.locImg_Kf c]
    exact commutes_map_planeGroup_of_orth S.two_le LF.d.ψ hP.1 (isHyperbolicPlane_stdPlane c)
      (fun x hx y hy => orth_stdPlane_of_mem_sup hab hca hcb (hP.2 hx) y hy)

omit [Finite G] in
theorem LocalFrame.Mf_le_locLayerW (S : CSetupW p f m Ω K z) (a b : Fin m) :
    Mf Fr (l.succAbove a) (l.succAbove b) ≤ locLayer Ω (Fr.zf l) :=
  iSup_le fun L => le_centralizingLayer (LocalFrame.mem_cent_of_memW S L.2)

theorem LocalFrame.locImg_MfW (S : CSetupW p f m Ω K z) (LF : LocalFrame Fr l) {a b : Fin m}
    (hab : a ≠ b) :
    locImg Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)) =
      (suppGroup (coords a ∪ coords b)).map LF.d.ψ := by
  have hle : ∀ L : memberSet Fr (l.succAbove a) (l.succAbove b),
      (L : Subgroup G) ≤ locLayer Ω (Fr.zf l) :=
    fun L => le_centralizingLayer (LocalFrame.mem_cent_of_memW S L.2)
  rw [Mf, locImg_iSup _ hle]
  apply le_antisymm
  · refine iSup_le fun L => ?_
    obtain ⟨P, hP, hLP⟩ := LF.exists_plane_of_memW S hab L.2
    rw [hLP]
    exact Subgroup.map_mono (Models.SymplecticPairs.planeGroup_le_suppGroup_pair hab hP.2)
  · rw [← Models.SymplecticPairs.pairPlaneSubgroup_eq S.four_le hab,
      Models.SymplecticPairs.pairPlaneSubgroup, Subgroup.map_iSup]
    refine iSup_le fun P => ?_
    obtain ⟨L, hL, hLP⟩ := LF.exists_mem_of_planeW S hab P.2
    rw [← hLP]
    exact le_iSup (fun L : memberSet Fr (l.succAbove a) (l.succAbove b) =>
      locImg Ω (Fr.zf l) (L : Subgroup G)) ⟨L, hL⟩

omit [Finite G] in
theorem LocalFrame.Mf_subtype_memW (S : CSetupW p f m Ω K z) (a b : Fin m)
    (y : ↥(Mf Fr (l.succAbove a) (l.succAbove b))) :
    (Mf Fr (l.succAbove a) (l.succAbove b)).subtype y ∈ locLayer Ω (Fr.zf l) :=
  LocalFrame.Mf_le_locLayerW S a b y.2

structure LocalFrameI (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) extends LocalFrame Fr l where
  inj : Function.Injective d.ψ

theorem LocalFrameI.injective_locHom_Mf (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    Function.Injective (locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_memW S a b)) := by
  set M := Mf Fr (l.succAbove a) (l.succAbove b) with hM
  set π := locHom Ω (Fr.zf l) M.subtype (LocalFrame.Mf_subtype_memW S a b) with hπ
  have hperf : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr (Mf_perfectW Fr S _ _)
  have hmemY : ∀ y : ↥M, M.subtype y ∈ locLayer Ω (Fr.zf l) :=
    LocalFrame.Mf_subtype_memW S a b
  have hmem : ∀ y : ↥π.ker, (⟨((y : ↥M) : G), hmemY y⟩ :
      ↥(locLayer Ω (Fr.zf l))) ∈ classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) :=
    fun y => (QuotientGroup.eq_one_iff _).mp y.2
  have hcen : π.ker ≤ Subgroup.center ↥M := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro w
    have h2 := Fr.p1W S l (hmem ⟨y, hy⟩)
    have := Subgroup.mem_center_iff.mp h2 ⟨(w : G), hmemY w⟩
    have h3 := congrArg (Subtype.val : ↥(locLayer Ω (Fr.zf l)) → G) this
    exact Subtype.ext h3
  have hodd : Odd (Nat.card π.ker) := by
    refine (CFSG.ComponentClassification.OddCore.odd_card
      ↥(locLayer Ω (Fr.zf l))).of_dvd_nat ?_
    let g : π.ker →* classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) :=
      { toFun := fun y => ⟨⟨((y : ↥M) : G), hmemY y⟩, hmem y⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective g fun y₁ y₂ h => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) => (w.1 : G)) h
  have hinj : Function.Injective (LF.d.ψ.comp (Models.SymplecticPairs.pairEmbed
      (GaloisField p f) hab)) :=
    LF.inj.comp (Models.SymplecticPairs.pairEmbed_injective hab)
  have hrange : (LF.d.ψ.comp (Models.SymplecticPairs.pairEmbed (GaloisField p f) hab)).range =
      π.range := by
    rw [MonoidHom.range_comp, Models.SymplecticPairs.range_pairEmbed, hπ, range_locHom,
      Subgroup.range_subtype, LF.locImg_MfW S hab]
  let e₀ : StatedSp 2 (GaloisField p f) ≃* ↥π.range :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hNC := CFSG.ClassicalInvolution.ModelFacts.OddCover.NoCover.of_mulEquiv e₀
    (CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sp4 (K := GaloisField p f)
      (p := p) (f := f) S.odd S.card_eq S.five)
  have hker := @hNC ↥M _ _ hperf π.rangeRestrict π.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hcen)
    (by rw [MonoidHom.ker_rangeRestrict]; exact hodd)
  rw [MonoidHom.ker_rangeRestrict] at hker
  exact (MonoidHom.ker_eq_bot_iff _).mp hker

theorem LocalFrameI.injOn_locImg_Mf (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l) {a b : Fin m}
    (hab : a ≠ b) {A B : Subgroup G} (hA : A ≤ Mf Fr (l.succAbove a) (l.succAbove b))
    (hB : B ≤ Mf Fr (l.succAbove a) (l.succAbove b))
    (h : locImg Ω (Fr.zf l) A = locImg Ω (Fr.zf l) B) : A = B := by
  set M := Mf Fr (l.succAbove a) (l.succAbove b) with hM
  have hmemY : ∀ y : ↥M, M.subtype y ∈ locLayer Ω (Fr.zf l) :=
    LocalFrame.Mf_subtype_memW S a b
  have hinj := LF.injective_locHom_Mf S hab
  have key : ∀ C : Subgroup G, C ≤ M →
      (C.subgroupOf M).map (locHom Ω (Fr.zf l) M.subtype hmemY) = locImg Ω (Fr.zf l) C := by
    intro C hC
    rw [map_locHom, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC]
  have h1 : A.subgroupOf M = B.subgroupOf M :=
    Subgroup.map_injective hinj (by rw [key A hA, key B hB, h])
  have h2 := (Subgroup.subgroupOf_inj).mp h1
  rwa [inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h2

omit [Finite G] in
theorem LocalFrameI.injective_comp_supp (LF : LocalFrameI Fr l) (a b : Fin m) :
    Function.Injective (LF.d.ψ.comp (suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f))).subtype) :=
  LF.inj.comp (Subgroup.subtype_injective _)

noncomputable def LocalFrameI.layerEquiv (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f))) ≃*
      ↥(Mf Fr (l.succAbove a) (l.succAbove b)) :=
  (MonoidHom.ofInjective (LF.injective_comp_supp a b)).trans
    ((MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, range_locHom, Subgroup.range_subtype,
          LF.locImg_MfW S hab])).trans
      (MonoidHom.ofInjective (LF.injective_locHom_Mf S hab)).symm)

theorem LocalFrameI.locHom_layerEquiv (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b)
    (s : ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f)))) :
    locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_memW S a b) (LF.layerEquiv S hab s) = LF.d.ψ s := by
  unfold LocalFrameI.layerEquiv
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

@[expose] noncomputable def LocalFrameI.layerHom (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f))) →* G :=
  (Mf Fr (l.succAbove a) (l.succAbove b)).subtype.comp (LF.layerEquiv S hab).toMonoidHom

theorem LocalFrameI.layerHom_injective (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) : Function.Injective (LF.layerHom S hab) :=
  (Subgroup.subtype_injective _).comp (LF.layerEquiv S hab).injective

theorem LocalFrameI.layerHom_range (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    (LF.layerHom S hab).range = Mf Fr (l.succAbove a) (l.succAbove b) := by
  unfold LocalFrameI.layerHom
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (LF.layerEquiv S hab).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem LocalFrameI.map_layerHom_le (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) (A : Subgroup ↥(suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))) :
    A.map (LF.layerHom S hab) ≤ Mf Fr (l.succAbove a) (l.succAbove b) := by
  rw [← LF.layerHom_range S hab]
  exact Subgroup.map_le_range _ _

theorem LocalFrameI.locImg_map_layerHom (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) (A : Subgroup ↥(suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))) :
    locImg Ω (Fr.zf l) (A.map (LF.layerHom S hab)) =
      (A.map (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f))).subtype).map LF.d.ψ := by
  unfold LocalFrameI.layerHom
  rw [← Subgroup.map_map, ← map_locHom, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  exact LF.locHom_layerEquiv S hab s

theorem LocalFrame.mk_zfW (S : CSetupW p f m Ω K z) (LF : LocalFrame Fr l) (c : Fin m) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)))
      ⟨Fr.zf (l.succAbove c), Fr.Kf_le_locLayerW S _ l (Frame.zf_memW S _)⟩ =
        LF.d.ψ (longInv (GaloisField p f) m c) := by
  have hle : ∀ a, Fr.ι (l.succAbove c) a ∈ locLayer Ω (Fr.zf l) := fun a =>
    Fr.Kf_le_locLayerW S _ l (by rw [← Fr.range_ι]; exact ⟨a, rfl⟩)
  have hβ : Function.Injective (locHom Ω (Fr.zf l) (Fr.ι (l.succAbove c)) hle) :=
    locHom_injective S.exact (Fr.mem_centW S _ l) (Fr.ι_inj _) (by rw [Fr.range_ι]) hle
  have hr : (locHom Ω (Fr.zf l) (Fr.ι (l.succAbove c)) hle).range =
      (longBlock (GaloisField p f) m c).range.map LF.d.ψ := by
    rw [range_locHom, Fr.range_ι, LF.adapted c]
  have h1 := map_neg_one_eq_of_range_eq (by have := S.two_le; omega) S.two_ne_zero LF.d.ψ
    LF.d.ker_le c _ hβ hr
  rw [locHom_apply] at h1
  have e : (⟨Fr.ι (l.succAbove c) (-1), hle (-1)⟩ : ↥(locLayer Ω (Fr.zf l))) =
      ⟨Fr.zf (l.succAbove c), Fr.Kf_le_locLayerW S _ l (Frame.zf_memW S _)⟩ :=
    Subtype.ext (Fr.ι_neg_oneW S _)
  rw [e] at h1
  exact h1

theorem LocalFrameI.map_layerEquiv_planeTorus (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) (c : Fin m) (hc : c = a ∨ c = b) :
    ((planeTorus (GaloisField p f) m c).subgroupOf (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerEquiv S hab).toMonoidHom =
      (Fr.Tf (l.succAbove c)).subgroupOf (Mf Fr (l.succAbove a) (l.succAbove b)) := by
  have hinj := LF.injective_locHom_Mf S hab
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_map]
  have h1 : (locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_memW S a b)).comp (LF.layerEquiv S hab).toMonoidHom =
      LF.d.ψ.comp (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f))).subtype := by
    ext s
    exact LF.locHom_layerEquiv S hab s
  rw [h1, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (Models.SymplecticPairs.planeTorus_le hc), map_locHom,
    Subgroup.subgroupOf_map_subtype]
  have hTf : Fr.Tf (l.succAbove c) ≤ Mf Fr (l.succAbove a) (l.succAbove b) :=
    Tf_le_Mf Fr _ (by rcases hc with rfl | rfl <;> simp)
  rw [inf_eq_left.mpr hTf]
  exact LF.torus c

theorem LocalFrameI.layerEquiv_longInv (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    LF.layerEquiv S hab ⟨longInv (GaloisField p f) m a,
        Models.SymplecticPairs.longInv_mem_suppGroup (Or.inl rfl)⟩ =
      ⟨Fr.zf (l.succAbove a), zf_mem_MfW Fr S _ (Or.inl rfl)⟩ := by
  apply LF.injective_locHom_Mf S hab
  rw [LF.locHom_layerEquiv S hab]
  exact (LF.mk_zfW S a).symm

theorem LocalFrameI.isAdaptedShortIn_iff (S : CSetupW p f m Ω K z) (LF : LocalFrameI Fr l)
    {a b : Fin m} (hab : a ≠ b) {T : Subgroup G}
    (hT : T ≤ Mf Fr (l.succAbove a) (l.succAbove b)) :
    IsAdaptedShortIn (Mf Fr (l.succAbove a) (l.succAbove b)) (Fr.Tf (l.succAbove a))
      (Fr.Tf (l.succAbove b)) (Fr.zf (l.succAbove a)) T ↔
      ∃ s : Subgroup (StatedSp m (GaloisField p f)),
        (s = (Models.SymplecticPairs.shortBlock (GaloisField p f) hab).range ∨
          s = Models.SymplecticPairs.shortGroupNeg (GaloisField p f) hab) ∧
        T = (s.subgroupOf (suppGroup (coords a ∪ coords b) :
          Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerHom S hab) := by
  set M := Mf Fr (l.succAbove a) (l.succAbove b) with hM
  have hTa : Fr.Tf (l.succAbove a) ≤ M := Tf_le_Mf Fr _ (Or.inl rfl)
  have hTb : Fr.Tf (l.succAbove b) ≤ M := Tf_le_Mf Fr _ (Or.inr rfl)
  rw [Models.SymplecticPairs.isAdaptedShortIn_iff_isAdaptedShort hTa hTb
    (zf_mem_MfW Fr S _ (Or.inl rfl)) hT]
  rw [Models.SymplecticPairs.isAdaptedShort_iff_of_mulEquiv hab S.two_ne_zero S.hex
    (LF.layerEquiv S hab) (LF.map_layerEquiv_planeTorus S hab a (Or.inl rfl))
    (LF.map_layerEquiv_planeTorus S hab b (Or.inr rfl)) (LF.layerEquiv_longInv S hab)]
  have hconv : ∀ X : Subgroup ↥M, T.subgroupOf M = X ↔ T = X.map M.subtype := by
    intro X
    constructor
    · rintro rfl
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT]
    · rintro rfl
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hT
  have hmap' : ∀ X : Subgroup ↥(suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f))),
      (X.map (LF.layerEquiv S hab).toMonoidHom).map M.subtype = X.map (LF.layerHom S hab) := by
    intro X
    rw [Subgroup.map_map]
    rfl
  constructor
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, by rw [← hmap']; exact (hconv _).mp h⟩
    · exact ⟨_, Or.inr rfl, by rw [← hmap']; exact (hconv _).mp h⟩
  · rintro ⟨s', hs, hTs⟩
    rcases hs with rfl | rfl
    · left
      rw [hconv, hmap']
      exact hTs
    · right
      rw [hconv, hmap']
      exact hTs

end Local

section Injective

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem typeC_not_mem_of_ne {m : ℕ} (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) : z ∉ L := by
  intro hzL
  obtain ⟨P, hP, hLP⟩ := typeC_exists_plane_of_ne hm h5 hΩ hex hK hz hP1 d hL hLK
  let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hL hzL⟩
  have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
      locImg Ω z L := ⟨zY, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  rw [hLP] at hzK
  obtain ⟨r, hrP, hr⟩ := hzK
  have hcentral : ∀ w : locQuot Ω z,
      w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} w'.2)
  have hrc : r ∈ Subgroup.center (StatedSp m (GaloisField p f)) := by
    refine Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center
      (Models.SymplecticPairs.isPerfect_statedSp_of_four_le (four_le_natCard_galoisField h5))
      fun s => d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hr]
    rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
  have hr1 : r = 1 := eq_one_of_mem_planeGroup_of_mem_center hm hP hrP hrc
  rw [hr1, map_one] at hr
  have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
    (QuotientGroup.eq_one_iff _).mp hr.symm
  have h2 : orderOf zY = 2 := by
    rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
  have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
  have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact h2
  rw [h4] at h3
  have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z)))
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective) in
theorem eq_longInv_mul_of_mem_center_ne_one {F : Type} [Field F] {x : StatedSp 2 F}
    (hx : x ∈ Subgroup.center (StatedSp 2 F)) (hx1 : x ≠ 1) :
    x = longInv F 2 0 * longInv F 2 1 := by
  obtain ⟨c, hc⟩ := Models.SymplecticPairs.exists_scalar_of_mem_center hx
  have hmat : mat 2 F x = Matrix.diagonal (fun _ => (c : F)) := by
    change ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hxx := Models.SymplecticPairs.mul_self_eq_one_of_mem_center (by omega : 1 ≤ 2) hx
  have hcc : (c : F) * (c : F) = 1 := by
    have := congrFun (congrFun (congrArg (mat 2 F) hxx) (Sum.inl 0)) (Sum.inl 0)
    rw [map_mul, hmat, Matrix.diagonal_mul_diagonal, map_one] at this
    simpa using this
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · refine absurd (mat_injective ?_) hx1
    rw [hmat, h1, map_one]
    ext a b
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  · have hpt : ∀ a : Fin 2 ⊕ Fin 2, (if a ∈ coords (0 : Fin 2) then (-1 : F) else 1) *
        (if a ∈ coords (1 : Fin 2) then (-1 : F) else 1) = -1 := by
      intro a
      rcases a with a | a <;> fin_cases a <;> simp [Models.SymplecticPairs.mem_coords]
    apply mat_injective
    rw [hmat, map_mul, Models.SymplecticPairs.mat_longInv, Models.SymplecticPairs.mat_longInv,
      Matrix.diagonal_mul_diagonal, h1]
    congr 1
    funext a
    exact (hpt a).symm

theorem LocalFrame.injective_psiW (S : CSetupW p f 2 Ω K z) {Fr : Frame p f 2 Ω K z}
    {l : Fin 3} (LF : LocalFrame Fr l) : Function.Injective LF.d.ψ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hxc : x ∈ Subgroup.center (StatedSp 2 (GaloisField p f)) :=
    LF.d.ker_le (MonoidHom.mem_ker.mpr hx)
  have hxe := eq_longInv_mul_of_mem_center_ne_one hxc hx1
  rw [hxe, map_mul] at hx
  have hne : l.succAbove 0 ≠ l.succAbove 1 := fun h =>
    absurd (Fin.succAbove_right_injective h) (by decide)
  have hle : ∀ c : Fin 2, Fr.zf (l.succAbove c) ∈ locLayer Ω (Fr.zf l) := fun c =>
    Fr.Kf_le_locLayerW S _ l (Frame.zf_memW S _)
  set zi : ↥(locLayer Ω (Fr.zf l)) := ⟨Fr.zf (l.succAbove 0), hle 0⟩ with hzi
  set zj : ↥(locLayer Ω (Fr.zf l)) := ⟨Fr.zf (l.succAbove 1), hle 1⟩ with hzj
  have hmul : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)))
      (zi * zj) = 1 := by
    rw [map_mul, LF.mk_zfW S 0, LF.mk_zfW S 1]
    exact hx
  have hO : zi * zj ∈ classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) :=
    (QuotientGroup.eq_one_iff _).mp hmul
  have hsq : ∀ c : Fin 2, Fr.zf (l.succAbove c) * Fr.zf (l.succAbove c) = 1 := fun c => by
    have h2 := (Fr.clsW S (l.succAbove c)).orderOf_eq_two
    rw [← pow_two]
    have := pow_orderOf_eq_one (Fr.zf (l.succAbove c))
    rwa [h2] at this
  have hcomm := Fr.zf_commW S (l.succAbove 0) (l.succAbove 1)
  have hsq2 : (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) *
      (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) = 1 := by
    calc (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) *
          (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) =
        Fr.zf (l.succAbove 0) * (Fr.zf (l.succAbove 1) * Fr.zf (l.succAbove 0)) *
          Fr.zf (l.succAbove 1) := by group
      _ = Fr.zf (l.succAbove 0) * (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) *
          Fr.zf (l.succAbove 1) := by rw [← hcomm]
      _ = (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 0)) *
          (Fr.zf (l.succAbove 1) * Fr.zf (l.succAbove 1)) := by group
      _ = 1 := by rw [hsq 0, hsq 1, one_mul]
  have hzz : zi * zj = 1 := by
    set g : classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) := ⟨zi * zj, hO⟩ with hg
    have h1 : orderOf g ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply Subtype.ext
      apply Subtype.ext
      rw [pow_two]
      exact hsq2
    have h2 := orderOf_dvd_natCard g
    have hodd := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω (Fr.zf l)))
    have h3 : orderOf g = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
    have h4 : g = 1 := orderOf_eq_one_iff.mp h3
    exact congrArg Subtype.val h4
  have hzG : Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1) = 1 := congrArg Subtype.val hzz
  have hzeq : Fr.zf (l.succAbove 0) = Fr.zf (l.succAbove 1) := by
    rw [eq_inv_of_mul_eq_one_left hzG, inv_eq_of_mul_eq_one_right (hsq 1)]
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem (l.succAbove 0))
    (Fr.clsW S (l.succAbove 0)) (S.shape.conj S.conjInvariant (Fr.gf (l.succAbove 0)))
  exact typeC_not_mem_of_ne S.two_le S.five S.inClass S.exact (Fr.mem (l.succAbove 0))
    (Fr.clsW S (l.succAbove 0)) (Fr.p1W S (l.succAbove 0)) d
    (Fr.mem_centW S (l.succAbove 1) (l.succAbove 0)) (Fr.ne_of_neW S hne.symm)
    (by rw [hzeq]; exact Frame.zf_memW S _)

theorem exists_localFrameIW (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) (l : Fin 3) :
    Nonempty (LocalFrameI Fr l) := by
  obtain ⟨LF⟩ := exists_localFrameW S Fr l
  exact ⟨{ toLocalFrame := LF, inj := LF.injective_psiW S }⟩

end Injective

end CFSG.ClassicalInvolution.RouteD
