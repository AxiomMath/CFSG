module

public import CFSG.ClassicalInvolution.RouteD.TypeCFrameData
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard
public import CFSG.ClassicalInvolution.RouteD.TypeCModelAux

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

@[expose] def memberSet (Fr : Frame p f m Ω K z) (i j : Fin (m + 1)) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∀ k, k ≠ i → k ≠ j → Commutes L (Fr.Kf k)}

@[expose] def Mf (Fr : Frame p f m Ω K z) (i j : Fin (m + 1)) : Subgroup G :=
  ⨆ L : memberSet Fr i j, (L : Subgroup G)

section Basic

variable (Fr : Frame p f m Ω K z)

theorem le_Mf {i j : Fin (m + 1)} {L : Subgroup G} (hL : L ∈ memberSet Fr i j) :
    L ≤ Mf Fr i j :=
  le_iSup (fun L : memberSet Fr i j => (L : Subgroup G)) ⟨L, hL⟩

theorem Kf_mem_memberSet {i j : Fin (m + 1)} (k : Fin (m + 1)) (hk : k = i ∨ k = j) :
    Fr.Kf k ∈ memberSet Fr i j := by
  refine ⟨Fr.mem k, fun k' hk'i hk'j => ?_⟩
  have : k ≠ k' := by
    rintro rfl
    rcases hk with rfl | rfl
    · exact hk'i rfl
    · exact hk'j rfl
  exact Fr.commute k k' this

theorem Kf_le_Mf {i j : Fin (m + 1)} (k : Fin (m + 1)) (hk : k = i ∨ k = j) :
    Fr.Kf k ≤ Mf Fr i j :=
  le_Mf Fr (Kf_mem_memberSet Fr k hk)

theorem Tf_le_Mf {i j : Fin (m + 1)} (k : Fin (m + 1)) (hk : k = i ∨ k = j) :
    Fr.Tf k ≤ Mf Fr i j :=
  (Frame.Tf_le k).trans (Kf_le_Mf Fr k hk)

theorem zf_mem_Mf (S : CSetup p f m Ω K z) {i j : Fin (m + 1)} (k : Fin (m + 1))
    (hk : k = i ∨ k = j) : Fr.zf k ∈ Mf Fr i j :=
  Kf_le_Mf Fr k hk (Frame.zf_mem S k)

theorem Mf_perfect (S : CSetup p f m Ω K z) (i j : Fin (m + 1)) :
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

omit [Finite G] in
theorem Frame.p1 (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) :
    LocalOddCentral Ω {Fr.zf l} :=
  S.p1cl _ (Fr.mem l) _ (Fr.cls S l)

omit [Finite G] in
theorem LocalFrame.locImg_Kf (LF : LocalFrame Fr l) (k : Fin m) :
    locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) =
      (planeGroup (stdPlane (GaloisField p f) m k)).map LF.d.ψ := by
  rw [← LF.adapted k, Models.SymplecticPairs.planeGroup_stdPlane]
  rfl

theorem LocalFrame.orth_of_commutes (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {P : Submodule (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)}
    (hP : IsHyperbolicPlane P) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {Fr.zf l})
    (hLP : locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ) {k : Fin m}
    (hc : Commutes L (Fr.Kf (l.succAbove k))) : ∀ u ∈ P, ∀ v ∈ stdPlane (GaloisField p f) m k,
      form u v = 0 := by
  have hKk : Fr.Kf (l.succAbove k) ∈ centralizingMembers Ω {Fr.zf l} := Fr.mem_cent S _ l
  have himg := LF.locImg_Kf k
  refine orth_of_commute_map S.two_ne_zero S.hex LF.d.ψ LF.d.ker_le hP
    (isHyperbolicPlane_stdPlane k) ?_ ?_
  · intro h
    have := locImg_injOn S.inClass (Fr.p1 S l) hL hKk (by rw [hLP, himg, h])
    rw [this] at hc
    exact not_commutes_self_of_isClassicalMember (Fr.cls S _) hc
  · rw [← hLP, ← himg]
    exact commutes_locImg_of_commutes hc

omit [Finite G] in
theorem LocalFrame.mem_cent_of_mem (S : CSetup p f m Ω K z) {a b : Fin m} {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) :
    L ∈ centralizingMembers Ω {Fr.zf l} :=
  ⟨hL.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
    (hL.2 l (Fin.succAbove_ne l a).symm (Fin.succAbove_ne l b).symm y hy _ (Frame.zf_mem S l))⟩

omit [Finite G] in
theorem LocalFrame.ne_Kf_of_mem (S : CSetup p f m Ω K z) {a b : Fin m} {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) : L ≠ Fr.Kf l := by
  rintro rfl
  exact not_commutes_self_of_isClassicalMember (Fr.cls S l)
    (hL.2 l (Fin.succAbove_ne l a).symm (Fin.succAbove_ne l b).symm)

theorem LocalFrame.exists_plane_of_mem (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) {L : Subgroup G}
    (hL : L ∈ memberSet Fr (l.succAbove a) (l.succAbove b)) :
    ∃ P ∈ pairPlanes (GaloisField p f) m a b,
      locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ := by
  have hcent := LocalFrame.mem_cent_of_mem S hL
  obtain ⟨P, hP, hLP⟩ := typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem l)
    (Fr.cls S l) (Fr.p1 S l) LF.d hcent (LocalFrame.ne_Kf_of_mem S hL)
  refine ⟨P, ⟨hP, fun u hu => ?_⟩, hLP⟩
  refine mem_sup_stdPlane_of_orth hab (fun c hca hcb v hv => ?_)
  exact LF.orth_of_commutes S hP hcent hLP
    (hL.2 _ (fun h => hca (Fin.succAbove_right_injective h))
      (fun h => hcb (Fin.succAbove_right_injective h))) u hu v hv

theorem commutes_map_planeGroup_of_orth {F : Type} [Field F] {n : ℕ} (hn : 2 ≤ n) {X : Type*}
    [Group X] (ψ : StatedSp n F →* X) {P Q : Submodule F (Fin n ⊕ Fin n → F)}
    (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, form x y = 0) :
    Commutes ((planeGroup P).map ψ) ((planeGroup Q).map ψ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, commute_planeGroup_of_orth hn hP hQ horth x hx y hy]

theorem LocalFrame.exists_mem_of_plane (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b)
    {P : Submodule (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)}
    (hP : P ∈ pairPlanes (GaloisField p f) m a b) :
    ∃ L ∈ memberSet Fr (l.succAbove a) (l.succAbove b),
      locImg Ω (Fr.zf l) L = (planeGroup P).map LF.d.ψ := by
  obtain ⟨L, hLc, hLK, hLimg⟩ := typeC_exists_member_of_plane S.two_le S.five S.inClass
    (Fr.mem l) (Fr.cls S l) (Fr.p1 S l) LF.d hP.1
  refine ⟨L, ⟨hLc.1, fun k hki hkj => ?_⟩, hLimg⟩
  by_cases hkl : k = l
  · subst hkl
    exact (typeC_commutes_K_of_ne S.two_le S.five S.inClass S.exact (Fr.mem k) (Fr.cls S k)
      (Fr.p1 S k) LF.d hLc hLK).symm
  · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hkl
    have hca : c ≠ a := fun h => hki (by rw [h])
    have hcb : c ≠ b := fun h => hkj (by rw [h])
    refine commutes_of_commutes_locImg S.inClass (Fr.p1 S l) hLc (Fr.mem_cent S _ l) ?_
    rw [hLimg, LF.locImg_Kf c]
    exact commutes_map_planeGroup_of_orth S.two_le LF.d.ψ hP.1 (isHyperbolicPlane_stdPlane c)
      (fun x hx y hy => orth_stdPlane_of_mem_sup hab hca hcb (hP.2 hx) y hy)

omit [Finite G] in
theorem locImg_mono {x : G} {A B : Subgroup G} (h : A ≤ B) : locImg Ω x A ≤ locImg Ω x B :=
  Subgroup.map_mono fun _ hy => h hy

omit [Finite G] in
theorem locImg_iSup {x : G} {ι : Type*} (A : ι → Subgroup G) (hA : ∀ i, A i ≤ locLayer Ω x) :
    locImg Ω x (⨆ i, A i) = ⨆ i, locImg Ω x (A i) := by
  unfold locImg
  rw [← Subgroup.map_iSup]
  congr 1
  apply Subgroup.map_injective (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_iSup]
  simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hA _)]
  exact inf_eq_left.mpr (iSup_le hA)

omit [Finite G] in
theorem LocalFrame.Mf_le_locLayer (S : CSetup p f m Ω K z) (a b : Fin m) :
    Mf Fr (l.succAbove a) (l.succAbove b) ≤ locLayer Ω (Fr.zf l) :=
  iSup_le fun L => le_centralizingLayer (LocalFrame.mem_cent_of_mem S L.2)

theorem LocalFrame.locImg_Mf (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l) {a b : Fin m}
    (hab : a ≠ b) :
    locImg Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)) =
      (suppGroup (coords a ∪ coords b)).map LF.d.ψ := by
  have hle : ∀ L : memberSet Fr (l.succAbove a) (l.succAbove b),
      (L : Subgroup G) ≤ locLayer Ω (Fr.zf l) :=
    fun L => le_centralizingLayer (LocalFrame.mem_cent_of_mem S L.2)
  rw [Mf, locImg_iSup _ hle]
  apply le_antisymm
  · refine iSup_le fun L => ?_
    obtain ⟨P, hP, hLP⟩ := LF.exists_plane_of_mem S hab L.2
    rw [hLP]
    exact Subgroup.map_mono (Models.SymplecticPairs.planeGroup_le_suppGroup_pair hab hP.2)
  · rw [← Models.SymplecticPairs.pairPlaneSubgroup_eq S.four_le hab,
      Models.SymplecticPairs.pairPlaneSubgroup, Subgroup.map_iSup]
    refine iSup_le fun P => ?_
    obtain ⟨L, hL, hLP⟩ := LF.exists_mem_of_plane S hab P.2
    rw [← hLP]
    exact le_iSup (fun L : memberSet Fr (l.succAbove a) (l.succAbove b) =>
      locImg Ω (Fr.zf l) (L : Subgroup G)) ⟨L, hL⟩

omit [Finite G] in
theorem LocalFrame.Mf_subtype_mem (S : CSetup p f m Ω K z) (a b : Fin m)
    (y : ↥(Mf Fr (l.succAbove a) (l.succAbove b))) :
    (Mf Fr (l.succAbove a) (l.succAbove b)).subtype y ∈ locLayer Ω (Fr.zf l) :=
  LocalFrame.Mf_le_locLayer S a b y.2

theorem LocalFrame.injective_locHom_Mf (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    Function.Injective (locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_mem S a b)) := by
  set M := Mf Fr (l.succAbove a) (l.succAbove b) with hM
  set π := locHom Ω (Fr.zf l) M.subtype (LocalFrame.Mf_subtype_mem S a b) with hπ
  have hperf : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr (Mf_perfect Fr S _ _)
  have hmemY : ∀ y : ↥M, M.subtype y ∈ locLayer Ω (Fr.zf l) :=
    LocalFrame.Mf_subtype_mem S a b
  have hmem : ∀ y : ↥π.ker, (⟨((y : ↥M) : G), hmemY y⟩ :
      ↥(locLayer Ω (Fr.zf l))) ∈ classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)) :=
    fun y => (QuotientGroup.eq_one_iff _).mp y.2
  have hcen : π.ker ≤ Subgroup.center ↥M := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro w
    have h2 := Fr.p1 S l (hmem ⟨y, hy⟩)
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
    Models.SymplecticPairs.injective_comp_pairEmbed S.three hab LF.d.ψ LF.d.ker_le
  have hrange : (LF.d.ψ.comp (Models.SymplecticPairs.pairEmbed (GaloisField p f) hab)).range =
      π.range := by
    rw [MonoidHom.range_comp, Models.SymplecticPairs.range_pairEmbed, hπ, range_locHom,
      Subgroup.range_subtype, LF.locImg_Mf S hab]
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

theorem LocalFrame.injOn_locImg_Mf (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l) {a b : Fin m}
    (hab : a ≠ b) {A B : Subgroup G} (hA : A ≤ Mf Fr (l.succAbove a) (l.succAbove b))
    (hB : B ≤ Mf Fr (l.succAbove a) (l.succAbove b))
    (h : locImg Ω (Fr.zf l) A = locImg Ω (Fr.zf l) B) : A = B := by
  set M := Mf Fr (l.succAbove a) (l.succAbove b) with hM
  have hmemY : ∀ y : ↥M, M.subtype y ∈ locLayer Ω (Fr.zf l) :=
    LocalFrame.Mf_subtype_mem S a b
  have hinj := LF.injective_locHom_Mf S hab
  have key : ∀ C : Subgroup G, C ≤ M →
      (C.subgroupOf M).map (locHom Ω (Fr.zf l) M.subtype hmemY) = locImg Ω (Fr.zf l) C := by
    intro C hC
    rw [map_locHom, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC]
  have h1 : A.subgroupOf M = B.subgroupOf M :=
    Subgroup.map_injective hinj (by rw [key A hA, key B hB, h])
  have h2 := (Subgroup.subgroupOf_inj).mp h1
  rwa [inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h2

theorem injective_comp_suppGroup_subtype {a b : Fin m} (hm : 3 ≤ m) (hab : a ≠ b)
    {X : Type*} [Group X] (ψ : StatedSp m (GaloisField p f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (StatedSp m (GaloisField p f))) :
    Function.Injective (ψ.comp (suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f))).subtype) := by
  have hinj := Models.SymplecticPairs.injective_comp_pairEmbed hm hab ψ hψ
  rw [injective_iff_map_eq_one] at hinj ⊢
  intro s hs
  have hs' : (s : StatedSp m (GaloisField p f)) ∈
      (Models.SymplecticPairs.pairEmbed (GaloisField p f) hab).range := by
    rw [Models.SymplecticPairs.range_pairEmbed]
    exact s.2
  obtain ⟨t, ht⟩ := hs'
  have h1 : (ψ.comp (Models.SymplecticPairs.pairEmbed (GaloisField p f) hab)) t = 1 := by
    rw [MonoidHom.comp_apply, ht]
    exact hs
  have h2 := hinj t h1
  apply Subtype.ext
  rw [← ht, h2, map_one]
  rfl

noncomputable def LocalFrame.layerEquiv (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f))) ≃*
      ↥(Mf Fr (l.succAbove a) (l.succAbove b)) :=
  (MonoidHom.ofInjective (injective_comp_suppGroup_subtype S.three hab LF.d.ψ LF.d.ker_le)).trans
    ((MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, range_locHom, Subgroup.range_subtype,
          LF.locImg_Mf S hab])).trans
      (MonoidHom.ofInjective (LF.injective_locHom_Mf S hab)).symm)

theorem LocalFrame.locHom_layerEquiv (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b)
    (s : ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f)))) :
    locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_mem S a b) (LF.layerEquiv S hab s) = LF.d.ψ s := by
  unfold LocalFrame.layerEquiv
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

@[expose] noncomputable def LocalFrame.layerHom (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f))) →* G :=
  (Mf Fr (l.succAbove a) (l.succAbove b)).subtype.comp (LF.layerEquiv S hab).toMonoidHom

theorem LocalFrame.layerHom_injective (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) : Function.Injective (LF.layerHom S hab) :=
  (Subgroup.subtype_injective _).comp (LF.layerEquiv S hab).injective

theorem LocalFrame.layerHom_range (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    (LF.layerHom S hab).range = Mf Fr (l.succAbove a) (l.succAbove b) := by
  unfold LocalFrame.layerHom
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (LF.layerEquiv S hab).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem LocalFrame.map_layerHom_le (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) (A : Subgroup ↥(suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))) :
    A.map (LF.layerHom S hab) ≤ Mf Fr (l.succAbove a) (l.succAbove b) := by
  rw [← LF.layerHom_range S hab]
  exact Subgroup.map_le_range _ _

theorem LocalFrame.locImg_map_layerHom (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) (A : Subgroup ↥(suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))) :
    locImg Ω (Fr.zf l) (A.map (LF.layerHom S hab)) =
      (A.map (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f))).subtype).map LF.d.ψ := by
  unfold LocalFrame.layerHom
  rw [← Subgroup.map_map, ← map_locHom, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  exact LF.locHom_layerEquiv S hab s

theorem LocalFrame.mk_zf (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l) (c : Fin m) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)))
      ⟨Fr.zf (l.succAbove c), Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _)⟩ =
        LF.d.ψ (longInv (GaloisField p f) m c) := by
  have hle : ∀ a, Fr.ι (l.succAbove c) a ∈ locLayer Ω (Fr.zf l) := fun a =>
    Fr.Kf_le_locLayer S _ l (by rw [← Fr.range_ι]; exact ⟨a, rfl⟩)
  have hβ : Function.Injective (locHom Ω (Fr.zf l) (Fr.ι (l.succAbove c)) hle) :=
    locHom_injective S.exact (Fr.mem_cent S _ l) (Fr.ι_inj _) (by rw [Fr.range_ι]) hle
  have hr : (locHom Ω (Fr.zf l) (Fr.ι (l.succAbove c)) hle).range =
      (longBlock (GaloisField p f) m c).range.map LF.d.ψ := by
    rw [range_locHom, Fr.range_ι, LF.adapted c]
  have h1 := map_neg_one_eq_of_range_eq (by have := S.two_le; omega) S.two_ne_zero LF.d.ψ
    LF.d.ker_le c _ hβ hr
  rw [locHom_apply] at h1
  have e : (⟨Fr.ι (l.succAbove c) (-1), hle (-1)⟩ : ↥(locLayer Ω (Fr.zf l))) =
      ⟨Fr.zf (l.succAbove c), Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _)⟩ :=
    Subtype.ext (Fr.ι_neg_one S _)
  rw [e] at h1
  exact h1

theorem LocalFrame.map_layerEquiv_planeTorus (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) (c : Fin m) (hc : c = a ∨ c = b) :
    ((planeTorus (GaloisField p f) m c).subgroupOf (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerEquiv S hab).toMonoidHom =
      (Fr.Tf (l.succAbove c)).subgroupOf (Mf Fr (l.succAbove a) (l.succAbove b)) := by
  have hinj := LF.injective_locHom_Mf S hab
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_map]
  have h1 : (locHom Ω (Fr.zf l) (Mf Fr (l.succAbove a) (l.succAbove b)).subtype
      (LocalFrame.Mf_subtype_mem S a b)).comp (LF.layerEquiv S hab).toMonoidHom =
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

theorem LocalFrame.layerEquiv_longInv (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) :
    LF.layerEquiv S hab ⟨longInv (GaloisField p f) m a,
        Models.SymplecticPairs.longInv_mem_suppGroup (Or.inl rfl)⟩ =
      ⟨Fr.zf (l.succAbove a), zf_mem_Mf Fr S _ (Or.inl rfl)⟩ := by
  apply LF.injective_locHom_Mf S hab
  rw [LF.locHom_layerEquiv S hab]
  exact (LF.mk_zf S a).symm

theorem LocalFrame.isAdaptedShortIn_iff (S : CSetup p f m Ω K z) (LF : LocalFrame Fr l)
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
    (zf_mem_Mf Fr S _ (Or.inl rfl)) hT]
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



end CFSG.ClassicalInvolution.RouteD
