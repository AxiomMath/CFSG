module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldAlign

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)
open scoped commutatorElement

local instance e6PilotQ2FieldFamilyNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Generic

variable {E D : Type*} [Group E] [Group D]

theorem eq_top_of_forall_exists_map_eq_of_perfect
    (hE : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤) {p : E →* D} (hker : p.ker ≤ center E)
    {H : Subgroup E} (hH : ∀ g : E, ∃ h ∈ H, p h = p g) : H = ⊤ := by
  have hdec : ∀ g : E, ∃ h ∈ H, ∃ z ∈ center E, g = h * z := by
    intro g
    obtain ⟨h, hh, hhg⟩ := hH g
    refine ⟨h, hh, h⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hhg, inv_mul_cancel]
  rw [eq_top_iff, ← hE, commutator_le]
  intro a _ b _
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hdec a
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hdec b
  rw [commutatorElement_mul_left_of_mem_center hz₁, commutatorElement_mul_right_of_mem_center hz₂,
    commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)

end Generic

section HomExt


variable {F : Type} [Field F] [CharP F 2] {H : Type*} [Group H]

theorem levi_hom_ext {J : Finset (Fin (Tag.rank .E6))}
    {f₁ f₂ : CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J →* H}
    (h : ∀ j ∈ J, ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
      ∀ (c : F) (g : CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J),
        ((g : adjointGroup .E6 F) : ModGL .E6 F) = pinnedX .E6 F γ c → f₁ g = f₂ g) :
    f₁ = f₂ := by
  have hle : CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J ≤
      (MonoidHom.eqLocus f₁ f₂).map
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J).subtype := by
    refine iSup₂_le fun j hj => sup_le ?_ ?_ <;> intro y hy
    · have hyS : y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_left hy)
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single .E6 j) y).1 hy
      exact ⟨⟨_, hyS⟩,
        h j hj _ (Or.inl rfl) c ⟨_, hyS⟩ (coe_xPar_eq_pinnedX (isRoot_single .E6 j) c), rfl⟩
    · have hyS : y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 F).rootGroup J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_right hy)
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single .E6 j) y).1 hy
      exact ⟨⟨_, hyS⟩,
        h j hj _ (Or.inr rfl) c ⟨_, hyS⟩ (coe_xPar_eq_pinnedX (isRoot_neg_single .E6 j) c), rfl⟩
  refine MonoidHom.ext fun y => ?_
  obtain ⟨y', hy', hyy'⟩ := hle y.2
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

end HomExt

section Generation


theorem chainNode_mem_nodes_high (t : Fin 5) : chainNode t ∈ E6Neighbour.high.nodes := by
  revert t
  decide

section Adjacent

variable {F : Type} [Field F]

@[expose] def q2AdjSet (F : Type) [Field F] : Set (Matrix.SpecialLinearGroup (Fin 6) F) :=
  {g | ∃ (t : Fin 5) (c : F),
    g = Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne c ∨
    g = Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne' c}

theorem commutator_mem_closure_q2 {M : Type*} [Group M] {S : Set M} {a b : M}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) :
    ⁅a, b⁆ ∈ Subgroup.closure S := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem upper_mem_closure_q2AdjSet : ∀ (d : ℕ) {i j : Fin 6} (hij : i < j),
    j.val = i.val + d + 1 → ∀ c : F,
      Matrix.SpecialLinearGroup.transvection hij.ne c ∈ Subgroup.closure (q2AdjSet F) := by
  intro d
  induction d with
  | zero =>
    intro i j hij hd c
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : j = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [hd])
    refine Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, Or.inl (Subtype.ext ?_)⟩
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      ← e1, ← e2]
  | succ d ih =>
    intro i j hij hd c
    have hk : i.val + 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val + 1, hk⟩
    have hik : i < k := Fin.lt_def.mpr (by simp [k])
    have hkj : k < j := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hik.ne hkj.ne hij.ne c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure_q2 ?_ (ih hkj (by simp [k]; omega) 1)
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : k = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [k])
    refine Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, Or.inl (Subtype.ext ?_)⟩
    simp only [Matrix.SpecialLinearGroup.transvection_coe, ← e1, ← e2]

theorem lower_mem_closure_q2AdjSet : ∀ (d : ℕ) {i j : Fin 6} (hji : j < i),
    i.val = j.val + d + 1 → ∀ c : F,
      Matrix.SpecialLinearGroup.transvection hji.ne' c ∈ Subgroup.closure (q2AdjSet F) := by
  intro d
  induction d with
  | zero =>
    intro i j hji hd c
    have hj : j.val < 5 := by omega
    have e1 : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨j.val, hj⟩ := Fin.ext (by simp [hd])
    refine Subgroup.subset_closure ⟨⟨j.val, hj⟩, c, Or.inr (Subtype.ext ?_)⟩
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      ← e1, ← e2]
  | succ d ih =>
    intro i j hji hd c
    have hk : i.val - 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val - 1, hk⟩
    have hki : k < i := Fin.lt_def.mpr (by simp [k]; omega)
    have hjk : j < k := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hki.ne' hjk.ne' hji.ne' c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure_q2 ?_ (ih hjk (by simp [k]; omega) 1)
    have hk5 : k.val < 5 := by simp [k]; omega
    have e1 : k = Fin.castSucc ⟨k.val, hk5⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨k.val, hk5⟩ := Fin.ext (by simp [k]; omega)
    refine Subgroup.subset_closure ⟨⟨k.val, hk5⟩, c, Or.inr (Subtype.ext ?_)⟩
    simp only [Matrix.SpecialLinearGroup.transvection_coe, ← e1, ← e2]

theorem closure_q2AdjSet : Subgroup.closure (q2AdjSet F) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact upper_mem_closure_q2AdjSet (j.val - i.val - 1) h (by omega) c
  · exact lower_mem_closure_q2AdjSet (i.val - j.val - 1) h (by omega) c

end Adjacent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem a5Levi_le_of_forall {H : Subgroup (adjointGroup .E6 K)}
    (hH : ∀ l ∈ E6Neighbour.high.nodes, ∀ c : K,
      (⟨pinnedX .E6 K (Pi.single l 1) c, pinnedX_mem_adjointGroup _ c⟩ : adjointGroup .E6 K) ∈ H ∧
      (⟨pinnedX .E6 K (-Pi.single l 1) c, pinnedX_mem_adjointGroup _ c⟩ :
        adjointGroup .E6 K) ∈ H) :
    a5Levi K ≤ H := by
  rw [← range_slToAdjointE6, MonoidHom.range_eq_map, ← closure_q2AdjSet (F := K),
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨t, c, rfl | rfl⟩, rfl⟩
  · have h1 : slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := t)).ne c) =
        ⟨pinnedX .E6 K (Pi.single (chainNode t) 1) c, pinnedX_mem_adjointGroup _ c⟩ :=
      Subtype.ext (by rw [coe_slToAdjointE6_transvection, a5Root_castSucc_succ_check t])
    rw [SetLike.mem_coe, h1]
    exact (hH _ (chainNode_mem_nodes_high t) c).1
  · have h1 : slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := t)).ne' c) =
        ⟨pinnedX .E6 K (-Pi.single (chainNode t) 1) c, pinnedX_mem_adjointGroup _ c⟩ :=
      Subtype.ext (by rw [coe_slToAdjointE6_transvection, a5Root_succ_castSucc_check t])
    rw [SetLike.mem_coe, h1]
    exact (hH _ (chainNode_mem_nodes_high t) c).2

end Generation

section Family


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

structure TwoCover.Section {N : E6Neighbour} {E : Subgroup G} (c : TwoCover σ e N E)
    (H : Subgroup (adjointGroup .E6 K)) where
  s : H →* G
  mem : ∀ y, s y ∈ E
  lift : ∀ y, ((c.p ⟨s y, mem y⟩ : N.levi K) : adjointGroup .E6 K) = y

theorem TwoCover.Section.isLift {N : E6Neighbour} {E : Subgroup G} {c : TwoCover σ e N E}
    {H : Subgroup (adjointGroup .E6 K)} (t : c.Section H) (y : H) (u : N.levi K)
    (hyu : (y : adjointGroup .E6 K) = u) (hu : u * u = 1) : c.IsLift u (t.s y) := by
  refine ⟨⟨t.s y, t.mem y⟩, rfl, Subtype.ext ((t.lift y).trans hyu), ?_⟩
  have hyy : y * y = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hyu, OneMemClass.coe_one, ← Subgroup.coe_mul, hu, OneMemClass.coe_one])
  exact Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, hyy, map_one, OneMemClass.coe_one])

@[expose] noncomputable def TwoCover.Section.ofHom {N : E6Neighbour} {E : Subgroup G}
    (c : TwoCover σ e N E) {H : Subgroup (adjointGroup .E6 K)} (s : H →* E)
    (hs : ∀ y, ((c.p (s y) : N.levi K) : adjointGroup .E6 K) = y) : c.Section H where
  s := E.subtype.comp s
  mem y := (s y).2
  lift y := hs y

@[expose] def TwoCover.Agree {N N' : E6Neighbour} {E E' : Subgroup G} (h : TwoCover σ e N E)
    (h' : TwoCover σ e N' E') (γ : Fin (Tag.rank .E6) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K) (g g' : G),
    h.IsLift (q2LeviRootElt N hγ a) g → h'.IsLift (q2LeviRootElt N' hγ' a) g' → g = g'

theorem TwoCover.TwistAt.agree {N N' : E6Neighbour} {E E' : Subgroup G} {h : TwoCover σ e N E}
    {h' : TwoCover σ e N' E'} {γ : Fin (Tag.rank .E6) → ℤ} (hT : h.TwistAt h' 1 γ) :
    h.Agree h' γ := by
  intro hγ hγ' a g g' hg hg'
  refine hT hγ hγ' a g g' hg ?_
  rw [RingAut.one_apply]
  exact hg'

theorem TwoCover.Agree.symm {N N' : E6Neighbour} {E E' : Subgroup G} {h : TwoCover σ e N E}
    {h' : TwoCover σ e N' E'} {γ : Fin (Tag.rank .E6) → ℤ} (hA : h.Agree h' γ) :
    h'.Agree h γ := fun hγ' hγ a g' g hg' hg => (hA hγ hγ' a g g' hg hg').symm

theorem TwoCover.agree_self {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    (γ : Fin (Tag.rank .E6) → ℤ) : h.Agree h γ := fun _ _ _ _ _ hg hg' => hg.eq hg'

@[expose] def TwoCoversAligned {EN : E6Neighbour → Subgroup G}
    (c : ∀ N, TwoCover σ e N (EN N)) : Prop :=
  ∀ (N N' : E6Neighbour) (j : Fin (Tag.rank .E6)), j ∈ N.nodes → j ∈ N'.nodes →
    (c N).Agree (c N') (Pi.single j 1) ∧ (c N).Agree (c N') (-Pi.single j 1)

variable {EN : E6Neighbour → Subgroup G} {c : ∀ N, TwoCover σ e N (EN N)}

@[expose] noncomputable def familyOfSections
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1))
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (adjDatumE6 K).leviAmalgam J →* G :=
  (sec J).s

theorem isLift_familyOfSections
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1))
    (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) {j : Fin (Tag.rank .E6)} (_hj : j ∈ J.1)
    {γ : Fin (Tag.rank .E6) → ℤ} (_hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1)
    (hγN : γ ∈ orthRoots (amalgamPlacement J.1).root) (a : K)
    (g : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1)
    (hg : ((g : adjointGroup .E6 K) : ModGL .E6 K) = pinnedX .E6 K γ a) :
    (c (amalgamPlacement J.1)).IsLift (q2LeviRootElt _ hγN a) ((sec J).s g) :=
  (sec J).isLift g _ (Subtype.ext hg) (q2LeviRootElt_mul_self _ hγN a)

theorem mem_orthRoots_placement {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {j : Fin (Tag.rank .E6)} (hj : j ∈ J) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) : γ ∈ orthRoots (amalgamPlacement J).root := by
  have h := single_mem_orthRoots_E6 (subset_nodes_amalgamPlacement hJ hj)
  rcases hγ with rfl | rfl
  exacts [h, neg_mem_orthRoots_E6 h]

theorem familyOfSections_eq_of_subset (hal : TwoCoversAligned c)
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1))
    {I J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}} (hIJ : I.1 ⊆ J.1)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I.1)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1)
    (hxy : (x : adjointGroup .E6 K) = y) : (sec I).s x = (sec J).s y := by
  have hle : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I.1 ≤
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 :=
    CFSG.LieType.CurtisTits.levi_mono _ hIJ
  have hext : (sec I).s = (sec J).s.comp (Subgroup.inclusion hle) := by
    refine levi_hom_ext fun l hl γ hγ a g hg => ?_
    have hγi := mem_orthRoots_placement I.2 hl hγ
    have hγj := mem_orthRoots_placement J.2 (hIJ hl) hγ
    have h1 := isLift_familyOfSections sec I hl hγ hγi a g hg
    have hincl : Subgroup.inclusion hle g = ⟨(g : adjointGroup .E6 K), hle g.2⟩ :=
      Subtype.ext (Subgroup.coe_inclusion hle g)
    have h2 := isLift_familyOfSections sec J (hIJ hl) hγ hγj a
      ⟨(g : adjointGroup .E6 K), hle g.2⟩ hg
    have hli := subset_nodes_amalgamPlacement I.2 hl
    have hlj := subset_nodes_amalgamPlacement J.2 (hIJ hl)
    have key : (c (amalgamPlacement I.1)).Agree (c (amalgamPlacement J.1)) γ := by
      rcases hγ with h | h
      · rw [h]
        exact (hal _ _ l hli hlj).1
      · rw [h]
        exact (hal _ _ l hli hlj).2
    change (sec I).s g = (sec J).s (Subgroup.inclusion hle g)
    rw [hincl]
    exact key hγi hγj a _ _ h1 h2
  have hx : Subgroup.inclusion hle x = y := Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hxy)
  exact (congrArg (fun f => f x) hext).trans (congrArg (sec J).s hx)

theorem isCompatible_familyOfSections (hal : TwoCoversAligned c)
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1)) :
    IsCompatible (adjDatumE6 K).leviAmalgam (familyOfSections sec) :=
  fun _ _ hij x y hxy => familyOfSections_eq_of_subset hal sec hij x y hxy

@[expose] noncomputable def leviFixedFieldInclusion (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J →*
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
  ((fixedFieldInclusion σ).comp
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J).subtype).codRestrict _
    fun y => by
      obtain ⟨y', hy'⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype y.2
      have h1 : fixedFieldInclusion σ y = y' :=
        Subtype.ext (by rw [coe_fixedFieldInclusion]; exact hy'.symm)
      rw [MonoidHom.comp_apply, coe_subtype, h1]
      exact y'.2

theorem fix_familyOfSections [CharP (fixSubfield σ) 2]
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1))
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2})
    (x : adjointGroup .E6 (fixSubfield σ))
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1)
    (y : (adjDatumE6 K).leviAmalgam J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    familyOfSections sec J y = ((e.symm x : L) : G) := by
  have hext : (sec J).s.comp (leviFixedFieldInclusion J.1) = L.subtype.comp
      (e.symm.toMonoidHom.comp
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1).subtype) := by
    refine levi_hom_ext fun l hl γ hγ a g hg => ?_
    have hγJ := mem_orthRoots_placement J.2 hl hγ
    have hgK : (((leviFixedFieldInclusion J.1 g :
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1) : adjointGroup .E6 K) :
          ModGL .E6 K) = pinnedX .E6 K γ (a : K) := by
      change baseChangeGL (fixSubfield σ).subtype ((g : adjointGroup .E6 (fixSubfield σ)) :
        ModGL .E6 (fixSubfield σ)) = _
      rw [hg, baseChangeGL_pinnedX]
      rfl
    have h1 := isLift_familyOfSections sec J hl hγ hγJ (a : K) _ hgK
    have h2 := (c (amalgamPlacement J.1)).isLift_q2LeviRootElt_fix hγJ a
    have hga : (g : adjointGroup .E6 (fixSubfield σ)) =
        (q2LeviRootElt (amalgamPlacement J.1) hγJ a : adjointGroup .E6 (fixSubfield σ)) :=
      Subtype.ext hg
    rw [MonoidHom.comp_apply, h1.eq h2]
    simp only [MonoidHom.comp_apply, coe_subtype, MulEquiv.coe_toMonoidHom]
    rw [hga]
  have hy : y = leviFixedFieldInclusion J.1 ⟨x, hx⟩ :=
    Subtype.ext (Subtype.ext hxy)
  change (sec J).s y = _
  rw [hy, ← MonoidHom.comp_apply, hext]
  rfl

theorem isTwoFieldFamilyE6_familyOfSections [CharP (fixSubfield σ) 2] (hal : TwoCoversAligned c)
    (sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (c (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1)) :
    IsTwoFieldFamilyE6 e (familyOfSections sec) :=
  ⟨isCompatible_familyOfSections hal sec, fix_familyOfSections sec⟩

end Family

end CFSG.SeitzReduction.E6Pilot
