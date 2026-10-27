module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadFrameStd
public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51
public import CFSG.ClassicalInvolution.Q3.Q3AMPspG01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs


@[expose] def nbrCoreFam {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Set (Subgroup G) :=
  {C | ∃ N ∈ omegaNbr Ω M, C = exactCore3 a N}

@[expose] def PspNbhdSp4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
        (centralizingLayer (nbrCoreFam Ω M a) {a})))),
    ∃ ha : a ∈ centralizingLayer (nbrCoreFam Ω M a) {a},
      ShapeSp4 D (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩)

@[expose] def PspNbhdL4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
        (centralizingLayer (nbrCoreFam Ω M a) {a})))),
    ∃ ha : a ∈ centralizingLayer (nbrCoreFam Ω M a) {a}, ∃ i₁ : ι, (∀ i, i = i₁) ∧
      D.kind i₁ = CompData.model .PSL 4 ∧ ∃ f ∈ Subgroup.center (D.kind i₁).G,
        D.hom i₁ f = QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩

@[expose] def PspShapeE4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J K' : Subgroup G)
    (z t : G) : Prop :=
  (PspNbhdSp4 Ω K z ∧ PspNbhdSp4 Ω J t ∧ PspNbhdSp4 Ω K' (z * t)) ∨
    (PspNbhdL4 Ω K z ∧ PspNbhdL4 Ω J t ∧ PspNbhdL4 Ω K' (z * t))

structure PspSetting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G) : Prop where
  bad : BadStd8 Ω K J S R T W z t
  intrinsic : IsIntrinsicU (.sl2 3 1) K z
  nbrK : K' ∈ omegaNbr Ω K
  nbrJ : K' ∈ omegaNbr Ω J

@[expose] def PspVertexCLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' →
      ∀ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃ →
        Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) z ∧
          Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) t ∧
            Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) (z * t)

@[expose] def PspLayersSp4Leaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' →
      ∀ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃ →
        PspNbhdSp4 Ω K z → PspNbhdSp4 Ω J t → PspNbhdSp4 Ω K' (z * t) →
          ∃ L₁ L₂ L₃ : Subgroup G,
            IsSectionMember3 (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₁ z ∧
              IsSectionMember3 (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₂ t ∧
                IsSectionMember3 (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₃ (z * t)

@[expose] def PspVertexSLeaf9 : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' →
      ∀ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃ →
        PspNbhdL4 Ω K z → PspNbhdL4 Ω J t → PspNbhdL4 Ω K' (z * t) →
          Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) (t₁ * t₂ * t₃)

@[expose] def PspLayerGenLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' →
      ∀ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃ →
        exactLayer3 Ω z ≤ rankTwoSpan (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G))

structure PspLeaves : Prop where
  vertexC : PspVertexCLeaf
  layers : PspLayersSp4Leaf
  vertexS9 : PspVertexSLeaf9
  gen : PspLayerGenLeaf

@[expose] def PspClose : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' →
      PspShapeE4 Ω K J K' z t → False

end Defs

section Route


theorem localAxisClosing_proved :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), BadStd8 Ω K J S R T W z t →
        ∀ B : Subgroup G, Hyp51 B → Subgroup.closure ({t, z} : Set G) ≤ B →
          exactLayer3 Ω z ≤ rankTwoSpan B → False :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hB hp hg => h.false_of_localAxis_layer hB hp hg

theorem closure_triple_eq_of_mul {G : Type} [Group G] {z t s s' c : G}
    (hc : c ∈ Subgroup.closure ({z, t} : Set G)) (hs : s' = c * s) :
    Subgroup.closure ({z, t, s'} : Set G) = Subgroup.closure ({z, t, s} : Set G) := by
  have hzt : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, t, s} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hsB : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hs'B : s' ∈ Subgroup.closure ({z, t, s} : Set G) := by
    rw [hs]
    exact Subgroup.mul_mem _ (hzt hc) hsB
  have hzt' : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, t, s'} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hs'B' : s' ∈ Subgroup.closure ({z, t, s'} : Set G) := Subgroup.subset_closure (by simp)
  have hsB' : s ∈ Subgroup.closure ({z, t, s'} : Set G) := by
    have e : s = c⁻¹ * s' := by rw [hs]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hzt' hc)) hs'B'
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact hs'B
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact hsB'

theorem hyp51At_s_of_leaves (hM11 : Q3CH.M11OddAutInner3) (hA : PspLayersSp4Leaf)
    (h9 : PspVertexSLeaf9) (hI9 : Asc77.IHInterface8 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} {K' : Subgroup G} (hb9 : Asc77.CITBelowAll 3 (Nat.card G))
    (hset : PspSetting Ω K J S R T W z t K') (hshape : PspShapeE4 Ω K J K' z t) {t₁ t₂ t₃ : G}
    {R₁ R₂ R₃ : Subgroup G} (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) :
    Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) (t₁ * t₂ * t₃) := by
  rcases hshape with hsh | ⟨hL1, hL2, hL3⟩
  · obtain ⟨L₁, L₂, L₃, h₁, h₂, h₃⟩ := hA G Ω K J S R T W z t K' hset t₁ t₂ t₃ R₁ R₂ R₃ hax
      hsh.1 hsh.2.1 hsh.2.2
    have hbad := hset.bad
    have hstd := hbad.std
    have hBelow : Q3.CIT3Below (Nat.card G) :=
      (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
    have hz2 := hstd.hz.sq
    have ht2 := hstd.ht.sq
    have hΩ : HypOmegaMod Ω := hstd.stand.hyp
    have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
      T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
    have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
    have hne : z ≠ t := fun e => by
      have : IsUniqueInvolution J z := e ▸ hstd.ht
      exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
    have hs2 := hax.s_mul_self
    have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
    have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
    have hindep : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z, t} : Set G) := hax.s_not_mem_pair
    have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h1 => hindep (h1 ▸ Subgroup.one_mem _)
    have hzB : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
    have htB : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
    have hsz : z ≠ t₁ * t₂ * t₃ := fun e => hindep (e ▸ hzB)
    have hst : t ≠ t₁ * t₂ * t₃ := fun e => hindep (e ▸ htB)
    have hzts : z * t ≠ t₁ * t₂ * t₃ := fun e => hindep (e ▸ Subgroup.mul_mem _ hzB htB)
    have helem := T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hcz hct
    exact Q3CH.hyp51At_of_layers hM11 hbad.nonabelian hBelow helem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) rfl hs1 hstd.hz.ne_one hstd.ht.ne_one hne hsz hst hzts
      h₁ h₂ h₃
  · exact h9 hI9 G Ω K J S R T W z t K' hb9 hset t₁ t₂ t₃ R₁ R₂ R₃ hax hL1 hL2 hL3

theorem pspClose_of_leaves (hM11 : Q3CH.M11OddAutInner3)
    (L : PspLeaves) : PspClose := by
  have hcl := CFSG.ClassicalInvolution.Q3.Q3AM.localAxisClosing_proved
  intro hI9 G _ _ _ Ω K J S R T W z t K' hb9 hset hshape
  have hbad := hset.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hK' : K' ∈ Ω := hset.nbrK.1
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hK'
  have hut : u = z * t := hbad.eq_mul_of_nbr_nbr hset.nbrK hset.nbrJ hu
  obtain ⟨t₁, t₂, t₃, R₁, R₂, R₃, hax⟩ := hbad.exists_axis_of_triangle hset.intrinsic
    hstd.stand.mem hstd.hJ hset.nbrK hset.nbrJ hstd.hz hstd.ht hu hut
  have vc := L.vertexC G Ω K J S R T W z t K' hset t₁ t₂ t₃ R₁ R₂ R₃ hax
  have hg := L.gen G Ω K J S R T W z t K' hset t₁ t₂ t₃ R₁ R₂ R₃ hax
  have hvs := hyp51At_s_of_leaves hM11 L.layers L.vertexS9 hI9 hb9 hset hshape hax
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have hs2 := hax.s_mul_self
  have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have hindep : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z, t} : Set G) := hax.s_not_mem_pair
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h1 => hindep (h1 ▸ Subgroup.one_mem _)
  have helem := T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hcz hct
  have hcard := T8T.natCard_closure_three hz2 ht2 hs2 hzt hcz hct hstd.hz.ne_one hstd.ht.ne_one
    hne hs1 hindep
  have hzB : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have c11 : Commute z t₁ := by
    show z * t₁ = t₁ * z
    rw [← hax.sq₁]
    group
  have hzs : Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) (z * (t₁ * t₂ * t₃)) := by
    have h1 := hyp51At_s_of_leaves hM11 L.layers L.vertexS9 hI9 hb9 hset hshape hax.flip₁
    have e : (t₁ * z) * t₂ * t₃ = z * (t₁ * t₂ * t₃) := by
      calc (t₁ * z) * t₂ * t₃ = (z * t₁) * t₂ * t₃ := by rw [← c11.eq]
        _ = z * (t₁ * t₂ * t₃) := by group
    rw [closure_triple_eq_of_mul hzB e, e] at h1
    exact h1
  have hts : Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) (t * (t₁ * t₂ * t₃)) := by
    have h1 := hyp51At_s_of_leaves hM11 L.layers L.vertexS9 hI9 hb9 hset hshape hax.flip₂
    have e : t₁ * (t₂ * t) * t₃ = t * (t₁ * t₂ * t₃) := by
      have c23 : t * t₃ = t₃ * t := hax.comm₂₃ t hax.z_mem₂ t₃ hax.mem₃
      calc t₁ * (t₂ * t) * t₃ = t₁ * t₂ * (t * t₃) := by group
        _ = t₁ * t₂ * (t₃ * t) := by rw [c23]
        _ = (t₁ * t₂ * t₃) * t := by group
        _ = t * (t₁ * t₂ * t₃) := hct.symm
    rw [closure_triple_eq_of_mul htB e, e] at h1
    exact h1
  have hzts : Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G))
      (z * t * (t₁ * t₂ * t₃)) := by
    have h1 := hyp51At_s_of_leaves hM11 L.layers L.vertexS9 hI9 hb9 hset hshape hax.flip₃
    have e : t₁ * t₂ * (t₃ * (z * t)) = z * t * (t₁ * t₂ * t₃) := by
      have h3 : (z * t) * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * (z * t) := by
        calc (z * t) * (t₁ * t₂ * t₃) = z * (t * (t₁ * t₂ * t₃)) := by group
          _ = z * ((t₁ * t₂ * t₃) * t) := by rw [hct]
          _ = (z * (t₁ * t₂ * t₃)) * t := by group
          _ = ((t₁ * t₂ * t₃) * z) * t := by rw [hcz]
          _ = (t₁ * t₂ * t₃) * (z * t) := by group
      calc t₁ * t₂ * (t₃ * (z * t)) = (t₁ * t₂ * t₃) * (z * t) := by group
        _ = z * t * (t₁ * t₂ * t₃) := h3.symm
    rw [closure_triple_eq_of_mul (Subgroup.mul_mem _ hzB htB) e, e] at h1
    exact h1
  have hvert : ∀ c ∈ Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G), c ≠ 1 →
      Hyp51At (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) c := by
    intro c hc hc1
    rcases T8T.mem_closure_three_involutions hz2 ht2 hs2 hzt hcz hct hc with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · rw [h]; exact vc.1
    · rw [h]; exact vc.2.1
    · rw [h]; exact hvs
    · rw [h]; exact vc.2.2
    · rw [h]; exact hzs
    · rw [h]; exact hts
    · rw [h]; exact hzts
  have hB : Hyp51 (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) := ⟨helem, hcard, hvert⟩
  have hzt_le : Subgroup.closure ({t, z} : Set G) ≤
      Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  exact hcl G Ω K J S R T W z t hbad _ hB hzt_le hg

end Route

end CFSG.ClassicalInvolution.Q3.Q3AM
