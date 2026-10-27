module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMaxBorel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (scalarKernel statedActionEquiv_scalarKernel)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open scoped Pointwise

theorem scalarKernel_eq_elemScalars {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : scalarKernel Q = elemScalars Q :=
  Subgroup.ext fun _ => by
    rw [scalarKernel, Subgroup.mem_subgroupOf, mem_scalars]
    rfl

theorem mem_scalarKernel_iff_elemScalars {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (g : elementaryGroup Q) : g ∈ scalarKernel Q ↔ g ∈ elemScalars Q := by
  rw [scalarKernel_eq_elemScalars]
  exact Iff.rfl

@[expose] def BorelInterface {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (p : ℕ) (Q0 : (ι → K) → K) {r : ℕ} (F : Fin r → Submodule K (ι → K)) : Prop :=
  (∀ i, (∀ x ∈ F i, Q0 x = 0) ∧ finrank K (F i) = i + 1) ∧
  (∃ S : Sylow p (StatedProj (StatedOmega Q0)),
    statedProjectiveFlagStabilizer Q0 F =
      Subgroup.normalizer ((S : Subgroup (StatedProj (StatedOmega Q0))) :
        Set (StatedProj (StatedOmega Q0)))) ∧
  (∀ α : MulAut (StatedProj (StatedOmega Q0)), ∃ g : StatedProj (StatedOmega Q0),
    (statedProjectiveFlagStabilizer Q0 F).map α.toMonoidHom =
      (statedProjectiveFlagStabilizer Q0 F).map (MulAut.conj g).toMonoidHom) ∧
  (∀ M : Subgroup (StatedProj (StatedOmega Q0)), IsCoatom M →
    statedProjectiveFlagStabilizer Q0 F ≤ M →
      ∃ i, M = statedProjectiveSubspaceStabilizer Q0 (F i)) ∧
  ∀ W L : Submodule K (ι → K), (∀ x ∈ W, Q0 x = 0) → 2 ≤ finrank K W →
    (∀ x ∈ L, Q0 x = 0) → finrank K L = 1 →
    (statedProjectiveSubspaceStabilizer Q0 L).index <
      (statedProjectiveSubspaceStabilizer Q0 W).index

section Transport

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type}
  [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
  (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

@[expose] def tailOmegaEquiv : StatedOmega Q0 ≃* orthElementaryGroup (quadTail r qA) :=
  (statedOmegaEquiv hQ hE).trans (elementaryIsometryEquiv ψ).symm

theorem tailOmegaEquiv_apply (g : StatedOmega Q0) (x : (Fin r ⊕ Fin r → K) × A) :
    (tailOmegaEquiv ψ hQ hE g).val x = ψ.symm (toLinEquiv ι K g.val (ψ x)) :=
  elementaryIsometryEquiv_symm_apply ψ _ x

theorem tailOmegaEquiv_comp (g : StatedOmega Q0) :
    (tailOmegaEquiv ψ hQ hE g).val.toLinearMap.comp ψ.symm.toLinearMap =
      ψ.symm.toLinearMap.comp (toLinEquiv ι K g.val).toLinearMap :=
  LinearMap.ext fun w => by
    change (tailOmegaEquiv ψ hQ hE g).val (ψ.symm w) = ψ.symm (toLinEquiv ι K g.val w)
    rw [tailOmegaEquiv_apply, ψ.apply_symm_apply]

theorem map_tailOmegaEquiv_iff (g : StatedOmega Q0) (W : Submodule K (ι → K)) :
    (W.map ψ.symm.toLinearMap).map (tailOmegaEquiv ψ hQ hE g).val.toLinearMap =
        W.map ψ.symm.toLinearMap ↔ W.map (toLinEquiv ι K g.val).toLinearMap = W := by
  rw [← Submodule.map_comp, tailOmegaEquiv_comp, Submodule.map_comp]
  exact (Submodule.map_injective_of_injective ψ.symm.toLinearEquiv.injective).eq_iff

theorem tailOmegaEquiv_scalars :
    ((StatedScalars ι K).subgroupOf (StatedOmega Q0)).map (tailOmegaEquiv ψ hQ hE).toMonoidHom =
      elemScalars (quadTail r qA) := by
  have key : ∀ x, (statedOmegaEquiv hQ hE).symm x ∈
      (StatedScalars ι K).subgroupOf (StatedOmega Q0) ↔ x ∈ scalarKernel Q := fun x => by
    rw [← Subgroup.mem_map_equiv, statedActionEquiv_scalarKernel hQ hE]
  ext h
  rw [Subgroup.mem_map_equiv]
  change (statedOmegaEquiv hQ hE).symm (elementaryIsometryEquiv ψ h) ∈ _ ↔ _
  rw [key]
  exact (mem_scalarKernel_isometry_iff ψ h).trans (mem_scalarKernel_iff_elemScalars _ h)

theorem tailOmegaEquiv_subspaceStabilizer (W : Submodule K (ι → K)) :
    (statedDerivedSubspaceStabilizer Q0 W).map (tailOmegaEquiv ψ hQ hE).toMonoidHom =
      MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) (W.map ψ.symm.toLinearMap) := by
  ext h
  obtain ⟨g, rfl⟩ := (tailOmegaEquiv ψ hQ hE).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_stabilizer_iff_map,
    mem_statedDerivedSubspaceStabilizer]
  exact (map_tailOmegaEquiv_iff ψ hQ hE g W).symm

theorem tailOmegaEquiv_flagStabilizer (F : Fin r → Submodule K (ι → K)) :
    (statedDerivedFlagStabilizer Q0 F).map (tailOmegaEquiv ψ hQ hE).toMonoidHom =
      MulAction.stabilizer (orthElementaryGroup (quadTail r qA))
        (fun i => (F i).map ψ.symm.toLinearMap) := by
  ext h
  obtain ⟨g, rfl⟩ := (tailOmegaEquiv ψ hQ hE).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_stabilizer_flag_iff]
  change g ∈ ⨅ i, statedDerivedSubspaceStabilizer Q0 (F i) ↔ _
  rw [Subgroup.mem_iInf]
  exact forall_congr' fun i => by
    rw [mem_statedDerivedSubspaceStabilizer]
    exact (map_tailOmegaEquiv_iff ψ hQ hE g (F i)).symm

@[expose] def tailProjEquiv :
    StatedProj (StatedOmega Q0) ≃*
      (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)) :=
  QuotientGroup.congr _ _ (tailOmegaEquiv ψ hQ hE) (tailOmegaEquiv_scalars ψ hQ hE)

theorem tailProjEquiv_mk (g : StatedOmega Q0) :
    tailProjEquiv ψ hQ hE (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' (elemScalars (quadTail r qA)) (tailOmegaEquiv ψ hQ hE g) :=
  rfl

theorem map_mk_tailProjEquiv (H : Subgroup (StatedOmega Q0)) :
    (H.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q0)))).map
        (tailProjEquiv ψ hQ hE).toMonoidHom =
      (H.map (tailOmegaEquiv ψ hQ hE).toMonoidHom).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
  have h : (tailProjEquiv ψ hQ hE).toMonoidHom.comp
        (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q0))) =
      (QuotientGroup.mk' (elemScalars (quadTail r qA))).comp
        (tailOmegaEquiv ψ hQ hE).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [Subgroup.map_map, h, ← Subgroup.map_map]

theorem tailProjEquiv_subspaceStabilizer (W : Submodule K (ι → K)) :
    (statedProjectiveSubspaceStabilizer Q0 W).map (tailProjEquiv ψ hQ hE).toMonoidHom =
      stabP (quadTail r qA) (W.map ψ.symm.toLinearMap) := by
  rw [← statedDerivedSubspaceStabilizer_map Q0 W, map_mk_tailProjEquiv,
    tailOmegaEquiv_subspaceStabilizer, stabP]

theorem tailProjEquiv_flagStabilizer (F : Fin r → Submodule K (ι → K)) :
    (statedProjectiveFlagStabilizer Q0 F).map (tailProjEquiv ψ hQ hE).toMonoidHom =
      stabFlagP r qA (fun i => (F i).map ψ.symm.toLinearMap) := by
  rw [← statedDerivedFlagStabilizer_map Q0 F, map_mk_tailProjEquiv,
    tailOmegaEquiv_flagStabilizer, stabFlagP]

end Transport

section Coatom

variable {G : Type*} [Group G]

theorem isCoatom_comap_mk {N : Subgroup G} [N.Normal] {M : Subgroup (G ⧸ N)} (hM : IsCoatom M) :
    IsCoatom (M.comap (QuotientGroup.mk' N)) := by
  have hker : (QuotientGroup.mk' N).ker ≤ M.comap (QuotientGroup.mk' N) := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact M.one_mem
  refine ⟨fun h => hM.1 ?_, fun X hX => ?_⟩
  · rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M, h,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  · have hXker : (QuotientGroup.mk' N).ker ≤ X := hker.trans hX.le
    have hle : M ≤ X.map (QuotientGroup.mk' N) := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M]
      exact Subgroup.map_mono hX.le
    rcases hM.le_iff.1 hle with h | h
    · rw [← Subgroup.comap_map_eq_self hXker, h, Subgroup.comap_top]
    · exfalso
      apply hX.ne
      apply le_antisymm hX.le
      rw [← Subgroup.comap_map_eq_self hXker, h]

theorem map_subtype_subgroupOf_eq {E : Subgroup G} (N : Subgroup E) :
    (N.map E.subtype).subgroupOf E = N :=
  Subgroup.ext fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem E.subtype_injective

theorem isMax_map_subtype {E : Subgroup G} {N : Subgroup E} (hN : IsCoatom N) (M' : Subgroup G)
    (h1 : N.map E.subtype ≤ M') (h2 : M' ≤ E) : M' = N.map E.subtype ∨ M' = E := by
  have hle : N ≤ M'.subgroupOf E := fun x hx => by
    rw [Subgroup.mem_subgroupOf]
    exact h1 ⟨x, hx, rfl⟩
  rcases hN.le_iff.1 hle with h | h
  · right
    exact le_antisymm h2 (Subgroup.subgroupOf_eq_top.1 h)
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le h2, h]

end Coatom

section Interface

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type}
  [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
  (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

omit [Fintype ι] [DecidableEq ι] in
theorem map_symm_map_isometry {W : Submodule K ((Fin r ⊕ Fin r → K) × A)} :
    (W.map ψ.toLinearMap).map ψ.symm.toLinearMap = W := by
  rw [← Submodule.map_comp]
  have h : ψ.symm.toLinearMap.comp ψ.toLinearMap = LinearMap.id :=
    LinearMap.ext fun v => ψ.symm_apply_apply v
  rw [h, Submodule.map_id]

omit [Fintype ι] [DecidableEq ι] in
include hQ in
theorem totSing_map_symm {W : Submodule K (ι → K)} (hW : ∀ x ∈ W, Q0 x = 0) :
    ∀ y ∈ W.map ψ.symm.toLinearMap, quadTail r qA y = 0 := by
  rintro _ ⟨x, hx, rfl⟩
  change quadTail r qA (ψ.symm x) = 0
  rw [ψ.symm.map_app, hQ]
  exact hW x hx

include hQ hE in
theorem borelInterface_of_tailIsometry [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hr : 3 ≤ r) (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : finrank K A = 1 ∨ finrank K A = 2) {F : Fin r → Submodule K (ι → K)}
    (hF : ∀ i, F i = (tailFlag K A r (i + 1)).map ψ.toLinearMap) :
    BorelInterface p Q0 F := by
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  have : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  have : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have : Finite A := Module.finite_of_finite K
  have : Finite (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _ =>
      (g : ((Fin r ⊕ Fin r → K) × A) → (Fin r ⊕ Fin r → K) × A)) DFunLike.coe_injective
  have hFi : ∀ i, (F i).map ψ.symm.toLinearMap = tailFlag K A r (i + 1) := fun i => by
    rw [hF, map_symm_map_isometry]
  have hFψ : (fun i => (F i).map ψ.symm.toLinearMap) = stdFlag K A r := funext hFi
  have hB : (statedProjectiveFlagStabilizer Q0 F).map (tailProjEquiv ψ hQ hE).toMonoidHom =
      ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
    rw [tailProjEquiv_flagStabilizer, hFψ, stabFlagP, tailBorel_subgroupOf_eq]
  have hB' : (((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
      (QuotientGroup.mk' (elemScalars (quadTail r qA)))).map
        (tailProjEquiv ψ hQ hE).symm.toMonoidHom = statedProjectiveFlagStabilizer Q0 F := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.map_symm_eq_iff_map_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact hB
  obtain ⟨-, -, ⟨S, hS⟩, hN, -, -⟩ :=
    orthogonal_geometry_tail_Sylow_flag_normalizer (p := p) hr hani hreg hm
  set S' : Sylow p (StatedProj (StatedOmega Q0)) :=
    S.mapSurjective (f := (tailProjEquiv ψ hQ hE).symm.toMonoidHom)
      (tailProjEquiv ψ hQ hE).symm.surjective
  have hBQ : statedProjectiveFlagStabilizer Q0 F =
      Subgroup.normalizer ((S' : Subgroup (StatedProj (StatedOmega Q0))) :
        Set (StatedProj (StatedOmega Q0))) := by
    have hS'eq : (S' : Subgroup (StatedProj (StatedOmega Q0))) =
        (S : Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))).map
          (tailProjEquiv ψ hQ hE).symm.toMonoidHom := rfl
    rw [hS'eq, ← hB', ← hN, ← hS]
    exact Subgroup.map_equiv_normalizer_eq _ _
  refine ⟨fun i => ⟨fun x hx => ?_, ?_⟩, ⟨S', hBQ⟩, fun α => ?_, fun M hM hBM => ?_,
    fun W L hWs hW2 hLs hL1 => ?_⟩
  ·
    rw [hF] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change Q0 (ψ y) = 0
    rw [← hQ, ψ.map_app]
    exact quadTail_eq_zero_of_mem_tailFlag hy
  · rw [hF, LinearEquiv.finrank_map_eq]
    exact finrank_tailFlag (by have := i.isLt; omega)
  ·
    have : Finite (StatedProj (StatedOmega Q0)) :=
      Finite.of_equiv _ (tailProjEquiv ψ hQ hE).symm.toEquiv
    obtain ⟨z, hz⟩ := exists_map_normalizer_conj S' α 1
    refine ⟨z, ?_⟩
    have hid : (MulEquiv.refl (StatedProj (StatedOmega Q0))).toMonoidHom = MonoidHom.id _ := rfl
    rw [hBQ, ← hz, map_one, MulAut.one_def, hid, Subgroup.map_id]
  ·
    set Φ := tailProjEquiv ψ hQ hE with hΦ
    have hM1 : IsCoatom (M.map Φ.toMonoidHom) :=
      (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup Φ) M).2 hM
    have hBM1 : ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) ≤ M.map Φ.toMonoidHom := by
      rw [← hB]
      exact Subgroup.map_mono hBM
    set N := (M.map Φ.toMonoidHom).comap (QuotientGroup.mk' (elemScalars (quadTail r qA)))
      with hNdef
    have hNc : IsCoatom N := isCoatom_comap_mk hM1
    have hBN : (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) ≤ N :=
      fun x hx => hBM1 ⟨x, hx, rfl⟩
    have hsub := map_subtype_subgroupOf_eq N
    have hBE : tailBorel r qA ≤ orthElementaryGroup (quadTail r qA) := inf_le_left
    have hBM'' : tailBorel r qA ≤ N.map (orthElementaryGroup (quadTail r qA)).subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hBE]
      exact Subgroup.map_mono hBN
    have hne : N.map (orthElementaryGroup (quadTail r qA)).subtype ≠
        orthElementaryGroup (quadTail r qA) := fun h => hNc.1 (by
      rw [← hsub, h, Subgroup.subgroupOf_self])
    obtain ⟨k, hk1, hkr, hk⟩ := eq_stabilizer_of_isMax_tail hani ha₀ (Subgroup.map_subtype_le N)
      hBM'' hne (fun M' h1 h2 => isMax_map_subtype hNc M' h1 h2)
    have hNstab : N = MulAction.stabilizer (orthElementaryGroup (quadTail r qA))
        (tailFlag K A r k) := by
      rw [← hsub, hk]
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    have hMbar : M.map Φ.toMonoidHom = stabP (quadTail r qA) (tailFlag K A r k) := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)
        (M.map Φ.toMonoidHom), ← hNdef, hNstab, stabP]
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    apply (MulEquiv.mapSubgroup Φ).injective
    change M.map Φ.toMonoidHom =
      (statedProjectiveSubspaceStabilizer Q0 (F ⟨k - 1, by omega⟩)).map Φ.toMonoidHom
    rw [hMbar, hΦ, tailProjEquiv_subspaceStabilizer, hFi]
    congr 2
    simp only
    omega
  ·
    have hidx : ∀ X : Submodule K (ι → K), (statedProjectiveSubspaceStabilizer Q0 X).index =
        (stabP (quadTail r qA) (X.map ψ.symm.toLinearMap)).index := fun X => by
      rw [← tailProjEquiv_subspaceStabilizer ψ hQ hE X, MulEquiv.toMonoidHom_eq_coe,
        Subgroup.index_map_equiv]
    have hfin : ∀ X : Submodule K (ι → K),
        finrank K (X.map ψ.symm.toLinearMap) = finrank K X := fun X =>
      LinearEquiv.finrank_map_eq ψ.symm.toLinearEquiv X
    rw [hidx, hidx]
    obtain ⟨-, hcmp⟩ := orthogonal_geometry_tail_geometric_stabilizer_indices (by omega : 1 ≤ r)
      hani hreg ⟨a₀, ha₀⟩
    have hWr : finrank K W ≤ r := by
      rw [← hfin]
      exact finrank_le_of_totSing_tail hani (totSing_map_symm ψ hQ hWs)
    exact hcmp hr (finrank K W) hW2 hWr _ ⟨hfin W, totSing_map_symm ψ hQ hWs⟩ _
      ⟨by rw [hfin, hL1], totSing_map_symm ψ hQ hLs⟩

end Interface

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
