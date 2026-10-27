module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def blockIsom {s : OGroup Q} (hs : s * s = 1) :
    ((Q.restrict (fixSp s)).prod (Q.restrict (commSp s))).IsometryEquiv Q :=
  { toLinearEquiv := Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) (isCompl_fixSp_commSp hs)
    map_app' := by
      intro x
      change Q ((x.1 : V) + x.2) = Q (x.1 : V) + Q x.2
      rw [QuadraticMap.map_add Q, polar_fixSp_commSp hs x.1.2 x.2.2, add_zero] }

@[expose] noncomputable def blockHom {s : OGroup Q} (hs : s * s = 1) :
    OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s)) →* OGroup Q :=
  (TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)).toMonoidHom.comp
    (QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s)))

theorem blockHom_apply {s : OGroup Q} (hs : s * s = 1)
    (p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s)))
    (w : fixSp s) (u : commSp s) :
    ((blockHom hs p : OGroup Q) : V ≃ₗ[ZMod 3] V) ((w : V) + (u : V)) =
      (((p.1 : fixSp s ≃ₗ[ZMod 3] fixSp s) w : fixSp s) : V) +
        (((p.2 : commSp s ≃ₗ[ZMod 3] commSp s) u : commSp s) : V) := by
  change (TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)
    (QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s)) p) :
      V ≃ₗ[ZMod 3] V) ((w : V) + (u : V)) = _
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
  have hsymm : (blockIsom hs).toLinearEquiv.symm ((w : V) + (u : V)) = (w, u) := by
    rw [LinearEquiv.symm_apply_eq]
    change (w : V) + (u : V) =
      (Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) (isCompl_fixSp_commSp hs)) (w, u)
    rw [Submodule.coe_prodEquivOfIsCompl']
  rw [hsymm, QuadraticMap.orthogonalGroupProd_apply]
  change (Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) (isCompl_fixSp_commSp hs))
    (((p.1 : fixSp s ≃ₗ[ZMod 3] fixSp s) w), ((p.2 : commSp s ≃ₗ[ZMod 3] commSp s) u)) = _
  rw [Submodule.coe_prodEquivOfIsCompl']

theorem exists_fixSp_add_commSp {s : OGroup Q} (hs : s * s = 1) (v : V) :
    ∃ (w : fixSp s) (u : commSp s), v = (w : V) + (u : V) := by
  have h : v ∈ fixSp s ⊔ commSp s := by
    rw [(isCompl_fixSp_commSp hs).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp h
  exact ⟨⟨w, hw⟩, ⟨u, hu⟩, rfl⟩

theorem blockHom_injective {s : OGroup Q} (hs : s * s = 1) : Function.Injective (blockHom hs) := by
  intro a b h
  exact QuadraticMap.orthogonalGroupProd_injective _ _
    ((TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)).injective h)

theorem range_blockHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    (blockHom hs).range = Subgroup.centralizer ({s} : Set (OGroup Q)) := by
  classical
  have hcompl : IsCompl (fixSp s) (commSp s) := isCompl_fixSp_commSp hs
  apply le_antisymm
  · rintro y hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [mem_centralizer_iff_map_commSp hQ hs]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro x ⟨n, hn, rfl⟩
      have hmem := blockHom_apply hs p 0 ⟨n, hn⟩
      rw [Submodule.coe_zero, zero_add, map_zero, Submodule.coe_zero, zero_add] at hmem
      show ((blockHom hs p : OGroup Q) : V ≃ₗ[ZMod 3] V) n ∈ commSp s
      rw [show ((⟨n, hn⟩ : commSp s) : V) = n from rfl] at hmem
      rw [hmem]
      exact ((p.2 : commSp s ≃ₗ[ZMod 3] commSp s) ⟨n, hn⟩).2
    · rw [LinearEquiv.finrank_map_eq]
  · intro g hg
    have hgN : (commSp s).map (g : V →ₗ[ZMod 3] V) = commSp s :=
      (mem_centralizer_iff_map_commSp hQ hs g).mp hg
    have hgs : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgCl : (fixSp s).map (g : V →ₗ[ZMod 3] V) ≤ fixSp s := by
      rintro x ⟨c, hc, rfl⟩
      rw [mem_fixSp_iff]
      have hgsL : (g : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) =
          (s : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) := by
        have h' := congrArg (fun u : OGroup Q => (u : V ≃ₗ[ZMod 3] V)) hgs
        simpa only [Subgroup.coe_mul] using h'
      calc (s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) c)
          = ((s : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V)) c :=
            (LinearEquiv.mul_apply _ _ _).symm
        _ = ((g : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V)) c := by rw [hgsL]
        _ = (g : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) c) :=
            LinearEquiv.mul_apply _ _ _
        _ = (g : V ≃ₗ[ZMod 3] V) c := by rw [mem_fixSp_iff.mp hc]
    have hgC : (fixSp s).map (g : V →ₗ[ZMod 3] V) = fixSp s :=
      Submodule.eq_of_le_of_finrank_eq hgCl (by rw [LinearEquiv.finrank_map_eq])
    have hg' : (TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)).symm g ∈
        (QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s))
          (Q.restrict (commSp s))).range := by
      rw [QuadraticMap.mem_range_orthogonalGroupProd_iff]
      constructor
      · intro m₁
        rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply]
        have hd : (blockIsom hs).toLinearEquiv (m₁, 0) = (m₁ : V) := by
          change (Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) hcompl) (m₁, 0) = (m₁ : V)
          rw [Submodule.coe_prodEquivOfIsCompl']
          simp
        rw [hd]
        have hmem : (g : V ≃ₗ[ZMod 3] V) (m₁ : V) ∈ fixSp s := by
          have h1 : (g : V ≃ₗ[ZMod 3] V) (m₁ : V) ∈ (fixSp s).map (g : V →ₗ[ZMod 3] V) :=
            Submodule.mem_map_of_mem m₁.2
          rwa [hgC] at h1
        change ((Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) hcompl).symm
          ((g : V ≃ₗ[ZMod 3] V) (m₁ : V))).2 = 0
        exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (fixSp s) (commSp s)
          hcompl).mpr hmem
      · intro m₂
        rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply]
        have hd : (blockIsom hs).toLinearEquiv (0, m₂) = (m₂ : V) := by
          change (Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) hcompl) (0, m₂) = (m₂ : V)
          rw [Submodule.coe_prodEquivOfIsCompl']
          simp
        rw [hd]
        have hmem : (g : V ≃ₗ[ZMod 3] V) (m₂ : V) ∈ commSp s := by
          have h1 : (g : V ≃ₗ[ZMod 3] V) (m₂ : V) ∈ (commSp s).map (g : V →ₗ[ZMod 3] V) :=
            Submodule.mem_map_of_mem m₂.2
          rwa [hgN] at h1
        change ((Submodule.prodEquivOfIsCompl (fixSp s) (commSp s) hcompl).symm
          ((g : V ≃ₗ[ZMod 3] V) (m₂ : V))).1 = 0
        exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero (fixSp s) (commSp s)
          hcompl).mpr hmem
    obtain ⟨p, hp⟩ := hg'
    refine ⟨p, ?_⟩
    change TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)
      ((QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s))) p) = g
    rw [hp]
    exact (TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)).apply_symm_apply g

theorem blockHom_one_piOrth {s : OGroup Q} (hs : s * s = 1) :
    blockHom hs (1, piOrth (Q.restrict (commSp s))) = s := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, u, rfl⟩ := exists_fixSp_add_commSp hs v
  rw [blockHom_apply hs]
  have h1 : (s : V ≃ₗ[ZMod 3] V) (w : V) = w := mem_fixSp_iff.mp w.2
  have h2 : (s : V ≃ₗ[ZMod 3] V) (u : V) = -u := (mem_commSp_iff hs).mp u.2
  rw [map_add, h1, h2]
  have h3 : (((piOrth (Q.restrict (commSp s)) : OGroup (Q.restrict (commSp s))) :
      commSp s ≃ₗ[ZMod 3] commSp s) u : V) = -(u : V) := by
    rw [coe_piOrth_apply]
    rfl
  rw [h3]
  rfl

theorem blockHom_piOrth_piOrth {s : OGroup Q} (hs : s * s = 1) :
    blockHom hs (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) = piOrth Q := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, u, rfl⟩ := exists_fixSp_add_commSp hs v
  rw [blockHom_apply hs]
  have h1 : (((piOrth (Q.restrict (fixSp s)) : OGroup (Q.restrict (fixSp s))) :
      fixSp s ≃ₗ[ZMod 3] fixSp s) w : V) = -(w : V) := by
    rw [coe_piOrth_apply]
    rfl
  have h2 : (((piOrth (Q.restrict (commSp s)) : OGroup (Q.restrict (commSp s))) :
      commSp s ≃ₗ[ZMod 3] commSp s) u : V) = -(u : V) := by
    rw [coe_piOrth_apply]
    rfl
  rw [h1, h2, coe_piOrth_apply, neg_add]

theorem orthogonalDet_blockHom {s : OGroup Q} (hs : s * s = 1)
    (p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))) :
    QuadraticMap.orthogonalDet Q (blockHom hs p) =
      QuadraticMap.orthogonalDet (Q.restrict (fixSp s)) p.1 *
        QuadraticMap.orthogonalDet (Q.restrict (commSp s)) p.2 := by
  rw [QuadraticMap.orthogonalDet_apply, QuadraticMap.orthogonalDet_apply,
    QuadraticMap.orthogonalDet_apply]
  have hconj : ((blockHom hs p : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((blockIsom hs).toLinearEquiv.symm.trans
        (QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s)) p :
          (fixSp s × commSp s) ≃ₗ[ZMod 3] (fixSp s × commSp s))).trans
        (blockIsom hs).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change (TauCeti.QuadraticMap.orthogonalGroupCongr (blockIsom hs)
      (QuadraticMap.orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s)) p) :
        V ≃ₗ[ZMod 3] V) v = _
    rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
    rfl
  rw [hconj, LinearEquiv.det_conj]
  exact QuadraticMap.det_orthogonalGroupProd (Q.restrict (fixSp s)) (Q.restrict (commSp s)) p

theorem mul_self_mem_omegaGroup (hQ : Q.Nondegenerate) (g : OGroup Q) :
    g * g ∈ omegaGroup hQ := by
  rw [mem_omegaGroup_iff hQ, map_mul]
  generalize CFSG.ClassicalInvolution.detSpinorNorm hQ g = z
  obtain ⟨u, y⟩ := z
  refine Prod.ext ?_ ?_
  · change u * u = 1
    revert u
    decide
  · change y * y = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem blockHom_left_mem_omegaGroup (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp s)) {a : OGroup (Q.restrict (fixSp s))}
    (ha : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :
    blockHom hs (a, 1) ∈ omegaGroup hQ := by
  rw [omegaGroup_eq_commutator (nondegenerate_restrict_fixSp hQ hs) hW] at ha
  have hmap : (blockHom hs).comp (MonoidHom.inl _ _) a ∈
      (commutator (OGroup (Q.restrict (fixSp s)))).map
        ((blockHom hs).comp (MonoidHom.inl _ (OGroup (Q.restrict (commSp s))))) :=
    Subgroup.mem_map_of_mem _ ha
  rw [commutator, Subgroup.map_commutator] at hmap
  exact commutator_le_omegaGroup hQ (Subgroup.commutator_mono le_top le_top hmap)

theorem blockHom_right_mem_omegaGroup (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) {b : OGroup (Q.restrict (commSp s))}
    (hb : b ∈ omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    blockHom hs (1, b) ∈ omegaGroup hQ := by
  rw [omegaGroup_eq_commutator (nondegenerate_restrict_commSp hQ hs) hU] at hb
  have hmap : (blockHom hs).comp (MonoidHom.inr _ _) b ∈
      (commutator (OGroup (Q.restrict (commSp s)))).map
        ((blockHom hs).comp (MonoidHom.inr (OGroup (Q.restrict (fixSp s))) _)) :=
    Subgroup.mem_map_of_mem _ hb
  rw [commutator, Subgroup.map_commutator] at hmap
  exact commutator_le_omegaGroup hQ (Subgroup.commutator_mono le_top le_top hmap)

@[expose] noncomputable def blockOmega (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    Subgroup (OGroup Q) :=
  (Subgroup.prod (omegaGroup (nondegenerate_restrict_fixSp hQ hs))
    (omegaGroup (nondegenerate_restrict_commSp hQ hs))).map (blockHom hs)

theorem mul_self_mem_blockOmega (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {g : OGroup Q} (hg : g ∈ Subgroup.centralizer ({s} : Set (OGroup Q))) :
    g * g ∈ blockOmega hQ hs := by
  rw [← range_blockHom hQ hs] at hg
  obtain ⟨p, rfl⟩ := hg
  refine Subgroup.mem_map.mpr ⟨p * p, ?_, map_mul _ p p⟩
  exact ⟨mul_self_mem_omegaGroup _ p.1, mul_self_mem_omegaGroup _ p.2⟩

theorem blockOmega_normal_in_centralizer (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    ((blockOmega hQ hs).subgroupOf (Subgroup.centralizer ({s} : Set (OGroup Q)))).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
  have hg : (g : OGroup Q) ∈ (blockHom hs).range := by
    rw [range_blockHom hQ hs]
    exact g.2
  obtain ⟨p, hp⟩ := hg
  refine Subgroup.mem_map.mpr ⟨p * q * p⁻¹, ?_, ?_⟩
  · haveI : (Subgroup.prod (omegaGroup (nondegenerate_restrict_fixSp hQ hs))
        (omegaGroup (nondegenerate_restrict_commSp hQ hs))).Normal := inferInstance
    exact this.conj_mem q hq p
  · rw [map_mul, map_mul, map_inv, hqx, hp]
    rfl

end CFSG.OddStandard.SmallF3.Omega
