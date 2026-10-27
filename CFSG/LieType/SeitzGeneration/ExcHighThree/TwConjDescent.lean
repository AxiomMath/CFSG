module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.AnisoE6
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Descent


theorem tw_e6_frobenius_fixed_eq_map {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L]
    [IsAlgClosed L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k L)) := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgΓ, hgF⟩ := hg
    have hfix : Units.map (entrywiseHom Fr) g = g := hgF
    have hΨ : Units.map (entrywiseHom Fr) (e6FixedToF4 L ⟨g, hgΓ⟩) = e6FixedToF4 L ⟨g, hgΓ⟩ := by
      have h := e6FixedToF4_baseChangeGL Fr ⟨g, hgΓ⟩
      have e : (⟨baseChangeGL Fr g, baseChangeGL_mem_twistedFixedGroup Fr hgΓ⟩ :
          twistedFixedGroup TwistTag.E6 L (RingHom.id L)) = ⟨g, hgΓ⟩ := Subtype.ext hfix
      rw [e] at h
      exact h.symm
    obtain ⟨f, hf, hfg⟩ := mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr
      (e6FixedToF4_mem_adjointGroup_all ⟨g, hgΓ⟩) hΨ
    obtain ⟨g', hg'⟩ := e6FixedToF4GroupAll_surjective (K := k) ⟨f, hf⟩
    have hg'f : e6FixedToF4 k g' = f := congrArg Subtype.val hg'
    refine ⟨g', g'.2, ?_⟩
    have h := e6FixedToF4_baseChangeGL (algebraMap k L) g'
    rw [hg'f, hfg] at h
    have hinj := e6FixedToF4GroupAll_injective (K := L)
      (a₁ := ⟨_, baseChangeGL_mem_twistedFixedGroup (algebraMap k L) g'.2⟩) (a₂ := ⟨g, hgΓ⟩)
      (Subtype.ext h)
    exact congrArg Subtype.val hinj
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨baseChangeGL_mem_twistedFixedGroup _ hg,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩

end Descent

section Fixed


theorem tw_mem_range_phiG {q : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ q) {k : Type} [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) (hkq : Nat.card k = q)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (z : twistedE6RootGroup K σ)
    (hz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) ∈
      graphCentralizer TwistTag.E6.tag (AlgebraicClosure K)
        (diagramMap TwistTag.E6 (AlgebraicClosure K))) :
    z ∈ (phiG σ hfix).range := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set zK : ModGL TwistTag.E6.tag K := (z : ModGL TwistTag.E6.tag K) with hzK
  obtain ⟨hzad, hzcent⟩ := Subgroup.mem_inf.1 hz
  have hPL : diagramMap TwistTag.E6 L * baseChangeGL ι zK * (diagramMap TwistTag.E6 L)⁻¹ =
      baseChangeGL ι zK := mem_centralizer_singleton_iff_conj_eq.1 hzcent
  have hPK : diagramMap TwistTag.E6 K * zK * (diagramMap TwistTag.E6 K)⁻¹ = zK := by
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv, baseChangeGL_diagramMap]
    exact hPL
  have hσz : Units.map (entrywiseHom σ.toRingHom) zK = zK := by
    have h1 := twistedE6RootGroup_fix K σ zK z.2
    rw [twistHom_apply] at h1
    have h2 : diagramMap TwistTag.E6 K * Units.map (entrywiseHom σ.toRingHom) zK *
        (diagramMap TwistTag.E6 K)⁻¹ =
        diagramMap TwistTag.E6 K * zK * (diagramMap TwistTag.E6 K)⁻¹ := h1.trans hPK.symm
    exact mul_left_cancel (mul_right_cancel h2)
  have hFrz : Units.map (entrywiseHom Fr) (baseChangeGL ι zK) = baseChangeGL ι zK := by
    change baseChangeGL Fr (baseChangeGL ι zK) = _
    rw [baseChangeGL_baseChangeGL]
    have hcomm : Fr.comp ι = ι.comp σ.toRingHom := by
      ext c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hFr, hσ,
        map_pow]
    rw [hcomm, ← baseChangeGL_baseChangeGL]
    have h3 : baseChangeGL σ.toRingHom zK = zK := hσz
    rw [h3]
  have hzΓ : baseChangeGL ι zK ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine ⟨⟨hzad, ?_⟩, hFrz⟩
    show twistHom TwistTag.E6 L (RingHom.id L) (baseChangeGL ι zK) = baseChangeGL ι zK
    rw [twistHom_id_eq]
    exact hPL
  have hFr' : ∀ c, Fr c = c ^ Nat.card k := fun c => by rw [hkq]; exact hFr c
  rw [tw_e6_frobenius_fixed_eq_map (k := k) (L := L) Fr hFr'] at hzΓ
  obtain ⟨γ, hγ, hγeq⟩ := hzΓ
  have hkL : algebraMap k L = ι.comp (algebraMap k K) := IsScalarTower.algebraMap_eq k K L
  have hγK : baseChangeGL (algebraMap k K) γ = zK := by
    apply baseChangeGL_injective ι
    rw [baseChangeGL_baseChangeGL, ← hkL]
    exact hγeq
  exact ⟨⟨γ, hγ⟩, Subtype.ext hγK⟩

end Fixed

end CFSG.LieType.SeitzGeneration.ExcHighThree
