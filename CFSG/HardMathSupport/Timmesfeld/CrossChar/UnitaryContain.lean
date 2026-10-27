module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem apply_eq_of_mem_specialBlock_X_sub_one {x g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ specialBlock B x (X - C 1)) :
    ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v := by
  intro b hb hb1 v hv
  refine (mem_specialBlock.mp hg).1.2 b hb ?_ v hv
  rintro (h1 | h1)
  · exact hb1 h1
  · rw [Set.mem_singleton_iff, dualPoly_X_sub_C_one] at h1
    exact hb1 h1

theorem det_eq_one_of_mem_specialBlock_X_sub_one {x : LinearMap.GeneralLinearGroup K V}
    (H : UnitaryPrimaryData hK.bar B x)
    (ha : (X - C 1 : K[X]) ∈ primaryFactors (x : Module.End K V))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ specialBlock B x (X - C 1)) :
    LinearMap.det (g : Module.End K V) = 1 := by
  have : Fact (Irreducible (X - C 1 : K[X])) := ⟨irreducible_X_sub_C 1⟩
  obtain ⟨-, hgc, hdet⟩ := mem_specialBlock.mp hg
  have hcomm : Commute (g : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hgc
  set γ := (blockRestrict x (X - C 1) ⟨g, hgc⟩).val with hγ
  have hres : γ.restrictScalars K = (g : Module.End K V).restrict
      (fun _ hv => apply_mem_primaryComponent hcomm hv) := by
    ext v
    rfl
  have h1 := det_restrictScalars_blockGL (x := (x : Module.End K V)) (X - C 1) γ
  rw [hres, ← det_eq_det_restrict_of_trivial_off H.squarefree ha hcomm
    (apply_eq_of_mem_specialBlock_X_sub_one hg)] at h1
  have hγ1 : LinearMap.det γ = 1 := by
    have := congrArg Units.val hdet
    simpa [blockDetHom, blockGLDet] using this
  rw [h1, hγ1, map_one]

theorem specialBlock_X_sub_one_le {x t : LinearMap.GeneralLinearGroup K V}
    (H : UnitaryPrimaryData hK.bar B x) (Ht : UnitaryPrimaryData hK.bar B t)
    (hxt : Commute (x : Module.End K V) (t : Module.End K V))
    (hfix : ∀ v : V, (x : Module.End K V) v = v → (t : Module.End K V) v = v)
    (hx1 : (X - C 1 : K[X]) ∈ primaryFactors (x : Module.End K V))
    (ht1 : (X - C 1 : K[X]) ∈ primaryFactors (t : Module.End K V)) :
    specialBlock B x (X - C 1) ≤ specialBlock B t (X - C 1) := by
  classical
  have : Fact (Irreducible (X - C 1 : K[X])) := ⟨irreducible_X_sub_C 1⟩
  intro g hg
  have hdet1 := det_eq_one_of_mem_specialBlock_X_sub_one H hx1 hg
  obtain ⟨hof, hgc, -⟩ := mem_specialBlock.mp hg
  have hgU : g ∈ sesqUnitaryGroup B := (mem_unitaryCentralizer.mp hof.1).1
  have hgx : Commute (g : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hgc
  have hoffx := apply_eq_of_mem_specialBlock_X_sub_one hg
  have hfixv : ∀ {c : K[X]} {v : V}, c = X - C 1 → v ∈ primaryComponent (x : Module.End K V) c →
      (x : Module.End K V) v = v := by
    rintro c v rfl hv
    simpa using mem_primaryComponent_X_sub_C.mp hv
  have hgt : Commute (g : Module.End K V) (t : Module.End K V) := by
    refine ext_primaryComponent H.squarefree fun c hc v hv => ?_
    simp only [Module.End.mul_apply]
    by_cases hc1 : c = X - C 1
    · have hgv : (g : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
        apply_mem_primaryComponent hgx hv
      rw [hfix v (hfixv hc1 hv), hfix _ (hfixv hc1 hgv)]
    · have htv : (t : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
        apply_mem_primaryComponent hxt.symm hv
      rw [hoffx c hc hc1 _ htv, hoffx c hc hc1 v hv]
  have hofft : ∀ b ∈ primaryFactors (t : Module.End K V), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (t : Module.End K V) b, (g : Module.End K V) v = v := by
    intro b hb hb1 v hv
    have hsum := LinearMap.congr_fun (sum_primaryProjection H.squarefree) v
    rw [LinearMap.sum_apply, Module.End.one_apply] at hsum
    have hterm : ∀ c ∈ primaryFactors (x : Module.End K V),
        (g : Module.End K V) (primaryProjection (x : Module.End K V) c v) =
          primaryProjection (x : Module.End K V) c v := by
      intro c hc
      by_cases hc1 : c = X - C 1
      · have hPx := primaryProjection_mem H.squarefree hc v
        have hcomm : Commute (t : Module.End K V) (primaryProjection (x : Module.End K V) c) :=
          commute_aeval hxt.symm _
        have hPb : primaryProjection (x : Module.End K V) c v ∈
            primaryComponent (t : Module.End K V) b := apply_mem_primaryComponent hcomm.symm hv
        have hPt : primaryProjection (x : Module.End K V) c v ∈
            primaryComponent (t : Module.End K V) (X - C 1) := by
          rw [mem_primaryComponent_X_sub_C, one_smul]
          exact hfix _ (hfixv hc1 hPx)
        have h0 : primaryProjection (x : Module.End K V) c v = 0 := by
          rw [← primaryProjection_of_mem Ht.squarefree hb hPb]
          exact primaryProjection_of_mem_ne Ht.squarefree hb ht1 (Ne.symm hb1) hPt
        rw [h0, map_zero]
      · exact hoffx c hc hc1 _ (primaryProjection_mem H.squarefree hc v)
    calc (g : Module.End K V) v
        = (g : Module.End K V) (∑ c ∈ primaryFactors (x : Module.End K V),
            primaryProjection (x : Module.End K V) c v) := by rw [hsum]
      _ = ∑ c ∈ primaryFactors (x : Module.End K V),
            (g : Module.End K V) (primaryProjection (x : Module.End K V) c v) := map_sum _ _ _
      _ = ∑ c ∈ primaryFactors (x : Module.End K V),
            primaryProjection (x : Module.End K V) c v := Finset.sum_congr rfl hterm
      _ = v := hsum
  have hgct : g ∈ gl_centralizer t := mem_gl_centralizer.mpr hgt
  refine mem_specialBlock.mpr ⟨⟨mem_unitaryCentralizer.mpr ⟨hgU, hgt⟩,
    fun b hb hbS v hv => hofft b hb (fun h1 => hbS (Or.inl h1)) v hv⟩, hgct, ?_⟩
  apply Units.ext
  rw [blockDetHom, MonoidHom.comp_apply, blockGLDet, Units.coe_map]
  set γ := (blockRestrict t (X - C 1) ⟨g, hgct⟩).val with hγ
  have hres : γ.restrictScalars K = (g : Module.End K V).restrict
      (fun _ hv => apply_mem_primaryComponent hgt hv) := by
    ext v
    rfl
  have h1 := det_restrictScalars_blockGL (x := (t : Module.End K V)) (X - C 1) γ
  rw [hres, ← det_eq_det_restrict_of_trivial_off Ht.squarefree ht1 hgt hofft, hdet1] at h1
  have h2 := eq_one_of_norm_eq_one (LinearMap.det γ) h1.symm
  rw [h2]
  rfl

end CFSG.HardMathSupport.Timmesfeld.CrossChar
