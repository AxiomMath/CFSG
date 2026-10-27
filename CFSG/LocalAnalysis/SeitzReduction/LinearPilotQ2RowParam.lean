module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamLift
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImagesConj

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section FromProj

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_proj_of_five_le [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 3 ≤ m)
    (hm5 : 5 ≤ m) (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut m F σ (p y))
    (hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G))
    (h2 : ∀ c y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩ y) =
      LinearFlag.conjAut m F (unitDiagGL (torusBlockUnits ι eN c)) (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  set E := centralizerPerfectCore X with hE
  have : Group.IsPerfect E :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ :=
    UnitaryPilot.exists_surjective_lift_of_ker_le_center' hm (Or.inr hm5) hp hpker
  let ψ₁ : SpecialLinearGroup (Fin m) K →* E :=
    MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      ((blockSpecialLinear (K := K) N).subtype.comp (blockSLEquiv N eN).toMonoidHom)))) E
      (fun x => hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2)))
  have hN1 : Φ₀.comp (SpecialLinearGroup.map ι) = ψ₁ :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, hΦ₀]
      exact (h1 x).symm
  have hN3 : (E.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (SpecialLinearGroup.map σ.toRingHom) :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀,
        LinearFlag.fieldAut_proj]
  have hN2 : ∀ c, (E.normalizerMonoidHom ⟨_, hg c⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
        (unitDiagGL (torusBlockUnits ι eN c))).toMonoidHom := fun c =>
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, h2, hΦ₀, hΦ₀, LinearFlag.conjAut_proj]
  let Φ : blockSpecialLinear (K := F) N →* G :=
    E.subtype.comp (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom)
  have hΦ : ∀ x', Φ (blockSLEquiv N eN x') = (Φ₀ x' : G) := fun x' => by
    change ((Φ₀ ((blockSLEquiv N eN).symm (blockSLEquiv N eN x')) : E) : G) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨⟨Φ, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hs : Function.Surjective (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom) := fun y => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨blockSLEquiv N eN x, by simp⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx' : Φ₀ x' = 1 := by
      apply Subtype.ext
      rw [← hΦ]
      exact hx
    have hz := hker hx'
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := (blockSLEquiv N eN).surjective y
    rw [← map_mul, ← map_mul, hz y']
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx : (⟨SpecialLinearGroup.map ι (blockSLEquiv N eN x' : SpecialLinearGroup (Fin n) K),
        map_ringHom_mem_blockSpecialLinear ι (blockSLEquiv N eN x').2⟩ :
          blockSpecialLinear (K := F) N) = blockSLEquiv N eN (SpecialLinearGroup.map ι x') :=
      Subtype.ext (blockSLEquiv_map ι N eN x').symm
    rw [hx, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) K →* E => (φ x' : G)) hN1
    exact this
  ·
    intro c x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [conjDiag_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) (hN2 c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this.symm
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [mapBlock_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) hN3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this

omit [Field K] in
theorem subsingleton_units_of_natCard_eq_two {R : Type*} [Field R] (hR : Nat.card R = 2) :
    Subsingleton Rˣ :=
  (Nat.card_eq_one_iff_unique.1 (by rw [Nat.card_units, hR])).1

theorem nonempty_fieldNeighbourParam_of_proj_two [Finite G] [Finite F] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm5 : 5 ≤ m)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut m F σ (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  have := subsingleton_units_of_natCard_eq_two hK
  have hc1 : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c = 1 :=
    fun c => Subsingleton.elim _ _
  have hg1 : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) = 1 := fun c => by
    rw [hc1 c, map_one, map_one, map_one, L.coe_one]
  have hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G) := fun c => by
    rw [hg1 c]
    exact one_mem _
  refine nonempty_fieldNeighbourParam_of_proj_of_five_le e t ι σ eN (by omega) hm5 p hp hpker hD h1
    ht h3 hg fun c y => ?_
  have hunits : torusBlockUnits ι eN c = 1 := by
    rw [hc1 c]
    funext a
    simp [torusBlockUnits]
  have hy : (centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩ y = y := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hg1 c, one_mul, inv_one, mul_one]
  rw [hy, hunits, unitDiagGL_one, map_one, MulAut.one_apply]

end FromProj

section One

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_fieldNeighbourParam_of_one {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    {F : Type} [Field F] (ι : K →+* F) {σ : F ≃+* F} (hσι : ∀ c : K, σ (ι c) = ι c)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b)
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e X₀) ({a, b}ᶜ : Finset (Fin n))))
    {a' b' : Fin n} (hab' : a' ≠ b') :
    ∃ Y : Subgroup (LinearFlag.projectiveSL n K), Y ≤ rootSL2 a' b' ∧
      Nat.card Y = Nat.card X₀ ∧
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e Y) ({a', b'}ᶜ : Finset (Fin n))) := by
  obtain ⟨P⟩ := hP
  obtain ⟨ρ, rfl, rfl⟩ := exists_perm_apply_eq_apply_eq hab hab'
  obtain ⟨g, hgd, hgP⟩ := exists_monomial (K := K) ρ
  have hN : (({a, b} : Finset (Fin n))ᶜ).map ρ.toEmbedding = ({ρ a, ρ b} : Finset (Fin n))ᶜ :=
    (Neighbour.index_map ρ (.root a b hab)).symm
  refine ⟨X₀.map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom, ?_, ?_, ?_⟩
  · have h := map_conj_blockSL_of_mul_eq (I := ({a, b} : Finset (Fin n)))
      (J := ({a, b} : Finset (Fin n)).map ρ.toEmbedding) g (hgP _)
    rw [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] at h
    rw [rootSL2, ← h]
    exact map_mono hX₀
  · exact Nat.card_congr (X₀.equivMapOfInjective _ (MulAut.conj _).injective).symm.toEquiv
  · have h := P.conj htC hσι hgd (hgP _)
    rw [← modelToG_map_conj, hN] at h
    exact h

end One

end CFSG.SeitzReduction.LinearPilot
