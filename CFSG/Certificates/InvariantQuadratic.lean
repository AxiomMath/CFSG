module

public import CFSG.Certificates.PolarScalar
public import Mathlib.LinearAlgebra.Determinant

public noncomputable section

namespace CFSG.Certificates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem glPullback_inv_glPullback (g : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    glPullback g⁻¹ (glPullback g q) = q := by
  rw [← glPullback_mul, inv_mul_cancel, glPullback_one]

theorem glPullback_glPullback_inv (g : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    glPullback g (glPullback g⁻¹ q) = q := by
  rw [← glPullback_mul, mul_inv_cancel, glPullback_one]

theorem glPullback_injective (g : LinearMap.GeneralLinearGroup K V) :
    Function.Injective (glPullback g : (V → K) → V → K) := fun q q' h => by
  rw [← glPullback_inv_glPullback g q, h, glPullback_inv_glPullback]

@[expose] def glPullbackStabilizer (X : Set (V → K)) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∀ q, glPullback g q ∈ X ↔ q ∈ X}
  mul_mem' {g h} hg hh q := by
    rw [Set.mem_ofPred_eq] at hg hh
    rw [glPullback_mul, hg, hh]
  one_mem' q := by rw [glPullback_one]
  inv_mem' {g} hg q := by
    rw [Set.mem_ofPred_eq] at hg
    rw [← hg, glPullback_glPullback_inv]

theorem mem_glPullbackStabilizer_of_mapsTo {X : Set (V → K)} (hX : X.Finite)
    {g : LinearMap.GeneralLinearGroup K V} (hg : ∀ q ∈ X, glPullback g q ∈ X) :
    g ∈ glPullbackStabilizer X := by
  intro q
  refine ⟨fun hq => ?_, hg q⟩
  have : Finite X := hX.to_subtype
  let f : X → X := fun p => ⟨glPullback g p, hg p p.2⟩
  have hinj : Function.Injective f := fun p p' h =>
    Subtype.ext (glPullback_injective g (congrArg Subtype.val h))
  obtain ⟨p, hp⟩ := Finite.surjective_of_injective hinj ⟨glPullback g q, hq⟩
  rw [← glPullback_injective g (congrArg Subtype.val hp)]
  exact p.2

theorem generated_pullback_mapsTo {ι : Type*} (A : ι → LinearMap.GeneralLinearGroup K V)
    {X : Set (V → K)} (hX : X.Finite) (hAX : ∀ i, ∀ q ∈ X, glPullback (A i) q ∈ X) :
    ∀ g ∈ Subgroup.closure (Set.range A), ∀ q ∈ X, glPullback g q ∈ X := by
  have hle : Subgroup.closure (Set.range A) ≤ glPullbackStabilizer X :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact mem_glPullbackStabilizer_of_mapsTo hX (hAX i))
  exact fun g hg q hq => (hle hg q).2 hq

@[expose] def glFormPreserving (B : LinearMap.BilinForm K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∀ u w, B ((g : V →ₗ[K] V) u) ((g : V →ₗ[K] V) w) = B u w}
  mul_mem' {g h} hg hh u w := by
    change B ((g : V →ₗ[K] V) ((h : V →ₗ[K] V) u)) ((g : V →ₗ[K] V) ((h : V →ₗ[K] V) w)) = _
    rw [hg, hh]
  one_mem' _ _ := rfl
  inv_mem' {g} hg u w := by
    have h := hg (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u)
      (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) w)
    rw [gl_apply_inv_apply, gl_apply_inv_apply] at h
    exact h.symm

@[expose] def glDetOne : Subgroup (LinearMap.GeneralLinearGroup K V) :=
  (LinearMap.det.comp (Units.coeHom (V →ₗ[K] V))).ker

theorem mem_glDetOne (g : LinearMap.GeneralLinearGroup K V) :
    g ∈ (glDetOne : Subgroup (LinearMap.GeneralLinearGroup K V)) ↔
      LinearMap.det (g : V →ₗ[K] V) = 1 :=
  MonoidHom.mem_ker

theorem pullbackPerm_range_closure {ι : Type*} (A : ι → LinearMap.GeneralLinearGroup K V)
    (X : Set (V → K))
    (hX : ∀ g ∈ Subgroup.closure (Set.range A), ∀ q ∈ X, glPullback g q ∈ X) :
    (pullbackPerm (Subgroup.closure (Set.range A)) X hX).range =
      Subgroup.closure (Set.range fun i =>
        pullbackPerm (Subgroup.closure (Set.range A)) X hX
          ⟨A i, Subgroup.subset_closure ⟨i, rfl⟩⟩) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := Set.range A),
    MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, ⟨i, hi⟩, rfl⟩
    exact ⟨i, congrArg _ (Subtype.ext hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨A i, Subgroup.subset_closure ⟨i, rfl⟩⟩, ⟨i, rfl⟩, rfl⟩

theorem invariant_quadratic_determinant_faithful_action [FiniteDimensional K V]
    (hroot : ∀ c : K, c ^ Module.finrank K V = 1 → c = 1)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (X : Set (V → K)) (hXfin : X.Finite) (β : (V → K) → LinearMap.BilinForm K V)
    (hβ : ∀ q ∈ X, ∀ u w, β q u w = q (u + w) - q u - q w)
    {ι : Type*} (A : ι → LinearMap.GeneralLinearGroup K V)
    (hdet : ∀ i, LinearMap.det (A i : V →ₗ[K] V) = 1)
    (hAB : ∀ i u w, B ((A i : V →ₗ[K] V) u) ((A i : V →ₗ[K] V) w) = B u w)
    (hAX : ∀ i, ∀ q ∈ X, glPullback (A i) q ∈ X)
    (S : Set (V → K)) (hSX : S ⊆ X) (T : (V → K) → Module.End K V)
    (hT : ∀ q ∈ S, ∀ u w, B u (T q w) = β q u w)
    (hcent : {M : Module.End K V | ∀ q ∈ S, M * T q = T q * M} =
      Set.range fun c : K => c • (LinearMap.id : V →ₗ[K] V)) :
    (∀ g ∈ Subgroup.closure (Set.range A), ∀ q ∈ X, glPullback g q ∈ X) ∧
    ∀ hX : ∀ g ∈ Subgroup.closure (Set.range A), ∀ q ∈ X, glPullback g q ∈ X,
      Function.Injective (pullbackPerm (Subgroup.closure (Set.range A)) X hX) ∧
      (pullbackPerm (Subgroup.closure (Set.range A)) X hX).range =
        Subgroup.closure (Set.range fun i =>
          pullbackPerm (Subgroup.closure (Set.range A)) X hX
            ⟨A i, Subgroup.subset_closure ⟨i, rfl⟩⟩) := by
  have hGB : Subgroup.closure (Set.range A) ≤ glFormPreserving B :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact hAB i)
  have hGdet : Subgroup.closure (Set.range A) ≤ glDetOne :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact (mem_glDetOne _).2 (hdet i))
  refine ⟨generated_pullback_mapsTo A hXfin hAX, fun hX => ⟨?_, pullbackPerm_range_closure A X hX⟩⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => Subtype.ext ?_
  have hfix : ∀ q ∈ X, glPullback (g : LinearMap.GeneralLinearGroup K V) q = q := fun q hq =>
    congrArg Subtype.val (Equiv.ext_iff.1 hg ⟨q, hq⟩)
  obtain ⟨c, hc⟩ := eq_smul_id_of_pullback_eq (ι := S) hB (hGB g.2)
    (q := fun s => s.1) (β := fun s => β s.1) (fun s => hβ s.1 (hSX s.2))
    (T := fun s => T s.1) (fun s => hT s.1 s.2)
    (by rw [← hcent]; ext M; simp)
    (fun s => hfix s.1 (hSX s.2))
  have hdetg := (mem_glDetOne _).1 (hGdet g.2)
  rw [hc, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdetg
  rw [hroot c hdetg, one_smul] at hc
  exact Units.ext hc

end CFSG.Certificates
