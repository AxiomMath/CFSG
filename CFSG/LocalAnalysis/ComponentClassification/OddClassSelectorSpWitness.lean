module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBConjugation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def planeMap (B : BilinForm K V) (u₁ u₂ : V) : V →ₗ[K] V :=
  LinearMap.id - (2 : K) • ((B.flip u₂).smulRight u₁ - (B.flip u₁).smulRight u₂)

theorem planeMap_apply (B : BilinForm K V) (u₁ u₂ x : V) :
    planeMap B u₁ u₂ x = x - (2 : K) • (B x u₂ • u₁ - B x u₁ • u₂) := by
  simp [planeMap]

variable {B : BilinForm K V}

theorem planeMap_involutive (hB : B.IsAlt) {u₁ u₂ : V} (h12 : B u₁ u₂ = 1) :
    Function.Involutive (planeMap B u₁ u₂) := by
  intro x
  have h21 : B u₂ u₁ = -1 := by rw [← hB.neg_eq, h12]
  rw [planeMap_apply, planeMap_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero, h12, h21]
  module

@[expose] def planeInvolution (hB : B.IsAlt) {u₁ u₂ : V} (h12 : B u₁ u₂ = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (planeMap B u₁ u₂) (planeMap_involutive hB h12)

theorem planeInvolution_apply (hB : B.IsAlt) {u₁ u₂ : V} (h12 : B u₁ u₂ = 1) (x : V) :
    planeInvolution hB h12 x = x - (2 : K) • (B x u₂ • u₁ - B x u₁ • u₂) :=
  planeMap_apply B u₁ u₂ x

theorem planeInvolution_mem (hB : B.IsAlt) {u₁ u₂ : V} (h12 : B u₁ u₂ = 1) :
    planeInvolution hB h12 ∈ isometryGroup B := by
  rw [mem_isometryGroup_iff]
  intro x y
  have h21 : B u₂ u₁ = -1 := by rw [← hB.neg_eq, h12]
  have h1y : B u₁ y = -B y u₁ := by rw [hB.neg_eq]
  have h2y : B u₂ y = -B y u₂ := by rw [hB.neg_eq]
  rw [planeInvolution_apply, planeInvolution_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero, h12, h21, h1y, h2y]
  ring

@[expose] def sympTransvectionEquiv (hB : B.IsAlt) (w : V) : V ≃ₗ[K] V :=
  LinearEquiv.transvection (show (B.flip w) w = 0 from hB w)

theorem sympTransvectionEquiv_apply (hB : B.IsAlt) (w x : V) :
    sympTransvectionEquiv hB w x = x + B x w • w :=
  rfl

@[expose] def sympTransvection (hB : B.IsAlt) (w : V) : isometryGroup B :=
  ⟨sympTransvectionEquiv hB w, by
    rw [mem_isometryGroup_iff]
    intro x y
    rw [sympTransvectionEquiv_apply, sympTransvectionEquiv_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero]
    rw [← hB.neg_eq w y]
    ring⟩

theorem sympTransvection_apply (hB : B.IsAlt) (w x : V) :
    ((sympTransvection hB w : isometryGroup B) : V ≃ₗ[K] V) x = x + B x w • w :=
  rfl

theorem fixes_of_witness (h2 : (2 : K) ≠ 0) (hB : B.IsAlt) {u₁ u₂ f f' m : V}
    (h12 : B u₁ u₂ = 1) (hff : B f f' = 1) (h1f : B u₁ f = 0) (h2f : B u₂ f = 0)
    (h1m : B u₁ m = 0) (h2m : B u₂ m = 0) (hf'm : B f' m = 0) {Y : Subgroup (isometryGroup B)}
    (hY : ∀ y ∈ Y, (y : V ≃ₗ[K] V) u₁ = u₁ ∧ (y : V ≃ₗ[K] V) u₂ = u₂ ∧
      (y : V ≃ₗ[K] V) f = f ∧ (y : V ≃ₗ[K] V) f' = f')
    (hN : ∀ t s : isometryGroup B, t * t ∈ scalarSigns B → t ∉ scalarSigns B →
      (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set (isometryGroup B))) :
    ∀ y ∈ Y, (y : V ≃ₗ[K] V) m = m := by
  intro y hy
  have h21 : B u₂ u₁ = -1 := by rw [← hB.neg_eq, h12]
  have hf'f : B f' f = -1 := by rw [← hB.neg_eq, hff]
  have hf1 : B f u₁ = 0 := by rw [← hB.neg_eq, h1f, neg_zero]
  have hf2 : B f u₂ = 0 := by rw [← hB.neg_eq, h2f, neg_zero]
  have hm1 : B m u₁ = 0 := by rw [← hB.neg_eq, h1m, neg_zero]
  have hm2 : B m u₂ = 0 := by rw [← hB.neg_eq, h2m, neg_zero]
  have hmf' : B m f' = 0 := by rw [← hB.neg_eq, hf'm, neg_zero]
  have hu0 : u₁ ≠ 0 := fun h => by rw [h, LinearMap.map_zero₂] at h12; exact zero_ne_one h12
  have hf0 : f ≠ 0 := fun h => by rw [h, LinearMap.map_zero₂] at hff; exact zero_ne_one hff
  set t : isometryGroup B := ⟨planeInvolution hB h12, planeInvolution_mem hB h12⟩ with htdef
  have hta : ∀ x, (t : V ≃ₗ[K] V) x = x - (2 : K) • (B x u₂ • u₁ - B x u₁ • u₂) :=
    planeInvolution_apply hB h12
  set w := m + f with hw
  set s := sympTransvection hB w with hsdef
  have hsa : ∀ x, (s : V ≃ₗ[K] V) x = x + B x w • w := sympTransvection_apply hB w
  have htt : t * t ∈ scalarSigns B := by
    left
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact planeMap_involutive hB h12 x
  have htZ : t ∉ scalarSigns B := by
    rintro (h | h)
    · have h1 := congrArg (fun g : isometryGroup B => (g : V ≃ₗ[K] V) u₁) h
      simp only [hta, hB.self_eq_zero, h12, one_smul, zero_smul, sub_zero] at h1
      change u₁ - (2 : K) • u₁ = u₁ at h1
      apply hu0
      have h3 : (2 : K) • u₁ = 0 := by
        rw [sub_eq_self] at h1
        exact h1
      exact (smul_eq_zero.mp h3).resolve_left h2
    · have h1 := congrArg (fun g : isometryGroup B => (g : V ≃ₗ[K] V) f) h
      simp only [hta, hf1, hf2, zero_smul, sub_self, smul_zero, sub_zero] at h1
      change f = -f at h1
      apply hf0
      have h3 : (2 : K) • f = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h1]
        exact neg_add_cancel f
      exact (smul_eq_zero.mp h3).resolve_left h2
  have htY : ∀ z ∈ Y, z * t = t * z := by
    intro z hz
    obtain ⟨hz1, hz2, -, -⟩ := hY z hz
    have hiso := (mem_isometryGroup_iff B (z : V ≃ₗ[K] V)).mp z.2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (z : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) x) = (t : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) x)
    rw [hta, hta, map_sub, map_smul, map_sub, map_smul, map_smul, hz1, hz2]
    have e1 : B ((z : V ≃ₗ[K] V) x) u₂ = B x u₂ := by rw [← hiso x u₂, hz2]
    have e2 : B ((z : V ≃ₗ[K] V) x) u₁ = B x u₁ := by rw [← hiso x u₁, hz1]
    rw [e1, e2]
  have hw1 : B w u₁ = 0 := by rw [hw, LinearMap.map_add₂, hm1, hf1, add_zero]
  have hw2 : B w u₂ = 0 := by rw [hw, LinearMap.map_add₂, hm2, hf2, add_zero]
  have h1w : B u₁ w = 0 := by rw [hw, map_add, h1m, h1f, add_zero]
  have h2w : B u₂ w = 0 := by rw [hw, map_add, h2m, h2f, add_zero]
  have hst : s * t = t * s := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (s : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) x) = (t : V ≃ₗ[K] V) ((s : V ≃ₗ[K] V) x)
    rw [hsa, hta, hta, hsa]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, h1w, h2w, hw1, hw2]
    module
  have hsN := hN t s htt htZ htY hst
  have hg : s⁻¹ * y * s ∈ Y := by
    have h1 := (mem_normalizer_iff.mp hsN (s⁻¹ * y * s)).mpr
    have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rw [e] at h1
    exact h1 hy
  obtain ⟨-, -, -, hgf'⟩ := hY _ hg
  have hyf := (hY y hy).2.2.1
  have hyf' := (hY y hy).2.2.2
  change (s : V ≃ₗ[K] V).symm ((y : V ≃ₗ[K] V) ((s : V ≃ₗ[K] V) f')) = f' at hgf'
  rw [LinearEquiv.symm_apply_eq] at hgf'
  have hsf' : (s : V ≃ₗ[K] V) f' = f' - m - f := by
    rw [hsa, hw, map_add, hf'm, hf'f, zero_add, neg_one_smul]
    abel
  rw [hsf', map_sub, map_sub, hyf, hyf'] at hgf'
  have h3 : (y : V ≃ₗ[K] V) m = m := by
    have := congrArg (fun v => f' - f - v) hgf'
    rw [show f' - f - (f' - (y : V ≃ₗ[K] V) m - f) = (y : V ≃ₗ[K] V) m by abel,
      show f' - f - (f' - m - f) = m by abel] at this
    exact this
  exact h3

variable [FiniteDimensional K V]

theorem sp_eq_one_of_normalizer (h2 : (2 : K) ≠ 0) (hB : B.IsAlt) {F : Submodule K V}
    (hFnd : (B.restrict F).Nondegenerate) (hF4 : 4 ≤ finrank K F)
    {Y : Subgroup (isometryGroup B)} (hYF : ∀ y ∈ Y, ∀ x ∈ F, (y : V ≃ₗ[K] V) x = x)
    (hN : ∀ t s : isometryGroup B, t * t ∈ scalarSigns B → t ∉ scalarSigns B →
      (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set (isometryGroup B))) :
    ∀ y ∈ Y, y = 1 := by
  classical
  have hBF : (B.restrict F).IsAlt := fun x => hB x
  obtain ⟨n, b, hn, hee, hff, hef⟩ := exists_blueprint_symplectic_basis (B.restrict F) hBF hFnd
  have hn2 : 2 ≤ n := by omega
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hB' : ∀ x y : F, B.restrict F x y = B (x : V) (y : V) := fun _ _ => rfl
  have e01 : B (b (Sum.inl i0) : V) (b (Sum.inl i1) : V) = 0 := hee i0 i1
  have ef00 : B (b (Sum.inl i0) : V) (b (Sum.inr i0) : V) = 1 := by simpa using hef i0 i0
  have ef11 : B (b (Sum.inl i1) : V) (b (Sum.inr i1) : V) = 1 := by simpa using hef i1 i1
  have ef10 : B (b (Sum.inl i1) : V) (b (Sum.inr i0) : V) = 0 := by
    simpa [h01.symm] using hef i1 i0
  have fe01 : B (b (Sum.inr i0) : V) (b (Sum.inl i1) : V) = 0 := by
    rw [← hB.neg_eq, ef10, neg_zero]
  have hM : ∀ y ∈ Y, ∀ x ∈ B.orthogonal F, (y : V ≃ₗ[K] V) x = x := by
    intro y hy x hx
    have hxF : ∀ u ∈ F, B u x = 0 := fun u hu => (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu
    exact fixes_of_witness h2 hB ef00 ef11 e01 fe01 (hxF _ (b _).2) (hxF _ (b _).2)
      (hxF _ (b _).2)
      (fun z hz => ⟨hYF z hz _ (b _).2, hYF z hz _ (b _).2, hYF z hz _ (b _).2,
        hYF z hz _ (b _).2⟩) hN y hy
  have hcompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (LinearMap.IsAlt.isRefl hB) hFnd
  intro y hy
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ F ⊔ B.orthogonal F := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  change (y : V ≃ₗ[K] V) (a + c) = a + c
  rw [map_add, hYF y hy a ha, hM y hy c hc]

end CFSG.ComponentClassification.OddClassSelector
