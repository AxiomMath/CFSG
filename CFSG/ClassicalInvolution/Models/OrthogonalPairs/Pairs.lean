module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import CFSG.ClassicalInvolution.Models.LinearPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Frame

variable (F : Frame Q)

theorem incl_injective : Function.Injective F.incl := fun X Y h => by
  have := congrArg F.coords h
  rwa [coords_incl, coords_incl] at this

theorem finrank_span : Module.finrank K F.span = 4 := by
  rw [span, LinearMap.finrank_range_of_inj F.incl_injective]
  simp [Module.finrank_matrix]

instance : FiniteDimensional K F.span :=
  inferInstanceAs (FiniteDimensional K (LinearMap.range F.incl))

variable {F}
variable {F' : Frame Q}

theorem coords_incl_eq_zero_of_orth (h : ∀ X Y, polar Q (F'.incl X) (F.incl Y) = 0)
    (Y : Matrix (Fin 2) (Fin 2) K) : F.coords (F'.incl Y) = 0 := by
  rw [← mem_perp_iff, mem_perp_iff_forall_incl]
  intro X
  exact h Y X

theorem La_comm_of_orth (h : ∀ X Y, polar Q (F.incl X) (F'.incl Y) = 0) (A B : SL(2, K)) :
    F.La A * F'.La B = F'.La B * F.La A := by
  have h' : ∀ X Y, polar Q (F'.incl X) (F.incl Y) = 0 := fun X Y => by
    rw [polar_comm]
    exact h Y X
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, La_apply, map_add, coords_incl_eq_zero_of_orth h,
    coords_incl_eq_zero_of_orth h']
  simp
  abel

theorem La_neg_one_eq_of_span_eq (h : F'.span = F.span) : F'.La (-1) = F.La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  rw [La_neg_one_apply, La_neg_one_apply, coords_eq_comparison h x,
    incl_comparison (F := F') (F' := F) h.symm]

section Centralizing

variable {g : V ≃ₗ[K] V}

theorem transport_commute_left (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (hcent : ∀ A : SL(2, K), g * F.La A = F.La A * g) (A : SL(2, K))
    (X : Matrix (Fin 2) (Fin 2) K) :
    F.transport g ((A : Matrix (Fin 2) (Fin 2) K) * X) =
      (A : Matrix (Fin 2) (Fin 2) K) * F.transport g X := by
  have h1 := embGrp_conj h2 hg (lmulEquiv A)
  rw [← La_eq_embGrp, hcent A, mul_inv_cancel_right, La_eq_embGrp] at h1
  have h3 := F.embGrp_injective h1
  have h4 : transportEquiv h2 hg * lmulEquiv A = lmulEquiv A * transportEquiv h2 hg := by
    calc transportEquiv h2 hg * lmulEquiv A
        = (transportEquiv h2 hg * lmulEquiv A * (transportEquiv h2 hg)⁻¹) *
            transportEquiv h2 hg := by group
      _ = lmulEquiv A * transportEquiv h2 hg := by rw [h3]
  exact LinearEquiv.congr_fun h4 X

theorem transport_eq_one_or_neg_one (h2 : (2 : K) ≠ 0)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hg : g * F.La (-1) = F.La (-1) * g) (hcent : ∀ A : SL(2, K), g * F.La A = F.La A * g) :
    F.transport g = 1 ∨ F.transport g = -1 := by
  refine eq_one_or_eq_neg_one_of_commute_left h2
    (fun A X => transport_commute_left h2 hg hcent A X) ?_ ?_
  · intro X
    have := LinearMap.congr_fun (transport_mul h2 hg (g := g)) X
    rw [hg2, transport_one] at this
    simpa using this.symm
  · intro X
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (transportEquiv_mem_orthogonalGroup h2 hgO hg) X
    rwa [detQ_apply, detQ_apply] at this

end Centralizing

variable {F₁ F₂ : Frame Q}

theorem orth_or_eq (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (hcent : ∀ A : SL(2, K), F₂.La (-1) * F₁.La A = F₁.La A * F₂.La (-1)) :
    (∀ X Y, polar Q (F₁.incl X) (F₂.incl Y) = 0) ∨ F₂.La (-1) = F₁.La (-1) := by
  have hgO := F₂.La_mem_orthogonalGroup (-1)
  rcases transport_eq_one_or_neg_one h2 hgO F₂.La_neg_one_mul_self hc hcent with h | h
  · left
    have hfix : ∀ Y, F₂.La (-1) (F₁.incl Y) = F₁.incl Y := fun Y => by
      rw [← incl_transport h2 hc, h]
      rfl
    exact fun X Y =>
      (mem_perp_iff_forall_incl F₂).mp ((mem_perp_iff_fix F₂ h2).mpr (hfix X)) Y
  · right
    have hneg : ∀ Y, F₂.La (-1) (F₁.incl Y) = -F₁.incl Y := fun Y => by
      rw [← incl_transport h2 hc, h]
      simp
    have hle : F₁.span ≤ F₂.span := by
      rintro _ ⟨Y, rfl⟩
      exact (mem_span_iff_inv F₂ h2).mpr (hneg Y)
    have heq : F₁.span = F₂.span :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span, finrank_span])
    exact La_neg_one_eq_of_span_eq heq.symm

theorem La_comm_or_eq (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (hcent : ∀ A : SL(2, K), F₂.La (-1) * F₁.La A = F₁.La A * F₂.La (-1)) :
    (∀ A B : SL(2, K), F₁.La A * F₂.La B = F₂.La B * F₁.La A) ∨ F₂.La (-1) = F₁.La (-1) :=
  (orth_or_eq h2 hc hcent).imp La_comm_of_orth id

section Geometry

theorem eigenspace_neg_one_La_neg_one (h2 : (2 : K) ≠ 0) (F : Frame Q) :
    Module.End.eigenspace ((F.La (-1) : V ≃ₗ[K] V) : Module.End K V) (-1) = F.span := by
  ext x
  rw [Module.End.mem_eigenspace_iff, mem_span_iff_inv F h2, neg_one_smul]
  rfl

theorem eigenspace_one_La_neg_one (h2 : (2 : K) ≠ 0) (F : Frame Q) :
    Module.End.eigenspace ((F.La (-1) : V ≃ₗ[K] V) : Module.End K V) 1 = F.perp := by
  ext x
  rw [Module.End.mem_eigenspace_iff, mem_perp_iff_fix F h2, one_smul]
  rfl

theorem La_neg_one_mul_self_end (F : Frame Q) :
    ((F.La (-1) : V ≃ₗ[K] V) : Module.End K V) * ((F.La (-1) : V ≃ₗ[K] V) : Module.End K V) = 1 :=
  LinearMap.ext fun x => by
    have := LinearEquiv.congr_fun F.La_neg_one_mul_self x
    simpa using this

variable (F₁ F₂ : Frame Q)

theorem jointEigenspace_false_false (h2 : (2 : K) ≠ 0) :
    jointEigenspace ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V)
      ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V) (false, false) = F₁.span ⊓ F₂.span := by
  rw [jointEigenspace, signOf_false, eigenspace_neg_one_La_neg_one h2,
    eigenspace_neg_one_La_neg_one h2]

theorem jointEigenspace_false_true (h2 : (2 : K) ≠ 0) :
    jointEigenspace ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V)
      ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V) (false, true) = F₁.span ⊓ F₂.perp := by
  rw [jointEigenspace, signOf_false, signOf_true, eigenspace_neg_one_La_neg_one h2,
    eigenspace_one_La_neg_one h2]

theorem jointEigenspace_true_false (h2 : (2 : K) ≠ 0) :
    jointEigenspace ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V)
      ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V) (true, false) = F₁.perp ⊓ F₂.span := by
  rw [jointEigenspace, signOf_false, signOf_true, eigenspace_neg_one_La_neg_one h2,
    eigenspace_one_La_neg_one h2]

variable {F₁ F₂}

theorem commute_end (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V) * ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V) =
      ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V) * ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V) :=
  LinearMap.ext fun x => by
    have := LinearEquiv.congr_fun hc.symm x
    simpa using this

theorem span_eq_sup (h2 : (2 : K) ≠ 0) (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    F₁.span = (F₁.span ⊓ F₂.perp) ⊔ (F₁.span ⊓ F₂.span) := by
  have := eigenspace_eq_sup_jointEigenspace (f := ((F₁.La (-1) : V ≃ₗ[K] V) : Module.End K V))
    (g := ((F₂.La (-1) : V ≃ₗ[K] V) : Module.End K V)) h2 (La_neg_one_mul_self_end F₂)
    (commute_end hc) false
  rwa [signOf_false, eigenspace_neg_one_La_neg_one h2, jointEigenspace_false_true F₁ F₂ h2,
    jointEigenspace_false_false F₁ F₂ h2] at this

theorem span_eq_sup' (h2 : (2 : K) ≠ 0) (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    F₂.span = (F₁.span ⊓ F₂.span) ⊔ (F₁.perp ⊓ F₂.span) := by
  have := span_eq_sup h2 hc.symm
  rw [inf_comm F₂.span F₁.perp, inf_comm F₂.span F₁.span, sup_comm] at this
  exact this

end Geometry

section Dimension

variable {g : V ≃ₗ[K] V}

theorem transport_inv_apply_eq_smul (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    {c : K} (hc2 : c * c = 1) (hS : ∀ Y, F.transport g Y = c • Y)
    (Y : Matrix (Fin 2) (Fin 2) K) : F.transport g⁻¹ Y = c • Y := by
  have h1 : F.transport g (F.transport g⁻¹ Y) = Y := by
    have := LinearMap.congr_fun (transport_mul_inv h2 hg) Y
    simpa using this
  rw [hS] at h1
  calc F.transport g⁻¹ Y = (c * c) • F.transport g⁻¹ Y := by rw [hc2, one_smul]
    _ = c • (c • F.transport g⁻¹ Y) := by rw [mul_smul]
    _ = c • Y := by rw [h1]

theorem commute_of_transport_eq_smul (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    {c : K} (hc2 : c * c = 1) (hS : ∀ Y, F.transport g Y = c • Y) (A : SL(2, K)) :
    g * F.La A = F.La A * g := by
  have h1 : g * F.La A * g⁻¹ = F.La A := by
    refine LinearEquiv.ext fun x => ?_
    have hx := conj_embLin h2 hg (rhoL A : Module.End K (Matrix (Fin 2) (Fin 2) K)) x
    have hT : F.transport g ∘ₗ (rhoL A : Module.End K (Matrix (Fin 2) (Fin 2) K)) ∘ₗ
        F.transport g⁻¹ = (rhoL A : Module.End K (Matrix (Fin 2) (Fin 2) K)) := by
      refine LinearMap.ext fun Y => ?_
      simp only [LinearMap.comp_apply, transport_inv_apply_eq_smul h2 hg hc2 hS, hS]
      change c • ((A : Matrix (Fin 2) (Fin 2) K) * (c • Y)) = (A : Matrix (Fin 2) (Fin 2) K) * Y
      rw [Matrix.mul_smul, smul_smul, hc2, one_smul]
    rw [hT] at hx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hx
  calc g * F.La A = g * F.La A * g⁻¹ * g := by group
    _ = F.La A * g := by rw [h1]

theorem map_incl_eigenspace_transport (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    (Module.End.eigenspace ((transportEquiv h2 hc : Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
      Matrix (Fin 2) (Fin 2) K) : Module.End K (Matrix (Fin 2) (Fin 2) K)) (-1)).map F₁.incl =
      F₁.span ⊓ F₂.span := by
  ext x
  rw [Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨⟨Y, rfl⟩, ?_⟩
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hY
    rw [mem_span_iff_inv F₂ h2, ← incl_transport h2 hc Y]
    have : F₁.transport (F₂.La (-1)) Y = -Y := hY
    rw [this, map_neg]
  · rintro ⟨hx1, hx2⟩
    refine ⟨F₁.coords x, ?_, ((mem_span_iff F₁).mp hx1).symm⟩
    rw [Module.End.mem_eigenspace_iff, neg_one_smul]
    have hx2' := (mem_span_iff_inv F₂ h2).mp hx2
    have := coords_map h2 hc x
    rw [hx2', map_neg] at this
    exact this.symm

theorem finrank_eigenspace_transport (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    Module.finrank K (Module.End.eigenspace ((transportEquiv h2 hc : Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
      Matrix (Fin 2) (Fin 2) K) : Module.End K (Matrix (Fin 2) (Fin 2) K)) (-1)) =
      Module.finrank K ↥(F₁.span ⊓ F₂.span) := by
  rw [← map_incl_eigenspace_transport h2 hc]
  exact (Submodule.equivMapOfInjective F₁.incl F₁.incl_injective _).finrank_eq

theorem transportEquiv_mul_self (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) (Y : Matrix (Fin 2) (Fin 2) K) :
    transportEquiv h2 hc (transportEquiv h2 hc Y) = Y := by
  have := LinearMap.congr_fun (transport_mul h2 hc (g := F₂.La (-1))) Y
  rw [F₂.La_neg_one_mul_self, transport_one] at this
  rw [transportEquiv_apply, transportEquiv_apply]
  simpa using this.symm

theorem conjSubgroup_eq_iff_even (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    conjSubgroup (F₂.La (-1)) F₁.La.range = F₁.La.range ↔
      Even (Module.finrank K ↥(F₁.span ⊓ F₂.span)) := by
  have hgO := F₂.La_mem_orthogonalGroup (-1)
  have hS2 := transportEquiv_mul_self h2 hc
  rcases conjSubgroup_La_range h2 hgO hc with ⟨hd, h1, -⟩ | ⟨hd, h1, -⟩
  · refine ⟨fun _ => ?_, fun _ => h1⟩
    have := even_finrank_of_det_eq_one h2 hS2 hd
    rwa [finrank_eigenspace_transport h2 hc] at this
  · refine ⟨fun h => absurd (h.symm.trans h1) (La_range_ne_swap_La_range F₁), fun h => ?_⟩
    have := odd_finrank_of_det_eq_neg_one h2 hS2 hd
    rw [finrank_eigenspace_transport h2 hc] at this
    exact absurd h (Nat.not_even_iff_odd.mpr this)

theorem finrank_inf_span_eq_two (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (hN : conjSubgroup (F₂.La (-1)) F₁.La.range = F₁.La.range)
    (hC : ∃ A : SL(2, K), F₂.La (-1) * F₁.La A ≠ F₁.La A * F₂.La (-1)) :
    Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2 := by
  have hgO := F₂.La_mem_orthogonalGroup (-1)
  rcases conjSubgroup_La_range h2 hgO hc with ⟨hd, -, -⟩ | ⟨-, hs, -⟩
  swap
  · exact absurd (hN.symm.trans hs) (La_range_ne_swap_La_range F₁)
  have hS2 := transportEquiv_mul_self h2 hc
  have heven := even_finrank_of_det_eq_one h2 hS2 hd
  rw [finrank_eigenspace_transport h2 hc] at heven
  obtain ⟨A, hA⟩ := hC
  have hle : Module.finrank K ↥(F₁.span ⊓ F₂.span) ≤ 4 := by
    calc Module.finrank K ↥(F₁.span ⊓ F₂.span) ≤ Module.finrank K F₁.span :=
          Submodule.finrank_mono inf_le_left
      _ = 4 := finrank_span F₁
  have h0 : Module.finrank K ↥(F₁.span ⊓ F₂.span) ≠ 0 := by
    intro h0
    rw [← finrank_eigenspace_transport h2 hc, Submodule.finrank_eq_zero] at h0
    refine hA (commute_of_transport_eq_smul h2 hc (c := 1) (by simp) (fun Y => ?_) A)
    have hY : Y - transportEquiv h2 hc Y ∈ Module.End.eigenspace
        ((transportEquiv h2 hc : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
          Module.End K (Matrix (Fin 2) (Fin 2) K)) (-1) := by
      rw [Module.End.mem_eigenspace_iff, neg_one_smul]
      change transportEquiv h2 hc (Y - transportEquiv h2 hc Y) = -(Y - transportEquiv h2 hc Y)
      rw [map_sub, hS2, neg_sub]
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hY
    rw [one_smul]
    exact hY.symm
  have h4 : Module.finrank K ↥(F₁.span ⊓ F₂.span) ≠ 4 := by
    intro h4
    rw [← finrank_eigenspace_transport h2 hc] at h4
    have htop := Submodule.eq_top_of_finrank_eq (K := K)
      (S := Module.End.eigenspace ((transportEquiv h2 hc : Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
        Matrix (Fin 2) (Fin 2) K) : Module.End K (Matrix (Fin 2) (Fin 2) K)) (-1))
      (by rw [h4]; simp [Module.finrank_matrix])
    refine hA (commute_of_transport_eq_smul h2 hc (c := -1) (by simp) (fun Y => ?_) A)
    have hY : Y ∈ Module.End.eigenspace ((transportEquiv h2 hc : Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
        Matrix (Fin 2) (Fin 2) K) : Module.End K (Matrix (Fin 2) (Fin 2) K)) (-1) := by
      rw [htop]; trivial
    exact Module.End.mem_eigenspace_iff.mp hY
  obtain ⟨k, hk⟩ := heven
  omega

end Dimension

end Frame

namespace IsFundamental

variable {L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V} [Finite K]

theorem commute_iff (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁) (hne : L₁ ≠ L₂) :
    (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ↔
      i₂ ∈ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)) := by
  have h2 := two_ne_zero_of_odd hodd
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h x hx i₂ h₂.mem
  · intro hcent
    rw [Subgroup.mem_centralizer_iff] at hcent
    obtain ⟨F₁, rfl, rfl⟩ := h₁
    obtain ⟨F₂, rfl, rfl⟩ := h₂
    rcases Frame.La_comm_or_eq h2 hc.symm
      (fun A => (hcent _ ⟨A, rfl⟩).symm) with h | h
    · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      exact h A B
    · obtain ⟨L', hL', hne', hcomm, huniq⟩ := exists_twin hodd (of_frame F₁)
      have h₂' : IsFundamental Q F₂.La.range (F₁.La (-1)) := ⟨F₂, rfl, h.symm⟩
      rcases huniq _ h₂' with h' | h'
      · exact absurd h'.symm hne
      · rw [h']
        exact hcomm

end IsFundamental

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
