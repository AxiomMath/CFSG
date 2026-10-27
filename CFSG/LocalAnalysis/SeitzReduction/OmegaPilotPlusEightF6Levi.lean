module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourF6
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBLevi

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr planeEnum
  planeEnum_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Level

omit [Finite K] [CharP K 2] in
theorem units_ne_inv_of_mul_self_ne_one' {α : Kˣ} (hα : α * α ≠ 1) : (α : K) ≠ ((α⁻¹ : Kˣ) : K) :=
  fun e => hα (by
    have h : α = α⁻¹ := Units.ext e
    calc α * α = α * α⁻¹ := congrArg (α * ·) h
      _ = 1 := mul_inv_cancel α)

theorem nonempty_perfectCore_centralizer_frameHom_const (hq : 4 ≤ Nat.card K) {α : Kˣ}
    (hα : α * α ≠ 1) (k : Fin 4) :
    Nonempty (perfectCore (centralizer ({(isHypFrame_plus K 4).frameHom (fun _ => α)} :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k) := by
  classical
  set s₀ : Fin 4 → Kˣ := fun _ => α with hs₀
  set φ := statedOmegaPlusEquiv K 4 (by norm_num) with hφ
  set x : StatedOmega (StatedQuadPlus 4 K) := φ.symm ((isHypFrame_plus K 4).frameHom s₀) with hxdef
  have hx : (x : GL (Fin 4 ⊕ Fin 4) K) = diagOmega K 4 s₀ :=
    statedOmegaPlusEquiv_symm_frameHom (by norm_num) s₀
  have hL := perfectCore_statedOmega_inf_centralizer_eq_level (m := 4) (F := K) hq
    (J := Finset.univ) (by simp) {s₀} (by rintro s rfl i - j -; rfl)
    (fun a b hab hJ => ⟨s₀, rfl, by
      rcases a with i | i <;> rcases b with j | j
      · exact absurd (Or.inl ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, rfl, rfl⟩) hJ
      · simpa [hs₀] using units_ne_inv_of_mul_self_ne_one' hα
      · simpa [hs₀] using (units_ne_inv_of_mul_self_ne_one' hα).symm
      · exact absurd (Or.inr ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, rfl, rfl⟩) hJ⟩)
  rw [Set.image_singleton, ← hx] at hL
  have h1 : (perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K))))).map
      (StatedOmega (StatedQuadPlus 4 K)).subtype =
      perfectCore (StatedOmega (StatedQuadPlus 4 K) ⊓
        centralizer ({(x : GL (Fin 4 ⊕ Fin 4) K)} : Set (GL (Fin 4 ⊕ Fin 4) K))) := by
    rw [LinearPilot.map_perfectCore_centralizer_singleton (Subgroup.subtype_injective _) x,
      Subgroup.range_subtype]
    rfl
  have h2 : (perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K))))).map
      φ.toMonoidHom = perfectCore (centralizer ({(isHypFrame_plus K 4).frameHom s₀} :
        Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) := by
    rw [LinearPilot.map_perfectCore_centralizer_singleton φ.injective x, MonoidHom.range_eq_top.2
      φ.surjective, top_inf_eq]
    congr 3
    change φ (φ.symm _) = _
    rw [MulEquiv.apply_symm_apply]
  have h1' := h1.trans hL
  have e₁ : perfectCore (centralizer ({(isHypFrame_plus K 4).frameHom s₀} :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃*
      perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K)))) :=
    (MulEquiv.subgroupCongr h2.symm).trans
      ((perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K))))).equivMapOfInjective
        φ.toMonoidHom φ.injective).symm
  have e₂ : perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K)))) ≃*
      (omegaLeviSL K (Finset.univ : Finset (Fin 4)).card).map
        (spEmbedGL (planeEnum (Finset.univ : Finset (Fin 4))) (planeEnum_injective _)) :=
    ((perfectCore (centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 K))))).equivMapOfInjective
      _ (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr h1')
  have e₃ : (omegaLeviSL K (Finset.univ : Finset (Fin 4)).card).map
      (spEmbedGL (planeEnum (Finset.univ : Finset (Fin 4))) (planeEnum_injective _)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) K :=
    ((omegaLeviSL K _).equivMapOfInjective _ (spEmbedGL_injective _)).symm.trans
      (omegaLeviSLEquiv.symm.trans (by rw [Finset.card_fin]))
  obtain ⟨e₄⟩ := nonempty_pairPerp_mulEquiv_SL4 (K := K) hq k
  exact ⟨((e₁.trans e₂).trans e₃).trans e₄.symm⟩

end Level

section Frame

omit [Finite K] [CharP K 2] in
theorem polar_plus_single {n : ℕ} (s t : Fin n ⊕ Fin n) :
    polar (coordinateQuadPlus n K) (Pi.single (plusIndexEquiv n s) 1)
        (Pi.single (plusIndexEquiv n t) 1) = if t = Sum.swap s then 1 else 0 := by
  rcases s with i | i
  · rw [(isHypCoord_coordinateQuadPlus (K := K) i).polar_left, Pi.single_apply]
    by_cases h : t = Sum.inr i
    · subst h
      simp
    · simp [h, Ne.symm h]
  · rw [(isHypCoord_coordinateQuadPlus (K := K) i).polar_right, Pi.single_apply]
    by_cases h : t = Sum.inl i
    · subst h
      simp
    · simp [h, Ne.symm h]

omit [Finite K] [CharP K 2] in
theorem coordinateQuadPlus_single {n : ℕ} (s : Fin n ⊕ Fin n) :
    coordinateQuadPlus n K (Pi.single (plusIndexEquiv n s) 1) = 0 := by
  rcases s with i | i
  · exact (isHypCoord_coordinateQuadPlus (K := K) i).map_left
  · exact (isHypCoord_coordinateQuadPlus (K := K) i).map_right

omit [Finite K] [CharP K 2] in
theorem linearIndependent_of_polar_dual {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (w : ι → V) (π : ι → ι)
    (h : ∀ c c', polar Q (w c) (w (π c')) = if c = c' then 1 else 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h0 := congrArg (fun z => (polarBilin Q).flip (w (π c)) z) hg
  simp only [map_sum, map_smul, LinearMap.flip_apply, polarBilin_apply_apply, h, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero] at h0
  exact h0

omit [Finite K] [CharP K 2] in
theorem frameLin_plus_single {n : ℕ} (t : Fin n → Kˣ) (s : Fin n ⊕ Fin n) :
    frameLin (plusFrameLeft n) (plusFrameRight n) t (Pi.single (plusIndexEquiv n s) 1) =
      (Sum.elim (fun i => ((t i : Kˣ) : K)) (fun i => (((t i)⁻¹ : Kˣ) : K)) s) •
        Pi.single (plusIndexEquiv n s) 1 := by
  funext c
  rw [frameLin_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc : c = plusIndexEquiv n s
  · subst hc
    rw [Pi.single_eq_same, mul_one, mul_one]
    rcases s with i | i
    · exact congrArg Units.val ((isHypFrame_plus K n).frameEntry_left t i)
    · exact congrArg Units.val ((isHypFrame_plus K n).frameEntry_right t i)
  · rw [Pi.single_eq_of_ne hc, mul_zero, mul_zero]

theorem nonempty_perfectCore_centralizer_of_frame (hq : 4 ≤ Nat.card K) {α : Kˣ}
    (hα : α * α ≠ 1) (k : Fin 4) (g : orthDerived (coordinateQuadPlus 4 K))
    (u v : Fin 4 → (Fin (2 * 4) → K))
    (hgu : ∀ i, (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (u i) = (α : K) • u i)
    (hgv : ∀ i, (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (v i) =
      ((α⁻¹ : Kˣ) : K) • v i)
    (hu : ∀ i, coordinateQuadPlus 4 K (u i) = 0) (hv : ∀ i, coordinateQuadPlus 4 K (v i) = 0)
    (huu : ∀ i j, polar (coordinateQuadPlus 4 K) (u i) (u j) = 0)
    (hvv : ∀ i j, polar (coordinateQuadPlus 4 K) (v i) (v j) = 0)
    (huv : ∀ i j, polar (coordinateQuadPlus 4 K) (u i) (v j) = if i = j then 1 else 0) :
    Nonempty (perfectCore (centralizer ({projHom _ g} :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k) := by
  classical
  obtain ⟨hQ, -⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  set w : Fin 4 ⊕ Fin 4 → (Fin (2 * 4) → K) := Sum.elim u v with hw
  have hpw : ∀ s t, polar (coordinateQuadPlus 4 K) (w s) (w t) = if t = Sum.swap s then 1 else 0 := by
    intro s t
    rcases s with i | i <;> rcases t with j | j
    · simp [hw, huu]
    · simp only [hw, Sum.elim_inl, Sum.elim_inr, Sum.swap_inl, Sum.inr.injEq, huv]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    · simp only [hw, Sum.elim_inl, Sum.elim_inr, Sum.swap_inr, Sum.inl.injEq]
      rw [polar_comm, huv]
    · simp [hw, hvv]
  set W₀ : Fin (2 * 4) → (Fin (2 * 4) → K) := fun c => w ((plusIndexEquiv 4).symm c) with hW₀
  set E₀ : Fin (2 * 4) → (Fin (2 * 4) → K) := fun c => Pi.single c 1 with hE₀
  have hpE : ∀ s t, polar (coordinateQuadPlus 4 K) (E₀ (plusIndexEquiv 4 s)) (E₀ (plusIndexEquiv 4 t)) =
      if t = Sum.swap s then 1 else 0 := fun s t => polar_plus_single s t
  have hpW : ∀ s t, polar (coordinateQuadPlus 4 K) (W₀ (plusIndexEquiv 4 s)) (W₀ (plusIndexEquiv 4 t)) =
      if t = Sum.swap s then 1 else 0 := fun s t => by
    simp only [hW₀, Equiv.symm_apply_apply]
    exact hpw s t
  set π : Fin (2 * 4) → Fin (2 * 4) :=
    fun c => plusIndexEquiv 4 (Sum.swap ((plusIndexEquiv 4).symm c)) with hπ
  have hdual : ∀ (F : Fin (2 * 4) → (Fin (2 * 4) → K)),
      (∀ s t, polar (coordinateQuadPlus 4 K) (F (plusIndexEquiv 4 s)) (F (plusIndexEquiv 4 t)) =
        if t = Sum.swap s then 1 else 0) →
      ∀ c c', polar (coordinateQuadPlus 4 K) (F c) (F (π c')) = if c = c' then 1 else 0 := by
    intro F hF c c'
    obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective c
    obtain ⟨t, rfl⟩ := (plusIndexEquiv 4).surjective c'
    have hπt : π (plusIndexEquiv 4 t) = plusIndexEquiv 4 (Sum.swap t) := by simp [hπ]
    rw [hπt, hF]
    by_cases h : s = t
    · subst h
      simp
    · have h1 : ¬ (Sum.swap t = Sum.swap s) := fun e =>
        h (Sum.swap_leftInverse.injective e).symm
      have h2 : ¬ (plusIndexEquiv 4 s = plusIndexEquiv 4 t) := fun e =>
        h ((plusIndexEquiv 4).injective e)
      simp only [h1, h2, ite_false]
  have hliE := linearIndependent_of_polar_dual E₀ π (hdual E₀ hpE)
  have hliW := linearIndependent_of_polar_dual W₀ π (hdual W₀ hpW)
  have hQE : ∀ c, (coordinateQuadPlus 4 K) (E₀ c) = 0 := fun c => by
    obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective c
    exact coordinateQuadPlus_single s
  have hQW : ∀ c, (coordinateQuadPlus 4 K) (W₀ c) = 0 := fun c => by
    simp only [hW₀]
    rcases (plusIndexEquiv 4).symm c with i | i
    · exact hu i
    · exact hv i
  obtain ⟨A, hA, hAE⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ E₀ W₀ hliE hliW (fun c => by rw [hQE, hQW]) (fun c c' => by
      obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective c
      obtain ⟨t, rfl⟩ := (plusIndexEquiv 4).surjective c'
      rw [hpE, hpW])
  set s₀ : Fin 4 → Kˣ := fun _ => α with hs₀
  set d := frameLin (plusFrameLeft 4) (plusFrameRight 4) s₀ with hd
  have hAE' : ∀ c, A (Pi.single c 1) = W₀ c := hAE
  have hgA : ∀ x, (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (A x) = A (d x) := by
    have hlin : ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :
        (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).comp
          (A : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
        (A : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).comp
          (d : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) := by
      refine LinearMap.pi_ext fun c t => ?_
      have hst : (Pi.single c t : Fin (2 * 4) → K) = t • Pi.single c 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective c
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hst]
      simp only [map_smul]
      rw [hAE', hd, frameLin_plus_single, map_smul, hAE']
      congr 1
      simp only [hW₀, Equiv.symm_apply_apply, hw]
      rcases s with i | i
      · exact hgu i
      · exact hgv i
    intro x
    exact LinearMap.congr_fun hlin x
  have hdO : d ∈ orthDerived (coordinateQuadPlus 4 K) := (isHypFrame_plus K 4).frameLin_mem_orthDerived s₀
  have hgeq : g = conjOrthDerived hA ⟨d, hdO⟩ := by
    apply Subtype.ext
    rw [coe_conjOrthDerived]
    apply LinearEquiv.ext
    intro x
    have h1 : A (A⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have h2 := hgA (A⁻¹ x)
    rw [h1] at h2
    rw [h2, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hne : ∃ v, (coordinateQuadPlus 4 K) v ≠ 0 := (isHypCoord_coordinateQuadPlus (K := K) (0 : Fin 4)).exists_ne_zero
  set γ := conjProj hne hA with hγ
  have hproj : projHom (coordinateQuadPlus 4 K) g = γ ((isHypFrame_plus K 4).frameHom s₀) := by
    rw [IsHypFrame.frameHom_apply, hγ, conjProj_projHom, ← hgeq]
  have hc1 : ∀ y : matrixProjectiveDerived (coordinateQuadPlus 4 K), centralizer ({y} : Set _) =
      centralizer ((zpowers y : Subgroup _) : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := fun y => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hmap : (zpowers ((isHypFrame_plus K 4).frameHom s₀)).map γ.toMonoidHom =
      zpowers (projHom (coordinateQuadPlus 4 K) g) := by
    rw [MonoidHom.map_zpowers, hproj]
    rfl
  obtain ⟨e₁⟩ := F4Pilot.nonempty_perfectCore_centralizer_map_mulAut γ
    (zpowers ((isHypFrame_plus K 4).frameHom s₀))
  rw [hmap, ← hc1, ← hc1] at e₁
  obtain ⟨e₂⟩ := nonempty_perfectCore_centralizer_frameHom_const hq hα k
  exact ⟨e₁.trans e₂⟩

end Frame

section Decomp

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_apply_of_mem_orthogonalGroup {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x y : V) :
    polar Q (g x) (g y) = polar Q x y := by
  simp only [polar, ← map_add, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg]

@[expose] def eigenSub (g : V ≃ₗ[K] V) (c : K) : Submodule K V where
  carrier := {x | g x = c • x}
  add_mem' {x y} hx hy := by
    change g (x + y) = c • (x + y)
    rw [map_add, hx, hy, smul_add]
  zero_mem' := by
    change g 0 = c • (0 : V)
    rw [map_zero, smul_zero]
  smul_mem' t x hx := by
    change g (t • x) = c • (t • x)
    rw [map_smul, hx, smul_comm]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_eigenSub {g : V ≃ₗ[K] V} {c : K} {x : V} : x ∈ eigenSub g c ↔ g x = c • x :=
  Iff.rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem eigenSub_singular {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {c : K} (hc : c * c ≠ 1) :
    (∀ x ∈ eigenSub g c, Q x = 0) ∧ ∀ x ∈ eigenSub g c, ∀ y ∈ eigenSub g c, polar Q x y = 0 := by
  have h1 : c * c - 1 ≠ 0 := sub_ne_zero.mpr hc
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x
    rw [mem_eigenSub.1 hx, QuadraticMap.map_smul, smul_eq_mul] at h
    have : (c * c - 1) * Q x = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h1
  · have h := polar_apply_of_mem_orthogonalGroup hg x y
    rw [mem_eigenSub.1 hx, mem_eigenSub.1 hy, polar_smul_left, polar_smul_right, smul_eq_mul,
      smul_eq_mul] at h
    have : (c * c - 1) * polar Q x y = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h1

omit [Finite K] [CharP K 2] in
theorem exists_frame_of_eigen_decomp (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {α : Kˣ}
    (hα : α * α ≠ 1)
    (hdec : ∀ x, ∃ x₁ x₂, x = x₁ + x₂ ∧ g x₁ = (α : K) • x₁ ∧ g x₂ = ((α⁻¹ : Kˣ) : K) • x₂) :
    ∃ u v : Fin 4 → V, (∀ i, g (u i) = (α : K) • u i) ∧
      (∀ i, g (v i) = ((α⁻¹ : Kˣ) : K) • v i) ∧ (∀ i, Q (u i) = 0) ∧ (∀ i, Q (v i) = 0) ∧
      (∀ i j, polar Q (u i) (u j) = 0) ∧ (∀ i j, polar Q (v i) (v j) = 0) ∧
      (∀ i j, polar Q (u i) (v j) = if i = j then 1 else 0) := by
  classical
  set V₁ := eigenSub g (α : K) with hV₁
  set V₂ := eigenSub g ((α⁻¹ : Kˣ) : K) with hV₂
  have hα' : ((α⁻¹ : Kˣ) : K) * ((α⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h
    apply hα
    have h' : (α⁻¹ * α⁻¹ : Kˣ) = 1 := Units.ext (by simpa using h)
    calc α * α = (α⁻¹ * α⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [h', inv_one]
  have hαK : (α : K) * (α : K) ≠ 1 := fun h => hα (Units.ext (by rw [Units.val_mul, h, Units.val_one]))
  obtain ⟨hQ₁, hB₁⟩ := eigenSub_singular hg hαK
  obtain ⟨hQ₂, hB₂⟩ := eigenSub_singular hg hα'
  have hzero : ∀ z : V, (∀ x ∈ V₁, polar Q x z = 0) → (∀ x ∈ V₂, polar Q x z = 0) → z = 0 := by
    intro z h1 h2
    apply hQ.2 z
    intro y
    obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := hdec y
    rw [polarBilin_apply_apply, polar_add_left, h1 y₁ hy₁, h2 y₂ hy₂, add_zero]
  have hle : ∀ (A B : Submodule K V), (∀ x ∈ B, ∀ y ∈ B, polar Q x y = 0) →
      (∀ z : V, (∀ x ∈ A, polar Q x z = 0) → (∀ x ∈ B, polar Q x z = 0) → z = 0) →
      finrank K B ≤ finrank K A := by
    intro A B hB hz
    let Φ : B →ₗ[K] Module.Dual K A :=
      { toFun := fun y => ((polarBilin Q).flip (y : V)) ∘ₗ A.subtype
        map_add' := fun y y' => by
          ext x
          simp
        map_smul' := fun t y => by
          ext x
          simp }
    have hΦ : Function.Injective Φ := by
      intro y y' hyy'
      apply Subtype.ext
      rw [← sub_eq_zero]
      apply hz
      · intro x hx
        have := LinearMap.congr_fun hyy' ⟨x, hx⟩
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.flip_apply,
          polarBilin_apply_apply, Submodule.coe_subtype] at this
        rw [polar_sub_right, this, sub_self]
      · intro x hx
        exact hB x hx _ (B.sub_mem y.2 y'.2)
    have h := LinearMap.finrank_le_finrank_of_injective hΦ
    rwa [Subspace.dual_finrank_eq] at h
  have h12 := hle V₁ V₂ hB₂ hzero
  have h21 := hle V₂ V₁ hB₁ fun z h2 h1 => hzero z h1 h2
  have hsup : V₁ ⊔ V₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨x₁, x₂, rfl, h1, h2⟩ := hdec x
    exact Submodule.add_mem_sup h1 h2
  have hinf : V₁ ⊓ V₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨h1, h2⟩
    rw [Submodule.mem_bot]
    have h : ((α : K) - ((α⁻¹ : Kˣ) : K)) • x = 0 := by
      rw [sub_smul, ← mem_eigenSub.1 h1, ← mem_eigenSub.1 h2, sub_self]
    exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (units_ne_inv_of_mul_self_ne_one' hα))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hsup, hinf, finrank_top, finrank_bot, hdim, add_zero] at hsum
  have h4 : finrank K V₁ = 4 := by omega
  have h4' : finrank K V₂ = 4 := by omega
  set b := Module.finBasisOfFinrankEq K V₁ h4 with hb
  set u : Fin 4 → V := fun i => (b i : V) with hu
  let Φ₂ : V₂ →ₗ[K] (Fin 4 → K) := LinearMap.pi fun i => (polarBilin Q (u i)) ∘ₗ V₂.subtype
  have hΦ₂ : Function.Injective Φ₂ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply hzero
    · intro x hx
      have : ∀ i, polar Q (u i) y = 0 := fun i => congrFun hy i
      have hxx : x = ((∑ i, b.repr ⟨x, hx⟩ i • b i : V₁) : V) := by
        rw [b.sum_repr ⟨x, hx⟩]
      rw [hxx]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [show polar Q (∑ i, b.repr ⟨x, hx⟩ i • (b i : V)) (y : V) =
          (polarBilin Q).flip (y : V) (∑ i, b.repr ⟨x, hx⟩ i • (b i : V)) from rfl, map_sum]
      simp only [map_smul, LinearMap.flip_apply, polarBilin_apply_apply]
      have this' : ∀ i, polar Q (b i : V) y = 0 := this
      simp [this']
    · intro x hx
      exact hB₂ x hx _ y.2
  have hΦ₂s : Function.Surjective Φ₂ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [h4', Module.finrank_fin_fun])).1 hΦ₂
  choose v' hv' using hΦ₂s
  set v : Fin 4 → V := fun j => (v' (Pi.single j (1 : K)) : V) with hv
  have hΦv : ∀ i j, polar Q (u i) (v j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (hv' (Pi.single j (1 : K))) i
    simp only [Φ₂, LinearMap.pi_apply, LinearMap.comp_apply, polarBilin_apply_apply,
      Submodule.coe_subtype] at h
    rw [show polar Q (u i) (v j) = _ from h, Pi.single_apply]
  refine ⟨u, v, fun i => (b i).2, fun j => (v' (Pi.single j (1 : K))).2,
    fun i => hQ₁ _ (b i).2, fun j => hQ₂ _ (v' (Pi.single j (1 : K))).2,
    fun i j => hB₁ _ (b i).2 _ (b j).2,
    fun i j => hB₂ _ (v' (Pi.single i (1 : K))).2 _ (v' (Pi.single j (1 : K))).2, hΦv⟩

end Decomp

section GLLevi

theorem nonempty_perfectCore_centralizer_of_eigen_decomp (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (g : orthDerived (coordinateQuadPlus 4 K)) {α : Kˣ} (hα : α * α ≠ 1)
    (hdec : ∀ x, ∃ x₁ x₂, x = x₁ + x₂ ∧
      (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x₁ = (α : K) • x₁ ∧
      (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x₂ = ((α⁻¹ : Kˣ) : K) • x₂) :
    Nonempty (perfectCore (centralizer ({projHom _ g} :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k) := by
  obtain ⟨hQ, -⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨u, v, hgu, hgv, hu, hv, huu, hvv, huv⟩ := exists_frame_of_eigen_decomp hQ
    (by rw [Module.finrank_fin_fun]) (Subgroup.commutator_le_self _ g.2) hα hdec
  exact nonempty_perfectCore_centralizer_of_frame hq hα k g u v hgu hgv hu hv huu hvv huv

@[expose] def PlusFourGLLeviEigenInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ i j k : Fin 4, i ≠ j →
    i ≠ k → j ≠ k → ∀ Y : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
    Y ≤ plusLevi K i j → IsCyclic Y → Nat.card Y = Nat.card K - 1 → ¬ Y ≤ stabTwoBar K i j →
    Nat.card (plusRadical K i j ⊓ centralizer (Y : Set (matrixProjectiveDerived
        (coordinateQuadPlus 4 K))) : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      Nat.card (plusRadical K i j ⊓ centralizer (pairTorus (K := K) k :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) →
    ∀ g : orthDerived (coordinateQuadPlus 4 K), Y = zpowers (projHom _ g) →
      ∃ α : Kˣ, α * α ≠ 1 ∧ ∀ x, ∃ x₁ x₂, x = x₁ + x₂ ∧
        (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x₁ = (α : K) • x₁ ∧
        (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x₂ = ((α⁻¹ : Kˣ) : K) • x₂

theorem plusFourGLLeviF6Input_of_eigen (h : PlusFourGLLeviEigenInput) : PlusFourGLLeviF6Input := by
  intro K _ _ _ hq i j k hij hik hjk Y hYM hYc hYcard hYB hcard
  obtain ⟨y₀, hy₀⟩ := hYc.exists_zpow_surjective
  obtain ⟨g, hg⟩ := projHom_surjective (coordinateQuadPlus 4 K) (y₀ : matrixProjectiveDerived _)
  have hYz : Y = zpowers (projHom _ g) := by
    rw [hg]
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := hy₀ ⟨x, hx⟩
      refine ⟨m, ?_⟩
      have := congrArg Subtype.val hm
      simpa using this
    · rintro ⟨m, rfl⟩
      exact zpow_mem y₀.2 m
  obtain ⟨α, hα, hdec⟩ := h K hq i j k hij hik hjk Y hYM hYc hYcard hYB hcard g hYz
  have hc : centralizer (Y : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      centralizer ({projHom _ g} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
    rw [hYz, zpowers_eq_closure, centralizer_closure]
  rw [hc]
  exact nonempty_perfectCore_centralizer_of_eigen_decomp hq k g hα hdec

theorem plusFourRefinedF6OffInput_of_eigen (h : PlusFourGLLeviEigenInput) :
    PlusFourRefinedF6OffInput :=
  plusFourRefinedF6OffInput_of_GLLevi (plusFourGLLeviF6Input_of_eigen h)

end GLLevi

end CFSG.SeitzReduction.OmegaPilot
