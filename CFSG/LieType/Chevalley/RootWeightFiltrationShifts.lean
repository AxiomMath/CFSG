module

public import CFSG.LieType.Chevalley.RootWeightFiltration
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.LieType.Chevalley.RootWeight

open scoped RealInnerProductSpace DirectSum

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {E : Type*} [DecidableEq E] {Ω : Finset E} {Vχ : E → Submodule K V}

@[expose] def weightProj (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ) (ψ : Ω) :
    Module.End K V :=
  (Vχ ψ).subtype ∘ₗ DirectSum.component K Ω (fun χ : Ω => Vχ χ) ψ ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun χ : Ω => Vχ χ) hV).symm.toLinearMap

@[expose] def weightBlock (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ) (a : Module.End K V)
    (χ ψ : Ω) : Vχ χ →ₗ[K] V :=
  weightProj hV ψ ∘ₗ a ∘ₗ (Vχ χ).subtype

open _root_.Classical in
@[expose] def shiftSupport (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ)
    (A : Finset (Module.End K V)) : Finset (Ω × Ω) :=
  Finset.univ.filter fun p => ∃ a ∈ A, weightBlock hV a p.1 p.2 ≠ 0

section Inner

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open _root_.Classical in
@[expose] def minWeightShift (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ)
    (A : Finset (Module.End K V)) (l : E) : ℝ :=
  if h : (shiftSupport hV A).Nonempty then
    (shiftSupport hV A).inf' h fun p => ⟪(p.2 : E) - p.1, l⟫
  else 0

end Inner

variable (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ)

theorem weightProj_apply (ψ : Ω) (x : V) :
    weightProj hV ψ x =
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun χ : Ω => Vχ χ) hV).symm x ψ :
        V) :=
  rfl

theorem weightProj_mem (ψ : Ω) (x : V) : weightProj hV ψ x ∈ Vχ ψ := by
  rw [weightProj_apply]
  exact Submodule.coe_mem _

theorem weightProj_of_mem {ψ : Ω} {x : V} (hx : x ∈ Vχ ψ) : weightProj hV ψ x = x := by
  rw [weightProj_apply, hV.ofBijective_coeLinearMap_of_mem hx]

theorem weightProj_of_mem_ne {χ ψ : Ω} (h : χ ≠ ψ) {x : V} (hx : x ∈ Vχ χ) :
    weightProj hV ψ x = 0 := by
  rw [weightProj_apply, hV.ofBijective_coeLinearMap_of_mem_ne h hx, Submodule.coe_zero]

theorem sum_weightProj (x : V) : ∑ ψ, weightProj hV ψ x = x := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun χ : Ω => Vχ χ) hV
  have h := congrArg (DirectSum.coeLinearMap fun χ : Ω => Vχ χ)
    (DirectSum.sum_univ_of (e.symm x))
  rw [map_sum] at h
  simp only [DirectSum.coeLinearMap_of] at h
  have hx : DirectSum.coeLinearMap (fun χ : Ω => Vχ χ) (e.symm x) = x := e.apply_symm_apply x
  rw [hx] at h
  exact h

theorem weightBlock_ne_zero_iff {a : Module.End K V} {χ ψ : Ω} :
    weightBlock hV a χ ψ ≠ 0 ↔ ∃ x ∈ Vχ χ, weightProj hV ψ (a x) ≠ 0 := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (LinearMap.ext fun x => h' x x.2)
  · rintro ⟨x, hx, hne⟩ h
    exact hne (LinearMap.congr_fun h ⟨x, hx⟩)

theorem mem_shiftSupport {A : Finset (Module.End K V)} {p : Ω × Ω} :
    p ∈ shiftSupport hV A ↔ ∃ a ∈ A, ∃ x ∈ Vχ p.1, weightProj hV p.2 (a x) ≠ 0 := by
  classical
  simp only [shiftSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun a => and_congr_right fun _ => weightBlock_ne_zero_iff hV

theorem shiftSupport_nonempty {A : Finset (Module.End K V)} (hA : A.Nonempty)
    (hA0 : (0 : Module.End K V) ∉ A) : (shiftSupport hV A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  have hne : a ≠ 0 := fun h => hA0 (h ▸ ha)
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  obtain ⟨χ, hχ⟩ : ∃ χ : Ω, a (weightProj hV χ x) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [← sum_weightProj hV x, map_sum]
    exact Finset.sum_eq_zero fun χ _ => h χ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ω, weightProj hV ψ (a (weightProj hV χ x)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hχ
    rw [← sum_weightProj hV (a (weightProj hV χ x))]
    exact Finset.sum_eq_zero fun ψ _ => h ψ
  exact ⟨(χ, ψ), (mem_shiftSupport hV).2 ⟨a, ha, _, weightProj_mem hV χ x, hψ⟩⟩

section Inner

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_weightFiltration_iff {l : E} {c : ℝ} {x : V} :
    x ∈ weightFiltration Ω Vχ l c ↔ ∀ ψ : Ω, ⟪(ψ : E), l⟫ < c → weightProj hV ψ x = 0 := by
  constructor
  · intro hx
    let S : Submodule K V := ⨅ (ψ : Ω) (_ : ⟪(ψ : E), l⟫ < c), LinearMap.ker (weightProj hV ψ)
    have hle : weightFiltration Ω Vχ l c ≤ S := by
      refine weightFiltration_le_iff.2 fun χ hχ hc y hy => ?_
      simp only [S, Submodule.mem_iInf, LinearMap.mem_ker]
      intro ψ hψ
      refine weightProj_of_mem_ne hV (χ := ⟨χ, hχ⟩) (fun h => ?_) hy
      rw [← h] at hψ
      exact absurd hc (not_le.2 hψ)
    have := hle hx
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this
  · intro h
    rw [← sum_weightProj hV x]
    refine Submodule.sum_mem _ fun ψ _ => ?_
    by_cases hψ : ⟪(ψ : E), l⟫ < c
    · rw [h ψ hψ]
      exact Submodule.zero_mem _
    · exact le_weightFiltration ψ.2 (not_lt.1 hψ) (weightProj_mem hV ψ x)

theorem minWeightShift_eq {A : Finset (Module.End K V)} (h : (shiftSupport hV A).Nonempty)
    (l : E) :
    minWeightShift hV A l = (shiftSupport hV A).inf' h fun p => ⟪(p.2 : E) - p.1, l⟫ := by
  simp only [minWeightShift, h, ↓reduceDIte]

theorem le_minWeightShift_iff {A : Finset (Module.End K V)} (hA : A.Nonempty)
    (hA0 : (0 : Module.End K V) ∉ A) (l : E) (r : ℝ) :
    r ≤ minWeightShift hV A l ↔ ∀ a ∈ A, ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map a ≤ weightFiltration Ω Vχ l (c + r) := by
  have hS := shiftSupport_nonempty hV hA hA0
  rw [minWeightShift_eq hV hS, Finset.le_inf'_iff]
  constructor
  · intro h a ha c
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap, mem_weightFiltration_iff hV]
    intro ψ hψ
    rw [← sum_weightProj hV x, map_sum, map_sum]
    refine Finset.sum_eq_zero fun χ _ => ?_
    by_contra hne
    have hmem : (χ, ψ) ∈ shiftSupport hV A :=
      (mem_shiftSupport hV).2 ⟨a, ha, _, weightProj_mem hV χ x, hne⟩
    have hr := h _ hmem
    have hχ0 : weightProj hV χ x ≠ 0 := fun h0 => hne (by rw [h0, map_zero, map_zero])
    have hχc : c ≤ ⟪(χ : E), l⟫ := by
      by_contra hlt
      exact hχ0 ((mem_weightFiltration_iff hV).1 hx χ (not_le.1 hlt))
    simp only [inner_sub_left] at hr
    linarith
  · rintro h ⟨χ, ψ⟩ hp
    obtain ⟨a, ha, x, hx, hne⟩ := (mem_shiftSupport hV).1 hp
    have hmem : a x ∈ weightFiltration Ω Vχ l (⟪(χ : E), l⟫ + r) :=
      h a ha _ (Submodule.mem_map_of_mem (le_weightFiltration χ.2 le_rfl hx))
    have hψ : ¬ ⟪(ψ : E), l⟫ < ⟪(χ : E), l⟫ + r := fun hlt =>
      hne ((mem_weightFiltration_iff hV).1 hmem ψ hlt)
    simp only [inner_sub_left]
    linarith

theorem minWeightShift_eq_of_iff {A A' : Finset (Module.End K V)} (hA : A.Nonempty)
    (hA0 : (0 : Module.End K V) ∉ A) (hA' : A'.Nonempty) (hA0' : (0 : Module.End K V) ∉ A')
    {l l' : E}
    (h : ∀ r : ℝ, (∀ a ∈ A, ∀ c : ℝ,
        (weightFiltration Ω Vχ l c).map a ≤ weightFiltration Ω Vχ l (c + r)) ↔
      ∀ a ∈ A', ∀ c : ℝ,
        (weightFiltration Ω Vχ l' c).map a ≤ weightFiltration Ω Vχ l' (c + r)) :
    minWeightShift hV A l = minWeightShift hV A' l' := by
  have key : ∀ r, r ≤ minWeightShift hV A l ↔ r ≤ minWeightShift hV A' l' := fun r => by
    rw [le_minWeightShift_iff hV hA hA0, le_minWeightShift_iff hV hA' hA0', h]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem map_weightFiltration {σ : K →+* K} [RingHomSurjective σ] (f : V →ₛₗ[σ] V)
    (u : E ≃ₗᵢ[ℝ] E) (hu : Ω.image u = Ω) (hf : ∀ χ ∈ Ω, (Vχ χ).map f = Vχ (u χ)) (l : E)
    (c : ℝ) : (weightFiltration Ω Vχ l c).map f = weightFiltration Ω Vχ (u l) c := by
  apply le_antisymm
  · rw [weightFiltration, Submodule.map_iSup]
    refine iSup_le fun χ => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hχ => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hc => ?_
    rw [hf χ hχ]
    have huχ : u χ ∈ Ω := hu ▸ Finset.mem_image_of_mem u hχ
    exact le_weightFiltration huχ (by rw [LinearIsometryEquiv.inner_map_map]; exact hc)
  · refine weightFiltration_le_iff.2 fun ψ hψ hc => ?_
    rw [← hu] at hψ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
    rw [← hf χ hχ]
    refine Submodule.map_mono (le_weightFiltration hχ ?_)
    rwa [LinearIsometryEquiv.inner_map_map] at hc

theorem map_inv_le_iff (b : (Module.End K V)ˣ) (X Y : Submodule K V) :
    X.map (↑b⁻¹ : Module.End K V) ≤ Y ↔ X ≤ Y.map (b : Module.End K V) := by
  have h1 : ∀ Z : Submodule K V, (Z.map (↑b⁻¹ : Module.End K V)).map (b : Module.End K V) = Z :=
    fun Z => by
      rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, Units.mul_inv, Module.End.one_eq_id,
        Submodule.map_id]
  have h2 : ∀ Z : Submodule K V, (Z.map (b : Module.End K V)).map (↑b⁻¹ : Module.End K V) = Z :=
    fun Z => by
      rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, Units.inv_mul, Module.End.one_eq_id,
        Submodule.map_id]
  constructor
  · intro h
    rw [← h1 X]
    exact Submodule.map_mono h
  · intro h
    rw [← h2 Y]
    exact Submodule.map_mono h

@[expose] def semilinearConj {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (s : V ≃ₛₗ[σ] V) (a : Module.End K V) : Module.End K V :=
  (s.toLinearMap ∘ₛₗ a) ∘ₛₗ s.symm.toLinearMap

theorem semilinearConj_apply {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (s : V ≃ₛₗ[σ] V) (a : Module.End K V) (x : V) : semilinearConj s a x = s (a (s.symm x)) :=
  rfl

open _root_.Classical in
theorem weight_filtration_endomorphism_shifts [FiniteDimensional ℝ E] [FiniteDimensional K V]
    (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ) (A : Finset (Module.End K V))
    (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A) :
    (shiftSupport hV A).Nonempty ∧
    (∀ (l : E) (r : ℝ), r ≤ minWeightShift hV A l ↔ ∀ a ∈ A, ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map a ≤ weightFiltration Ω Vχ l (c + r)) ∧
    (∀ (l : E) (b : (Module.End K V)ˣ),
      (∀ c : ℝ, (weightFiltration Ω Vχ l c).map (b : Module.End K V) =
        weightFiltration Ω Vχ l c) →
      minWeightShift hV (A.image fun a => (↑b⁻¹ : Module.End K V) * a * b) l =
        minWeightShift hV A l) ∧
    Continuous (minWeightShift hV A) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ l : E, minWeightShift hV A (t • l) = t * minWeightShift hV A l) ∧
    (∀ l m : E, minWeightShift hV A l + minWeightShift hV A m ≤ minWeightShift hV A (l + m)) ∧
    (∀ u : E ≃ₗᵢ[ℝ] E, Ω.image u = Ω → ∀ n : (Module.End K V)ˣ,
      (∀ χ ∈ Ω, (Vχ χ).map (n : Module.End K V) = Vχ (u χ)) →
      (∀ (l : E) (c : ℝ), (weightFiltration Ω Vχ l c).map (n : Module.End K V) =
        weightFiltration Ω Vχ (u l) c) ∧
      ∀ l : E, minWeightShift hV (A.image fun a => (↑n⁻¹ : Module.End K V) * a * n) l =
        minWeightShift hV A (u l)) ∧
    (∀ u : E ≃ₗᵢ[ℝ] E, Ω.image u = Ω → ∀ (σ σ' : K →+* K) [RingHomInvPair σ σ']
      [RingHomInvPair σ' σ] (s : V ≃ₛₗ[σ] V), (∀ χ ∈ Ω, (Vχ χ).map s.toLinearMap = Vχ (u χ)) →
      (∀ (l : E) (c : ℝ), (weightFiltration Ω Vχ l c).map s.toLinearMap =
        weightFiltration Ω Vχ (u l) c) ∧
      ∀ l : E, minWeightShift hV (A.image (semilinearConj s)) (u l) =
        minWeightShift hV A l) := by
  have hS := shiftSupport_nonempty hV hA hA0
  have hconj : ∀ n : (Module.End K V)ˣ,
      (A.image fun a => (↑n⁻¹ : Module.End K V) * a * n).Nonempty ∧
        (0 : Module.End K V) ∉ A.image fun a => (↑n⁻¹ : Module.End K V) * a * n := fun n => by
    refine ⟨hA.image _, fun h0 => ?_⟩
    obtain ⟨a, ha, h⟩ := Finset.mem_image.1 h0
    have : a = (n : Module.End K V) * ((↑n⁻¹ : Module.End K V) * a * n) * ↑n⁻¹ := by
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h, mul_zero, zero_mul] at this
    exact hA0 (this ▸ ha)
  have hraise : ∀ (n : (Module.End K V)ˣ) (l l' : E),
      (∀ c, (weightFiltration Ω Vχ l c).map (n : Module.End K V) = weightFiltration Ω Vχ l' c) →
      ∀ (a : Module.End K V) (c r : ℝ),
        (weightFiltration Ω Vχ l c).map ((↑n⁻¹ : Module.End K V) * a * (n : Module.End K V)) ≤
            weightFiltration Ω Vχ l (c + r) ↔
          (weightFiltration Ω Vχ l' c).map a ≤ weightFiltration Ω Vχ l' (c + r) := by
    intro n l l' hn a c r
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, Submodule.map_comp, Submodule.map_comp,
      hn, map_inv_le_iff, hn]
  refine ⟨hS, le_minWeightShift_iff hV hA hA0, fun l b hb => ?_, ?_, fun t ht l => ?_,
    fun l m => ?_, fun u hu n hn => ?_, fun u hu σ σ' _ _ s hs => ?_⟩
  ·
    obtain ⟨hA', hA0'⟩ := hconj b
    refine minWeightShift_eq_of_iff hV hA' hA0' hA hA0 fun r => ?_
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun a _ => forall_congr' fun c => hraise b l l hb a c r
  ·
    have : minWeightShift hV A = fun l => (shiftSupport hV A).inf' hS fun p =>
        ⟪(p.2 : E) - p.1, l⟫ := funext (minWeightShift_eq hV hS)
    rw [this]
    exact Continuous.finset_inf'_apply hS fun p _ => continuous_const.inner continuous_id
  ·
    rw [minWeightShift_eq hV hS, minWeightShift_eq hV hS]
    simp only [inner_smul_right]
    exact (Finset.apply_inf'_eq_inf'_comp hS (t * ·) fun x y => mul_min_of_nonneg x y ht).symm
  ·
    rw [minWeightShift_eq hV hS, minWeightShift_eq hV hS, minWeightShift_eq hV hS]
    refine Finset.le_inf' _ _ fun p hp => ?_
    rw [inner_add_right]
    exact add_le_add (Finset.inf'_le _ hp) (Finset.inf'_le _ hp)
  ·
    have hF : ∀ l c, (weightFiltration Ω Vχ l c).map (n : Module.End K V) =
        weightFiltration Ω Vχ (u l) c := fun l c =>
      map_weightFiltration (n : Module.End K V) u hu hn l c
    refine ⟨hF, fun l => ?_⟩
    obtain ⟨hA', hA0'⟩ := hconj n
    refine minWeightShift_eq_of_iff hV hA' hA0' hA hA0 fun r => ?_
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun a _ => forall_congr' fun c => hraise n l (u l) (hF l) a c r
  ·
    have hF : ∀ l c, (weightFiltration Ω Vχ l c).map s.toLinearMap =
        weightFiltration Ω Vχ (u l) c :=
      fun l c => map_weightFiltration s.toLinearMap u hu hs l c
    refine ⟨hF, fun l => ?_⟩
    have hA' : (A.image (semilinearConj s)).Nonempty := hA.image _
    have hA0' : (0 : Module.End K V) ∉ A.image (semilinearConj s) := fun h0 => by
      obtain ⟨a, ha, h⟩ := Finset.mem_image.1 h0
      have : a = 0 := LinearMap.ext fun x => by
        have hx := LinearMap.congr_fun h (s x)
        rw [semilinearConj_apply, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at hx
        rw [LinearMap.zero_apply]
        exact s.map_eq_zero_iff.1 hx
      exact hA0 (this ▸ ha)
    have hinv : ∀ c, (weightFiltration Ω Vχ (u l) c).map s.symm.toLinearMap =
        weightFiltration Ω Vχ l c :=
      fun c => by
        rw [← hF l c, ← Submodule.map_comp]
        simp only [LinearEquiv.symm_comp, Submodule.map_id]
    have hmapiff : ∀ X Y : Submodule K V, X.map s.toLinearMap ≤ Y.map s.toLinearMap ↔ X ≤ Y :=
      fun X Y =>
      Submodule.map_le_map_iff_of_injective s.injective X Y
    refine minWeightShift_eq_of_iff hV hA' hA0' hA hA0 fun r => ?_
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine forall₂_congr fun a _ => forall_congr' fun c => ?_
    have e : (weightFiltration Ω Vχ (u l) c).map (semilinearConj s a) =
        ((weightFiltration Ω Vχ l c).map a).map s.toLinearMap := by
      rw [semilinearConj, Submodule.map_comp, Submodule.map_comp, hinv]
    rw [e, ← hF l (c + r), hmapiff]

end Inner

end CFSG.LieType.Chevalley.RootWeight
