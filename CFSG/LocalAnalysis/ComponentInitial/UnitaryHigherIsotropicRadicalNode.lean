module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
  (hC : IsPrimeFormGram C)

include hC in
theorem gramForm_map_ringEquiv (φ : K ≃+* K) (x y : Fin n → K) :
    φ (gramForm h (C : Matrix (Fin n) (Fin n) K) x y) =
      gramForm h (C : Matrix (Fin n) (Fin n) K) (fun i => φ (x i)) (fun i => φ (y i)) := by
  rw [gramForm_apply, gramForm_apply]
  simp only [dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_bar_comm, show φ (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) =
    (φ : K →+* K) (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) from rfl, RingHom.map_mulVec,
    hC.map_eq (φ : K →+* K)]
  rfl

include hC in
theorem eq_of_primeFormConjHom_eq (hn : 3 ≤ n)
    {X Y : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)}
    (hXY : primeFormConjHom h _ X = primeFormConjHom h _ Y) (hX : X ^ 4 = 1) (hY : Y ^ 4 = 1) :
    X = Y := by
  have : CharP K 2 := h.charP
  have h1 : primeFormConjHom h _ (X * Y⁻¹) = 1 := by rw [map_mul, hXY, map_inv, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hn h1
  have hXc : (X : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * Y := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  have hX4 : (X : GL (Fin n) K) ^ 4 = 1 := by
    rw [← SubgroupClass.coe_pow, hX, OneMemClass.coe_one]
  have hY4 : (Y : GL (Fin n) K) ^ 4 = 1 := by
    rw [← SubgroupClass.coe_pow, hY, OneMemClass.coe_one]
  have h4 : GeneralLinearGroup.scalar (Fin n) (c ^ 4) = 1 := by
    have h2 : (GeneralLinearGroup.scalar (Fin n) c * (Y : GL (Fin n) K)) ^ 4 =
        GeneralLinearGroup.scalar (Fin n) c ^ 4 * (Y : GL (Fin n) K) ^ 4 :=
      (commute_scalar c (Y : GL (Fin n) K)).symm.mul_pow 4
    rw [← hXc, hX4, hY4, mul_one] at h2
    rw [map_pow]
    exact h2.symm
  have hc1 : c = 1 := by
    have h2 := congrArg (fun Z : GL (Fin n) K =>
      (Z : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h4
    have h3 : ((c : K) ^ 4) = 1 := by
      have h5 : ((GeneralLinearGroup.scalar (Fin n) (c ^ 4) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩ = ((c ^ 4 : Kˣ) : K) := by
        rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
      rw [← Units.val_pow_eq_pow_val, ← h5]
      exact h2.trans (by rw [Units.val_one, one_apply_eq])
    exact Units.ext (eq_one_of_pow_four_eq_one_of_charTwo h3)
  refine Subtype.ext ?_
  rw [hXc, hc1, map_one, one_mul]

section Normalizer

variable {W : Submodule K (Fin n → K)}

omit hC in
theorem isRadicalMatrix_conj {G : Matrix (Fin n) (Fin n) K} {Am Ai gm : Matrix (Fin n) (Fin n) K}
    (hAA : Am * Ai = 1) (φ : K ≃+* K) (hg : IsRadicalMatrix h G W gm)
    (hTW : ∀ v, Am *ᵥ (fun i => φ (v i)) ∈ W ↔ v ∈ W)
    (hTL : ∀ v, Am *ᵥ (fun i => φ (v i)) ∈ W.orthogonalBilin (gramForm h G) ↔
      v ∈ W.orthogonalBilin (gramForm h G)) :
    IsRadicalMatrix h G W (Am * gm.map φ * Ai) := by
  set T : (Fin n → K) → Fin n → K := fun v => Am *ᵥ fun i => φ (v i) with hT
  set T' : (Fin n → K) → Fin n → K := fun v => fun i => φ.symm ((Ai *ᵥ v) i) with hT'
  have hTT' : ∀ v, T (T' v) = v := fun v => by
    simp only [hT, hT', RingEquiv.apply_symm_apply]
    rw [mulVec_mulVec, hAA, one_mulVec]
  have hTsub : ∀ u u', T (u - u') = T u - T u' := fun u u' => by
    simp only [hT, Pi.sub_apply, map_sub]
    rw [← mulVec_sub]
    rfl
  have hX : ∀ v, (Am * gm.map φ * Ai) *ᵥ v = T (gm *ᵥ T' v) := fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    simp only [hT, hT']
    congr 1
    funext i
    rw [show φ ((gm *ᵥ fun i => φ.symm ((Ai *ᵥ v) i)) i) =
      (φ : K →+* K) ((gm *ᵥ fun i => φ.symm ((Ai *ᵥ v) i)) i) from rfl, RingHom.map_mulVec]
    congr 1
    funext j
    exact (φ.apply_symm_apply _).symm
  obtain ⟨g1, g2, g3⟩ := hg
  have hT'W : ∀ v, T' v ∈ W ↔ v ∈ W := fun v => by
    have := hTW (T' v)
    change T (T' v) ∈ W ↔ T' v ∈ W at this
    rw [hTT'] at this
    exact this.symm
  have hT'L : ∀ v, T' v ∈ W.orthogonalBilin (gramForm h G) ↔
      v ∈ W.orthogonalBilin (gramForm h G) := fun v => by
    have := hTL (T' v)
    change T (T' v) ∈ W.orthogonalBilin (gramForm h G) ↔
      T' v ∈ W.orthogonalBilin (gramForm h G) at this
    rw [hTT'] at this
    exact this.symm
  have hsub : ∀ v, T (gm *ᵥ T' v) - v = T (gm *ᵥ T' v - T' v) := fun v => by
    rw [hTsub, hTT']
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hX, g1 _ ((hT'W w).mpr hw), hTT']
  · rw [hX, hsub]
    exact (hTW _).mpr (g2 _ ((hT'L v).mpr hv))
  · rw [hX, hsub]
    exact (hTL _).mpr (g3 _)

include hC in
theorem psi_conj_mem_radicalImage
    (x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K))
    (hTW : ∀ v, ((x.left : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => x.right (v i)) ∈ W ↔ v ∈ W)
    (hTL : ∀ v, ((x.left : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => x.right (v i)) ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
        v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)))
    {y : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hy : y ∈ radicalImage h (C : Matrix (Fin n) (Fin n) K) W) :
    primeFormPsi h hC x * y * (primeFormPsi h hC x)⁻¹ ∈ radicalImage h _ W := by
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨A, φ⟩ := x
  rw [show radicalConjHom h _ W g = primeFormConjHom h _ (gramSUToUnitary h _ g) from rfl,
    psi_mul_conj_mul_inv]
  have hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hrad := isRadicalMatrix_conj h hAA φ (mem_isotropicRadical.mp g.2) hTW hTL
  have hXSU : ((A * primeFormFieldU h hC φ (gramSUToUnitary h _ g) * A⁻¹ :
      primeFormUnitary h _) : GL (Fin n) K) ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) :=
    conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC φ g.1.2)
  exact ⟨⟨⟨_, hXSU⟩, hrad⟩, rfl⟩

include hC in
theorem psi_mem_normalizer_radicalImage (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K)
    (hTW : ∀ v, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ W ↔
      v ∈ W)
    (hTL : ∀ v, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈
      W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) ↔
        v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) :
    primeFormPsi h hC ⟨A, φ⟩ ∈ Subgroup.normalizer
      (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) := by
  set x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K) :=
    ⟨A, φ⟩ with hx
  set Ai := (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAi
  have hinv : ∀ v, (((x⁻¹).left : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => (x⁻¹).right (v i)) = fun i => φ.symm ((Ai *ᵥ v) i) := fun v => by
    funext i
    change (Ai.map φ.symm *ᵥ fun i => φ.symm (v i)) i = (φ.symm : K →+* K) ((Ai *ᵥ v) i)
    rw [RingHom.map_mulVec]
    rfl
  have hTT' : ∀ v, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => φ (φ.symm ((Ai *ᵥ v) i))) = v := fun v => by
    simp only [RingEquiv.apply_symm_apply]
    rw [hAi, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hW' : ∀ v, (((x⁻¹).left : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => (x⁻¹).right (v i)) ∈ W ↔ v ∈ W := fun v => by
    rw [hinv]
    have := hTW (fun i => φ.symm ((Ai *ᵥ v) i))
    rw [hTT'] at this
    exact this.symm
  have hL' : ∀ v, (((x⁻¹).left : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => (x⁻¹).right (v i)) ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))
        ↔ v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) := fun v => by
    rw [hinv]
    have := hTL (fun i => φ.symm ((Ai *ᵥ v) i))
    rw [hTT'] at this
    exact this.symm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact psi_conj_mem_radicalImage h hC x hTW hTL
  · intro hy
    have h1 := psi_conj_mem_radicalImage h hC x⁻¹ hW' hL' hy
    rwa [map_inv, inv_inv, show ∀ a b : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
      a⁻¹ * (a * b * a⁻¹) * a = b from fun a b => by group] at h1

theorem mem_iff_of_mapsTo_of_finite {α : Type*} [Finite α] {T : α → α}
    (hT : Function.Injective T) {S : Set α} (hS : ∀ v ∈ S, T v ∈ S) (v : α) :
    T v ∈ S ↔ v ∈ S := by
  refine ⟨fun hv => ?_, hS v⟩
  obtain ⟨w, hw, hwv⟩ :=
    (((Set.toFinite S).injOn_iff_bijOn_of_mapsTo hS).mp hT.injOn).surjOn hv
  rwa [← hT hwv]

theorem mulVec_map_injective (A : GL (Fin n) K) (φ : K ≃+* K) :
    Function.Injective fun v : Fin n → K => (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i) := by
  intro v v' hvv'
  have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) hvv'
  simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h1
  funext i
  exact φ.injective (congrFun h1 i)

include hC in
theorem psi_mem_normalizer_radicalImage_of_mapsTo
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hTW : ∀ v ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ W)
    (hTL : ∀ v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)),
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈
        W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) :
    primeFormPsi h hC ⟨A, φ⟩ ∈ Subgroup.normalizer
      (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) := by
  have : Finite K := h.finite
  have hinj := mulVec_map_injective (A : GL (Fin n) K) φ
  exact psi_mem_normalizer_radicalImage h hC A φ
    (mem_iff_of_mapsTo_of_finite hinj (S := (W : Set (Fin n → K))) hTW)
    (mem_iff_of_mapsTo_of_finite hinj
      (S := (W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) : Set (Fin n → K)))
      hTL)

end Normalizer

section Centralizers

variable {W : Submodule K (Fin n → K)}
  (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (C : Matrix (Fin n) (Fin n) K) v w = 0)

include hC in
theorem conj_eq_of_mem_centralizer (hn : 3 ≤ n)
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)} {φ : K ≃+* K}
    (hα : primeFormPsi h hC ⟨A, φ⟩ ∈
      Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _))
    (g : isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W) :
    A * primeFormFieldU h hC φ (gramSUToUnitary h _ g) * A⁻¹ = gramSUToUnitary h _ g := by
  have : CharP K 2 := h.charP
  have hg4 : gramSUToUnitary h _ (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) ^ 4 = 1 := by
    rw [← map_pow, pow_four_eq_one_of_mem_radical g.2, map_one]
  have h1 : primeFormPsi h hC ⟨A, φ⟩ * primeFormConjHom h _ (gramSUToUnitary h _ g) *
      (primeFormPsi h hC ⟨A, φ⟩)⁻¹ = primeFormConjHom h _ (gramSUToUnitary h _ g) := by
    have h2 := Subgroup.mem_centralizer_iff.mp hα (radicalConjHom h _ W g) ⟨g, rfl⟩
    rw [radicalConjHom_apply] at h2
    rw [← h2, mul_inv_cancel_right]
  rw [psi_mul_conj_mul_inv] at h1
  refine eq_of_primeFormConjHom_eq h hC hn h1 ?_ hg4
  rw [conj_pow, ← map_pow, hg4, map_one, mul_one, mul_inv_cancel]

include hC hWiso in
theorem centralizer_inf_primeFormD (hn : 3 ≤ n) (hW0 : W ≠ ⊥) :
    Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) ⊓
        primeFormD h (C : Matrix (Fin n) (Fin n) K) =
      (Subgroup.center (radicalImage h (C : Matrix (Fin n) (Fin n) K) W)).map
        (radicalImage h (C : Matrix (Fin n) (Fin n) K) W).subtype := by
  have : CharP K 2 := h.charP
  apply le_antisymm
  · rintro α ⟨hαc, ⟨A, rfl⟩⟩
    have hαc' : primeFormPsi h hC ⟨A, 1⟩ ∈
        Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) := by
      rwa [← primeFormConjHom_eq_psi h hC]
    have hcomm : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W,
        (A : GL (Fin n) K) * ((g : gramSU h _) : GL (Fin n) K) = (g : GL (Fin n) K) * A := by
      intro g hg
      have h1 := conj_eq_of_mem_centralizer h hC hn hαc' ⟨g, hg⟩
      have h2 : (A : GL (Fin n) K) * ((g : gramSU h _) : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
          (g : GL (Fin n) K) := by
        have h3 := congrArg (fun X : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) =>
          (X : GL (Fin n) K)) h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_one, MulAut.one_apply] at h3
        exact h3
      calc (A : GL (Fin n) K) * ((g : gramSU h _) : GL (Fin n) K) =
          ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) * A := by group
        _ = g * A := by rw [h2]
    obtain ⟨μ, hμ, z, hz, hzA⟩ := exists_scalar_mul_mem_radical h hC hWiso hW0 A.2 hcomm
    have hcA : primeFormConjHom h _ A = radicalConjHom h _ W ⟨z, hz⟩ := by
      have hX : ((A * (gramSUToUnitary h _ z)⁻¹ : primeFormUnitary h _) : GL (Fin n) K) =
          GeneralLinearGroup.scalar (Fin n) μ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv,
          show ((gramSUToUnitary h _ z : primeFormUnitary h _) : GL (Fin n) K) = z from rfl, hzA,
          _root_.mul_inv_rev, ← map_inv, inv_inv, mul_inv_cancel_left]
      have h1 : primeFormConjHom h _ (A * (gramSUToUnitary h _ z)⁻¹) = 1 := by
        rw [primeFormConjHom_eq_psi h hC]
        exact (primeFormPsi_eq_one_iff h hC hn _).mpr ⟨rfl, μ, hμ, hX⟩
      calc primeFormConjHom h _ A = primeFormConjHom h _ (A * (gramSUToUnitary h _ z)⁻¹) *
          primeFormConjHom h _ (gramSUToUnitary h _ z) := by rw [← map_mul, inv_mul_cancel_right]
        _ = radicalConjHom h _ W ⟨z, hz⟩ := by rw [h1, one_mul, radicalConjHom_apply]
    refine ⟨⟨_, ⟨⟨z, hz⟩, hcA.symm⟩⟩, Subgroup.mem_center_iff.mpr fun β => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hαc β β.2
  · rintro _ ⟨β, hβ, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hβ ⟨y, hy⟩)
    · obtain ⟨g, hg⟩ := β.2
      exact ⟨gramSUToUnitary h _ g, hg⟩

include hC hWiso in
theorem fixes_fixedField_of_mem_centralizer (hn : 3 ≤ n) (hW0 : W ≠ ⊥)
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)} {φ : K ≃+* K}
    (hα : primeFormPsi h hC ⟨A, φ⟩ ∈
      Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _)) :
    ∀ a ∈ h.fixedField, φ a = a := by
  have : CharP K 2 := h.charP
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set Ai := (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAi
  have hAiA : Ai * Am = 1 := by rw [hAi, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set T : (Fin n → K) → Fin n → K := fun v => Am *ᵥ fun i => φ (v i) with hT
  have hTg : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W, ∀ v,
      T ((((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ T v := by
    intro g hg v
    set gm := (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgm
    have h1 := conj_eq_of_mem_centralizer h hC hn hα ⟨g, hg⟩
    have h3 : Am * gm.map φ * Ai = gm := by
      have h4 := congrArg (fun X : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) =>
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, Units.val_mul,
        coe_glAut] at h4
      exact h4
    have h2 : Am * gm.map φ = gm * Am := by
      calc Am * gm.map φ = Am * gm.map φ * (Ai * Am) := by rw [hAiA, Matrix.mul_one]
        _ = gm * Am := by rw [← Matrix.mul_assoc, h3]
    simp only [hT]
    rw [show (fun i => φ ((gm *ᵥ v) i)) = gm.map φ *ᵥ fun i => φ (v i) from
      funext fun i => RingHom.map_mulVec (φ : K →+* K) gm v i, mulVec_mulVec, h2,
      ← mulVec_mulVec]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨x₀, hx₀⟩ := exists_gramForm_ne_zero h (C := C) hw0
  have htv : ∀ a ∈ h.fixedField, ∀ x, (φ a * φ (Hf w x)) • T w = (a * Hf w (T x)) • w := by
    intro a ha x
    obtain ⟨t, ht, htx⟩ := transvection_mem_radical h hC hWiso hw ha
    have h1 := hTg t ht x
    rw [htx, htx] at h1
    have hTadd : T (x + (a * Hf w x) • w) = T x + (φ a * φ (Hf w x)) • T w := by
      simp only [hT]
      rw [← mulVec_smul, ← mulVec_add]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    exact add_left_cancel (hTadd.symm.trans h1)
  have hφx₀ : φ (Hf w x₀) ≠ 0 := (map_ne_zero φ).mpr hx₀
  have h1 := htv 1 (one_mem _) x₀
  rw [map_one, one_mul, one_mul] at h1
  set b := (φ (Hf w x₀))⁻¹ * Hf w (T x₀) with hb
  have hTw : T w = b • w := by rw [hb, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hφx₀, one_smul]
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_smul] at hTw
    apply hw0
    have h2 : Ai *ᵥ T w = fun i => φ (w i) := by
      simp only [hT]
      rw [mulVec_mulVec, hAiA, one_mulVec]
    rw [hTw, mulVec_zero] at h2
    funext i
    have h3 := congrFun h2 i
    exact (map_eq_zero φ).mp h3.symm
  have hTx : ∀ x, Hf w (T x) = φ (Hf w x) * b := by
    intro x
    have h2 := htv 1 (one_mem _) x
    rw [map_one, one_mul, one_mul, hTw, smul_smul] at h2
    exact (smul_left_injective K hw0 h2).symm
  intro a ha
  have h3 := htv a ha x₀
  rw [hTw, smul_smul, hTx x₀] at h3
  have h4 := smul_left_injective K hw0 h3
  have hne : φ (Hf w x₀) * b ≠ 0 := mul_ne_zero hφx₀ hb0
  have h5 : φ a * (φ (Hf w x₀) * b) = a * (φ (Hf w x₀) * b) := by
    rw [← mul_assoc]
    exact h4
  exact mul_right_cancel₀ hne h5

include hC hWiso in
theorem primeFormFieldFactor_of_mem_centralizer (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hW0 : W ≠ ⊥) {α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hα : α ∈ Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _)) :
    primeFormFieldFactor h hC hn hq α = RingEquiv.refl K ∨
      ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x := by
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
  rw [primeFormFieldFactor_psi]
  exact ringEquiv_eq_refl_or_bar_of_fixes h
    (fixes_fixedField_of_mem_centralizer h hC hWiso hn hW0 hα)

include hC hWiso in
theorem isPGroup_centralizer_radicalImage (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hW0 : W ≠ ⊥) :
    IsPGroup 2 (Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W :
      Set (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))))) := by
  have : CharP K 2 := h.charP
  intro α
  refine ⟨3, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  set a : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := ↑α with ha
  have hF2 : primeFormFieldFactor h hC hn hq (a ^ 2) = 1 := by
    rw [map_pow]
    rcases primeFormFieldFactor_of_mem_centralizer h hC hWiso hn hq hW0 α.2 with h1 | h1
    · rw [h1]
      rfl
    · refine RingEquiv.ext fun c => ?_
      rw [sq]
      change primeFormFieldFactor h hC hn hq a (primeFormFieldFactor h hC hn hq a c) = c
      rw [h1, h1, h.bar_bar]
  have hD : a ^ 2 ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
    exact hF2
  have hcen : a ^ 2 ∈ Subgroup.centralizer
      (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) := pow_mem α.2 2
  obtain ⟨β, -, hβ⟩ := (centralizer_inf_primeFormD h hC hWiso hn hW0).le ⟨hcen, hD⟩
  obtain ⟨g, hg⟩ := β.2
  have hg4 : g ^ 4 = 1 := Subtype.ext (pow_four_eq_one_of_mem_radical g.2)
  rw [show (2 : ℕ) ^ 3 = 2 * 4 from rfl, pow_mul, ← hβ, Subgroup.coe_subtype, ← hg, ← map_pow,
    hg4, map_one]

end Centralizers

theorem even_unitary_isotropic_radical_centralizer (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (W : Submodule K (Fin n → K)) (hW0 : W ≠ ⊥)
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (C : Matrix (Fin n) (Fin n) K) v w = 0) :
    IsPGroup 2 (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W) ∧
    (∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W, g ^ 4 = 1) ∧
    Function.Injective (radicalConjHom h (C : Matrix (Fin n) (Fin n) K) W) ∧
    (∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      (∀ v ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ W) →
      (∀ v ∈ W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)),
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈
          W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) →
        primeFormPsi h hC ⟨A, φ⟩ ∈ Subgroup.normalizer
          (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _)) ∧
    Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) ⊓
        primeFormD h (C : Matrix (Fin n) (Fin n) K) =
      (Subgroup.center (radicalImage h (C : Matrix (Fin n) (Fin n) K) W)).map
        (radicalImage h (C : Matrix (Fin n) (Fin n) K) W).subtype ∧
    IsPGroup 2 (Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W :
      Set (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))))) ∧
    ∀ α ∈ Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _),
      primeFormFieldFactor h hC hn hq α = RingEquiv.refl K ∨
        ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x := by
  have : CharP K 2 := h.charP
  refine ⟨fun g => ⟨2, ?_⟩, fun g hg => pow_four_eq_one_of_mem_radical hg,
    radicalConjHom_injective h hC hn hW0,
    fun A φ hTW hTL => psi_mem_normalizer_radicalImage_of_mapsTo h hC A φ hTW hTL,
    centralizer_inf_primeFormD h hC hWiso hn hW0,
    isPGroup_centralizer_radicalImage h hC hWiso hn hq hW0,
    fun α hα => primeFormFieldFactor_of_mem_centralizer h hC hWiso hn hq hW0 hα⟩
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  exact Subtype.ext (pow_four_eq_one_of_mem_radical g.2)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
