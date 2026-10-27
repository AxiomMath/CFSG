module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Permutation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

variable {k : Type*} [Field k] {σ : k →+* k}

section Summand

variable {A : Type*} [AddCommGroup A] [Module k A]

@[expose] def sesqOrthSum {W : Type*} [AddCommGroup W] [Module k W] (hA : A →ₛₗ[σ] A →ₗ[k] k)
    (hW : W →ₛₗ[σ] W →ₗ[k] k) : A × W →ₛₗ[σ] A × W →ₗ[k] k :=
  LinearMap.mk₂'ₛₗ σ (RingHom.id k) (fun x y => hA x.1 y.1 + hW x.2 y.2)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
      ring)

@[simp] theorem sesqOrthSum_apply {W : Type*} [AddCommGroup W] [Module k W]
    (hA : A →ₛₗ[σ] A →ₗ[k] k) (hW : W →ₛₗ[σ] W →ₗ[k] k) (x y : A × W) :
    sesqOrthSum hA hW x y = hA x.1 y.1 + hW x.2 y.2 :=
  rfl

variable (k A) in
@[expose] def summandGL (W : Type*) [AddCommGroup W] [Module k W] :
    LinearMap.GeneralLinearGroup k A →* LinearMap.GeneralLinearGroup k (A × W) :=
  Units.map
    { toFun := fun g => g.prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }

@[simp] theorem summandGL_apply {W : Type*} [AddCommGroup W] [Module k W]
    (g : LinearMap.GeneralLinearGroup k A) (v : A) (w : W) :
    (summandGL k A W g : A × W →ₗ[k] A × W) (v, w) = ((g : A →ₗ[k] A) v, w) :=
  rfl

theorem summandGL_apply_fst {W : Type*} [AddCommGroup W] [Module k W]
    (g : LinearMap.GeneralLinearGroup k A) (x : A × W) :
    ((summandGL k A W g : A × W →ₗ[k] A × W) x).1 = (g : A →ₗ[k] A) x.1 :=
  rfl

theorem summandGL_apply_snd {W : Type*} [AddCommGroup W] [Module k W]
    (g : LinearMap.GeneralLinearGroup k A) (x : A × W) :
    ((summandGL k A W g : A × W →ₗ[k] A × W) x).2 = x.2 :=
  rfl

@[expose] def summandSpecialUnitary (hA : A →ₛₗ[σ] A →ₗ[k] k) (W : Type*) [AddCommGroup W]
    [Module k W] : Subgroup (LinearMap.GeneralLinearGroup k (A × W)) :=
  (sesqSpecialUnitaryGroup hA).map (summandGL k A W)

variable {W : Type*} [AddCommGroup W] [Module k W]

theorem summandSpecialUnitary_le (hA : A →ₛₗ[σ] A →ₗ[k] k) (hW : W →ₛₗ[σ] W →ₗ[k] k) :
    summandSpecialUnitary hA W ≤ sesqUnitaryGroup (sesqOrthSum hA hW) := by
  rintro _ ⟨g, hg, rfl⟩ x y
  change hA ((g : A →ₗ[k] A) x.1) ((g : A →ₗ[k] A) y.1) + hW x.2 y.2 = hA x.1 y.1 + hW x.2 y.2
  rw [(mem_sesqSpecialUnitaryGroup.mp hg).1]

end Summand

section Basis

variable {A : Type*} [AddCommGroup A] [Module k A] {m : ℕ} (e : Module.Basis (Fin m) k A)

@[expose] def basisGL (M : Matrix (Fin m) (Fin m) k) (hM : M.det = 1) :
    LinearMap.GeneralLinearGroup k A :=
  Units.map (Matrix.toLinAlgEquiv e : Matrix (Fin m) (Fin m) k →* Module.End k A)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero))

theorem coe_basisGL (M : Matrix (Fin m) (Fin m) k) (hM : M.det = 1) :
    (basisGL e M hM : A →ₗ[k] A) = Matrix.toLin e e M :=
  rfl

theorem det_basisGL (M : Matrix (Fin m) (Fin m) k) (hM : M.det = 1) :
    LinearMap.det (basisGL e M hM : A →ₗ[k] A) = 1 := by
  rw [coe_basisGL, LinearMap.det_toLin, hM]

theorem mem_sesqUnitaryGroup_of_basis {hA : A →ₛₗ[σ] A →ₗ[k] k}
    (he : ∀ i j, hA (e i) (e j) = if i = j then 1 else 0) {g : LinearMap.GeneralLinearGroup k A}
    (π : Equiv.Perm (Fin m)) (t : Fin m → k) (ht : ∀ i, σ (t i) * t i = 1)
    (hg : ∀ i, (g : A →ₗ[k] A) (e i) = t i • e (π i)) : g ∈ sesqUnitaryGroup hA := by
  intro x y
  have hext : (hA.comp (g : A →ₗ[k] A)).compl₂ (g : A →ₗ[k] A) = hA := by
    refine LinearMap.ext_basis e e fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hg, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, he, π.injective.eq_iff]
    split_ifs with hij
    · subst hij
      rw [mul_one, RingHom.id_apply, mul_comm, ht]
    · rw [mul_zero, mul_zero]
  exact LinearMap.congr_fun₂ hext x y

@[expose] def pairDiag (i j : Fin m) (ζ : k) : Fin m → k :=
  Function.update (Function.update 1 j ζ⁻¹) i ζ

theorem det_pairDiag {i j : Fin m} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) :
    (diagonal (pairDiag i j ζ)).det = 1 := by
  rw [det_diagonal, pairDiag, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  simp [hζ]

@[expose] def pairDiagGL {i j : Fin m} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) :
    LinearMap.GeneralLinearGroup k A :=
  basisGL e (diagonal (pairDiag i j ζ)) (det_pairDiag hij hζ)

theorem pairDiagGL_apply_basis {i j : Fin m} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) (l : Fin m) :
    (pairDiagGL e hij hζ : A →ₗ[k] A) (e l) = pairDiag i j ζ l • e l := by
  rw [pairDiagGL, coe_basisGL, Matrix.toLin_self]
  simp [Matrix.diagonal_apply]

theorem repr_pairDiagGL_apply {i j : Fin m} (hij : i ≠ j) {ζ : k} (hζ : ζ ≠ 0) (x : A)
    (l : Fin m) :
    e.repr ((pairDiagGL e hij hζ : A →ₗ[k] A) x) l = pairDiag i j ζ l * e.repr x l := by
  rw [pairDiagGL, coe_basisGL, Matrix.toLin_apply, Module.Basis.repr_sum_self,
    Matrix.mulVec_diagonal]

theorem pairDiagGL_mem {hA : A →ₛₗ[σ] A →ₗ[k] k}
    (he : ∀ i j, hA (e i) (e j) = if i = j then 1 else 0) {i j : Fin m} (hij : i ≠ j) {ζ : k}
    (hζ : ζ ≠ 0) (hζ1 : σ ζ * ζ = 1) : pairDiagGL e hij hζ ∈ sesqSpecialUnitaryGroup hA := by
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨mem_sesqUnitaryGroup_of_basis e he 1 (pairDiag i j ζ)
    (fun l => ?_) (fun l => pairDiagGL_apply_basis e hij hζ l), det_basisGL _ _ _⟩
  simp only [pairDiag, Function.update_apply, Pi.one_apply]
  split_ifs
  · exact hζ1
  · rw [map_inv₀, ← mul_inv, hζ1, inv_one]
  · rw [map_one, mul_one]

@[expose] def swapSign (j : Fin m) : Fin m → k :=
  Function.update 1 j (-1)

theorem det_swapMatrix {i j : Fin m} (hij : i ≠ j) :
    ((Equiv.swap i j).permMatrix k * diagonal (swapSign j : Fin m → k)).det = 1 := by
  rw [det_mul, det_permutation, Equiv.Perm.sign_swap hij, det_diagonal, swapSign,
    Finset.prod_update_of_mem (Finset.mem_univ j)]
  simp

@[expose] def swapGL {i j : Fin m} (hij : i ≠ j) : LinearMap.GeneralLinearGroup k A :=
  basisGL e ((Equiv.swap i j).permMatrix k * diagonal (swapSign j : Fin m → k))
    (det_swapMatrix hij)

theorem swapGL_apply_basis {i j : Fin m} (hij : i ≠ j) (l : Fin m) :
    (swapGL e hij : A →ₗ[k] A) (e l) = (swapSign j l : k) • e (Equiv.swap i j l) := by
  rw [swapGL, coe_basisGL, Matrix.toLin_self]
  simp [Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.swap_apply_eq_iff]

theorem swapGL_mem {hA : A →ₛₗ[σ] A →ₗ[k] k}
    (he : ∀ i j, hA (e i) (e j) = if i = j then 1 else 0) {i j : Fin m} (hij : i ≠ j) :
    swapGL e hij ∈ sesqSpecialUnitaryGroup hA := by
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨mem_sesqUnitaryGroup_of_basis e he (Equiv.swap i j)
    (swapSign j) (fun l => ?_) (fun l => swapGL_apply_basis e hij l), det_basisGL _ _ _⟩
  simp only [swapSign, Function.update_apply, Pi.one_apply]
  split_ifs
  · rw [map_neg, map_one, neg_mul_neg, mul_one]
  · rw [map_one, mul_one]

end Basis

section Commutant

variable {A W : Type*} [AddCommGroup A] [Module k A] [AddCommGroup W] [Module k W]
  {hA : A →ₛₗ[σ] A →ₗ[k] k} {m : ℕ} (e : Module.Basis (Fin m) k A)

theorem eq_zero_of_forall_pairDiagGL_apply_eq (hm : 2 ≤ m) {ζ : k} (hζ : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {a : A} (ha : ∀ (i j : Fin m) (hij : i ≠ j), (pairDiagGL e hij hζ : A →ₗ[k] A) a = a) :
    a = 0 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  refine e.repr.injective (Finsupp.ext fun l => ?_)
  obtain ⟨j, hj⟩ := exists_ne l
  have h := congrArg (fun x => e.repr x l) (ha l j hj.symm)
  simp only [repr_pairDiagGL_apply, pairDiag, Function.update_self] at h
  have h' : (ζ - 1) * e.repr a l = 0 := by linear_combination h
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hζ1)

theorem exists_smul_prod_of_commute_summandGL
    (he : ∀ i j, hA (e i) (e j) = if i = j then 1 else 0) (hm : 2 ≤ m) {ζ : k}
    (hζ1 : σ ζ * ζ = 1) (hζ2 : ζ * ζ ≠ 1) {L : A × W →ₗ[k] A × W}
    (hL : ∀ g ∈ sesqSpecialUnitaryGroup hA, ∀ x,
      (summandGL k A W g : A × W →ₗ[k] A × W) (L x) =
        L ((summandGL k A W g : A × W →ₗ[k] A × W) x)) :
    ∃ (c : k) (D : W →ₗ[k] W), ∀ v w, L (v, w) = (c • v, D w) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hζne1 : ζ ≠ 1 := by
    rintro rfl
    simp at hζ2
  have hζinv : ζ⁻¹ ≠ ζ := fun h => hζ2 (calc ζ * ζ = ζ⁻¹ * ζ := by rw [h]
    _ = 1 := inv_mul_cancel₀ hζ0)
  have hd : ∀ (i j : Fin m) (hij : i ≠ j), pairDiagGL e hij hζ0 ∈ sesqSpecialUnitaryGroup hA :=
    fun i j hij => pairDiagGL_mem e he hij hζ0 hζ1
  have h0 : ∀ w, (L (0, w)).1 = 0 := by
    intro w
    refine eq_zero_of_forall_pairDiagGL_apply_eq e hm hζ0 hζne1 fun i j hij => ?_
    have h := congrArg Prod.fst (hL _ (hd i j hij) (0, w))
    have h0w : (summandGL k A W (pairDiagGL e hij hζ0) : A × W →ₗ[k] A × W) (0, w) = (0, w) := by
      rw [summandGL_apply, map_zero]
    rw [h0w, summandGL_apply_fst] at h
    exact h
  have hC : ∀ i, ∃ c : k, L (e i, 0) = (c • e i, 0) := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have hij : i ≠ j := hj.symm
    have h := hL _ (hd i j hij) (e i, 0)
    have hdi : (summandGL k A W (pairDiagGL e hij hζ0) : A × W →ₗ[k] A × W) (e i, 0) =
        ζ • (e i, 0) := by
      rw [summandGL_apply, pairDiagGL_apply_basis, pairDiag, Function.update_self]
      simp
    rw [hdi, map_smul] at h
    have h1 : (pairDiagGL e hij hζ0 : A →ₗ[k] A) (L (e i, 0)).1 = ζ • (L (e i, 0)).1 :=
      congrArg Prod.fst h
    have h2 : (L (e i, 0)).2 = ζ • (L (e i, 0)).2 := congrArg Prod.snd h
    have hx2 : (L (e i, 0)).2 = 0 := by
      have h3 : (ζ - 1) • (L (e i, 0)).2 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hζne1)
    have hx1 : ∀ l, l ≠ i → e.repr (L (e i, 0)).1 l = 0 := by
      intro l hl
      have h3 := congrArg (fun y => e.repr y l) h1
      simp only [repr_pairDiagGL_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
      have hne : pairDiag i j ζ l ≠ ζ := by
        simp only [pairDiag, Function.update_apply, hl, ↓reduceIte, Pi.one_apply]
        split_ifs
        · exact hζinv
        · exact fun h4 => hζne1 h4.symm
      have h4 : (pairDiag i j ζ l - ζ) * e.repr (L (e i, 0)).1 l = 0 := by
        linear_combination h3
      exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne)
    refine ⟨e.repr (L (e i, 0)).1 i, Prod.ext ?_ hx2⟩
    refine e.repr.injective (Finsupp.ext fun l => ?_)
    rw [map_smul, e.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hil
    · subst hil
      simp
    · rw [hx1 l (Ne.symm hil), smul_zero]
  choose c hc using hC
  have hceq : ∀ i j, i ≠ j → c i = c j := by
    intro i j hij
    have h := hL _ (swapGL_mem e he hij) (e i, 0)
    have hsi : (swapGL e hij : A →ₗ[k] A) (e i) = e j := by
      rw [swapGL_apply_basis, swapSign, Function.update_of_ne hij, Pi.one_apply, one_smul,
        Equiv.swap_apply_left]
    rw [hc i, summandGL_apply, summandGL_apply, map_smul, hsi, hc j] at h
    have h3 := congrArg (fun y : A × W => e.repr y.1 j) h
    simpa using h3
  let i₀ : Fin m := ⟨0, by omega⟩
  have hcall : ∀ i, c i = c i₀ := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
    · exact hceq i i₀ hi
  have hv : ∀ v : A, L (v, 0) = (c i₀ • v, 0) := by
    have hext : L ∘ₗ LinearMap.inl k A W = LinearMap.inl k A W ∘ₗ (c i₀ • LinearMap.id) :=
      e.ext fun i => by simp [hc i, hcall i]
    intro v
    simpa using LinearMap.congr_fun hext v
  refine ⟨c i₀, LinearMap.snd k A W ∘ₗ L ∘ₗ LinearMap.inr k A W, fun v w => ?_⟩
  have hvw : ((v, w) : A × W) = (v, 0) + (0, w) := by simp
  rw [hvw, map_add, hv v]
  refine Prod.ext ?_ ?_
  · simp [h0 w]
  · simp

end Commutant

theorem UnitaryFieldData.exists_norm_one_mul_self_ne_one {p f : ℕ} (h : UnitaryFieldData p f k) :
    ∃ ζ : k, h.bar ζ * ζ = 1 ∧ ζ * ζ ≠ 1 := by
  have := h.finite
  have hq := h.one_lt_pow
  by_contra! hcon
  have hle : (Units.map h.normHom).ker ≤ rootsOfUnity 2 k := by
    intro u hu
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
    have hn : (u : k) * h.bar u = 1 := h.mem_ker_normUnits.mp hu
    exact hcon u (by rw [mul_comm]; exact hn)
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_ker_normUnits_and_surjective.1] at h1
  have h2 := card_rootsOfUnity k 2
  omega

section Centralizer

variable {p f : ℕ} (h : UnitaryFieldData p f k) {A W : Type*} [AddCommGroup A] [Module k A]
  [FiniteDimensional k A] [AddCommGroup W] [Module k W]

theorem mem_centralizer_summandSpecialUnitary_inf_iff {hA : A →ₛₗ[h.bar] A →ₗ[k] k}
    (hAs : hA.IsSymm) (hAl : hA.SeparatingLeft) (hW : W →ₛₗ[h.bar] W →ₗ[k] k)
    (hm : 2 ≤ Module.finrank k A) (g : LinearMap.GeneralLinearGroup k (A × W)) :
    g ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
        sesqUnitaryGroup (sesqOrthSum hA hW) ↔
      ∃ a : kˣ, h.norm a = 1 ∧ ∃ gW ∈ sesqUnitaryGroup hW, ∀ (v : A) (w : W),
        (g : A × W →ₗ[k] A × W) (v, w) = ((a : k) • v, (gW : W →ₗ[k] W) w) := by
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hAs hAl
  obtain ⟨ζ, hζ1, hζ2⟩ := h.exists_norm_one_mul_self_ne_one
  have hcomm : ∀ g' : LinearMap.GeneralLinearGroup k (A × W),
      g' ∈ Subgroup.centralizer (summandSpecialUnitary hA W) →
      ∀ s ∈ sesqSpecialUnitaryGroup hA, ∀ x,
        (summandGL k A W s : A × W →ₗ[k] A × W) ((g' : A × W →ₗ[k] A × W) x) =
          (g' : A × W →ₗ[k] A × W) ((summandGL k A W s : A × W →ₗ[k] A × W) x) :=
    fun g' hg' s hs x => congrArg
      (fun u : LinearMap.GeneralLinearGroup k (A × W) => (u : A × W →ₗ[k] A × W) x)
      (Subgroup.mem_centralizer_iff.mp hg' _ ⟨s, hs, rfl⟩)
  constructor
  · rintro ⟨hgC, hgU⟩
    obtain ⟨c, D, hcD⟩ := exists_smul_prod_of_commute_summandGL e he hm hζ1 hζ2 (hcomm g hgC)
    obtain ⟨c', D', hcD'⟩ := exists_smul_prod_of_commute_summandGL e he hm hζ1 hζ2
      (hcomm g⁻¹ (Subgroup.inv_mem _ hgC))
    have h₁ : ∀ x, (g : A × W →ₗ[k] A × W)
        (((g⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W) x) = x :=
      fun x => by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]
    have h₂ : ∀ x, ((g⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W)
        ((g : A × W →ₗ[k] A × W) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    let i₀ : Fin (Module.finrank k A) := ⟨0, by omega⟩
    have hcc : c * c' = 1 := by
      have := congrArg (fun x : A × W => e.repr x.1 i₀) (h₁ (e i₀, 0))
      simpa [hcD, hcD', smul_smul] using this
    have hD : ∀ w, D (D' w) = w := fun w => by
      simpa [hcD, hcD'] using congrArg Prod.snd (h₁ (0, w))
    have hD' : ∀ w, D' (D w) = w := fun w => by
      simpa [hcD, hcD'] using congrArg Prod.snd (h₂ (0, w))
    have hnorm : h.norm c = 1 := by
      have := hgU (e i₀, 0) (e i₀, 0)
      rw [hcD, sesqOrthSum_apply, sesqOrthSum_apply] at this
      simp only [map_zero, add_zero, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, he,
        ↓reduceIte, RingHom.id_apply, mul_one] at this
      rw [UnitaryFieldData.norm]
      linear_combination this
    refine ⟨⟨c, c', hcc, by rw [mul_comm, hcc]⟩, hnorm,
      ⟨D, D', LinearMap.ext hD, LinearMap.ext hD'⟩, fun w w' => ?_, hcD⟩
    have := hgU (0, w) (0, w')
    simpa [hcD] using this
  · rintro ⟨a, ha, gW, hgW, hg⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, fun x y => ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      refine Units.ext (LinearMap.ext fun x => ?_)
      obtain ⟨v, w⟩ := x
      change (summandGL k A W s : A × W →ₗ[k] A × W) ((g : A × W →ₗ[k] A × W) (v, w)) =
        (g : A × W →ₗ[k] A × W) ((summandGL k A W s : A × W →ₗ[k] A × W) (v, w))
      rw [hg, summandGL_apply, summandGL_apply, hg, map_smul]
    · obtain ⟨v, w⟩ := x
      obtain ⟨v', w'⟩ := y
      rw [hg, hg, sesqOrthSum_apply, sesqOrthSum_apply]
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      rw [hgW w w']
      have ha' : h.bar a * a = 1 := by rw [mul_comm]; exact ha
      linear_combination hA v v' * ha'

open scoped commutatorElement in
theorem apply_inl_eq_of_isPerfect_of_le_centralizer_inf {hA : A →ₛₗ[h.bar] A →ₗ[k] k}
    (hAs : hA.IsSymm) (hAl : hA.SeparatingLeft) (hW : W →ₛₗ[h.bar] W →ₗ[k] k)
    (hm : 2 ≤ Module.finrank k A) (R : Subgroup (LinearMap.GeneralLinearGroup k (A × W)))
    (hR : R ≤ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
      sesqUnitaryGroup (sesqOrthSum hA hW))
    (hRp : Group.IsPerfect R) {g : LinearMap.GeneralLinearGroup k (A × W)} (hg : g ∈ R)
    (v : A) : (g : A × W →ₗ[k] A × W) (v, 0) = (v, 0) := by
  let F : Subgroup (LinearMap.GeneralLinearGroup k (A × W)) :=
    { carrier := {g | ∀ v : A, (g : A × W →ₗ[k] A × W) (v, 0) = (v, 0)}
      mul_mem' := fun {a b} ha hb v => by
        rw [Units.val_mul, Module.End.mul_apply, hb v, ha v]
      one_mem' := fun v => rfl
      inv_mem' := fun {a} ha v => by
        conv_lhs => rw [← ha v]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply] }
  have hscalar : ∀ a ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
      sesqUnitaryGroup (sesqOrthSum hA hW), ∃ c : kˣ,
      (∀ v, (a : A × W →ₗ[k] A × W) (v, 0) = ((c : k) • v, 0)) ∧
      ∀ v, ((a⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W) (v, 0) =
        (((c⁻¹ : kˣ) : k) • v, 0) := by
    intro a ha
    obtain ⟨c, -, gW, -, hcD⟩ :=
      (mem_centralizer_summandSpecialUnitary_inf_iff h hAs hAl hW hm a).mp ha
    refine ⟨c, fun v => by simp [hcD], fun v => ?_⟩
    have h1 : (a : A × W →ₗ[k] A × W) (((c⁻¹ : kˣ) : k) • v, 0) = (v, 0) := by
      simp [hcD, smul_smul]
    conv_lhs => rw [← h1]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hC : ∀ a b : LinearMap.GeneralLinearGroup k (A × W),
      a ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
        sesqUnitaryGroup (sesqOrthSum hA hW) →
      b ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
        sesqUnitaryGroup (sesqOrthSum hA hW) → ⁅a, b⁆ ∈ F := by
    intro a b ha hb v
    obtain ⟨ca, hca, hca'⟩ := hscalar a ha
    obtain ⟨cb, hcb, hcb'⟩ := hscalar b hb
    have hsc : (ca : k) * cb * ((ca⁻¹ : kˣ) : k) * ((cb⁻¹ : kˣ) : k) = 1 := by
      rw [mul_right_comm (ca : k), Units.mul_inv, one_mul, Units.mul_inv]
    change ((⁅a, b⁆ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W) (v, 0) = (v, 0)
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hcb', hca', hcb, hca, smul_smul, smul_smul,
      smul_smul, hsc, one_smul]
  have hRF : R ≤ F := calc
    R = ⁅R, R⁆ := (Subgroup.isPerfect_iff.mp hRp).symm
    _ ≤ F := Subgroup.commutator_le.mpr fun a ha b hb => hC a b (hR ha) (hR hb)
  exact hRF hg v

theorem special_unitary_summand_centralizer (hA : A →ₛₗ[h.bar] A →ₗ[k] k) (hAs : hA.IsSymm)
    (hAl : hA.SeparatingLeft) (hW : W →ₛₗ[h.bar] W →ₗ[k] k) (hm : 2 ≤ Module.finrank k A) :
    summandSpecialUnitary hA W ≤ sesqUnitaryGroup (sesqOrthSum hA hW) ∧
    {x : A × W | ∀ d ∈ summandSpecialUnitary hA W, (d : A × W →ₗ[k] A × W) x = x} =
      Set.range (LinearMap.inr k A W) ∧
    (∀ g : LinearMap.GeneralLinearGroup k (A × W),
      g ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
          sesqUnitaryGroup (sesqOrthSum hA hW) ↔
        ∃ a : kˣ, h.norm a = 1 ∧ ∃ gW ∈ sesqUnitaryGroup hW, ∀ (v : A) (w : W),
          (g : A × W →ₗ[k] A × W) (v, w) = ((a : k) • v, (gW : W →ₗ[k] W) w)) ∧
    ∀ R : Subgroup (LinearMap.GeneralLinearGroup k (A × W)),
      R ≤ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
          sesqUnitaryGroup (sesqOrthSum hA hW) →
      Group.IsPerfect R → ∀ g ∈ R, ∀ v : A, (g : A × W →ₗ[k] A × W) (v, 0) = (v, 0) := by
  refine ⟨summandSpecialUnitary_le hA hW, ?_,
    mem_centralizer_summandSpecialUnitary_inf_iff h hAs hAl hW hm,
    fun R hR hRp g hg v => apply_inl_eq_of_isPerfect_of_le_centralizer_inf h hAs hAl hW hm R hR
      hRp hg v⟩
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hAs hAl
  obtain ⟨ζ, hζ1, hζ2⟩ := h.exists_norm_one_mul_self_ne_one
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hζne1 : ζ ≠ 1 := by
    rintro rfl
    simp at hζ2
  ext ⟨v, w⟩
  constructor
  · intro hx
    have hv : v = 0 := eq_zero_of_forall_pairDiagGL_apply_eq e hm hζ0 hζne1 fun i j hij =>
      congrArg Prod.fst (hx _ ⟨_, pairDiagGL_mem e he hij hζ0 hζ1, rfl⟩)
    exact ⟨w, by rw [hv]; rfl⟩
  · rintro ⟨w', hw'⟩ _ ⟨g, -, rfl⟩
    rw [← hw']
    simp

end Centralizer

theorem natural_odd_special_unitary_summand_centralizer {p f : ℕ} {k : Type*} [Field k]
    (h : UnitaryFieldData p f k) (_hp : Odd p) {A W : Type*} [AddCommGroup A] [Module k A]
    [FiniteDimensional k A] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (hA : A →ₛₗ[h.bar] A →ₗ[k] k) (hAs : hA.IsSymm) (hAn : hA.Nondegenerate)
    (hW : W →ₛₗ[h.bar] W →ₗ[k] k) (_hWs : hW.IsSymm) (_hWn : hW.Nondegenerate)
    (hm : 2 ≤ Module.finrank k A) :
    summandSpecialUnitary hA W ≤ sesqUnitaryGroup (sesqOrthSum hA hW) ∧
    {x : A × W | ∀ d ∈ summandSpecialUnitary hA W, (d : A × W →ₗ[k] A × W) x = x} =
      Set.range (LinearMap.inr k A W) ∧
    (∀ g : LinearMap.GeneralLinearGroup k (A × W),
      g ∈ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
          sesqUnitaryGroup (sesqOrthSum hA hW) ↔
        ∃ a : kˣ, h.norm a = 1 ∧ ∃ gW ∈ sesqUnitaryGroup hW, ∀ (v : A) (w : W),
          (g : A × W →ₗ[k] A × W) (v, w) = ((a : k) • v, (gW : W →ₗ[k] W) w)) ∧
    ∀ R : Subgroup (LinearMap.GeneralLinearGroup k (A × W)),
      R ≤ Subgroup.centralizer (summandSpecialUnitary hA W) ⊓
          sesqUnitaryGroup (sesqOrthSum hA hW) →
      Group.IsPerfect R → ∀ g ∈ R, ∀ v : A, (g : A × W →ₗ[k] A × W) (v, 0) = (v, 0) :=
  special_unitary_summand_centralizer h hA hAs hAn.1 hW hm

end CFSG.LocalAnalysis.ComponentInitial
