module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem eq_one_of_fix_norm_one {σ τ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (hσ : σ ≠ 1)
    (hστ : ∀ x, σ (τ x) = τ (σ x)) (hτ : ∀ u, u * σ u = 1 → τ u = u) : τ = 1 := by
  have hc : ∀ x, x ≠ 0 → σ (τ x / x) = τ x / x := by
    intro x hx
    have hσx : σ x ≠ 0 := by
      intro h
      apply hx
      rw [← hσσ x, h, map_zero]
    have hu := hτ (x / σ x) (by rw [map_div₀, hσσ]; field_simp)
    rw [map_div₀] at hu
    have hτx : τ x ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hστx : τ (σ x) ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have key : τ x * σ x = x * τ (σ x) := by
      field_simp at hu
      linear_combination hu
    have e : σ (τ x / x) = τ (σ x) / σ x := by rw [map_div₀ σ, hστ x]
    rw [e, div_eq_div_iff hσx hx]
    linear_combination -key
  have hmain : ∀ x, σ x ≠ x → τ x = x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (map_zero σ)
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      rw [eq_neg_of_add_eq_zero_left h, map_neg, map_one]
    set c := τ x / x
    set d := τ (x + 1) / (x + 1)
    have hcx : τ x = c * x := by rw [div_mul_cancel₀ _ hx0]
    have hdx : τ (x + 1) = d * (x + 1) := by rw [div_mul_cancel₀ _ hx1]
    have hσc := hc x hx0
    have hσd := hc (x + 1) hx1
    have hlin : (d - c) * x = 1 - d := by
      have := hdx
      rw [map_add, map_one, hcx] at this
      linear_combination -this
    by_cases hdc : d = c
    · rw [hdc, sub_self, zero_mul] at hlin
      have hc1 : c = 1 := by linear_combination hlin
      rw [hcx, hc1, one_mul]
    · exfalso
      apply hx
      have hxe : x = (1 - d) / (d - c) := by
        rw [eq_div_iff (sub_ne_zero.2 hdc), mul_comm, hlin]
      rw [hxe, map_div₀, map_sub, map_sub, map_one, hσc, hσd]
  obtain ⟨x₀, hx₀⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  refine RingEquiv.ext fun x => ?_
  by_cases hx : σ x = x
  · by_cases hx0 : x = 0
    · rw [hx0, map_zero]
      rfl
    have hxx₀ : σ (x * x₀) ≠ x * x₀ := by
      rw [map_mul, hx]
      intro h
      exact hx₀ (mul_left_cancel₀ hx0 h)
    have h1 := hmain _ hxx₀
    rw [map_mul, hmain _ hx₀] at h1
    have hx₀0 : x₀ ≠ 0 := by
      rintro rfl
      exact hx₀ (map_zero σ)
    exact mul_right_cancel₀ hx₀0 h1
  · exact hmain x hx

@[expose] def gfLift (σ : K ≃+* K) :
    SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K :=
  (SpecialLinearGroup.map σ.toRingHom).comp (CatalogueBGraphForm.slGraphAut n K).toMonoidHom

theorem fieldAut_mul_dualAut_proj (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    (fieldAut n K σ * dualAut n K) (proj n K g) = proj n K (gfLift σ g) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  rfl

variable (n) in
abbrev unitarySL (σ : K ≃+* K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (SUid σ n).comap SpecialLinearGroup.toGL

theorem mem_unitarySL {σ : K ≃+* K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ unitarySL n σ ↔ conjTr σ (g : Matrix (Fin n) (Fin n) K) * g = 1 := by
  rw [mem_comap, mem_SUid]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem gfLift_eq_iff {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (g : SpecialLinearGroup (Fin n) K) :
    gfLift σ g = g ↔ g ∈ unitarySL n σ := by
  rw [mem_unitarySL]
  have h1 : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1' : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmm : ∀ X : Matrix (Fin n) (Fin n) K, (X.map σ).map σ = X := fun X => by
    ext i j
    simp [hσσ]
  have hlift : ((gfLift σ g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map σ := rfl
  constructor
  · intro h
    have h' : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map σ =
        (g : Matrix (Fin n) (Fin n) K) := by rw [← hlift, h]
    have e : conjTr σ (g : Matrix (Fin n) (Fin n) K) =
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [conjTr, ← h', hmm, transpose_transpose]
    rw [e, h1']
  · intro h
    apply Subtype.ext
    rw [hlift]
    have h2 : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ =
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      calc ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ
          = ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * ((g : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [h1, Matrix.mul_one]
        _ = ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [← Matrix.mul_assoc, ← conjTr, h, Matrix.one_mul]
    have h3 : (g : Matrix (Fin n) (Fin n) K).map σ =
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
      rw [← h2, transpose_transpose]
    rw [← h3, hmm]

theorem conj_mem_unitarySL {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x)
    {h : SpecialLinearGroup (Fin n) K} (hh : h⁻¹ * gfLift σ h ∈ scalars n K)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ unitarySL n σ) :
    h * g * h⁻¹ ∈ unitarySL n σ := by
  rw [← gfLift_eq_iff hσσ]
  exact conj_mem_eqLocus_of_scalar (gfLift σ) hh ((gfLift_eq_iff hσσ g).2 hg)

theorem signSL_mem_unitarySL (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) :
    signSL K {i, j} (by rw [Finset.card_pair hij]; exact even_two) ∈ unitarySL n σ := by
  rw [mem_unitarySL, coe_signSL, conjTr]
  have hmap : (signMat K {i, j}).map σ = signMat K {i, j} := by
    ext a b
    simp only [signMat, map_apply, diagonal_apply]
    split_ifs <;> simp
  rw [hmap, signMat, diagonal_transpose, ← signMat, signMat_mul_self]

@[expose] def rotSL {i j : Fin n} (hij : i ≠ j) : SpecialLinearGroup (Fin n) K :=
  SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij.symm (-1) *
    SpecialLinearGroup.transvection hij 1

theorem coe_rotSL {i j : Fin n} (hij : i ≠ j) :
    ((rotSL hij : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 - single i i 1 - single j j 1 + single i j 1 - single j i 1 := by
  have h2 : ∀ (a d : Fin n) (c c' : K), single a j c * single i d c' = 0 := fun a d c c' => by
    rw [single_mul_single_of_ne]; exact hij.symm
  have hneg : ∀ a b : Fin n, single a b (-1 : K) = -single a b 1 := fun a b => by
    ext x y
    simp only [single_apply, Matrix.neg_apply]
    split_ifs <;> simp
  simp only [rotSL, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, hneg]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, single_mul_single_same, h2, add_zero, mul_one]
  abel

theorem rotSL_mem_unitarySL (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) :
    rotSL hij ∈ unitarySL n σ := by
  rw [mem_unitarySL, coe_rotSL, conjTr]
  have hmap : (1 - single i i 1 - single j j 1 + single i j 1 - single j i (1 : K)).map σ =
      1 - single i i 1 - single j j 1 + single i j 1 - single j i 1 := by
    ext a b
    simp only [map_apply, Matrix.add_apply, Matrix.sub_apply, single_apply, one_apply]
    split_ifs <;> simp
  have h1 : ∀ a d : Fin n, single a i (1 : K) * single j d 1 = 0 := fun a d => by
    rw [single_mul_single_of_ne]; exact hij
  have h2 : ∀ a d : Fin n, single a j (1 : K) * single i d 1 = 0 := fun a d => by
    rw [single_mul_single_of_ne]; exact hij.symm
  rw [hmap]
  simp only [transpose_add, transpose_sub, transpose_one, transpose_single, Matrix.add_mul,
    Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
    single_mul_single_same, mul_one, h1, h2]
  abel

@[expose] def diagSL {i j : Fin n} (hij : i ≠ j) {u : K} (hu : u ≠ 0) :
    SpecialLinearGroup (Fin n) K :=
  ⟨diagonal fun k => if k = i then u else if k = j then u⁻¹ else 1, by
    rw [det_diagonal]
    have : ∀ k : Fin n, (if k = i then u else if k = j then u⁻¹ else 1) =
        (if k = i then u else 1) * (if k = j then u⁻¹ else 1) := fun k => by
      by_cases hki : k = i
      · subst hki
        simp [hij]
      · simp [hki]
    rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ i, Finset.prod_ite_eq' Finset.univ j]
    simp [hu]⟩

theorem diagSL_mem_unitarySL {σ : K ≃+* K} {i j : Fin n} (hij : i ≠ j) {u : K} (hu : u ≠ 0)
    (hN : σ u * u = 1) : diagSL hij hu ∈ unitarySL n σ := by
  rw [mem_unitarySL, conjTr]
  change ((diagonal fun k => if k = i then u else if k = j then u⁻¹ else 1).map σ)ᵀ *
    diagonal (fun k => if k = i then u else if k = j then u⁻¹ else 1) = 1
  rw [diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext k
  by_cases hki : k = i
  · simp [hki, hN]
  · by_cases hkj : k = j
    · subst hkj
      simp only [hki, ↓reduceIte, map_inv₀]
      rw [← mul_inv, hN, inv_one]
    · simp [hki, hkj]

theorem eq_scalar_of_commute_sign_rot (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {D : Matrix (Fin n) (Fin n) K}
    (hs : ∀ i j : Fin n, (hij : i ≠ j) → D * signMat K {i, j} = signMat K {i, j} * D)
    (hr : ∀ i j : Fin n, i ≠ j → D * (1 - single i i 1 - single j j 1 + single i j 1 -
      single j i 1) = (1 - single i i 1 - single j j 1 + single i j 1 - single j i 1) * D) :
    D = Matrix.scalar (Fin n) (D ⟨0, by omega⟩ ⟨0, by omega⟩) := by
  have hoff : ∀ x y : Fin n, x ≠ y → D x y = 0 := by
    intro x y hxy
    obtain ⟨z, hzx, hzy⟩ : ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
      by_contra hc
      push Not at hc
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {x, y} := fun z _ => by
        by_cases hz : z = x
        · simp [hz]
        · simp [hc z hz]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hxy] at this
      omega
    have e := congrFun (congrFun (hs y z hzy.symm) x) y
    simp only [signMat, mul_diagonal, diagonal_mul, Finset.mem_insert, Finset.mem_singleton,
      hxy, hzx.symm, or_self, ↓reduceIte, true_or] at e
    have : (2 : K) * D x y = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left h2
  have hdiag : ∀ i j : Fin n, D i i = D j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have e := congrFun (congrFun (hr i j hij) i) j
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
      Matrix.add_apply, Matrix.sub_apply, mul_single_apply_same,
      single_mul_apply_same, mul_one, one_mul, mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij),
      single_mul_apply_of_ne _ _ _ _ _ hij] at e
    rw [hoff i j hij] at e
    linear_combination e
  ext i j
  rw [scalar_apply, diagonal_apply]
  split_ifs with hij
  · rw [hij, hdiag j ⟨0, by omega⟩]
  · exact hoff i j hij

theorem commutator_eq_self_of_isQuasisimple {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsQuasisimple H) : ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, hH.1.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem map_signSL (τ : K ≃+* K) (J : Finset (Fin n)) (hJ : Even J.card) :
    SpecialLinearGroup.map τ.toRingHom (signSL K J hJ) = signSL K J hJ := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_signSL, RingHom.mapMatrix_apply]
  ext a b
  simp only [signMat, map_apply, diagonal_apply]
  split_ifs <;> simp

theorem map_rotSL (τ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.map τ.toRingHom (rotSL hij) = rotSL hij := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_rotSL, RingHom.mapMatrix_apply]
  ext a b
  simp only [map_apply, Matrix.add_apply, Matrix.sub_apply, single_apply, one_apply]
  split_ifs <;> simp

theorem isQuasisimple_unitarySL [Finite K] {p e : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hKe : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n) :
    IsQuasisimple (unitarySL n (unitaryInvolution K p e)) := by
  set σ := unitaryInvolution K p e with hσ
  have hnq : (n, p ^ e) ≠ (3, 2) := by
    intro h
    have h2 : p ^ e = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ e) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rw [h2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hmap : (unitarySL n σ).map SpecialLinearGroup.toGL = SUid σ n := by
    ext G
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hG
      have hGe : SpecialLinearGroup.toGL
          (⟨(G : Matrix (Fin n) (Fin n) K), hG.1⟩ : SpecialLinearGroup (Fin n) K) = G :=
        Units.ext rfl
      refine ⟨_, ?_, hGe⟩
      show _ ∈ unitarySL n σ
      exact Subgroup.mem_comap.2 (by rw [hGe]; exact hG)
  obtain ⟨P, hP⟩ := exists_wittMatrix hKe n
  have hSU : IsQuasisimple (SUid σ n) :=
    LocalCores.isQuasisimple_of_mulEquiv (conjEquiv P hP) (isQuasisimple_SU hKe hn hnq)
  exact LocalCores.isQuasisimple_of_mulEquiv (((unitarySL n σ).equivMapOfInjective _
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm hSU

theorem isQuasisimple_unitaryImage [Finite K] {p e : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hKe : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) :
    IsQuasisimple ((unitarySL n (unitaryInvolution K p e)).map (conjProj n K)) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  refine LocalCores.isQuasisimple_map (isQuasisimple_unitarySL hp2 hKe hn) _ fun hle => ?_
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hmem := signSL_mem_unitarySL (unitaryInvolution K p e) h01
  have hker := hle hmem
  have hproj : proj n K (signSL K {⟨0, by omega⟩, ⟨1, by omega⟩}
      (by rw [Finset.card_pair h01]; exact even_two)) = 1 :=
    hinj (by rw [map_one]; exact hker)
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hproj
  have e0 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
  have e2 := congrFun (congrFun hc ⟨2, by omega⟩) ⟨2, by omega⟩
  simp only [coe_signSL, signMat, diagonal_apply_eq, scalar_apply, Finset.mem_insert,
    Finset.mem_singleton, true_or, ↓reduceIte] at e0 e2
  simp only [Fin.ext_iff, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, or_self,
    ↓reduceIte] at e2
  apply h2
  linear_combination e2 - e0

theorem graphField_oddCoreIn_eq_bot [Finite K] {p e : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hKe : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B) :
    oddCoreIn B (fieldAut n K (unitaryInvolution K p e) * dualAut n K) = ⊥ := by
  set σ := unitaryInvolution K p e with hσdef
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hKe
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hKe
    intro h
    exact ha (by rw [← hσdef, h]; rfl)
  have hστ : ∀ τ : K ≃+* K, ∀ x, σ (τ x) = τ (σ x) := fun τ x => by
    rw [hσdef, unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hq := isQuasisimple_unitaryImage hp2 hKe hn hinj
  have hfix : ∀ g ∈ unitarySL n σ,
      (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g :=
    fun g hg => commute_oddCoreIn_of_fixed hinj hB (gfLift σ) (fieldAut_mul_dualAut_proj σ)
      (fun g hg => (gfLift_eq_iff hσσ g).2 hg) (fun _ hh _ hg => conj_mem_unitarySL hσσ hh hg)
      hq hy hg
  have hperf := commutator_eq_self_of_isQuasisimple (isQuasisimple_unitarySL hp2 hKe hn)
  have hex : ∀ g ∈ unitarySL n σ, (D : Matrix (Fin n) (Fin n) K) *
      ((SpecialLinearGroup.map τ.toRingHom g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g := by
    intro g hg
    have h := slConj_map_eq_of_commutator_eq hperf hfix hg
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simpa only [CatalogueBHigherLinearAction.slConjugation_matrix] using this
  have hDD : ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ g ∈ unitarySL n σ, SpecialLinearGroup.map τ.toRingHom g = g →
      (D : Matrix (Fin n) (Fin n) K) * g = g * D := by
    intro g hg hgτ
    have h1 := hex g hg
    rw [hgτ] at h1
    calc (D : Matrix (Fin n) (Fin n) K) * g
        = (D : Matrix (Fin n) (Fin n) K) * g * (((D⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * D) := by rw [hDD, Matrix.mul_one]
      _ = g * D := by rw [← Matrix.mul_assoc, h1]
  have hDs : (D : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) ((D : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) := by
    refine eq_scalar_of_commute_sign_rot h2 hn (fun i j hij => ?_) (fun i j hij => ?_)
    · have := hcomm _ (signSL_mem_unitarySL σ hij) (map_signSL τ _ _)
      rwa [coe_signSL] at this
    · have := hcomm _ (rotSL_mem_unitarySL σ hij) (map_rotSL τ hij)
      rwa [coe_rotSL] at this
  have hD : conjAut n K D = 1 := conjAut_eq_one_of_eq_scalar _ hDs
  have hτ : τ = 1 := by
    refine eq_one_of_fix_norm_one hσσ hσ1 (hστ τ) fun u hu => ?_
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hu
      exact zero_ne_one hu
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hN : σ u * u = 1 := by rw [mul_comm]; exact hu
    have h1 := hex _ (diagSL_mem_unitarySL h01 hu0 hN)
    have hsc : ∀ M : Matrix (Fin n) (Fin n) K, (D : Matrix (Fin n) (Fin n) K) * M *
        ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
      intro M
      have hcD : Commute (D : Matrix (Fin n) (Fin n) K) M := by
        rw [hDs]
        exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) M
      rw [hcD.eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    rw [hsc] at h1
    have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    simpa [diagSL] using this
  rw [hD, hτ, map_one, one_mul]

theorem graphField_eq_bot [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL n K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (htA : ψ t = conjAut n K A * fieldAut n K σ * dualAut n K) {Y : Subgroup X}
    (hYO : Y ≤ oddCentralizerCore t) : Y = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
    rw [← htA, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨hfe, hσp, H, hH⟩ :=
    LocalAnalysis.ComponentInitial.LinearFlag.odd_linear_graph_field_involution_conjugacy hp hf
      hKc hn A σ hσ hα
  obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
  have hKe : Nat.card K = (p ^ e) ^ 2 := by rw [hKc, he, ← pow_mul, mul_comm]
  have hσe : σ = unitaryInvolution K p e := by
    ext x
    rw [hσp, unitaryInvolution_apply, he, Nat.mul_div_cancel_left _ two_pos]
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut n K H)⁻¹
  set ψ' := (MulAut.conj (conjAut n K H)⁻¹).toMonoidHom.comp ψ with hψ'def
  have hψ't : ψ' t = fieldAut n K σ * dualAut n K := by
    change (conjAut n K H)⁻¹ * ψ t * ((conjAut n K H)⁻¹)⁻¹ = _
    rw [htA, hH]
    group
  refine eq_bot_of_oddCoreIn hinj' ?_ hYO
  rw [hψ't, hσe]
  exact graphField_oddCoreIn_eq_bot hp2 hKe hn hinj hInn'

end CFSG.ComponentClassification.Burgoyne.PSL
