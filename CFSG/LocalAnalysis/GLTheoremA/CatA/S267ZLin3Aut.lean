module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
import CFSG.LieType.SeitzGeneration.OuterLinearDescent
import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {K : Type} [Field K]

noncomputable abbrev slC : GL (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K

noncomputable abbrev slF : (K ≃+* K) →* MulAut (SpecialLinearGroup (Fin 3) K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K

theorem slC_coe (A : GL (Fin 3) K) (g : SpecialLinearGroup (Fin 3) K) :
    ((slC A g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A.val * (g : Matrix (Fin 3) (Fin 3) K) * (A⁻¹).val :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix 3 K A g

theorem slF_coe (σ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    ((slF σ g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K).map σ := rfl

theorem slC_mul_slF_coe (A : GL (Fin 3) K) (σ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    (((slC A * slF σ) g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A.val * (g : Matrix (Fin 3) (Fin 3) K).map σ * (A⁻¹).val := by
  rw [MulAut.mul_apply, slC_coe, slF_coe]

theorem eq_one_of_mul_inv_mem_center {G : Type*} [Group G] (hG : commutator G = ⊤) {γ : MulAut G}
    (h : ∀ g, γ g * g⁻¹ ∈ Subgroup.center G) : γ = 1 := by
  let f : G →* Subgroup.center G :=
    { toFun := fun g => ⟨γ g * g⁻¹, h g⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [map_mul, Subgroup.coe_mul]
        have hy := Subgroup.mem_center_iff.1 (h y)
        calc γ x * γ y * (x * y)⁻¹ = γ x * ((γ y * y⁻¹) * x⁻¹) := by group
          _ = γ x * (x⁻¹ * (γ y * y⁻¹)) := by rw [hy x⁻¹]
          _ = γ x * x⁻¹ * (γ y * y⁻¹) := by group }
  ext x
  have hx : x ∈ f.ker := Abelianization.commutator_subset_ker f (hG ▸ Subgroup.mem_top x)
  have h1 : γ x * x⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

theorem descendAut_injective : Function.Injective (descendAut 3 K) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine eq_one_of_mul_inv_mem_center
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (le_refl 3)) fun g => ?_
  have h1 := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K g)) hγ
  simp only [descendAut_proj, MulAut.one_apply] at h1
  have h2 : (γ g)⁻¹ * g ∈ scalars 3 K := proj_eq_proj_iff.1 h1
  rw [← scalars_eq_center]
  have h3 := (scalars 3 K).inv_mem h2
  rw [_root_.mul_inv_rev, inv_inv] at h3
  have h4 : γ g * g⁻¹ = (γ g) * (g⁻¹ * γ g) * (γ g)⁻¹ := by group
  rw [h4]
  exact (scalars_normal 3 K).conj_mem _ h3 (γ g)

theorem descendAut_slC (A : GL (Fin 3) K) : descendAut 3 K (slC A) = conjAut 3 K A := rfl

theorem descendAut_slF (σ : K ≃+* K) : descendAut 3 K (slF σ) = fieldAut 3 K σ := rfl

theorem exists_eq_slC_mul_slF [Finite K] {γ : MulAut (SpecialLinearGroup (Fin 3) K)}
    (hγ : Odd (orderOf γ)) : ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), γ = slC A * slF σ := by
  have hodd : Odd (orderOf (descendAut 3 K γ)) :=
    Odd.of_dvd_nat hγ (orderOf_map_dvd (descendAut 3 K) γ)
  have hE := CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
    (le_refl 3) hodd
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.1 hE
  refine ⟨A, σ, descendAut_injective ?_⟩
  rw [hAσ, map_mul, descendAut_slC, descendAut_slF]

theorem slC_eq_one_iff [Finite K] (A : GL (Fin 3) K) :
    slC A = 1 ↔ ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = A := by
  constructor
  · intro h
    have h1 : conjAut 3 K A * fieldAut 3 K 1 = 1 := by
      rw [map_one, mul_one, ← descendAut_slC, h, map_one]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) A 1 h1).2
  · rintro ⟨c, rfl⟩
    exact CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar 3 K c

theorem slC_toGL (g : SpecialLinearGroup (Fin 3) K) :
    slC (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj g := by
  ext x : 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [slC_coe, MulAut.conj_apply]
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.toGL]

theorem slF_mul_slC_mul_inv (σ : K ≃+* K) (A : GL (Fin 3) K) :
    slF σ * slC A * (slF σ)⁻¹ = slC (Matrix.GeneralLinearGroup.map (σ : K →+* K) A) := by
  ext g : 1
  apply Subtype.ext
  change ((slF σ (slC A (((slF σ)⁻¹ : MulAut _) g)) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((slC _ g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [← map_inv, slF_coe, slC_coe, slF_coe, slC_coe, Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
  have hid : (⇑σ ∘ ⇑(σ⁻¹ : K ≃+* K)) = id := by
    funext x
    simp [RingAut.inv_apply]
  rw [hid, Matrix.map_id]
  rfl

theorem exists_cube_of_fixed [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {x : K} (hx : x ≠ 0) (hxσ : σ x = x) : ∃ c : K, c ^ 3 = x := by
  classical
  obtain ⟨h3f, hq₀⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ
  set q₀ := Nat.card (semilinearFixedSubfield σ) with hq₀def
  have hKq : Nat.card K = q₀ ^ 3 := by
    rw [hK, hq₀, ← pow_mul, Nat.div_mul_cancel h3f]
  have hq₀2 : 2 ≤ q₀ := Finite.one_lt_card
  have hx0 : (⟨x, hxσ⟩ : semilinearFixedSubfield σ) ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hxq : x ^ (q₀ - 1) = 1 := by
    have : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨x, hxσ⟩ : semilinearFixedSubfield σ) hx0
    rw [← Nat.card_eq_fintype_card] at h1
    exact congrArg Subtype.val h1
  have : Fintype Kˣ := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hgen : ∀ y : Kˣ, ∃ k : ℕ, g ^ k = y := by
    intro y
    have hy : y ∈ Subgroup.zpowers g := by
      have htop : Subgroup.zpowers g = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hg]
      rw [htop]
      exact Subgroup.mem_top y
    exact (mem_powers_iff_mem_zpowers).2 hy
  obtain ⟨k, hk⟩ := hgen (Units.mk0 x hx)
  have hn : Nat.card Kˣ = (q₀ - 1) * (q₀ ^ 2 + q₀ + 1) := by
    rw [Nat.card_units, hKq]
    obtain ⟨t, ht⟩ : ∃ t, q₀ = t + 1 := ⟨q₀ - 1, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hgk : g ^ (k * (q₀ - 1)) = 1 := by
    rw [pow_mul, hk]
    exact Units.ext (by simpa using hxq)
  have hdvd : Nat.card Kˣ ∣ k * (q₀ - 1) := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hgk
  rw [hn, mul_comm k] at hdvd
  have hdvd2 : q₀ ^ 2 + q₀ + 1 ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have h3q : 3 ∣ q₀ ^ 2 + q₀ + 1 := by
    obtain ⟨t, ht⟩ := h3
    have hq : q₀ = 3 * t + 1 := by omega
    rw [hq]
    exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
  obtain ⟨m, hm⟩ := h3q.trans hdvd2
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hm, hk, Units.val_mk0]

theorem slC_mem_range_conj_of_commute [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (h3 : 3 ∣ Nat.card (semilinearFixedSubfield σ) - 1) {A : GL (Fin 3) K}
    (h : slF σ * slC A = slC A * slF σ) :
    slC A ∈ (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range := by
  have h1 : slC (Matrix.GeneralLinearGroup.map (σ : K →+* K) A) = slC A := by
    rw [← slF_mul_slC_mul_inv, h, mul_inv_cancel_right]
  have h2 : slC (Matrix.GeneralLinearGroup.map (σ : K →+* K) A * A⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (slC_eq_one_iff _).1 h2
  have hX : (A : Matrix (Fin 3) (Fin 3) K).map σ = (c : K) • (A : Matrix (Fin 3) (Fin 3) K) := by
    have h3 : Matrix.GeneralLinearGroup.map (σ : K →+* K) A =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c * A := by
      rw [hc, inv_mul_cancel_right]
    have h4 : (A : Matrix (Fin 3) (Fin 3) K).map σ =
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) c * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← h3]
      rfl
    rw [h4, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.smul_eq_diagonal_mul]
    rfl
  have hA0 : (A : Matrix (Fin 3) (Fin 3) K) ≠ 0 := Units.ne_zero A
  obtain ⟨μ, hμ, hμA⟩ := CFSG.LieType.SeitzGeneration.exists_rational_smul Nat.prime_three hℓ hf hK σ hσ
    hA0 hX
  set d := (μ • (A : Matrix (Fin 3) (Fin 3) K)).det with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hμ) (by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _)
  have hdσ : σ d = d := by
    have h5 := RingHom.map_det (σ : K →+* K) (μ • (A : Matrix (Fin 3) (Fin 3) K))
    rw [RingHom.mapMatrix_apply] at h5
    change (σ : K →+* K) d = d
    rw [hd, h5]
    congr 1
  obtain ⟨c', hc'⟩ := exists_cube_of_fixed hℓ hf hK hσ h3 hd0 hdσ
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hc'
    exact hd0 hc'.symm
  set S0 : Matrix (Fin 3) (Fin 3) K := (c'⁻¹ * μ) • (A : Matrix (Fin 3) (Fin 3) K) with hS0
  have hd' : d = μ ^ 3 * (A : Matrix (Fin 3) (Fin 3) K).det := by
    rw [hd, Matrix.det_smul, Fintype.card_fin]
  have hS0det : S0.det = 1 := by
    rw [hS0, Matrix.det_smul, Fintype.card_fin, mul_pow, inv_pow, mul_assoc, ← hd', ← hc',
      inv_mul_cancel₀ (pow_ne_zero 3 hc'0)]
  let S : SpecialLinearGroup (Fin 3) K := ⟨S0, hS0det⟩
  have hu0 : c'⁻¹ * μ ≠ 0 := mul_ne_zero (inv_ne_zero hc'0) hμ
  have hSA : Matrix.SpecialLinearGroup.toGL S =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hu0) * A := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
    change S0 = _
    rw [hS0, Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨S, ?_⟩
  rw [← slC_toGL, hSA, map_mul,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

end
