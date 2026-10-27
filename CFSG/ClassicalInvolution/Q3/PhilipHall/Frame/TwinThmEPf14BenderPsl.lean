module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinThmE

namespace BenderPsl

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts

section Cyc

variable {K : Type} [Field K] [Finite K]

theorem pglAction_inj : Function.Injective (pglAction K) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K

noncomputable def innDiag (K : Type) [Field K] : Subgroup (MulAut (PSL2 K)) :=
  (stdPinnedPSL2 K).inndiag

theorem innDiag_normal : (innDiag K).Normal :=
  (stdPinnedPSL2_stable (K := K)).normal

instance innDiag_normal_inst : (innDiag K).Normal := innDiag_normal

theorem quot_innDiag_isCyclic : IsCyclic (MulAut (PSL2 K) ⧸ innDiag K) := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  refine isCyclic_of_surjective ((QuotientGroup.mk' (innDiag K)).comp (psl2FieldAut K)) ?_
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
  refine ⟨σ, ?_⟩
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  have := (innDiag_normal_inst (K := K)).conj_mem _ (show pglAction K g ∈ innDiag K from ⟨g, rfl⟩)
    ((psl2FieldAut K σ)⁻¹)
  simpa [mul_assoc] using this

end Cyc

section Pgl

open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pow_four_injective : Function.Injective (fun x : K => x ^ 4) := by
  intro x y h
  have h1 : (x - y) ^ 4 = 0 := by
    have := sub_pow_char_pow (R := K) (p := 2) (n := 2) x y
    simpa [h] using this
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)

theorem exists_pow_four (u : K) : ∃ μ : K, μ ^ 4 = u :=
  (Finite.injective_iff_surjective.mp pow_four_injective) u

theorem sq_eq_one_of_pow_four (M : Matrix (Fin 2) (Fin 2) K) (h : M ^ 4 = 1) : M ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  have hch : M ^ 2 = M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := Matrix.aeval_self_charpoly M
    rw [Matrix.charpoly_fin_two] at this
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] at this
    have e : M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
      calc M ^ 2 = (M ^ 2 - M.trace • M + M.det • 1) + M.trace • M - M.det • 1 := by abel
        _ = _ := by rw [show M ^ 2 - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 from
          by simpa [sub_eq_add_neg, smul_neg] using this]; simp
    rw [e, sub_eq_add_neg, ← neg_smul, hneg]
  set t := M.trace with ht
  set d := M.det with hd
  have h4 : M ^ 4 = (t ^ 3) • M + (t ^ 2 * d + d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e1 : M ^ 4 = M ^ 2 * M ^ 2 := by rw [← pow_add]
    have e2 : (t * d + d * t) = 0 := by rw [mul_comm d t, ← two_mul, h2, zero_mul]
    rw [e1, hch]
    have hMM : M * M = t • M + d • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [← pow_two]; exact hch
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
    rw [hMM]
    simp only [smul_add, smul_smul]
    have : (t * d) • M + (d * t) • M = 0 := by rw [← add_smul, e2, zero_smul]
    calc _ = (t * t * t) • M + (t * t * d + d * d) • (1 : Matrix (Fin 2) (Fin 2) K)
          + ((t * d) • M + (d * t) • M) := by module
      _ = _ := by rw [this]; simp [pow_succ, mul_assoc]
  by_cases ht0 : t = 0
  · rw [ht0, zero_smul, zero_add] at hch
    rw [ht0] at h4
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, zero_add,
      mul_zero, zero_mul] at h4
    have hd1 : d ^ 2 = 1 := by
      have : (d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [← h4, h]
      have h7 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) this
      simpa using h7
    have hd' : d = 1 := by
      have : (d - 1) ^ 4 = 0 := by
        have := sub_pow_char_pow (R := K) (p := 2) (n := 2) d 1
        simpa [show d ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hd1, one_pow]] using this
      have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp this
      exact sub_eq_zero.mp this
    rw [hch, hd']; simp
  · have hM : M = ((1 + t ^ 2 * d + d ^ 2) / t ^ 3) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h5 : (t ^ 3) • M = (1 + t ^ 2 * d + d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        have : (t ^ 3) • M + (t ^ 2 * d + d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
          rw [← h4, h]
        have h6 : (t ^ 3) • M = 1 - (t ^ 2 * d + d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) :=
          eq_sub_of_add_eq this
        rw [h6]
        have : (1 : Matrix (Fin 2) (Fin 2) K) = (1 : K) • 1 := (one_smul _ _).symm
        rw [sub_eq_add_neg, ← neg_smul, hneg]
        nth_rewrite 1 [this]
        rw [← add_smul, add_assoc]
      have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
      calc M = (t ^ 3)⁻¹ • (t ^ 3) • M := by rw [smul_smul, inv_mul_cancel₀ ht3, one_smul]
        _ = _ := by rw [h5, smul_smul, div_eq_inv_mul]
    set c := (1 + t ^ 2 * d + d ^ 2) / t ^ 3
    have hc4 : c ^ 4 = 1 := by
      have : M ^ 4 = (c ^ 4) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [hM, smul_pow, one_pow]
      rw [h] at this
      have h7 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) this
      simpa using h7.symm
    have hc1 : c = 1 := pow_four_injective (a₁ := c) (a₂ := 1) (by simpa using hc4)
    rw [hM, hc1]; simp

theorem coe_scalar (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem pgl2_sq_eq_one_of_pow_four (g : PGL2 K) (h : g ^ 4 = 1) : g ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective (n := Fin 2) (R := K) g
  rw [← map_pow] at h ⊢
  obtain ⟨u, hu⟩ := CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mp h
  obtain ⟨μ, hμ⟩ := exists_pow_four (u : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [← hμ]; norm_num)
  have hx4 : ((x : Matrix (Fin 2) (Fin 2) K)) ^ 4 = (u : K) • 1 := by
    have := congrArg (fun y : GL (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K)) hu
    simp only [Units.val_pow_eq_pow_val, coe_scalar] at this
    exact this
  have hX : (μ⁻¹ • (x : Matrix (Fin 2) (Fin 2) K)) ^ 4 = 1 := by
    rw [smul_pow, hx4, smul_smul, ← hμ]
    have : (μ⁻¹) ^ 4 * μ ^ 4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
    rw [this, one_smul]
  have hX2 := sq_eq_one_of_pow_four _ hX
  rw [smul_pow] at hX2
  have hx2 : ((x : Matrix (Fin 2) (Fin 2) K)) ^ 2 = (μ ^ 2) • 1 := by
    calc ((x : Matrix (Fin 2) (Fin 2) K)) ^ 2
        = (μ ^ 2) • ((μ⁻¹ ^ 2) • ((x : Matrix (Fin 2) (Fin 2) K)) ^ 2) := by
          rw [smul_smul, ← mul_pow, mul_inv_cancel₀ hμ0, one_pow, one_smul]
      _ = (μ ^ 2) • 1 := by rw [hX2]
  refine CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mpr ⟨Units.mk0 (μ ^ 2) (pow_ne_zero 2 hμ0), ?_⟩
  apply Units.ext
  rw [coe_scalar]
  simpa using hx2

theorem innDiag_sq_eq_one (α : MulAut (PSL2 K)) (hα : α ∈ innDiag K) (h : α ^ 4 = 1) :
    α ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := hα
  rw [← map_pow] at h ⊢
  have : g ^ 4 = 1 := pglAction_inj (h.trans (map_one _).symm)
  rw [pgl2_sq_eq_one_of_pow_four g this, map_one]

end Pgl

section QuatCheck

open QuaternionGroup

theorem false_of_q8_cyclic_quotient {A C : Type} [Group A] [Group C] [IsCyclic C]
    (e : A ≃* QuaternionGroup 2) (φ : A →* C) (hker : ∀ x : A, φ x = 1 → x * x = 1) : False := by
  classical
  have hcomm : ∀ x y : A, φ x * φ y = φ y * φ x := fun x y =>
    (IsCyclic.commGroup (α := C)).mul_comm _ _
  set i : A := e.symm (a 1) with hi
  set j : A := e.symm (xa 0) with hj
  set z : A := e.symm (a 2) with hz
  have hij : i * j = (j * i) * z := by
    apply e.injective
    simp only [map_mul, hi, hj, hz, MulEquiv.apply_symm_apply]
    decide
  have hφz : φ z = 1 := by
    have h1 : φ (j * i * z) = φ (j * i) := by
      rw [← hij, map_mul, map_mul, hcomm]
    rw [map_mul] at h1
    exact mul_left_cancel (a := φ (j * i)) (by rw [mul_one]; exact h1)
  have hsq : ∀ x : A, φ x * φ x = 1 := by
    intro x
    rw [← map_mul]
    have h : ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = a 2 := by decide
    rcases h (e x) with h1 | h1
    · have : x * x = 1 := e.injective (by rw [map_mul, h1, map_one])
      rw [this, map_one]
    · have : x * x = z := e.injective (by rw [map_mul, h1, hz, MulEquiv.apply_symm_apply])
      rw [this, hφz]
  have hii : i * i ≠ 1 := by
    intro h'
    have := congrArg e h'
    simp only [map_mul, hi, MulEquiv.apply_symm_apply, map_one] at this
    revert this; decide
  have hjj : j * j ≠ 1 := by
    intro h'
    have := congrArg e h'
    simp only [map_mul, hj, MulEquiv.apply_symm_apply, map_one] at this
    revert this; decide
  have hkk : (i⁻¹ * j) * (i⁻¹ * j) ≠ 1 := by
    intro h'
    have := congrArg e h'
    simp only [map_mul, map_inv, hi, hj, MulEquiv.apply_symm_apply, map_one] at this
    revert this; decide
  have hi1 : φ i ≠ 1 := fun h => hii (hker i h)
  have hj1 : φ j ≠ 1 := fun h => hjj (hker j h)
  have hij1 : φ i ≠ φ j := fun h => hkk (hker _ (by rw [map_mul, map_inv, ← h, inv_mul_cancel]))
  have : Finite A := Finite.of_equiv _ e.symm.toEquiv
  let H : Subgroup C := φ.range
  have : IsCyclic H := inferInstance
  have : Finite H := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have : Fintype H := Fintype.ofFinite H
  let a : H := ⟨φ i, i, rfl⟩
  let b : H := ⟨φ j, j, rfl⟩
  have hH : ∀ h : H, h ^ 2 = 1 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    simpa [pow_two] using hsq x
  have hcard := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset H) ⊆ Finset.univ.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH x
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, a, b, ?_, ?_, ?_, rfl⟩
    · exact fun h => hi1 (congrArg Subtype.val h).symm
    · exact fun h => hj1 (congrArg Subtype.val h).symm
    · exact fun h => hij1 (congrArg Subtype.val h)
  have := Finset.card_le_card hsub
  omega

end QuatCheck

section Final

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem no_q8_mulAut_psl2 (A : Subgroup (MulAut (PSL2 K))) (e : A ≃* QuaternionGroup 2) : False := by
  have := quot_innDiag_isCyclic (K := K)
  refine false_of_q8_cyclic_quotient e
    ((QuotientGroup.mk' (innDiag K)).comp A.subtype) ?_
  intro x hx
  have hxN : (x : MulAut (PSL2 K)) ∈ innDiag K := (QuotientGroup.eq_one_iff _).mp hx
  have h4 : x ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
    exact hq _
  have h2 := innDiag_sq_eq_one (x : MulAut (PSL2 K)) hxN (by simpa using congrArg Subtype.val h4)
  apply Subtype.ext
  simpa [pow_two] using h2

end Final

section Embed

theorem conjNormal_injective {G : Type} [Group G] (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) : Function.Injective (MulAut.conjNormal (H := F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun α : MulAut F => (α ⟨h, hh⟩ : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc h * g = (g * h * g⁻¹) * g := by rw [this]
      _ = g * h := by group
  rw [hC] at this
  exact (Subgroup.mem_bot).mp this

theorem no_q8_of_psl2 {G : Type} [Group G] (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) (n : ℕ)
    (e : F ≃* CFSG.Theory.Comparator.PSL2Model n) (R : Subgroup G) (eR : R ≃* QuaternionGroup 2) :
    False := by
  let ρ : G →* MulAut (CFSG.Theory.Comparator.PSL2Model n) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := F))
  have hρ : Function.Injective ρ := by
    refine (MulAut.congr e).injective.comp (conjNormal_injective F hC)
  exact no_q8_mulAut_psl2 (K := GaloisField 2 n) (R.map ρ)
    ((Subgroup.equivMapOfInjective R ρ hρ).symm.trans eR)

end Embed

end BenderPsl

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
