module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangianElements
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearHermGram
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents

public section

namespace CFSG.SeitzReduction

namespace UnitaryLagrangian

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents
  (conj_injective_primeFormP)
open scoped commutatorElement

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem primeFormPsi_apply_proj {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormPsi h hC ⟨A, φ⟩ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      ((⟨(A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹,
        conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC φ g.2)⟩ :
          gramSU h (C : Matrix (Fin n) (Fin n) K)) : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  rw [primeFormPsi_apply, MulAut.mul_apply]
  change primeFormConjHom h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem mul_glAut_eq_of_psi_apply_eq (hn : 1 ≤ n) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) (hg : (g : GL (Fin n) K) * g = 1)
    (hfix : primeFormPsi h hC ⟨A, φ⟩ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = g) :
    (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) = g * A := by
  have : CharP K 2 := h.charP
  rw [primeFormPsi_apply_proj] at hfix
  obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq (s := normOneScalars h _ n)).mp hfix
  set y : GL (Fin n) K := (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹
    with hy
  have hc' : y⁻¹ * g = GeneralLinearGroup.scalar (Fin n) c := hc
  have hyy : y * y = 1 := by
    rw [hy, show (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ *
        ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹) =
          (A : GL (Fin n) K) * (glAut φ (g : GL (Fin n) K) * glAut φ (g : GL (Fin n) K)) *
            (A : GL (Fin n) K)⁻¹ by group, ← map_mul, hg, map_one, mul_one, mul_inv_cancel]
  have hgy : (g : GL (Fin n) K) = y * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc', mul_inv_cancel_left]
  have hcc : GeneralLinearGroup.scalar (Fin n) (c * c) = 1 := by
    have h1 := hg
    rw [hgy, show y * GeneralLinearGroup.scalar (Fin n) c * (y * GeneralLinearGroup.scalar (Fin n) c) =
        y * y * (GeneralLinearGroup.scalar (Fin n) c * GeneralLinearGroup.scalar (Fin n) c) by
        rw [mul_assoc, ← mul_assoc (GeneralLinearGroup.scalar (Fin n) c),
          (commute_scalar c y).eq.symm]
        group, hyy, one_mul, ← map_mul] at h1
    exact h1
  have hc1 : c = 1 := by
    have h1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hcc
    simp only [GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Units.val_mul] at h1
    have h2 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
      linear_combination h1 - ((c : K) - 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have h3 := mul_self_eq_zero.mp h2
    exact Units.ext (sub_eq_zero.mp h3)
  rw [hc1, map_one, mul_one] at hgy
  calc (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) = y * A := by rw [hy, inv_mul_cancel_right]
    _ = g * A := by rw [hgy]

section Supply

variable {C : GL (Fin n) K} {l : ℕ} {e d : Fin l → Fin n → K}
  {s : gramSU h (C : Matrix (Fin n) (Fin n) K)}

theorem gramSU_ext {x y : gramSU h (C : Matrix (Fin n) (Fin n) K)}
    (hxy : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((y : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) : x = y :=
  Subtype.ext (Units.ext hxy)

theorem lagRad_mem_closure_odd (hF : IsLagrangianFrame h (C : Matrix (Fin n) (Fin n) K)
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) e d)
    (hH : (gramForm h (C : Matrix (Fin n) (Fin n) K)).IsSymm) {τ σ : K} (hτσ : τ * σ = 1)
    (hτ : h.bar τ * τ = 1) (hσ : h.bar σ * σ = 1) (hστ : h.bar τ = σ)
    (h1σ : 1 + σ * σ ≠ 0) (c : K) {i j : Fin l} (hij : i ≠ j) :
    ((lagRadSU hF hH c i j : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∈
      closure {x : primeFormP h (C : Matrix (Fin n) (Fin n) K) |
        MulAut.conj (s : primeFormP h (C : Matrix (Fin n) (Fin n) K)) x = x ∧
          Odd (orderOf x)} := by
  have := h.finite
  have : CharP K 2 := h.charP
  set radSet : Set (gramSU h (C : Matrix (Fin n) (Fin n) K)) := {x | ∃ (c : K) (i j : Fin l), i ≠ j ∧ x = lagRadSU hF hH c i j}
    with hradSet
  set torSet : Set (gramSU h (C : Matrix (Fin n) (Fin n) K)) := {x | ∃ i j : Fin l, i ≠ j ∧ x = lagTorusSU hF hH hτσ hτ hσ i j}
    with htorSet
  set Asub := closure radSet with hAsub
  set Psub := closure (radSet ∪ torSet) with hPsub
  have hAP : Asub ≤ Psub := closure_mono Set.subset_union_left
  have hPs : Psub ≤ centralizer {s} := by
    rw [hPsub, closure_le]
    rintro x (⟨c, i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact gramSU_ext h (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lagRadSU]
        exact (lagRad_commute hF c i j).symm)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact gramSU_ext h (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lagTorusSU]
        exact (lagTorus_commute hF τ σ hij).symm)
  have hσσ : σ * τ = 1 := by rw [mul_comm]; exact hτσ
  have hcomm : ∀ (c : K) (i j : Fin l), i ≠ j →
      ⁅lagRadSU hF hH c i j, lagTorusSU hF hH hτσ hτ hσ i j⁆ =
        lagRadSU hF hH (c + c * σ * σ) i j := by
    intro c i j hij
    have hu2 : lagRadSU hF hH c i j * lagRadSU hF hH c i j = 1 :=
      gramSU_ext h (by
        rw [Subgroup.coe_mul, Units.val_mul, coe_lagRadSU, lagRad_mul_self hF]
        rfl)
    have hinv : (lagRadSU hF hH c i j)⁻¹ = lagRadSU hF hH c i j :=
      inv_eq_of_mul_eq_one_right hu2
    have htu : lagTorusSU hF hH hτσ hτ hσ i j * lagRadSU hF hH c i j =
        lagRadSU hF hH (c * σ * σ) i j * lagTorusSU hF hH hτσ hτ hσ i j :=
      gramSU_ext h (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lagRadSU,
          coe_lagRadSU, coe_lagTorusSU]
        exact lagTorus_mul_lagRad hF hσσ hστ hij c)
    have huu : lagRadSU hF hH c i j * lagRadSU hF hH (c * σ * σ) i j =
        lagRadSU hF hH (c + c * σ * σ) i j :=
      gramSU_ext h (by
        rw [Subgroup.coe_mul, Units.val_mul, coe_lagRadSU, coe_lagRadSU, coe_lagRadSU,
          lagRad_mul hF])
    calc ⁅lagRadSU hF hH c i j, lagTorusSU hF hH hτσ hτ hσ i j⁆
        = lagRadSU hF hH c i j * (lagTorusSU hF hH hτσ hτ hσ i j * lagRadSU hF hH c i j) *
            (lagTorusSU hF hH hτσ hτ hσ i j)⁻¹ := by
          rw [commutatorElement_def, hinv]
          group
      _ = lagRadSU hF hH c i j * lagRadSU hF hH (c * σ * σ) i j := by
          rw [htu]
          group
      _ = lagRadSU hF hH (c + c * σ * σ) i j := huu
  have hA : Asub ≤ ⁅Asub, Psub⁆ := by
    rw [hAsub, closure_le]
    rintro x ⟨c, i, j, hij, rfl⟩
    set c' := c / (1 + σ * σ) with hc'
    have hc : c' + c' * σ * σ = c := by
      rw [hc', mul_assoc, ← mul_one_add, div_mul_cancel₀ _ h1σ]
    rw [SetLike.mem_coe, ← hc, ← hcomm c' i j hij]
    exact commutator_mem_commutator (subset_closure ⟨c', i, j, hij, rfl⟩)
      (subset_closure (Or.inr ⟨i, j, hij, rfl⟩))
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)
    with hπ
  have hP' : ∀ p ∈ Psub.map π,
      MulAut.conj (s : primeFormP h (C : Matrix (Fin n) (Fin n) K)) p = p := by
    rintro _ ⟨q, hq, rfl⟩
    have hqs := mem_centralizer_singleton_iff.mp (hPs hq)
    rw [MulAut.conj_apply]
    change π s * π q * (π s)⁻¹ = π q
    rw [← map_mul, ← hqs, map_mul, mul_inv_cancel_right]
  have hD := le_closure_odd_fixed_of_le_commutator (map_mono hAP) hP'
    (by rw [← map_commutator]; exact map_mono hA)
  exact hD ⟨_, subset_closure ⟨c, i, j, hij, rfl⟩, rfl⟩

end Supply

theorem exists_norm_one_ne_one :
    ∃ τ σ : K, τ * σ = 1 ∧ h.bar τ * τ = 1 ∧ h.bar σ * σ = 1 ∧ h.bar τ = σ ∧
      1 + σ * σ ≠ 0 := by
  have : CharP K 2 := h.charP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  have hbc0 : h.bar c ≠ 0 := fun h0 => hc0 ((h.bar_eq_zero_iff).mp h0)
  refine ⟨c * (h.bar c)⁻¹, h.bar c * c⁻¹, by field_simp, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv₀, h.bar_bar]
    field_simp
  · rw [map_mul, map_inv₀, h.bar_bar]
    field_simp
  · rw [map_mul, map_inv₀, h.bar_bar]
  · intro h0
    have h1 : (h.bar c * c⁻¹ + 1) * (h.bar c * c⁻¹ + 1) = 0 := by
      linear_combination h0 + (h.bar c * c⁻¹) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have h2 := mul_self_eq_zero.mp h1
    apply hc
    have h3 : h.bar c * c⁻¹ = 1 := by
      linear_combination h2 - (CharTwo.two_eq_zero : (2 : K) = 0)
    field_simp at h3
    exact h3

theorem involutionCriterion_conj_of_eq (hn : 6 ≤ n) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (s : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hs2 : (s : GL (Fin n) K) * s = 1)
    (hWL : LinearMap.range (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
      LinearMap.ker (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) :
    InvolutionCriterion (MulAut.conj (s : primeFormP h (C : Matrix (Fin n) (Fin n) K))) := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hH := gramForm_isSymm h (hC.barTranspose h)
  have hsm : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (s : GL (Fin n) K) = 1 := by
    rw [← Units.val_mul, hs2, Units.val_one]
  have hsiso : ∀ x y, gramForm h (C : Matrix (Fin n) (Fin n) K)
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) =
        gramForm h (C : Matrix (Fin n) (Fin n) K) x y :=
    (mem_gramSU_iff_isometry.mp s.2).1
  obtain ⟨l, hnl, e, d, hF⟩ := exists_isLagrangianFrame h (hC.barTranspose h)
    (primeFormGram_det_ne_zero C) hsiso hsm hWL
  have hl : 3 ≤ l := by omega
  obtain ⟨τ, σ, hτσ, hτ, hσ, hστ, h1σ⟩ := exists_norm_one_ne_one h
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)
    with hπ
  set D : Subgroup (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
    closure {x | ∃ (c : K) (i j : Fin l), i ≠ j ∧
      x = ((lagRadSU hF hH c i j : gramSU h _) : primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    with hD
  have hDle : D ≤ closure {x : primeFormP h (C : Matrix (Fin n) (Fin n) K) |
      MulAut.conj (s : primeFormP h (C : Matrix (Fin n) (Fin n) K)) x = x ∧
        Odd (orderOf x)} := by
    rw [hD, closure_le]
    rintro _ ⟨c, i, j, hij, rfl⟩
    exact lagRad_mem_closure_odd h hF hH hτσ hτ hσ hστ h1σ c hij
  refine involutionCriterion_of_fixes hDle fun β hβx hβD => ?_
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC (by omega) hq β
  have hfs : primeFormPsi h hC ⟨A, φ⟩ (s : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = s :=
    apply_eq_of_mul_conj_eq (conj_injective_primeFormP h hC (by omega)) hβx
  have hAs := mul_glAut_eq_of_psi_apply_eq h (by omega) hC A φ s hs2 hfs
  have hAu : ∀ (c : K) (i j : Fin l), i ≠ j →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (lagRad h (C : Matrix (Fin n) (Fin n) K) e c i j).map φ =
          lagRad h (C : Matrix (Fin n) (Fin n) K) e c i j * (A : GL (Fin n) K) := by
    intro c i j hij
    have hfix := hβD _ (subset_closure ⟨c, i, j, hij, rfl⟩)
    have hu2 : ((lagRadSU hF hH c i j : gramSU h _) : GL (Fin n) K) *
        (lagRadSU hF hH c i j : gramSU h _) = 1 :=
      Units.ext (by rw [Units.val_mul, coe_lagRadSU, lagRad_mul_self hF]; rfl)
    have h1 := mul_glAut_eq_of_psi_apply_eq h (by omega) hC A φ _ hu2 hfix
    have h2 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) h1
    simpa only [Units.val_mul, coe_glAut, coe_lagRadSU] using h2
  have hAs' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
        (s : GL (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h2 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hAs
    simpa only [Units.val_mul, coe_glAut] using h2
  obtain ⟨hφ, μ, hAA⟩ := rigidity_of_commute hF hl (A : GL (Fin n) K) φ hAs' hAu
  subst hφ
  rw [primeFormPsi_apply, show RingEquiv.refl K = 1 from rfl, map_one, mul_one, ← map_pow]
  exact SesqShear.primeFormConjHom_sq_eq_one_of_mul_self h A hAA

theorem involutionCriterion_primeFormConj_of_eq (hn : 6 ≤ n) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (s : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hs2 : (s : GL (Fin n) K) * s = 1)
    (hWL : LinearMap.range (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
      LinearMap.ker (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) :
    InvolutionCriterion (primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩) := by
  rw [primeFormConjHom_eq_conj]
  exact involutionCriterion_conj_of_eq h hn hC s hs2 hWL

end UnitaryLagrangian

end CFSG.SeitzReduction
