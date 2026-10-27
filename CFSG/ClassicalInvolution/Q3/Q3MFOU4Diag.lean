module

public import CFSG.ClassicalInvolution.Q3.Q3NMDiagSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NM

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem mem_normalizer_SUid {n : ℕ} {D : GL (Fin n) E}
    (hD : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * 1 *
      (D : Matrix (Fin n) (Fin n) E) = 1) :
    D ∈ Subgroup.normalizer (SUid (unitaryInvolution E 3 1) n : Set (GL (Fin n) E)) := by
  have := mem_normalizer_SUG (unitaryInvolution E 3 1) hD
  rwa [SUG_one] at this

theorem oddCoreIn_fixed_conjSUid_eq_bot (hE : Nat.card E = 9) {n : ℕ}
    (hZ : IsPGroup 2 (Subgroup.center (SUid (unitaryInvolution E 3 1) n)))
    (D : GL (Fin n) E) (hDD : D * D = 1)
    (hDg : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * 1 *
      (D : Matrix (Fin n) (Fin n) E) = 1)
    (hne : conjAut (SUid (unitaryInvolution E 3 1) n) D (mem_normalizer_SUid hDg) ≠ 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (SUid (unitaryInvolution E 3 1) n)
      (conjAut (SUid (unitaryInvolution E 3 1) n) D (mem_normalizer_SUid hDg)))) = ⊥ := by
  have hDm : (D : Matrix (Fin n) (Fin n) E) * D = 1 := by
    rw [← Units.val_mul, hDD, Units.val_one]
  have hgg : (D : Matrix (Fin n) (Fin n) E) * D = ((1 : E) * 1) • 1 := by
    rw [hDm, one_mul, one_smul]
  obtain ⟨a, b, Q, Q', h1, h2', hQ1, hgQ⟩ := exists_normal_form_one hE (μ := (1 : E))
    (one_pow 4) (cT_one _) (by simp) hDg hgg
  have hab : 1 ≤ a ∧ 1 ≤ b := by
    constructor
    · by_contra h0
      obtain rfl : a = 0 := by omega
      exact hne (conjAut_eq_one_of_smul_one _ D _ (-1)
        (eq_smul_one_of_mul_eq h1 hgQ (dgn_left_zero (1 : E))))
    · by_contra h0
      obtain rfl : b = 0 := by omega
      exact hne (conjAut_eq_one_of_smul_one _ D _ 1
        (eq_smul_one_of_mul_eq h1 hgQ (dgn_right_zero (1 : E))))
  set e' : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) ≃*
      SUid (unitaryInvolution E 3 1) n :=
    (conjSUG (unitaryInvolution E 3 1) h1 h2' hQ1).trans
      (MulEquiv.subgroupCongr (SUG_one (unitaryInvolution E 3 1) n)) with he'
  have hcoe : ∀ x, (((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = Q * umat x * Q' := fun x => rfl
  have hZ' := isPGroup_center_of_mulEquiv e' hZ
  set τ := conjAut (SUid (unitaryInvolution E 3 1) n) D (mem_normalizer_SUid hDg) with hτdef
  set τ' := MulAut.congr e'.symm τ with hτ'
  have hτ'fix : ∀ x, x ∈ fixedSubgroup τ' ↔
      umat x * dgn (1 : E) a b = dgn (1 : E) a b * umat x := by
    intro x
    rw [mem_fixedSubgroup_iff]
    have h1' : τ' x = x ↔ τ (e' x) = e' x := by
      show e'.symm (τ (e' x)) = x ↔ _
      rw [MulEquiv.symm_apply_eq]
    have hy : τ (e' x) = e' x ↔ (D : Matrix (Fin n) (Fin n) E) *
        (((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
          D := by
      constructor
      · intro h
        have h' : D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ =
            ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) := congrArg Subtype.val h
        have : D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) =
            ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D := by
          calc D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E)
              = D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ * D := by
                group
            _ = _ := by rw [h']
        exact congrArg Units.val this
      · intro h
        apply Subtype.ext
        show D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ =
          ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E)
        have : D * ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) =
            ((e' x : SUid (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D := Units.ext h
        rw [this]
        group
    rw [h1', hy, hcoe]
    exact (commute_conj_iff h1 h2' hgQ (umat x)).trans eq_comm
  have hres := oddCoreIn_fixed_dgn_eq_bot hE (μ := (1 : E)) (one_pow 4) hab.1 hab.2 hZ' τ' hτ'fix
  have := oddCoreIn_fixed_congr_eq_bot e' τ' hres
  have hcongr : MulAut.congr e' τ' = τ := MulEquiv.ext fun y => by
    show e' (e'.symm (τ (e' (e'.symm y)))) = τ y
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rwa [hcongr] at this


end CFSG.ClassicalInvolution.Q3.Q3MFOU4
