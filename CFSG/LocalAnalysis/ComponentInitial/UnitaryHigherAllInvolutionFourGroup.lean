module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_four_group_of_scalar_square (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : Kˣ}
    (hAc : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c) :
    ∃ V : Subgroup (hypPSU h r ε), IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      ∀ x ∈ V, ∃ g : hypSU h r ε, hypProj h r ε g = x ∧ A * (g : GL (HypIndex r ε) K) = g * A := by
  set Alin := (Matrix.GeneralLinearGroup.toLin A :
    LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) with hAlin
  have hAlinU : Alin ∈ sesqUnitaryGroup (hypForm h r ε) := by
    refine mem_sesqUnitaryGroup.mpr fun x y => ?_
    rw [hAlin, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact (gramForm_isometry_iff h _ _).mpr (mem_hypUnitary.mp hA) x y
  have hAlinc : (Alin : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) * Alin =
      (c : K) • (1 : Module.End K (HypIndex r ε → K)) := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hAlin, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, mulVec_mulVec, ← Units.val_mul, hAc, GeneralLinearGroup.coe_scalar,
      LinearMap.smul_apply, Module.End.one_apply]
    funext a
    simp [scalar_apply, mulVec_diagonal]
  have hfinV : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  obtain ⟨W, hWle, hWab, hWcard⟩ := odd_unitary_scalar_square_centralizer_projective_four_group h
    hp (by omega) (hypForm_isSymm h) (hypForm_separatingLeft h) Alin hAlinU c hAlinc
  set ρ := (unitaryProjMk (hypForm h r ε)).comp
    (unitaryCentralizer (hypForm h r ε) Alin).subtype with hρdef
  set φ := (hypSesqProjEquiv r ε h (by omega)).symm.toMonoidHom.comp ρ with hφdef
  have hker : ρ.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change ρ g = 1 ↔ (hypSesqProjEquiv r ε h (by omega)).symm (ρ g) = 1
    rw [MulEquiv.map_eq_one_iff]
  have hWle' : W ≤ ρ.range := by
    rw [hρdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hWle
  have : IsElementaryAbelian 2 W := hWab
  obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_subgroup_of_ker_eq (p := 2) ρ φ hker W hWle'
  refine ⟨V, hVab, hVcard.trans hWcard, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hVmem x hx
  refine ⟨(hypSesqSUEquiv r ε h).symm g, ?_, ?_⟩
  · change hypProj h r ε ((hypSesqSUEquiv r ε h).symm g) =
      (hypSesqProjEquiv r ε h (by omega)).symm (ρ g)
    rw [eq_comm, MulEquiv.symm_apply_eq, hypSesqProjEquiv_hypProj, MulEquiv.apply_symm_apply]
    rfl
  · have hcomm : Alin * ((g : sesqSpecialUnitaryGroup (hypForm h r ε)) :
        LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) =
          ((g : sesqSpecialUnitaryGroup (hypForm h r ε)) :
            LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) * Alin :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp g.2)).symm
    have hg : Matrix.GeneralLinearGroup.toLin (((hypSesqSUEquiv r ε h).symm g : hypSU h r ε) :
        GL (HypIndex r ε) K) = ((g : sesqSpecialUnitaryGroup (hypForm h r ε)) :
          LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) := by
      rw [← coe_hypSesqSUEquiv, MulEquiv.apply_symm_apply]
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_mul, map_mul, hg]
    exact hcomm

theorem exists_fixed_four_group_hyp (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (β : MulAut (hypPSU h r ε)) (hβ : β ^ 2 = 1) :
    ∃ V : Subgroup (hypPSU h r ε), V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  by_cases hβ1 : β = 1
  · obtain ⟨V, hVab, hVcard, -⟩ := exists_four_group_of_scalar_square h hp hn (one_mem _)
      (c := 1) (by rw [mul_one, map_one])
    refine ⟨V, fun x _ => ?_, hVab, hVcard⟩
    change β x = x
    rw [hβ1, MulAut.one_apply]
  have hord : orderOf β = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hβ hβ1
  obtain ⟨hΦapply, -, -, hrep⟩ := odd_unitary_automorphism_semilinear_representation h hp hr hε hn
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ := hrep β hord
  have hfix : ∀ g : hypSU h r ε, (A : GL (HypIndex r ε) K) * glAut σ (g : GL (HypIndex r ε) K) =
      (g : GL (HypIndex r ε) K) * A → β (hypProj h r ε g) = hypProj h r ε g := by
    intro g hg
    rw [← hΦ, hΦapply]
    congr 1
    apply Subtype.ext
    change A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ = g
    rw [hg, mul_inv_cancel_right]
  rcases hσ with hσ1 | hσbar
  ·
    have h1 := hid hσ1
    have h2 : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) ^ 2 = 1 := by
      rw [← h1, pow_orderOf_eq_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
    obtain ⟨c, -, -, hc⟩ := h2
    have hAc : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c := by
      rw [← hc, sq]
      rfl
    obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_four_group_of_scalar_square h hp hn hA hAc
    refine ⟨V, fun x hx => ?_, hVab, hVcard⟩
    obtain ⟨g, rfl, hg⟩ := hVmem x hx
    refine hfix g ?_
    rw [hσ1, show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one, MulAut.one_apply]
    exact hg
  ·
    obtain ⟨c, hc0, hAc⟩ := hbar hσbar
    obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_four_group_of_antiunitary h hp hn hA hc0 hAc
    refine ⟨V, fun x hx => ?_, hVab, hVcard⟩
    obtain ⟨g, rfl, hg⟩ := hVmem x hx
    refine hfix g (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, coe_glAut]
    have hmap : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar :=
      Matrix.ext fun i j => hσbar _
    rw [hmap]
    exact hg

theorem odd_unitary_all_involution_fixed_four_group (L : Type) [Group L] {p f n : ℕ}
    (hp : p ≠ 2) (hL : StatedClassicalModel L .PSU n p f) (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨⟨hprime, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have h : UnitaryFieldData p f K := ⟨hprime, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, (Nat.div_add_mod n 2).symm⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set ψ : L ≃* hypPSU h r ε := e.trans (hypPSUEquivStatedProj h hR (by omega)).symm with hψ
  set β : MulAut (hypPSU h r ε) := MulAut.congr ψ α with hβdef
  have hβ : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  obtain ⟨V, hVfix, hVab, hVcard⟩ := exists_fixed_four_group_hyp h hp hr hε hn β hβ
  refine ⟨V.map ψ.symm.toMonoidHom, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    change α (ψ.symm y) = ψ.symm y
    have h1 : β y = y := hVfix hy
    rw [hβdef, MulAut.congr_apply] at h1
    have h2 := congrArg ψ.symm h1
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  · rw [Subgroup.card_map_of_injective ψ.symm.injective]
    exact hVcard

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
