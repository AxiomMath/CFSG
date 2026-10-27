module

public import CFSG.HardMathSupport.Solomon.Coordinator.U38Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10U38Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

local notation "ρ" => primeFormConjHom h (idGram K 3)

theorem u38_rho_eq_conj (g : gramSU h (idGram K 3))
    (hg : (g : GL (Fin 3) K) ∈ primeFormUnitary h (idGram K 3)) :
    ρ ⟨g, hg⟩ = MulAut.conj (g : primeFormP h (idGram K 3)) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun y => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  rfl

theorem u38_innerAut_le : innerAut (primeFormP h (idGram K 3)) ≤ primeFormD h (idGram K 3) := by
  rintro _ ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | H g =>
    exact ⟨⟨g, ((mem_gramSU_iff_unitary h).1 g.2).1⟩,
      u38_rho_eq_conj h g ((mem_gramSU_iff_unitary h).1 g.2).1⟩

theorem u38_innerAut_normal (g x : MulAut (primeFormP h (idGram K 3)))
    (hx : x ∈ innerAut (primeFormP h (idGram K 3))) :
    g * x * g⁻¹ ∈ innerAut (primeFormP h (idGram K 3)) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply, MulAut.mul_apply]

section Omega

variable {ω : K} (hω : ω ^ 2 + ω + 1 = 0)

include h hω in
theorem u38_sigma_omega {σ : K ≃+* K} (hσ : orderOf σ = 3) : σ ω = ω := by
  have h3 := u38_omega_pow_three hω
  have h2 := u38_two_eq_zero h
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hroot : (σ ω - ω) * (σ ω - ω ^ 2) = 0 := by
    have hs : σ ω ^ 2 + σ ω + 1 = 0 := by
      have := congrArg σ hω
      simpa [map_add, map_pow, map_one] using this
    linear_combination hs - σ ω * hω + h3
  rcases mul_eq_zero.1 hroot with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have e1 : σ ω = ω ^ 2 := sub_eq_zero.1 h1
    have e2 : σ (σ ω) = ω := by
      rw [e1, map_pow, e1, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    have e3 : σ (σ (σ ω)) = ω ^ 2 := by rw [e2, e1]
    have e4 : σ (σ (σ ω)) = ω := by
      have := congrArg (fun τ : K ≃+* K => τ ω) hσ3
      exact this
    rw [e4] at e3
    have hω1 := u38_omega_ne_one h hω
    have hω0 : ω ≠ 0 := by
      rintro rfl
      norm_num at hω
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination -e3
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hω0
    · exact sub_eq_zero.1 h0

theorem u38_fieldHom_comm {σ : K ≃+* K} (X : primeFormUnitary h (idGram K 3))
    (hX : ∀ i j, σ (((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) :
    primeFormFieldHom h isPrimeFormGram_one σ * ρ X = ρ X * primeFormFieldHom h isPrimeFormGram_one σ := by
  have e : primeFormFieldU h isPrimeFormGram_one σ X = X := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_primeFormFieldU, coe_glAut]
    ext i j
    exact hX i j
  have := primeFormField_conj_eq h isPrimeFormGram_one σ X
  rw [e] at this
  calc primeFormFieldHom h isPrimeFormGram_one σ * ρ X =
      primeFormFieldHom h isPrimeFormGram_one σ * ρ X *
        (primeFormFieldHom h isPrimeFormGram_one σ)⁻¹ *
        primeFormFieldHom h isPrimeFormGram_one σ := by group
    _ = ρ X * primeFormFieldHom h isPrimeFormGram_one σ := by rw [this]

include h hω in
theorem u38_sigma_mA {σ : K ≃+* K} (hσ : orderOf σ = 3) (i j : Fin 3) :
    σ (mA ω i j) = mA ω i j := by
  have hs := u38_sigma_omega h hω hσ
  fin_cases i <;> fin_cases j <;> simp [mA, hs, map_pow]

theorem u38_sigma_mP (σ : K ≃+* K) (i j : Fin 3) : σ ((mP : Matrix (Fin 3) (Fin 3) K) i j) =
    (mP : Matrix (Fin 3) (Fin 3) K) i j := by
  fin_cases i <;> fin_cases j <;> simp [mP]

theorem u38_not_comm_uP_uQ : ¬ (ρ (uP h hω) * ρ (uQ h hω) = ρ (uQ h hω) * ρ (uP h hω)) := by
  intro hc
  obtain ⟨c, hc⟩ := primeFormUnitary_exists_comm_scalar h le_rfl u38_hne hc
  have e : mP * mQ ω = (c : K) • (mQ ω * mP) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uP, coe_uQ] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have e02 := congrFun (congrFun e 0) 2
  have e10 := congrFun (congrFun e 1) 0
  simp [mP, mQ, Matrix.mul_apply, Fin.sum_univ_three] at e02 e10
  apply u38_omega_ne_one h hω
  rw [← e02] at e10
  linear_combination -e10

theorem u38_uA_comm_uQ : ρ (uA h hω) * ρ (uQ h hω) = ρ (uQ h hω) * ρ (uA h hω) := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_uA, coe_uQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mQ, Matrix.mul_apply, Fin.sum_univ_three]

noncomputable abbrev E₀ : Subgroup (MulAut (primeFormP h (idGram K 3))) :=
  Subgroup.closure {ρ (uA h hω), ρ (uP h hω)}

theorem u38_E₀_comm {x y : MulAut (primeFormP h (idGram K 3))} (hx : x ∈ E₀ h hω)
    (hy : y ∈ E₀ h hω) : x * y = y * x := by
  obtain ⟨i, j, -, -, rfl⟩ := mem_plane_iff h hω hx
  obtain ⟨k, l, -, -, rfl⟩ := mem_plane_iff h hω hy
  have hap : Commute (ρ (uA h hω)) (ρ (uP h hω)) := rho_uA_comm_uP h hω
  have c1 : Commute (ρ (uA h hω) ^ i * ρ (uP h hω) ^ j) (ρ (uA h hω) ^ k) :=
    ((Commute.refl _).pow_pow i k).mul_left ((hap.pow_pow k j).symm)
  have c2 : Commute (ρ (uA h hω) ^ i * ρ (uP h hω) ^ j) (ρ (uP h hω) ^ l) :=
    (hap.pow_pow i l).mul_left ((Commute.refl _).pow_pow j l)
  exact (c1.mul_right c2).eq

theorem u38_E₀_pow_three {x : MulAut (primeFormP h (idGram K 3))} (hx : x ∈ E₀ h hω) :
    x ^ 3 = 1 := by
  obtain ⟨i, j, -, -, rfl⟩ := mem_plane_iff h hω hx
  have hap : Commute (ρ (uA h hω)) (ρ (uP h hω)) := rho_uA_comm_uP h hω
  rw [((hap.pow_left i).pow_right j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
    pow_mul, pow_mul, rho_uA_pow_three h hω, rho_uP_pow_three h hω, one_pow, one_pow, one_mul]

theorem u38_three_lt_card_E₀ : 3 < Nat.card (E₀ h hω) := by
  have := h.finite
  have : Finite (primeFormP h (idGram K 3)) := finite_primeFormP
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := ρ (uA h hω)
  have ha1 : a ≠ 1 := by
    intro e
    apply u38_not_comm_uP_uQ h hω
    have hz : ρ (uP h hω) ∈ Subgroup.zpowers a ∨ True := Or.inr trivial
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne le_rfl u38_hne _).1 e
    have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [coe_uA, GeneralLinearGroup.coe_scalar] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e11 := congrFun (congrFun hm 1) 1
    simp [mA] at e00 e11
    exact absurd (e11.trans e00.symm) (u38_omega_ne_one h hω)
  have hao : orderOf a = 3 := orderOf_eq_prime (rho_uA_pow_three h hω) ha1
  have hz : Subgroup.zpowers a ≤ E₀ h hω :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hpz : ρ (uP h hω) ∉ Subgroup.zpowers a := by
    intro hp
    apply u38_not_comm_uP_uQ h hω
    obtain ⟨k, hk⟩ := hp
    rw [← hk]
    exact ((Commute.zpow_left (u38_uA_comm_uQ h hω) k)).eq
  have hlt : Subgroup.zpowers a < E₀ h hω := lt_of_le_of_ne hz (fun e => hpz (by
    rw [e]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have := Subgroup.card_lt_of_lt hlt
  rwa [Nat.card_zpowers, hao] at this

end Omega

end CFSG.HardMathSupport.Solomon.Coordinator.U38
