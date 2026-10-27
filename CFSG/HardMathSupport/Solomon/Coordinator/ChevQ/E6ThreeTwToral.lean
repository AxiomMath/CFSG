module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneStmt
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlanePair
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneLift
public import CFSG.LieType.SeitzGeneration.UnitaryNonabToral


public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KCUnitaryModel

section Toral

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem twToral_suConj_eq_one_of_scalar {A : unitaryIsom3 h} {c : Kˣ}
    (hA : (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c) : suConj h A = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  show (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ = g
  rw [hA]
  exact (commute_scalar c (g : GL (Fin 3) K)).symm.mul_inv_cancel

theorem twToral_suConj_pow_mul_eq_one {γ₁ γ₂ : unitaryIsom3 h} {a b : ℕ} {c : K}
    (hc : (((γ₁ : GL (Fin 3) K) ^ a * (γ₂ : GL (Fin 3) K) ^ b : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    suConj h γ₁ ^ a * suConj h γ₂ ^ b = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 := GeneralLinearGroup.det_ne_zero
      ((γ₁ : GL (Fin 3) K) ^ a * (γ₂ : GL (Fin 3) K) ^ b)
    rw [hc, zero_smul, Matrix.det_zero] at h0
    exact h0 rfl
  have hscal : ((γ₁ ^ a * γ₂ ^ b : unitaryIsom3 h) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [twPlane_coe_scalar]
    exact hc
  have e : suConj h (γ₁ ^ a * γ₂ ^ b) = suConj h γ₁ ^ a * suConj h γ₂ ^ b := by
    rw [map_mul, map_pow, map_pow]
  rw [← e]
  exact twToral_suConj_eq_one_of_scalar hscal

theorem twToral_word (a b : Kˣ) (A B : GL (Fin 3) K) (i j : ℕ) :
    (GeneralLinearGroup.scalar (Fin 3) a * A) ^ i * (GeneralLinearGroup.scalar (Fin 3) b * B) ^ j =
      GeneralLinearGroup.scalar (Fin 3) (a ^ i * b ^ j) * (A ^ i * B ^ j) := by
  have e1 : (GeneralLinearGroup.scalar (Fin 3) a * A) ^ i =
      GeneralLinearGroup.scalar (Fin 3) (a ^ i) * A ^ i := by
    rw [(commute_scalar a A).symm.mul_pow, map_pow]
  have e2 : (GeneralLinearGroup.scalar (Fin 3) b * B) ^ j =
      GeneralLinearGroup.scalar (Fin 3) (b ^ j) * B ^ j := by
    rw [(commute_scalar b B).symm.mul_pow, map_pow]
  rw [e1, e2, (commute_scalar (b ^ j) (A ^ i)).mul_mul_mul_comm, map_mul]

theorem twToral_three_dvd_card_sub_one (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) :
    3 ∣ Nat.card K - 1 := by
  have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpos : 0 < ℓ ^ f := pow_pos h.prime.pos f
  have hq' : ℓ ^ f % 3 = 2 := by omega
  have : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq']
  omega

theorem twToral_exists_cube_roots (hq3 : 3 ∣ ℓ ^ f + 1) {γ₁ γ₂ : unitaryIsom3 h}
    (hc : γ₁ * γ₂ = γ₂ * γ₁) (h13 : suConj h γ₁ ^ 3 = 1) (h23 : suConj h γ₂ ^ 3 = 1)
    (hind : ∀ i j : ℕ, suConj h γ₁ ^ i * suConj h γ₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    ∃ μ ν : Kˣ, h.norm (μ : K) = 1 ∧ h.norm (ν : K) = 1 ∧
      (γ₁ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) ∧
      (γ₂ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (ν ^ 3) := by
  obtain ⟨α, hαN, hα⟩ := twPlane_exists_scalar_of_suConj_eq_one (A := γ₁ ^ 3)
    (by rw [map_pow]; exact h13)
  obtain ⟨β, hβN, hβ⟩ := twPlane_exists_scalar_of_suConj_eq_one (A := γ₂ ^ 3)
    (by rw [map_pow]; exact h23)
  haveI : Finite K := h.finite
  have hx3 : (((γ₁ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (α : K) • 1 := by
    have h1 : (γ₁ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) α := hα
    rw [h1, twPlane_coe_scalar]
  have hy3 : (((γ₂ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (β : K) • 1 := by
    have h1 : (γ₂ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) β := hβ
    rw [h1, twPlane_coe_scalar]
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := exists_cube_roots_of_commute (twToral_three_dvd_card_sub_one h hq3)
    (CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h Nat.prime_three hq3)
    (x := (γ₁ : GL (Fin 3) K)) (y := (γ₂ : GL (Fin 3) K)) (congrArg Subtype.val hc) α.ne_zero
    β.ne_zero hx3 hy3 (fun a b ⟨c, hc'⟩ => hind a b (twToral_suConj_pow_mul_eq_one hc'))
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact α.ne_zero (by rw [← hμ]; norm_num)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact β.ne_zero (by rw [← hν]; norm_num)
  refine ⟨Units.mk0 μ hμ0, Units.mk0 ν hν0, ?_, ?_, ?_, ?_⟩
  · apply twPlane_norm_eq_one_of_pow_three hq3 hμ0
    rw [← twPlane_norm_pow, hμ, hαN]
  · apply twPlane_norm_eq_one_of_pow_three hq3 hν0
    rw [← twPlane_norm_pow, hν, hβN]
  · have h1 : (γ₁ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) α := hα
    rw [h1]
    congr 1
    exact Units.ext hμ.symm
  · have h1 : (γ₂ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) β := hβ
    rw [h1]
    congr 1
    exact Units.ext hν.symm

end Toral

section Group

variable {Γ : Type*} [Group Γ]

theorem twToral_comm_of_mem_closure_pair {a b : Γ} (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) {x y : Γ} (hx : x ∈ Subgroup.closure ({a, b} : Set Γ))
    (hy : y ∈ Subgroup.closure ({a, b} : Set Γ)) : x * y = y * x := by
  have hx' : x ∈ Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
    rw [← twPlane_closure_pair_eq_range hab ha hb]
    exact hx
  have hy' : y ∈ Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
    rw [← twPlane_closure_pair_eq_range hab ha hb]
    exact hy
  obtain ⟨⟨i, j⟩, rfl⟩ := hx'
  obtain ⟨⟨k, l⟩, rfl⟩ := hy'
  show (a ^ (i : ℕ) * b ^ (j : ℕ)) * (a ^ (k : ℕ) * b ^ (l : ℕ)) =
    (a ^ (k : ℕ) * b ^ (l : ℕ)) * (a ^ (i : ℕ) * b ^ (j : ℕ))
  rw [twPlane_pair_mul hab, twPlane_pair_mul hab, add_comm (i : ℕ), add_comm (j : ℕ)]

end Group

theorem twToralPlane_holds : TwToralPlane := by
  intro ℓ f K _ h hq3 hq γ₁ γ₂ hc h13 h23 hind
  obtain ⟨μ, ν, hμN, hνN, hμ3, hν3⟩ := twToral_exists_cube_roots hq3 hc h13 h23 hind
  set D := Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
    Set (MulAut (unitarySU ℓ f K 3))) with hD
  have haD : suConj h γ₁ ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : suConj h γ₂ ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc' : (γ₁ : GL (Fin 3) K) * γ₂ = γ₂ * γ₁ := congrArg Subtype.val hc
  have hμi : GeneralLinearGroup.scalar (Fin 3) μ⁻¹ ∈ unitaryIsom3 h := by
    apply scalar_mem_unitaryIsom3_of_norm
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμN, inv_one]
  have hνi : GeneralLinearGroup.scalar (Fin 3) ν⁻¹ ∈ unitaryIsom3 h := by
    apply scalar_mem_unitaryIsom3_of_norm
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hνN, inv_one]
  obtain ⟨x₁, hx₁⟩ : ∃ x : primeFormUnitary h (idGram K 3),
      (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * γ₁ :=
    ⟨⟨_, mem_primeFormUnitary_one ((unitaryIsom3 h).mul_mem hμi γ₁.2)⟩, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x : primeFormUnitary h (idGram K 3),
      (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * γ₂ :=
    ⟨⟨_, mem_primeFormUnitary_one ((unitaryIsom3 h).mul_mem hνi γ₂.2)⟩, rfl⟩
  have hx13 : x₁ ^ 3 = 1 := by
    apply Subtype.ext
    show (x₁ : GL (Fin 3) K) ^ 3 = 1
    have e1 : (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) K) ^ 3 =
        GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ 3) := (map_pow _ _ _).symm
    rw [hx₁, (commute_scalar μ⁻¹ (γ₁ : GL (Fin 3) K)).symm.mul_pow, hμ3, e1, ← map_mul,
      ← mul_pow, inv_mul_cancel, one_pow, map_one]
  have hx23 : x₂ ^ 3 = 1 := by
    apply Subtype.ext
    show (x₂ : GL (Fin 3) K) ^ 3 = 1
    have e1 : (GeneralLinearGroup.scalar (Fin 3) ν⁻¹ : GL (Fin 3) K) ^ 3 =
        GeneralLinearGroup.scalar (Fin 3) (ν⁻¹ ^ 3) := (map_pow _ _ _).symm
    rw [hx₂, (commute_scalar ν⁻¹ (γ₂ : GL (Fin 3) K)).symm.mul_pow, hν3, e1, ← map_mul,
      ← mul_pow, inv_mul_cancel, one_pow, map_one]
  have hab : Commute x₁ x₂ := by
    apply Subtype.ext
    show (x₁ : GL (Fin 3) K) * x₂ = x₂ * x₁
    have w1 := twToral_word μ⁻¹ ν⁻¹ (γ₁ : GL (Fin 3) K) γ₂ 1 1
    have w2 := twToral_word ν⁻¹ μ⁻¹ (γ₂ : GL (Fin 3) K) γ₁ 1 1
    simp only [pow_one] at w1 w2
    rw [hx₁, hx₂, w1, w2, mul_comm μ⁻¹ ν⁻¹, hc']
  have hword : ∀ i j : ℕ, ((x₁ ^ i * x₂ ^ j : primeFormUnitary h (idGram K 3)) :
      GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ i * ν⁻¹ ^ j) *
        ((γ₁ : GL (Fin 3) K) ^ i * (γ₂ : GL (Fin 3) K) ^ j) := by
    intro i j
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hx₁, hx₂, twToral_word]
  have hind' : ∀ i j : ℕ, x₁ ^ i * x₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    apply hind i j
    have h1 : ((x₁ ^ i * x₂ ^ j : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) = 1 := by
      rw [hij]
      rfl
    rw [hword] at h1
    have h2 : (γ₁ : GL (Fin 3) K) ^ i * (γ₂ : GL (Fin 3) K) ^ j =
        GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ i * ν⁻¹ ^ j)⁻¹ :=
      calc (γ₁ : GL (Fin 3) K) ^ i * (γ₂ : GL (Fin 3) K) ^ j
          = GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ i * ν⁻¹ ^ j)⁻¹ *
              (GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ i * ν⁻¹ ^ j) *
                ((γ₁ : GL (Fin 3) K) ^ i * (γ₂ : GL (Fin 3) K) ^ j)) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
        _ = GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ i * ν⁻¹ ^ j)⁻¹ := by rw [h1, mul_one]
    have e : suConj h (γ₁ ^ i * γ₂ ^ j) = suConj h γ₁ ^ i * suConj h γ₂ ^ j := by
      rw [map_mul, map_pow, map_pow]
    rw [← e]
    exact twToral_suConj_eq_one_of_scalar h2
  set G := Subgroup.closure ({x₁, x₂} : Set (primeFormUnitary h (idGram K 3))) with hG
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy =>
    twToral_comm_of_mem_closure_pair hab hx13 hx23 hx hy
  have hGexp : ∀ x ∈ G, x ^ 3 = 1 := fun x hx =>
    twPlane_pow_three_of_mem_closure_pair hab hx13 hx23 hx
  have hGcard : Nat.card G = 3 ^ 2 := by
    rw [twPlane_card_closure_pair hab hx13 hx23 hind']
    norm_num
  have hclos : Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ x ∈ G, x ≠ 1 ∧
      (g : GL (Fin 3) K) * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * (g : GL (Fin 3) K)} = ⊤ :=
    closure_centralizers_unitarySU_of_dvd_add_one_gu h Nat.prime_three hq3 hq G hGcomm hGexp hGcard
  have hsub : {g : unitarySU ℓ f K 3 | ∃ x ∈ G, x ≠ 1 ∧
      (g : GL (Fin 3) K) * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * (g : GL (Fin 3) K)} ⊆
        {k | ∃ e ∈ D, e ≠ 1 ∧ e k = k} := by
    rintro g ⟨x, hxG, hx1, hgx⟩
    have hx' : x ∈ Set.range (fun p : Fin 3 × Fin 3 => x₁ ^ (p.1 : ℕ) * x₂ ^ (p.2 : ℕ)) := by
      rw [← twPlane_closure_pair_eq_range hab hx13 hx23]
      exact hxG
    obtain ⟨⟨i, j⟩, rfl⟩ := hx'
    refine ⟨suConj h γ₁ ^ (i : ℕ) * suConj h γ₂ ^ (j : ℕ),
      D.mul_mem (D.pow_mem haD _) (D.pow_mem hbD _), ?_, ?_⟩
    · intro he1
      obtain ⟨hi, hj⟩ := hind _ _ he1
      apply hx1
      have hi0 : (i : ℕ) = 0 := by
        have := i.2
        omega
      have hj0 : (j : ℕ) = 0 := by
        have := j.2
        omega
      show x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) = 1
      rw [hi0, hj0, pow_zero, pow_zero, mul_one]
    · have hgx' : (g : GL (Fin 3) K) * ((x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) :
          primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) =
          ((x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) *
            (g : GL (Fin 3) K) := hgx
      rw [hword] at hgx'
      have h1 : (g : GL (Fin 3) K) * ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) * (γ₂ : GL (Fin 3) K) ^ (j : ℕ))
          = ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) * (γ₂ : GL (Fin 3) K) ^ (j : ℕ)) * g := by
        have e1 : (g : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ (i : ℕ) *
            ν⁻¹ ^ (j : ℕ)) * ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) * (γ₂ : GL (Fin 3) K) ^ (j : ℕ))) =
            GeneralLinearGroup.scalar (Fin 3) (μ⁻¹ ^ (i : ℕ) * ν⁻¹ ^ (j : ℕ)) *
              ((g : GL (Fin 3) K) * ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) *
                (γ₂ : GL (Fin 3) K) ^ (j : ℕ))) := by
          rw [← mul_assoc, (commute_scalar (μ⁻¹ ^ (i : ℕ) * ν⁻¹ ^ (j : ℕ))
            (g : GL (Fin 3) K)).eq, mul_assoc]
        rw [e1, mul_assoc] at hgx'
        exact mul_left_cancel hgx'
      refine Subtype.ext ?_
      have e : suConj h γ₁ ^ (i : ℕ) * suConj h γ₂ ^ (j : ℕ) =
          suConj h (γ₁ ^ (i : ℕ) * γ₂ ^ (j : ℕ)) := by
        rw [map_mul, map_pow, map_pow]
      rw [e]
      show ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) * (γ₂ : GL (Fin 3) K) ^ (j : ℕ)) * g *
        ((γ₁ : GL (Fin 3) K) ^ (i : ℕ) * (γ₂ : GL (Fin 3) K) ^ (j : ℕ))⁻¹ = g
      rw [← h1, mul_inv_cancel_right]
  show Subgroup.closure {k | ∃ e ∈ D, e ≠ 1 ∧ e k = k} = ⊤
  rw [eq_top_iff, ← hclos]
  exact Subgroup.closure_mono hsub

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
