module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusBase

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.AGLEmbedding.LieOut (NoAp)

variable {n : ℕ} {F : Type} [Field F]

section Isometry

theorem statedQuadPlus_elim (x y : Fin n → F) :
    StatedQuadPlus n F (Sum.elim x y) = x ⬝ᵥ y := by
  simp [StatedQuadPlus, dotProduct]

theorem leviSp_mem_orthGroup (A : GL (Fin n) F) :
    ((leviSp A : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈ orthGroup (StatedQuadPlus n F) := by
  apply Subgroup.subset_closure
  intro v
  have hv : v = Sum.elim (fun a => v (Sum.inl a)) (fun a => v (Sum.inr a)) := by
    ext (a | a) <;> rfl
  rw [coe_leviSp, hv, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr,
    statedQuadPlus_elim]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  have h1 : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1, Matrix.one_mulVec]

end Isometry

section Perfect

theorem perfect_SL [Finite F] [CharP F 2] (k : ℕ) (h : ¬ (k = 2 ∧ Nat.card F = 2)) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) F))⁆ = ⊤ := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · have : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) F) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact Subsingleton.elim _ _
    · have h1 : ∀ A : Matrix.SpecialLinearGroup (Fin 1) F, (A : Matrix (Fin 1) (Fin 1) F) = 1 := by
        intro A
        have hd := A.2
        rw [Matrix.det_fin_one] at hd
        ext i j
        fin_cases i
        fin_cases j
        simp [hd]
      have : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) F) :=
        ⟨fun a b => Subtype.ext ((h1 a).trans (h1 b).symm)⟩
      exact Subsingleton.elim _ _
    · have hne : Nat.card F ≠ 2 := fun h2 => h ⟨rfl, h2⟩
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨m, -, hm⟩ := FiniteField.card F 2
      have hcard : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
      have hm1 : 2 ≤ (m : ℕ) := by
        by_contra hlt
        have : (m : ℕ) = 1 := by have := m.pos; omega
        rw [this] at hcard
        exact hne (by simpa using hcard)
      have h4 : 4 ≤ Nat.card F := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm1
      exact Group.isPerfect_def.1
        (LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4).1
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact Group.isPerfect_def.1
      (LieType.Universal.SpecialLinear.isQuasisimple m F (by omega)).1

end Perfect

section Lift

variable [Finite F] [CharP F 2] {S : Finset ℕ}

theorem stepLevi_mem_om (ℓ : ℕ)
    (hperf : ¬ (Fintype.card (StepCoord n S ℓ) = 2 ∧ Nat.card F = 2))
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F) :
    ((stepLevi S ℓ A : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈ Om n F := by
  set f : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F →*
      GL (Fin n ⊕ Fin n) F := (StatedSp n F).subtype.comp (stepLevi S ℓ) with hf
  have hrange : f.range ≤ orthGroup (StatedQuadPlus n F) := by
    rintro _ ⟨B, rfl⟩
    exact leviSp_mem_orthGroup (stepLeviGL S ℓ B)
  have hA' : f A ∈ Subgroup.map f ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup
      (Fin (Fintype.card (StepCoord n S ℓ))) F)), ⊤⁆ :=
    Subgroup.mem_map_of_mem f (by rw [perfect_SL _ hperf]; exact Subgroup.mem_top A)
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at hA'
  exact Subgroup.commutator_mono hrange hrange hA'

theorem exists_stepLeviO (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (ℓ : ℕ)
    (hperf : ¬ (Fintype.card (StepCoord n S ℓ) = 2 ∧ Nat.card F = 2)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F →* ↥(Om n F),
      Function.Injective φ ∧ (∀ A, omSp (φ A) = stepLevi S ℓ A) ∧ ∀ A, φ A ∈ JO n F S := by
  refine ⟨((StatedSp n F).subtype.comp (stepLevi S ℓ)).codRestrict (Om n F)
    (stepLevi_mem_om ℓ hperf), ?_, fun A => rfl, fun A => stepLevi_mem hS ℓ A⟩
  intro A B h
  exact stepLevi_injective S ℓ (congrArg omSp h)

end Lift

section Orders

variable [Finite F] [CharP F 2] {S : Finset ℕ}

omit [CharP F 2] in
theorem not_sq_dvd_card_SL_corner {G : Type*} [Group G] {J : Subgroup G} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F)
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) {k : ℕ}
    (hφ : ¬ (k = 2 ∧ Nat.card F = 2) → ∃ φ : Matrix.SpecialLinearGroup (Fin k) F →* G,
      Function.Injective φ ∧ ∀ A, φ A ∈ J) :
    ¬ p ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) F) := by
  by_cases hc : k = 2 ∧ Nat.card F = 2
  · obtain ⟨rfl, hK2⟩ := hc
    have : Fintype F := Fintype.ofFinite F
    have h1 := Matrix.card_SL_field (𝔽 := F) 2
    rw [← Nat.card_eq_fintype_card, hK2] at h1
    simp [Fin.prod_univ_two] at h1
    rw [h1]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    rcases hp57 with rfl | rfl <;> omega
  · obtain ⟨φ, hinj, hJ⟩ := hφ hc
    exact not_sq_dvd_card_SL hp57 hK hA1 φ hinj hJ

theorem not_sq_dvd_card_step_D {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) (ℓ : ℕ) :
    ¬ p ^ 2 ∣ Nat.card (GL (StepCoord n S ℓ) F) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  rw [card_GL_congr (Fintype.equivFin (StepCoord n S ℓ))]
  set k := Fintype.card (StepCoord n S ℓ) with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
    have : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    rw [Nat.card_of_subsingleton (1 : GL (Fin 0) F)]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    rcases hp57 with rfl | rfl <;> omega
  · have : NeZero k := ⟨hpos.ne'⟩
    rw [card_GL_eq_mul_card_SL]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (Nat.card F - 1) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    refine not_sq_dvd_card_SL_corner (J := JO n F S) hp57 hK hA1 (k := k) ?_
      (hcop.dvd_of_dvd_mul_left hd)
    intro hperf
    obtain ⟨φ, hinj, -, hJ⟩ := exists_stepLeviO hS ℓ hperf
    exact ⟨φ, hinj, hJ⟩

theorem step_card_le_two_D {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) (ℓ : ℕ) : Fintype.card (StepCoord n S ℓ) ≤ 2 := by
  by_contra hk
  push Not at hk
  have hperf : ¬ (Fintype.card (StepCoord n S ℓ) = 2 ∧ Nat.card F = 2) := fun h => by omega
  obtain ⟨φ, hinj, -, hJ⟩ := exists_stepLeviO hS ℓ hperf
  refine not_sq_dvd_card_SL hp57 hK hA1 φ hinj hJ ?_
  have h1 := pow_dvd_card_SL (K := F) (Fintype.card (StepCoord n S ℓ)) (by omega)
  exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans h1

end Orders

section Commute

variable [Finite F] [CharP F 2] {S : Finset ℕ}

omit [Finite F] in
theorem stepLeviO_commute {ℓ ℓ' : ℕ} (hℓ : ℓ < S.card) (hℓ' : ℓ' < S.card) (hne : ℓ ≠ ℓ')
    (φ : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F →* ↥(Om n F))
    (φ' : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ'))) F →* ↥(Om n F))
    (hφ : ∀ A, omSp (φ A) = stepLevi S ℓ A) (hφ' : ∀ A, omSp (φ' A) = stepLevi S ℓ' A)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F)
    (B : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ'))) F) :
    φ A * φ' B = φ' B * φ A := by
  apply omSp_injective
  rw [map_mul, map_mul, hφ, hφ']
  exact stepLevi_commute_stepLevi hℓ hℓ' hne A B

theorem levi_data_sl2_D {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F)
    (hpq : p ∣ Nat.card F - 1) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (ℓ : ℕ)
    (hk : Fintype.card (StepCoord n S ℓ) = 2) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord n S ℓ))) F →* ↥(Om n F),
      Function.Injective φ ∧ (∀ A, omSp (φ A) = stepLevi S ℓ A) ∧ (∀ A, φ A ∈ JO n F S) ∧
      φ.range ≤ JO n F S ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧ p ∣ Nat.card φ.range ∧
        NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  have hK4 : 4 ≤ Nat.card F := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have hperf : ¬ (Fintype.card (StepCoord n S ℓ) = 2 ∧ Nat.card F = 2) := fun h => by omega
  obtain ⟨φ, hinj, hφ, hJ⟩ := exists_stepLeviO hS ℓ hperf
  exact ⟨φ, hinj, hφ, hJ, levi_data_sl2 (J := JO n F S) hp57 hK hpq hk φ hinj hJ⟩

end Commute

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
