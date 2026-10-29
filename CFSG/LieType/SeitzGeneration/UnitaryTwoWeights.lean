module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LieType.SeitzGeneration.UnitaryONExt

public section

namespace CFSG.LieType.SeitzGeneration.UnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt

section Transfer

variable {G G' : Type*} [Group G] [Group G']

theorem closure_centralizers_of_equiv (φ : G ≃* G') (X : Set G)
    (h : Subgroup.closure {g' : G' | ∃ x ∈ φ '' X, g' * x = x * g'} = ⊤) :
    Subgroup.closure {g : G | ∃ x ∈ X, g * x = x * g} = ⊤ := by
  have hset : {g' : G' | ∃ x ∈ φ '' X, g' * x = x * g'} =
      φ '' {g : G | ∃ x ∈ X, g * x = x * g} := by
    ext g'
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hg⟩
      refine ⟨φ.symm g', ⟨x, hx, ?_⟩, by simp⟩
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    · rintro ⟨g, ⟨x, hx, hg⟩, rfl⟩
      exact ⟨φ x, ⟨x, hx, rfl⟩, by rw [← map_mul, ← map_mul, hg]⟩
  rw [hset] at h
  have h2 : (Subgroup.closure {g : G | ∃ x ∈ X, g * x = x * g}).map φ.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure]
    exact h
  have h3 : (Subgroup.closure {g : G | ∃ x ∈ X, g * x = x * g}).map φ.toMonoidHom =
      (⊤ : Subgroup G).map φ.toMonoidHom := by
    rw [h2, Subgroup.map_top_of_surjective _ φ.surjective]
  exact Subgroup.map_injective φ.injective h3

end Transfer

section Combinatorics

theorem card_pairs_le_two : ∀ c : Fin 5 → Fin 3,
    (∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k → c i = c j → c i = c k → False) →
    (Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ c p.1 = c p.2)).card ≤ 2 := by
  decide +kernel

theorem exists_two_complement : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
    ∃ l m : Fin 5, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ l ≠ m := by
  decide +kernel

variable {E C : Type*} [Group E] [Finite E] [CommGroup C] [Finite C]

theorem three_le_card_eq (hE : Nat.card E = 9) (hC : Nat.card C = 3) (χ χ' : E →* C) :
    3 ≤ Nat.card {x : E // χ x = χ' x} := by
  have h := Subgroup.card_ker_mul_card_range (χ / χ')
  have hr : Nat.card (χ / χ').range ≤ 3 := hC ▸ Subgroup.card_le_card_group _
  have hk : Nat.card {x : E // χ x = χ' x} = Nat.card (χ / χ').ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MonoidHom.mem_ker, MonoidHom.div_apply, div_eq_one]
  rw [hk]
  by_contra hlt
  push Not at hlt
  rw [hE] at h
  nlinarith

theorem exists_ne_one_eq (hE : Nat.card E = 9) (hC : Nat.card C = 3) (χ χ' : E →* C) :
    ∃ x : E, x ≠ 1 ∧ χ x = χ' x := by
  have h := three_le_card_eq hE hC χ χ'
  have : Nontrivial {x : E // χ x = χ' x} :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨x, hx⟩, hne⟩ := exists_ne (⟨1, by simp⟩ : {x : E // χ x = χ' x})
  exact ⟨x, fun h1 => hne (Subtype.ext h1), hx⟩

theorem exists_eq_triple (hE : Nat.card E = 9) (hC : Nat.card C = 3) (χ : Fin 5 → E →* C) :
    ∃ x : E, x ≠ 1 ∧ ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ χ i x = χ j x ∧
      χ i x = χ k x := by
  classical
  by_contra hno
  push Not at hno
  have := Fintype.ofFinite E
  have hEc : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card, hE]
  set P : Finset (Fin 5 × Fin 5) := Finset.univ.filter (fun p => p.1 < p.2) with hP
  have hPcard : P.card = 10 := by rw [hP]; decide +kernel
  have hlow : ∀ p ∈ P, 3 ≤ (Finset.univ.filter (fun x : E => χ p.1 x = χ p.2 x)).card := by
    intro p _
    have := three_le_card_eq hE hC (χ p.1) (χ p.2)
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  have hcount : ∑ p ∈ P, (Finset.univ.filter (fun x : E => χ p.1 x = χ p.2 x)).card =
      ∑ x : E, (P.filter (fun p => χ p.1 x = χ p.2 x)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hup : ∀ x : E, x ≠ 1 → (P.filter (fun p => χ p.1 x = χ p.2 x)).card ≤ 2 := by
    intro x hx
    let e : C ≃ Fin 3 := (Finite.equivFin C).trans (finCongr hC)
    have h := card_pairs_le_two (fun i => e (χ i x)) (fun i j k hij hik hjk h1 h2 =>
      hno x hx i j k hij hik hjk (e.injective h1) (e.injective h2))
    rw [hP, Finset.filter_filter]
    simpa only [e.apply_eq_iff_eq] using h
  have hone : (P.filter (fun p => χ p.1 (1 : E) = χ p.2 1)).card = 10 := by
    simp [hPcard]
  have hsum : ∑ x : E, (P.filter (fun p => χ p.1 x = χ p.2 x)).card ≤ 10 + 8 * 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E)), hone]
    have := Finset.sum_le_card_nsmul (Finset.univ.erase (1 : E))
      (fun x => (P.filter (fun p => χ p.1 x = χ p.2 x)).card) 2
      (fun x hx => hup x (Finset.ne_of_mem_erase hx))
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hEc] at this
    simpa using Nat.add_le_add_left this 10
  have hlow' : 3 * 10 ≤ ∑ p ∈ P, (Finset.univ.filter (fun x : E => χ p.1 x = χ p.2 x)).card := by
    have := Finset.card_nsmul_le_sum P _ 3 hlow
    rwa [hPcard, smul_eq_mul, mul_comm] at this
  rw [hcount] at hlow'
  omega

end Combinatorics

section Frame

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_eigenframe (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (E : Subgroup (unitarySU ℓ f K n)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ u : Fin n → Fin n → K, IsON (unitaryInvolution K ℓ f) u ∧ (∀ v, ∃ c, orthoEmb u c = v) ∧
      ∀ y ∈ E, ∃ d : Fin n → K, ∀ i,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = d i • u i := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : (⇑σ : K → K) = ⇑h.bar :=
    funext fun c => by rw [hσdef, unitaryInvolution_apply, h.bar_apply]
  set G : Subgroup (primeFormUnitary h (idGram K n)) :=
    E.map (Subgroup.inclusion (unitarySU_le_primeFormUnitary h)) with hG
  have hcommG : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hpowG : ∀ x ∈ G, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hq3 G hcommG hpowG
  set Pm : Matrix (Fin n) (Fin n) K := ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPm
  have hPunit : conjTr σ Pm * Pm = 1 := by
    have h1 := mem_primeFormUnitary.1 P.2
    simp only [idGram, Units.val_one, Matrix.mul_one] at h1
    rw [conjTr, hσ]
    exact h1
  have hPinv : Pm * ((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) = 1 := by
    rw [hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPinv' : (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm = 1 := by
    rw [hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨fun i => Pm *ᵥ Pi.single i 1, ?_, ?_, ?_⟩
  · intro i j
    rw [herm_mulVec, hPunit, one_mulVec, herm_single_left, map_one, one_mul, Pi.single_apply]
  · intro v
    refine ⟨(((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v, ?_⟩
    have hcol : colMat (fun i => Pm *ᵥ (Pi.single i 1 : Fin n → K)) = Pm := by
      ext k j
      simp [colMat, Matrix.mulVec_single_one]
    rw [← colMat_mulVec, hcol, mulVec_mulVec, hPinv, one_mulVec]
  · intro y hy
    have hdiag := hP _ ⟨y, hy, rfl⟩
    set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
    set Pi' : Matrix (Fin n) (Fin n) K :=
      (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPi'
    have hcoe : (((P⁻¹ * Subgroup.inclusion (unitarySU_le_primeFormUnitary h) y * P :
        primeFormUnitary h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Pi' * Y * Pm := by
      simp [hPi', hY, hPm, Units.val_mul]
    rw [hcoe] at hdiag
    obtain ⟨d, hd⟩ : ∃ d : Fin n → K, Pi' * Y * Pm = diagonal d :=
      ⟨_, hdiag.diagonal_diag.symm⟩
    have hYP : Y * Pm = Pm * diagonal d := by
      calc Y * Pm = (Pm * Pi') * Y * Pm := by rw [hPinv, Matrix.one_mul]
        _ = Pm * (Pi' * Y * Pm) := by simp only [Matrix.mul_assoc]
        _ = Pm * diagonal d := by rw [hd]
    refine ⟨d, fun i => ?_⟩
    have hdi : (diagonal d *ᵥ (Pi.single i 1 : Fin n → K)) = d i • Pi.single i 1 := by
      funext k
      simp only [mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp_all
    rw [mulVec_mulVec, hYP, ← mulVec_mulVec, hdi, mulVec_smul]

end Frame

end CFSG.LieType.SeitzGeneration.UnitaryTwo
