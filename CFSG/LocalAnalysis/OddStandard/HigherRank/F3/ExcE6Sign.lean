module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Levi

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG.ClassicalInvolution.WeakCT
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.RouteD (path6 path6_ne theta6)
open scoped MatrixGroups

section Matrices

def negOneTwo (K : Type) [Field K] : SL(2, K) :=
  ⟨-1, by norm_num [Matrix.det_neg]⟩

def negOneSix (K : Type) [Field K] : SL(6, K) :=
  ⟨-1, by norm_num [Matrix.det_neg]⟩

theorem negOneTwo_mul_comm {K : Type} [Field K] (A : SL(2, K)) :
    negOneTwo K * A = A * negOneTwo K := by
  ext i j
  show ((-1 : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)) i j =
    ((A : Matrix (Fin 2) (Fin 2) K) * (-1)) i j
  simp

theorem negOneTwo_ne_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) : negOneTwo K ≠ 1 := by
  intro h
  have h' : (-1 : K) = 1 := by
    simpa [negOneTwo] using
      congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have : (2 : K) = 0 := by
    rw [show (2 : K) = 1 - (-1) by ring, h', sub_self]
  exact h2 this

theorem negOneSix_mem_center (K : Type) [Field K] : negOneSix K ∈ center SL(6, K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  show ((g : Matrix (Fin 6) (Fin 6) K) * (-1)) i j =
    ((-1) * (g : Matrix (Fin 6) (Fin 6) K)) i j
  simp

theorem orderOf_negOneSix {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    orderOf (negOneSix K) = 2 := by
  apply orderOf_eq_prime
  · ext i j
    show ((-1 : Matrix (Fin 6) (Fin 6) K) ^ 2) i j = (1 : Matrix (Fin 6) (Fin 6) K) i j
    simp [pow_two]
  · intro h
    have h' : (-1 : K) = 1 := by
      simpa [negOneSix] using
        congrArg (fun g : SL(6, K) => (g : Matrix (Fin 6) (Fin 6) K) 0 0) h
    have : (2 : K) = 0 := by
      rw [show (2 : K) = 1 - (-1) by ring, h', sub_self]
    exact h2 this

theorem gf3_eq_zero_or_one_or_neg_one (x : GaloisField 3 1) : x = 0 ∨ x = 1 ∨ x = -1 := by
  letI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.ClassicalInvolution.Q3.Q3W.card_gf3
  have h3 : x ^ 3 = x := by
    have := FiniteField.pow_card x
    rwa [hcard] at this
  have h4 : x * ((x - 1) * (x + 1)) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.1 h4 with h | h
  · exact Or.inl h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem eq_one_or_eq_negOneSix_of_mem_center {g : SL(6, GaloisField 3 1)}
    (hg : g ∈ center SL(6, GaloisField 3 1)) : g = 1 ∨ g = negOneSix (GaloisField 3 1) := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rcases gf3_eq_zero_or_one_or_neg_one r with rfl | rfl | rfl
  · simp at hr
  · left
    apply Subtype.ext
    rw [← hrg]
    simp
  · right
    apply Subtype.ext
    rw [← hrg]
    ext i j
    by_cases h : i = j <;>
      simp [negOneSix, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, h]

theorem blockMat_six_neg_one_eq_diagonal {K : Type} [Field K] (i : ℕ) :
    CFSG.ClassicalInvolution.Phan.blockMat 6 i (-1 : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun a : Fin 6 => if i ≤ a.val ∧ a.val < i + 2 then (-1 : K) else 1) := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : i ≤ a.val ∧ a.val < i + 2
    · simp [ha]
    · simp [ha]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    by_cases hA : (i ≤ a.val ∧ a.val < i + 2) ∧ (i ≤ b.val ∧ b.val < i + 2)
    · rw [dif_pos hA, Matrix.diagonal_apply_ne _ hab]
      have : (⟨a.val - i, by omega⟩ : Fin 2) ≠ ⟨b.val - i, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [Matrix.one_apply, this]
    · rw [dif_neg hA, Matrix.diagonal_apply_ne _ hab]
      simp [Matrix.one_apply, hab]

theorem negOneSix_eq_mul_blocks (K : Type) [Field K] :
    negOneSix K = blockSL2 K 5 0 (negOneTwo K) * blockSL2 K 5 2 (negOneTwo K) *
      blockSL2 K 5 4 (negOneTwo K) := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 6) (Fin 6) K) = _
  simp only [Matrix.SpecialLinearGroup.coe_mul, blockSL2, coe_blockSL]
  change (-1 : Matrix (Fin 6) (Fin 6) K) =
    CFSG.ClassicalInvolution.Phan.blockMat 6 0 (-1 : Matrix (Fin 2) (Fin 2) K) *
      CFSG.ClassicalInvolution.Phan.blockMat 6 2 (-1 : Matrix (Fin 2) (Fin 2) K) *
      CFSG.ClassicalInvolution.Phan.blockMat 6 4 (-1 : Matrix (Fin 2) (Fin 2) K)
  rw [blockMat_six_neg_one_eq_diagonal, blockMat_six_neg_one_eq_diagonal,
    blockMat_six_neg_one_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst hab
    fin_cases a <;> simp
  · simp [Matrix.one_apply, hab, Matrix.diagonal_apply_ne _ hab]

end Matrices

section Diagonal

theorem iform_parity_e6 : ∀ i : Fin (Tag.rank .E6),
    (iform (τ := .E6) (Pi.single (path6 0 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) +
      iform (τ := .E6) (Pi.single (path6 2 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) +
      iform (τ := .E6) (Pi.single (path6 4 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) -
      (if i.val = 1 then 1 else 0)) % 2 = 0 := by
  decide +kernel

theorem thetaDiag_mul_blocks {K : Type} [Field K] :
    thetaDiag (τ := .E6) (Pi.single (path6 0 : Fin (Tag.rank .E6)) 1) (-1 : Kˣ) *
      thetaDiag (τ := .E6) (Pi.single (path6 2 : Fin (Tag.rank .E6)) 1) (-1 : Kˣ) *
      thetaDiag (τ := .E6) (Pi.single (path6 4 : Fin (Tag.rank .E6)) 1) (-1 : Kˣ) =
    thetaDiag thetaE6 (-1 : Kˣ) := by
  funext i
  simp only [Pi.mul_apply, thetaDiag]
  rw [← zpow_add, ← zpow_add, iform_thetaE6_single i]
  have he := Int.even_iff.2 (iform_parity_e6 i)
  generalize iform (τ := .E6) (Pi.single (path6 0 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) = a
    at he ⊢
  generalize iform (τ := .E6) (Pi.single (path6 2 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) = b
    at he ⊢
  generalize iform (τ := .E6) (Pi.single (path6 4 : Fin (Tag.rank .E6)) 1) (Pi.single i 1) = c
    at he ⊢
  generalize (if i.val = 1 then (1 : ℤ) else 0) = d at he ⊢
  calc (-1 : Kˣ) ^ (a + b + c) = (-1) ^ (d + (a + b + c - d)) := by congr 1; ring
    _ = (-1) ^ d * (-1) ^ (a + b + c - d) := zpow_add _ _ _
    _ = (-1) ^ d := by rw [he.neg_one_zpow, mul_one]

theorem rootDiagUnit_thetaDiag_ne_one_e6 {K : Type} [Field K] (hK : ringChar K ≠ 2)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    rootDiagUnit .E6 (thetaDiag γ (-1 : Kˣ)) ≠ 1 := by
  rw [← rootTorusSL2_eq_thetaDiag_e6 hγ (-1)]
  exact rootTorusSL2_neg_one_ne_one hK γ

end Diagonal

section Block


theorem e6Eps_theta_block_neg
    {Θ : SL(6, GaloisField 3 1) →* ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hker : Θ.ker ≤ Subgroup.center SL(6, GaloisField 3 1))
    (hblk : ∀ i : Fin 5, (blockSL2 (GaloisField 3 1) 5 i).range.map Θ =
      CFSG.LieType.CurtisTits.rankOne (e6Datum (GaloisField 3 1)).rootGroup (path6 i))
    (i : Fin 5) :
    e6Eps (Θ (blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)))) =
      rootDiagUnit .E6 (thetaDiag (Pi.single (path6 i : Fin (Tag.rank .E6)) 1)
        (-1 : (GaloisField 3 1)ˣ)) := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hγ : IsRoot .E6 (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := isRoot_single .E6 _
  have hmemR : ∀ x : SL(6, GaloisField 3 1), x ∈ (blockSL2 (GaloisField 3 1) 5 i).range →
      Θ x ∈ stdRankOne (e6Datum (GaloisField 3 1))
        (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := by
    intro x hx
    have h := Subgroup.mem_map_of_mem Θ hx
    rw [hblk i] at h
    exact h
  have hbmem : blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)) ∈
      (blockSL2 (GaloisField 3 1) 5 i).range := ⟨_, rfl⟩
  have hz : e6Isogeny (GaloisField 3 1)
      (Θ (blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)))) ∈
      stdRankOne (e6AdjDatum (GaloisField 3 1)) (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := by
    rw [← map_stdRankOne_e6_gen hγ]
    exact Subgroup.mem_map_of_mem _ (hmemR _ hbmem)
  have hzc : ∀ r ∈ stdRankOne (e6AdjDatum (GaloisField 3 1))
      (Pi.single (path6 i : Fin (Tag.rank .E6)) 1),
      e6Isogeny (GaloisField 3 1)
        (Θ (blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)))) * r =
      r * e6Isogeny (GaloisField 3 1)
        (Θ (blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)))) := by
    intro r hr
    rw [← map_stdRankOne_e6_gen hγ] at hr
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hr
    have hs' : s ∈ (blockSL2 (GaloisField 3 1) 5 i).range.map Θ := by
      rw [hblk i]
      exact hs
    obtain ⟨a, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hs'
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      negOneTwo_mul_comm A]
  rcases central_stdRankOne_e6_gen hF hγ hz hzc with h1 | h1
  · exfalso
    have h2 : e6Eps (Θ (blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)))) =
        e6Eps 1 := by
      rw [map_one]
      exact h1
    have h3 := e6Eps_injective h2
    have h4 : blockSL2 (GaloisField 3 1) 5 i (negOneTwo (GaloisField 3 1)) ∈ Θ.ker := h3
    have h5 := eq_one_of_blockSL_mem_center (K := GaloisField 3 1) (m := 6) (k := 2)
      (i := (i : ℕ)) (by omega) (by omega) (hker h4)
    exact negOneTwo_ne_one (CFSG.ClassicalInvolution.Q3.Q3W.two_ne_zero_gf3) h5
  · exact h1

theorem e6Eps_theta_negOneSix
    {Θ : SL(6, GaloisField 3 1) →* ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hker : Θ.ker ≤ Subgroup.center SL(6, GaloisField 3 1))
    (hblk : ∀ i : Fin 5, (blockSL2 (GaloisField 3 1) 5 i).range.map Θ =
      CFSG.LieType.CurtisTits.rankOne (e6Datum (GaloisField 3 1)).rootGroup (path6 i)) :
    e6Eps (Θ (negOneSix (GaloisField 3 1))) =
      rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (GaloisField 3 1)ˣ)) := by
  rw [negOneSix_eq_mul_blocks, map_mul, map_mul, map_mul, map_mul,
    e6Eps_theta_block_neg hker hblk 0, e6Eps_theta_block_neg hker hblk 2,
    e6Eps_theta_block_neg hker hblk 4, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    thetaDiag_mul_blocks]

theorem theta_negOneSix_ne_one
    {Θ : SL(6, GaloisField 3 1) →* ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hker : Θ.ker ≤ Subgroup.center SL(6, GaloisField 3 1))
    (hblk : ∀ i : Fin 5, (blockSL2 (GaloisField 3 1) 5 i).range.map Θ =
      CFSG.LieType.CurtisTits.rankOne (e6Datum (GaloisField 3 1)).rootGroup (path6 i)) :
    Θ (negOneSix (GaloisField 3 1)) ≠ 1 := by
  intro h
  have h1 := e6Eps_theta_negOneSix hker hblk
  rw [h, map_one] at h1
  exact rootDiagUnit_thetaDiag_ne_one_e6 (ringChar_galoisField_ne_two (by norm_num))
    isRoot_thetaE6 h1.symm

theorem theta_injective_e6
    {Θ : SL(6, GaloisField 3 1) →* ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hker : Θ.ker ≤ Subgroup.center SL(6, GaloisField 3 1))
    (hblk : ∀ i : Fin 5, (blockSL2 (GaloisField 3 1) 5 i).range.map Θ =
      CFSG.LieType.CurtisTits.rankOne (e6Datum (GaloisField 3 1)).rootGroup (path6 i)) :
    Function.Injective Θ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases eq_one_or_eq_negOneSix_of_mem_center (hker hg) with h | h
  · exact h
  · rw [h] at hg
    exact absurd hg (theta_negOneSix_ne_one hker hblk)

end Block

end CFSG.OddStandard.HigherRank.F3
