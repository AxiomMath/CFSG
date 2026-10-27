module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Emb
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Type

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
  CFSG.AGLEmbedding.U62ThreeCent CFSG.RankThree.PartOne.KCOrthogonal

theorem commutator_gramSU_four :
    ⁅gramSU uData (1 : Matrix (Fin 4) (Fin 4) F4), gramSU uData (1 : Matrix (Fin 4) (Fin 4) F4)⁆ =
      gramSU uData (1 : Matrix (Fin 4) (Fin 4) F4) := by
  have := uData.charP
  have h := (statedSU_four_char_two_perfect_simple uData).1
  rw [Subgroup.isPerfect_iff] at h
  rw [← unitarySU_eq_gramSU uData 4]
  exact h

theorem diagHom_mem_gramSU {n : ℕ} (d : Fin n → F4ˣ) (hd : ∏ i, d i = 1) :
    CFSG.RankThree.PartTwo.Sec4.Census.diagHom d ∈
      gramSU uData (1 : Matrix (Fin n) (Fin n) F4) := by
  refine ⟨?_, ?_⟩
  · rw [CFSG.RankThree.PartTwo.Sec4.Census.coe_diagHom, Matrix.diagonal_map (map_zero _),
      diagonal_transpose, Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply]
    calc ((d i : F4ˣ) : F4) ^ 2 ^ 1 * (d i : F4ˣ) = ((d i : F4ˣ) : F4) ^ 3 := by ring
      _ = 1 := pow_three_F4 (d i).ne_zero
  · rw [CFSG.RankThree.PartTwo.Sec4.Census.coe_diagHom, det_diagonal]
    have h1 := congrArg Units.val hd
    rwa [Units.coe_prod, Units.val_one] at h1

theorem exists_equiv_four (κ : Fin 6 → ZMod 3) (t : ZMod 3) (h4 : Ncnt κ t = 4) :
    ∃ e : Fin 4 ⊕ Fin 2 ≃ Fin 6, ∀ a, κ (e (Sum.inl a)) = t := by
  have hJ : Fintype.card {i : Fin 6 // ¬κ i = t} = 2 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin]
    have : Fintype.card {i : Fin 6 // κ i = t} = 4 := h4
    omega
  let eI : {i : Fin 6 // κ i = t} ≃ Fin 4 := Fintype.equivFinOfCardEq h4
  let eJ : {i : Fin 6 // ¬κ i = t} ≃ Fin 2 := Fintype.equivFinOfCardEq hJ
  refine ⟨(Equiv.sumCongr eI.symm eJ.symm).trans (Equiv.sumCompl fun i => κ i = t), fun a => ?_⟩
  exact (eI.symm a).2

theorem exists_perfect_of_four (κ : Fin 6 → ZMod 3) (a : gramSU uData M6)
    (ha : (a : GL (Fin 6) F4) = dK κ) (t : ZMod 3) (h4 : Ncnt κ t = 4) :
    ∃ D : Subgroup P6, D ≤ Subgroup.centralizer ({(a : P6)} : Set P6) ∧ ⁅D, D⁆ = D ∧
      3 ∣ Nat.card D := by
  obtain ⟨e, he⟩ := exists_equiv_four κ t h4
  let G4 := gramSU uData (1 : Matrix (Fin 4) (Fin 4) F4)
  have : Group.IsPerfect G4 := Subgroup.isPerfect_iff.2 commutator_gramSU_four
  let embSU : G4 →* gramSU uData M6 :=
    ((embGL e).comp G4.subtype).codRestrict _ fun A => embGL_mem_gramSU e A.2
  let Φ : G4 →* P6 := (QuotientGroup.mk' (normOneScalars uData (gramSU uData M6) 6)).comp embSU
  have hΦ : ∀ A : G4, (Φ A : P6) = ((embSU A : gramSU uData M6) : P6) := fun A => rfl
  refine ⟨Φ.range, ?_, Subgroup.isPerfect_iff.1 (Group.IsPerfect.range Φ), ?_⟩
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hΦ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    have hd : ∀ p q : Fin 4, ((rootUnit (κ (e (Sum.inl p))) : F4ˣ) : F4) =
        ((rootUnit (κ (e (Sum.inl q))) : F4ˣ) : F4) := fun p q => by rw [he p, he q]
    have := embGL_commute e (A : GL (Fin 4) F4) (fun i => ((rootUnit (κ i) : F4ˣ) : F4)) hd
    change ((embGL e A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = ((a : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) * ((embGL e A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
    rw [ha, coe_diagGL6]
    exact this
  ·
    let d : Fin 4 → F4ˣ := ![rootUnit 1, rootUnit 2, 1, 1]
    have hd : ∏ i, d i = 1 := by
      rw [Fin.prod_univ_four]
      have h3 : rootUnit 1 * rootUnit 2 = 1 := by
        rw [← rootUnit_add, show (1 : ZMod 3) + 2 = 0 from by decide, rootUnit_zero]
      simp [d, h3]
    let A₀ : G4 := ⟨CFSG.RankThree.PartTwo.Sec4.Census.diagHom d, diagHom_mem_gramSU d hd⟩
    have hA₀3 : A₀ ^ 3 = 1 := by
      apply Subtype.ext
      change (CFSG.RankThree.PartTwo.Sec4.Census.diagHom d) ^ 3 = 1
      rw [← map_pow]
      have : d ^ 3 = 1 := funext fun i => units_pow_three (d i)
      rw [this, map_one]
    have hne : Φ A₀ ≠ 1 := by
      intro h1
      rw [show Φ A₀ = ((embSU A₀ : gramSU uData M6) : P6) from rfl, QuotientGroup.eq_one_iff] at h1
      obtain ⟨c, -, -, hc⟩ := h1
      have hc' := congrArg (fun m : GL (Fin 6) F4 => (m : Matrix (Fin 6) (Fin 6) F4)) hc
      have e1 := congrFun (congrFun hc' (e (Sum.inl 0))) (e (Sum.inl 0))
      have e2 := congrFun (congrFun hc' (e (Sum.inr 0))) (e (Sum.inr 0))
      change embMat e (CFSG.RankThree.PartTwo.Sec4.Census.diagHom d : Matrix (Fin 4) (Fin 4) F4)
        (e (Sum.inl 0)) (e (Sum.inl 0)) = _ at e1
      change embMat e (CFSG.RankThree.PartTwo.Sec4.Census.diagHom d : Matrix (Fin 4) (Fin 4) F4)
        (e (Sum.inr 0)) (e (Sum.inr 0)) = _ at e2
      rw [embMat_apply] at e1 e2
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        fromBlocks_apply₁₁, fromBlocks_apply₂₂, CFSG.RankThree.PartTwo.Sec4.Census.coe_diagHom,
        Matrix.one_apply_eq] at e1 e2
      have h5 : rootUnit 1 = 1 := by
        apply Units.ext
        rw [Units.val_one]
        simpa [d, e2] using e1
      rw [← rootUnit_zero] at h5
      exact absurd (rootUnit_injective h5) (by decide)
    have hcube : Φ A₀ ^ 3 = 1 := by rw [← map_pow, hA₀3, map_one]
    have hord : orderOf (Φ A₀) = 3 := orderOf_eq_prime hcube hne
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard Φ.range (⟨A₀, rfl⟩ : Φ A₀ ∈ Φ.range)

end CFSG.AGLEmbedding.U62O10Cent
