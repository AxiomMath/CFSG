module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverSp4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (ParClosed suppGroup coords mem_coords inl_mem_coords parClosed_coords longBlock
    longBlock_injective longInv mat_longInv range_longBlock spEmbed spEmbed_injective range_spEmbed)
open CFSG.ClassicalInvolution.Asc77.C5O.M (phiSL negOne mat_negOne)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

theorem a2l_typU_statedSp_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    TypU (StatedSp 2 F) := by
  have hq : CFSG.IsQuasisimple (StatedSp 2 F) :=
    LieType.Universal.Symplectic.isQuasisimple 2 F (by omega) (Or.inr (Or.inl ⟨hF, le_rfl⟩))
  have h2 : IsPGroup 2 ↥(center (StatedSp 2 F)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nat.card (center (StatedSp 2 F)) = 2 := by
      rw [LieType.Universal.Symplectic.center_eq]
      exact a2l_card_scalars_sp_four (by rw [hF]; decide)
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by simp⟩
  have hm : LieModel (StatedSp 2 F ⧸ center (StatedSp 2 F)) .PSp 2 3 1 :=
    (LieModel.classical_iff (by decide)).2
      (LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 F hadm
        (by rw [hF]; norm_num))
  have hO : pPrimeCore 2 (StatedSp 2 F) = ⊥ := HypA2.pPrimeCore_eq_bot_of_isQuasisimple hq h2
  have hZs : Open.fusionZStar (StatedSp 2 F) = center (StatedSp 2 F) :=
    HypA2.fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  exact Or.inr (Or.inr (Or.inl
    (LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZs).symm hm)))

theorem a2l_rowPSp_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 2 ≤ n) (hf : 2 ≤ f)
    (hm : LieModel X .PSp n 3 f) : a2lDatum X := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hFc : Fintype.card F = 3 ^ f := by rw [← Nat.card_eq_fintype_card, hcard]
  have hodd : Odd (3 ^ f) := Odd.pow (by decide)
  have h9 : 9 ≤ 3 ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (a2l_ringChar_ne_two (by rw [hFc]; exact hodd))
  obtain ⟨s, -, hs⟩ : ∃ s ⊆ (Finset.univ : Finset F), s.card = 4 :=
    Finset.exists_subset_card_eq (by rw [Finset.card_univ, hFc]; omega)
  have hq : CFSG.IsQuasisimple SL(2, F) := CFSG.RankThree.Classical.isQuasisimple_SL2 ⟨s, hs⟩
  let k₀ : Fin n := ⟨0, by omega⟩
  let eJ : ↥(longBlock F n k₀).range ≃* SL(2, F) :=
    (MonoidHom.ofInjective (longBlock_injective k₀)).symm
  have hN : HarrisLit.IsSLTwoOver (3 ^ f) ↥(longBlock F n k₀).range :=
    ⟨F, inferInstance, inferInstance, hFc, ⟨eJ⟩⟩
  have ha : (Sum.inl ⟨1, by omega⟩ : Fin n ⊕ Fin n) ∉ coords k₀ := by
    intro h
    rcases mem_coords.1 h with h | h
    · exact absurd (congrArg Fin.val (Sum.inl.inj h)) (by simp [k₀])
    · exact absurd h (by simp)
  have hd := a2lDatum_psp_block h2 (parClosed_coords k₀) ha (inl_mem_coords k₀)
    (mat_longInv (K := F) k₀) hodd (by omega) (range_longBlock k₀) le_rfl ⟨-1, rfl⟩
    (CFSG.IsQuasisimple.of_mulEquiv eJ hq) hN (a2l_typU_of_isSLTwoOver hodd h9 hN)
  exact a2lDatum_of_mulEquiv e.symm hd

theorem a2l_rowPSp_one {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (hm : LieModel X .PSp n 3 1) : a2lDatum X := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  classical
  haveI := Fintype.ofFinite F
  have hF3 : Nat.card F = 3 := by rw [hcard]; norm_num
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hF3]
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (a2l_ringChar_ne_two (by rw [hF]; decide))
  haveI : Fact (¬ IsSquare (-1 : F)) :=
    ⟨fun h => FiniteField.isSquare_neg_one_iff.1 h (by rw [hF])⟩
  haveI := a2l_finite_quadAlg (-1 : F)
  haveI := Fintype.ofFinite (QuadraticAlgebra F (-1) 0)
  have hE : Fintype.card (QuadraticAlgebra F (-1) 0) = 9 := by
    rw [← Nat.card_eq_fintype_card, a2l_card_quadAlg, hF3]
  let σ : Fin 2 → Fin n := Fin.castLE (by omega)
  have hσ : Function.Injective σ := Fin.castLE_injective _
  have hT : ParClosed (Set.range (Sum.map σ σ)) := by
    rintro a ⟨x, rfl⟩
    refine ⟨Sum.swap x, ?_⟩
    rcases x with x | x <;> rfl
  have ha : (Sum.inl ⟨2, by omega⟩ : Fin n ⊕ Fin n) ∉ Set.range (Sum.map σ σ) := by
    rintro ⟨x, hx⟩
    rcases x with x | x
    · have h := congrArg Fin.val (Sum.inl.inj hx)
      have hx2 := x.2
      simp [σ] at h
      omega
    · exact absurd hx (by simp)
  have hs₀ : (Sum.inl (σ 0) : Fin n ⊕ Fin n) ∈ Set.range (Sum.map σ σ) := ⟨Sum.inl 0, rfl⟩
  have ht := a2l_mat_spEmbed_neg hσ (mat_negOne (F := F))
  have hq : CFSG.IsQuasisimple (StatedSp 2 F) :=
    LieType.Universal.Symplectic.isQuasisimple 2 F (by omega) (Or.inr (Or.inl ⟨hF3, le_rfl⟩))
  let eJ : ↥(spEmbed σ hσ).range ≃* StatedSp 2 F :=
    (MonoidHom.ofInjective (spEmbed_injective hσ)).symm
  let φ : SL(2, QuadraticAlgebra F (-1) 0) →* StatedSp n F := (spEmbed σ hσ).comp (phiSL (-1 : F))
  have hφ : Function.Injective φ := (spEmbed_injective hσ).comp (a2l_phiSL_injective _)
  have hN : HarrisLit.IsSLTwoOver 9 ↥φ.range :=
    ⟨QuadraticAlgebra F (-1) 0, inferInstance, inferInstance, hE,
      ⟨(MonoidHom.ofInjective hφ).symm⟩⟩
  have hd := a2lDatum_psp_block h2 hT ha hs₀ ht (by decide) (by norm_num)
    (range_spEmbed hσ) (N := φ.range)
    (fun x hx => by obtain ⟨y, rfl⟩ := hx; exact ⟨phiSL (-1 : F) y, rfl⟩)
    ⟨a2lNegOne (QuadraticAlgebra F (-1) 0), by
      change spEmbed σ hσ (phiSL (-1 : F) (a2lNegOne (QuadraticAlgebra F (-1) 0))) = _
      rw [a2l_phiSL_negOne]⟩
    (CFSG.IsQuasisimple.of_mulEquiv eJ hq) hN
    (a2l_typU_of_mulEquiv eJ.symm (a2l_typU_statedSp_four hF3))
  exact a2lDatum_of_mulEquiv e.symm hd

theorem a2l_rowPSp : a2lRowPSp := by
  intro X _ _ n f hn hf hm
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · have hf1 : 1 ≤ f := hm.admissible.2.1
    obtain rfl : f = 1 := by omega
    exact a2l_rowPSp_one (by omega) hm
  · exact a2l_rowPSp_two hn hge hm

end CFSG.OddStandard.SmallF3.HypA2Leaves
