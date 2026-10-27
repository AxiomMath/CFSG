module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SULevi
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLeviConnected
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUBlocks

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary
open CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
open CFSG.ClassicalGroups.UnitaryFlag

private theorem cartanC_ne_zero_iff {m : ℕ} {i j : Fin m}
    (h : CFSG.LieType.Universal.Symplectic.cartanC m i j ≠ 0) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  by_cases hij : i = j
  · exact Or.inl hij
  · by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · exact Or.inr hadj
    · exfalso
      rw [CFSG.LieType.Universal.Symplectic.cartanC, Matrix.of_apply] at h
      simp only [hij, hadj, if_false] at h
      exact h rfl

private theorem cartan_ne_zero_iff {n : ℕ} {i j : Fin (n / 2)}
    (h : CFSG.LieType.Universal.Unitary.cartan n i j ≠ 0) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rw [CFSG.LieType.Universal.Unitary.cartan] at h
  split_ifs at h with he
  · exact cartanC_ne_zero_iff h
  · rw [Matrix.transpose_apply] at h
    rcases cartanC_ne_zero_iff h with h' | h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl h')

private theorem nodeAdj_val_su {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {C : Set (Fin (n / 2))} {i j : Fin (n / 2)}
    (h : NodeAdj (CFSG.LieType.Universal.Unitary.rootDatum (p := 2) hF n) C i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have h1 : (TauCeti.diagramGraph (CFSG.LieType.Universal.Unitary.cartan n)).Adj i j :=
    h.2.2
  rw [TauCeti.diagramGraph_adj] at h1
  rcases cartan_ne_zero_iff h1.2.1 with heq | hadj
  · exact absurd heq h1.1
  · exact hadj

private theorem nodesOf_Icc {m : ℕ} {a b : Fin m} :
    nodesOf (Finset.Icc a.castSucc b.succ) = Set.Icc a b := by
  ext k
  simp only [nodesOf, Set.mem_setOf_eq, Finset.mem_Icc, Set.mem_Icc, Fin.le_def,
    Fin.val_castSucc, Fin.val_succ]
  omega

private theorem eq_nodesOf_blkSet_of_isNodeConnected {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {C : Set (Fin (n / 2))}
    (hC : IsNodeConnected (CFSG.LieType.Universal.Unitary.rootDatum (p := 2) hF n) C) :
    ∃ p : Fin (n / 2 + 1), C = nodesOf (blkSet C p) := by
  obtain ⟨a, b, ha, _, hCab⟩ : ∃ a b : Fin (n / 2), a ∈ C ∧ b ∈ C ∧ C = Set.Icc a b :=
    hC.exists_eq_Icc (fun _ _ h => nodeAdj_val_su hF h)
  refine ⟨a.castSucc, ?_⟩
  rw [blkSet_eq_Icc (i := a) hCab ha, nodesOf_Icc, hCab]

private theorem odd_two_pow_add_one {f : ℕ} (hf : f ≠ 0) : Odd (2 ^ f + 1) :=
  (Even.pow_of_ne_zero (show Even (2 : ℕ) by norm_num) (n := f) hf).add_one

private theorem odd_card_center_su {F : Type} [Field F] [Finite F] [CharP F 2] {f N : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hN : 4 ≤ N) :
    Odd (Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) N))) := by
  have hN3 : 3 ≤ N := by omega
  have hnq : (N, 2 ^ f) ≠ (3, 2) := by
    rintro h
    have := congrArg Prod.fst h
    omega
  have hcenter := (isQuasisimple_statedSU_of_card (p := 2) hF hN3 hnq).2
  have hcard : Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) N)) =
      Nat.card (Subgroup.center (StatedSU N (2 ^ f) F)) := by
    have hmap := map_center_mulEquiv (equivStatedSU (p := 2) (f := f) hF N)
    rw [← hmap,
      Subgroup.card_map_of_injective (equivStatedSU (p := 2) (f := f) hF N).injective]
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    { prime := Nat.prime_two, one_le := one_le_f hF
      card := by rw [hF, ← pow_mul, Nat.mul_comm] }
  rw [hcard, hcenter]
  have huc : (StatedScalars (Fin N) F).subgroupOf (StatedSU N (2 ^ f) F) =
      unitaryScalars h N :=
    (unitaryScalars_eq h (by omega : 1 ≤ N)).symm
  rw [huc, card_unitaryScalars h (by omega : 1 ≤ N)]
  exact (odd_two_pow_add_one (f := f) (by have := one_le_f hF; omega)).of_dvd_nat
    (Nat.gcd_dvd_right N (2 ^ f + 1))

private theorem gomiLeviFactor_gbU_su {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {C : Set (Fin (n / 2))}
    {B : Finset (Fin (n / 2 + 1))} (hCB : C = nodesOf B) (h2C : 2 ≤ C.ncard)
    (hsl : ∀ k : ℕ, (3 ≤ k ∨ (k = 2 ∧ 4 ≤ Nat.card F)) →
      CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) F) ∧
        IsClassicalTwoOrG2 (Matrix.SpecialLinearGroup (Fin k) F ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin k) F)))
    (hsu : ∀ N : ℕ, 4 ≤ N →
      CFSG.IsQuasisimple (SU (unitaryInvolution F 2 f) N) ∧
        IsClassicalTwoOrG2 (SU (unitaryInvolution F 2 f) N ⧸
          Subgroup.center (SU (unitaryInvolution F 2 f) N))) :
    GomiLeviFactor ↥(GbU hF B) := by
  classical
  have hsub : C ⊆ (coordsOf B : Set (Fin (n / 2))) := by
    intro k hk
    rw [hCB] at hk
    exact mem_coordsOf.mpr hk.1
  have hk2 : 2 ≤ (coordsOf B).card := by
    have h1 : C.ncard ≤ ((coordsOf B : Finset (Fin (n / 2))) : Set (Fin (n / 2))).ncard :=
      Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset] at h1
    omega
  have hf1 : 1 ≤ f := one_le_f hF
  have h4F : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1) 2
  by_cases hl : Fin.last (n / 2) ∈ B
  · rw [show GbU hF B = GEu hF (coordsOf B) by simp [GbU, hl]]
    refine GomiLeviFactor.of_mulEquiv (GEu_equiv hF (coordsOf B)).symm ?_
    left
    have hN4 : 4 ≤ (ePos (coordsOf B)).card := by
      rw [ePos_card]
      split_ifs <;> omega
    exact IsGomiChevTwo.of_isQuasisimple (hsu _ hN4).1 (odd_card_center_su hF hN4)
      (isChevTwo_of_classicalTwoOrG2 (hsu _ hN4).2)
  · rw [show GbU hF B = GAu hF (coordsOf B) by simp [GbU, hl]]
    refine GomiLeviFactor.of_mulEquiv (GAu_equiv hF (coordsOf B)).symm ?_
    left
    have hk : 3 ≤ (coordsOf B).card ∨ ((coordsOf B).card = 2 ∧ 4 ≤ Nat.card F) := by
      rcases (by omega : (coordsOf B).card = 2 ∨ 3 ≤ (coordsOf B).card) with h2 | h3
      · exact Or.inr ⟨h2, h4F⟩
      · exact Or.inl h3
    exact IsGomiChevTwo.of_isQuasisimple (hsl _ hk).1
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup))
      (isChevTwo_of_classicalTwoOrG2 (hsl _ hk).2)

theorem gomiLeviFactorsSU_holds : GomiLeviFactorsSU := by
  intro F _ _ _ f hF n C hC h2C _
  let C' : Set (Fin (n / 2)) := C
  change GomiLeviFactor ↥(leviM (rootDatum (p := 2) hF n) C')
  have hC' : IsNodeConnected (rootDatum (p := 2) hF n) C' := hC
  have h2C' : 2 ≤ C'.ncard := h2C
  have hn : 2 ≤ n := by
    have hle : C'.ncard ≤ n / 2 := by simpa using Set.ncard_le_card C'
    omega
  obtain ⟨p, hp⟩ := eq_nodesOf_blkSet_of_isNodeConnected hF hC'
  have hne : (nodesOf (blkSet C' p)).Nonempty := by rw [← hp]; exact hC'.1
  have hGb1 : GbU hF (blkSet C' p) =
      leviM (rootDatum (p := 2) hF n) (nodesOf (blkSet C' p)) :=
    GbU_eq hF hn rfl hne
  have hGb : GbU hF (blkSet C' p) = leviM (rootDatum (p := 2) hF n) C' := by
    rw [hGb1]
    exact congrArg (leviM (rootDatum (p := 2) hF n)) hp.symm
  exact GomiLeviFactor.of_mulEquiv (MulEquiv.subgroupCongr hGb)
    (gomiLeviFactor_gbU_su hF hp h2C'
      (fun k hk => isChevComponent_sl hk)
      (fun N hN => isChevComponent_su hF (by omega)
        (by rintro h; exact absurd (congrArg Prod.fst h) (by omega))))

end CFSG.GroupTheory
