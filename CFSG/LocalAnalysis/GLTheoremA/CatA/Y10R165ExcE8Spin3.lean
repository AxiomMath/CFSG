module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.RankThree.Classical2
open scoped MatrixGroups


theorem e8D4Perp_le_centralizer_e8D4Levi (K : Type) [Field K] :
    e8D4Perp K ≤ Subgroup.centralizer (e8D4Levi K : Set (adjointGroup .E8 K)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact e8D4Levi_commute_perp x hx y hy

theorem isQuasisimple_e8D4Perp (K : Type) [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥(e8D4Perp K) := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D4_E8 K
  have hsurj : Function.Surjective Ψ.rangeRestrict := Ψ.rangeRestrict_surjective
  have hker' : Ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadPlus 4 K)) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hquot : CFSG.IsQuasisimple
      (spinGroup (quadPlus 4 K) ⧸ Ψ.rangeRestrict.ker) :=
    CFSG.Quasithin.H13.Ch4.J4KX.isQuasisimple_quot_of_le_center
      (isQuasisimple_spinGroup_quadPlus (by norm_num)) _ hker'
  have hlevi : CFSG.IsQuasisimple ↥(e8D4Levi K) := by
    have h := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective Ψ.rangeRestrict hsurj) hquot
    rwa [hrange] at h
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective (e8D4Levi K)
      (MulAut.conj (weylWordElt .E8 K e8D4Word)).toMonoidHom (MulEquiv.injective _)) hlevi

theorem center_spinGroup_quadPlus_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) : Subgroup.center (spinGroup (quadPlus n K)) = ⊥ := by
  have hle := center_le_ker_spinAction_quadPlus (K := K) hn
  have hbot : (spinAction (quadPlus n K)).ker = ⊥ := by
    haveI := isCentral_cliffordAlgebra_quadPlus K n
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero K 2)
  rw [hbot] at hle
  exact le_antisymm hle bot_le

theorem card_e8D4Perp_eq_card_statedProj (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card ↥(e8D4Perp K) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadPlus 4 K))) := by
  classical
  have hcen : Subgroup.center (spinGroup (quadPlus 4 K)) = ⊥ :=
    center_spinGroup_quadPlus_eq_bot (by norm_num)
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D4_E8 K
  have hsurj : Function.Surjective Ψ.rangeRestrict := Ψ.rangeRestrict_surjective
  have hkerbot : Ψ.rangeRestrict.ker = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [MonoidHom.ker_rangeRestrict]
    exact hker.trans (le_of_eq hcen)
  have hquot1 : Nat.card (spinGroup (quadPlus 4 K) ⧸ Ψ.rangeRestrict.ker) =
      Nat.card ↥(spinGroup (quadPlus 4 K)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.rangeRestrict.ker
      (α := spinGroup (quadPlus 4 K))
    rw [hkerbot, Subgroup.card_bot, mul_one] at h1
    rw [hkerbot]
    exact h1.symm
  have hlevi : Nat.card ↥(e8D4Levi K) = Nat.card ↥(spinGroup (quadPlus 4 K)) := by
    have hstep : Nat.card ↥(Ψ.range) =
        Nat.card (spinGroup (quadPlus 4 K) ⧸ Ψ.rangeRestrict.ker) :=
      (Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective Ψ.rangeRestrict hsurj).toEquiv).symm
    rw [← hrange, ← hquot1]
    exact hstep
  have hspin : Nat.card ↥(spinGroup (quadPlus 4 K)) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadPlus 4 K))) := by
    obtain ⟨hsurjπ, -, hkerπ⟩ := spinToStatedProj_quadPlus (n := 4) (K := K) (by norm_num)
    have h1 : Nat.card (spinGroup (quadPlus 4 K) ⧸
        (spinToStatedProj (quadPlus 4 K) (range_spinMatrix_quadPlus (by norm_num))).ker) =
        Nat.card ↥(spinGroup (quadPlus 4 K)) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (spinToStatedProj (quadPlus 4 K) (range_spinMatrix_quadPlus (by norm_num))).ker
        (α := spinGroup (quadPlus 4 K))
      rw [hkerπ, hcen, Subgroup.card_bot, mul_one] at h
      rw [hkerπ, hcen]
      exact h.symm
    rw [← h1]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (spinToStatedProj_quadPlus (n := 4) (K := K) (by norm_num)).1).toEquiv
  rw [show e8D4Perp K = (e8D4Levi K).map
      (MulAut.conj (weylWordElt .E8 K e8D4Word)).toMonoidHom from rfl,
    Subgroup.card_map_of_injective (MulEquiv.injective _), hlevi, hspin]

theorem dvd_card_e8D4Perp (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K ^ 2 + 1) : p ∣ Nat.card ↥(e8D4Perp K) := by
  have hdvd4 : p ∣ Nat.card K ^ 4 - 1 := by
    have h1 : p ∣ (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := Dvd.dvd.mul_right hpq _
    have h2 : (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) = Nat.card K ^ 4 - 1 := by
      have h3 : Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 := by ring
      rw [h3]
      exact (Nat.sq_sub_sq (Nat.card K ^ 2) 1).symm
    rwa [h2] at h1
  have hcard : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus 4 K))) = ordPOmegaPlus4 (Nat.card K) := by
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
      (K := K) (n := 4) (by norm_num)
    rw [← cast_ordPOmegaPlus4 Nat.card_pos] at h
    exact_mod_cast h
  rw [card_e8D4Perp_eq_card_statedProj K, hcard, ordPOmegaPlus4_eq]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd4 _) _

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
