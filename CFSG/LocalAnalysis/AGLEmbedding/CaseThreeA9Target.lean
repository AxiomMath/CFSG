module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
import CFSG.LocalAnalysis.AGLEmbedding.AThreePLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem card_dvd_of_isPGroup_mulAut_of_coprime {L : Type*} [Group L] [Finite L] {p a m : ℕ}
    [Fact p.Prime] (hcard : Nat.card L = p ^ a * m) (hm : p.Coprime (m * Nat.card (Outer L)))
    (S : Subgroup (MulAut L)) (hS : IsPGroup p S) : Nat.card S ∣ p ^ a := by
  have : Finite (MulAut L) := MulEquiv.finite_left
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hAut : Nat.card (MulAut L) = Nat.card (Outer L) * Nat.card (inner L) :=
    (inner L).card_eq_card_quotient_mul_card_subgroup
  have hInn : Nat.card (inner L) ∣ Nat.card L := Subgroup.card_range_dvd _
  have hdvd : Nat.card S ∣ p ^ a * (m * Nat.card (Outer L)) := by
    refine (Subgroup.card_subgroup_dvd_card S).trans ?_
    rw [hAut]
    refine (Nat.mul_dvd_mul_left _ hInn).trans ?_
    rw [hcard]
    exact ⟨1, by ring⟩
  rw [hk] at hdvd ⊢
  exact (Nat.Coprime.pow_left k hm).dvd_of_dvd_mul_right hdvd

theorem le_pRank_of_mulEquiv_alternatingGroup {L : Type*} [Group L] [Finite L] {k n : ℕ}
    (e : L ≃* alternatingGroup (Fin n)) (h : k * 3 ≤ n) :
    k ≤ Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨φ, hφ⟩ := exists_injective_pi_alternatingGroup h
  exact SectionRank.le_pRank_of_injective (by norm_num)
    (fun a b => funext fun i => alternatingGroup_three_comm (a i) (b i))
    (fun a => funext fun i => alternatingGroup_three_pow (a i))
    (by rw [Nat.card_fun, natCard_alternatingGroup_three, Nat.card_eq_fintype_card,
      Fintype.card_fin])
    (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ) le_top

theorem stmtA3pTarget_nine : @StmtA3pTarget 3 4 (3 ^ 4) ⟨Nat.prime_three⟩ := by
  intro L _ _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e9 : L ≃* alternatingGroup (Fin 9) := e
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card L = 3 ^ 4 * 2240 := by
    rw [Nat.card_congr e9.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hOut : Nat.card (Outer L) ∣ 2 := outer_card_dvd_two_of_equiv_outside_six (by norm_num) e9
  have h3Out : ¬ 3 ∣ Nat.card (Outer L) := fun h => absurd (h.trans hOut) (by norm_num)
  refine ⟨⟨MulEquiv.isSimpleGroup e9, ?_, le_pRank_of_mulEquiv_alternatingGroup e9 (by norm_num),
    outer_solvable_of_equiv_outside_six (by norm_num) e9,
    ⟨7, by norm_num, by norm_num, ?_, ?_⟩⟩,
    ⟨card_sylow_eq_pow_of_card_eq hcard (by norm_num),
      card_dvd_of_isPGroup_mulAut_of_coprime hcard ?_⟩, h3Out⟩
  · by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative (alternatingGroup (Fin 9)) :=
      ⟨⟨fun x y => e9.symm.injective (by rw [map_mul, map_mul, hcomm])⟩⟩
    have h := alternatingGroup.isMulCommutative_iff_card_le_three.mp this
    simp at h
  · rw [hcard]
    norm_num
  · intro k hk hkB
    have hk4 : k ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hkB
    interval_cases k <;> norm_num
  · exact Nat.Coprime.mul_right (by norm_num)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Out)

end CFSG.AGLEmbedding
