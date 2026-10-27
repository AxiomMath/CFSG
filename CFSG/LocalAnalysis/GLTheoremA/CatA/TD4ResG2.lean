module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.GLTheoremA.Y10F

set_option linter.unusedSectionVars false


theorem glaPLayer_centralizer_ne_bot_g2 {k : Type} [Field k] [Finite k]
    (hk3 : ringChar k ≠ 3) (hk4 : 4 ≤ Nat.card k) {z : adjointGroup .G2 k}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    GLAPLayer 3 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 k))) ≠ ⊥ := by
  classical
  have hq3 : ¬ 3 ∣ Nat.card k := by
    intro h3
    haveI : Fintype k := Fintype.ofFinite k
    haveI := ringChar.charP k
    obtain ⟨m, hp, hcard⟩ := FiniteField.card k (ringChar k)
    rw [Nat.card_eq_fintype_card, hcard] at h3
    exact hk3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds k hk3 hk4 z hz3 hz1
  set w := g * z * g⁻¹ with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, conj_pow, hz3, mul_one, mul_inv_cancel]
  have hw1 : w ≠ 1 := by
    rw [hw]
    intro h
    exact hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
  have hmain : GLAPLayer 3 (Subgroup.centralizer ({w} : Set (adjointGroup .G2 k))) ≠ ⊥ := by
    rcases hg with hS | hM
    · obtain ⟨N, hNC, hcomm, hNq, x, hxN, -, hx1, hx3⟩ :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeACent_holds k hk3 hk4 w hS hw3 hw1
      have hNn : (N.subgroupOf
          (Subgroup.centralizer ({w} : Set (adjointGroup .G2 k)))).Normal :=
        (Subgroup.normal_subgroupOf_iff hNC).2 fun n c hn hc => by
          have h1 := hcomm c hc n (hNC hn)
          have h2 : c * n * c⁻¹ = (c * n * c⁻¹ * n⁻¹) * n := by group
          rw [h2]
          exact N.mul_mem h1 hn
      have h3N : 3 ∣ Nat.card N := by
        have hxN3 : (⟨x, hxN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        have hxN1 : (⟨x, hxN⟩ : ↥N) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
        have ho : orderOf (⟨x, hxN⟩ : ↥N) = 3 := orderOf_eq_prime hxN3 hxN1
        exact ho ▸ orderOf_dvd_natCard _
      have hNopen : CFSG.Open.IsQuasisimple ↥N :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open N).1
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native N).2 hNq)
      exact glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three hNC hNn hNopen
        (CFSG.dvd_card_quotient_center_of_quasisimple hNq Nat.prime_three h3N)
    · obtain ⟨hcomm, -⟩ :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ThreeBCent_holds k hk3 hk4 w hM hw3 hw1
      have hSC : CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k ≤
          Subgroup.centralizer ({w} : Set (adjointGroup .G2 k)) := by
        intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hM
      have hNn : ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k).subgroupOf
          (Subgroup.centralizer ({w} : Set (adjointGroup .G2 k)))).Normal :=
        (Subgroup.normal_subgroupOf_iff hSC).2 fun n c hn hc => by
          have h1 := hcomm c hc n (hSC hn)
          have h2 : c * n * c⁻¹ = (c * n * c⁻¹ * n⁻¹) * n := by group
          rw [h2]
          exact (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k).mul_mem h1 hn
      have h3S : 3 ∣ Nat.card (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k) := by
        have h3q : 3 ∣ Nat.card k ^ 2 - 1 := by
          refine Nat.dvd_of_mod_eq_zero ?_
          apply Nat.sub_mod_eq_zero_of_mod_eq
          have hmod : Nat.card k % 3 = 1 ∨ Nat.card k % 3 = 2 := by
            have hlt := Nat.mod_lt (Nat.card k) (by norm_num : 0 < 3)
            have hne : Nat.card k % 3 ≠ 0 := fun h => hq3 (Nat.dvd_of_mod_eq_zero h)
            omega
          rcases hmod with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
        obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2
          (K := k)
        rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
        exact dvd_mul_of_dvd_right h3q _
      have hqS : CFSG.IsQuasisimple (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k) :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_g2ShortSL2 hk4
      have hSopen : CFSG.Open.IsQuasisimple
          ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 k) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hqS)
      exact glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three hSC hNn hSopen
        (CFSG.dvd_card_quotient_center_of_quasisimple hqS Nat.prime_three h3S)
  intro hz
  have h := glaPLayer_map_eq_of_injective Nat.prime_three (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (Subgroup.centralizer ({z} : Set (adjointGroup .G2 k)))
  rw [CFSG.Walter.map_centralizer_singleton_mulEquiv (MulAut.conj g) z, MulAut.conj_apply,
    ← hw] at h
  rw [hz, Subgroup.map_bot] at h
  exact hmain h.symm

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4

end
