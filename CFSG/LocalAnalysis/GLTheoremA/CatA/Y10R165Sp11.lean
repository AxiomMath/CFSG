module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp7
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinComm
public import CFSG.GroupTheory.ElemAbelianPlaneAction
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace SpEngine

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Finite (V ≃ₗ[F] V)]

theorem prime_dvd_card_statedSp_two_eq_five {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hncard : Nat.card F = 2)
    (hpP : p ∣ Nat.card (StatedSp 2 F)) : p = 5 := by
  have hPcard : Nat.card (StatedSp 2 F) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hncard]
    norm_num
  have hp720 : p ∣ 720 := by rwa [hPcard] at hpP
  have hdvd : p ∣ 2 ^ 4 * 3 ^ 2 * 5 := by
    rwa [show (2 : ℕ) ^ 4 * 3 ^ 2 * 5 = 720 from by norm_num]
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · obtain ⟨k, hk, hpk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
      have hp2' : p = 2 := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          rw [hpk] at hp
          norm_num at hp
        · have hprime : Nat.Prime (2 ^ k) := hpk ▸ hp
          have hdvd2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
          rcases (Nat.dvd_prime hprime).mp hdvd2 with h1 | h1
          · omega
          · rw [hpk, ← h1]
      exact absurd hp2' hp2
    · obtain ⟨k, hk, hpk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h
      have hp3' : p = 3 := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          rw [hpk] at hp
          norm_num at hp
        · have hprime : Nat.Prime (3 ^ k) := hpk ▸ hp
          have hdvd3 : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
          rcases (Nat.dvd_prime hprime).mp hdvd3 with h1 | h1
          · omega
          · rw [hpk, ← h1]
      exact absurd hp3' hp3
  · rcases (Nat.dvd_prime Nat.prime_five).mp h with h1 | h1
    · subst h1
      norm_num at hp
    · exact h1

theorem exists_commutator_pointwiseStab_sp4_two {B : LinearMap.BilinForm F V}
    (hBalt : B.IsAlt) (hBnd : B.Nondegenerate) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (h4 : 4 ≤ Module.finrank F ↥(B.orthogonal U))
    (h6 : Module.finrank F ↥(B.orthogonal U) < 6)
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : n = 1)
    (hcardF : Nat.card F = 2 ^ n)
    (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    {J : Subgroup ↥(linIsometryGroup B)}
    (hPU : pointwiseStab (linIsometryGroup B) U ≤ J)
    {zH : ↥(linIsometryGroup B)}
    (hPz : pointwiseStab (linIsometryGroup B) U ≤
      Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))
    (hPn : ((pointwiseStab (linIsometryGroup B) U).subgroupOf
      (J ⊓ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))).Normal)
    (hpP : p ∣ Nat.card ↥(pointwiseStab (linIsometryGroup B) U)) :
    ∃ Q : Subgroup ↥(linIsometryGroup B), Q ≤ J ∧
      Q ≤ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer ({zH} :
        Set ↥(linIsometryGroup B)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card ↥Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hncard : Nat.card F = 2 := by rw [hcardF, hn1]; norm_num
  obtain ⟨s, hs, ⟨eSp⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_bilinIsometryGroup_equiv_statedSp
      (f := B.restrict (B.orthogonal U))
      (orthogonal_nondegenerate hBalt hBnd hU) (fun z => hBalt.self_eq_zero z)
  have hs2 : s = 2 := by
    have h := hs
    rcases Nat.lt_or_ge s 2 with h2 | h2
    · interval_cases s <;> omega
    · rcases Nat.lt_or_ge s 3 with h3 | h3
      · omega
      · exfalso; omega
  subst hs2
  let P : Subgroup ↥(linIsometryGroup B) := pointwiseStab (linIsometryGroup B) U
  let eP : P ≃* StatedSp 2 F := (pointwiseStabEquiv hBalt hU).trans eSp
  let QP : Subgroup ↥P := ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆
  have htopP : (⊤ : Subgroup ↥P).map P.subtype = P := by
    have h := Subgroup.subgroupOf_map_subtype (⊤ : Subgroup ↥(linIsometryGroup B)) P
    rw [Subgroup.top_subgroupOf, top_inf_eq] at h
    exact h
  let Q : Subgroup ↥(linIsometryGroup B) := QP.map P.subtype
  have hQeq : Q = ⁅P, P⁆ := by
    show QP.map P.subtype = ⁅P, P⁆
    rw [show QP = ⁅(⊤ : Subgroup ↥P), ⊤⁆ from rfl, Subgroup.map_commutator, htopP]
  have hQJ : Q ≤ J := by
    rw [hQeq]
    exact (CFSG.LocalAnalysis.GLTheoremA.HSubT.commutator_self_le P).trans hPU
  have hQz : Q ≤ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)) := by
    rw [hQeq]
    exact (CFSG.LocalAnalysis.GLTheoremA.HSubT.commutator_self_le P).trans hPz
  have hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({zH} :
      Set ↥(linIsometryGroup B)))).Normal := by
    rw [hQeq]
    exact CFSG.LocalAnalysis.GLTheoremA.HSubT.commutator_subgroupOf_normal
      (le_inf hPU hPz) hPn
  have hmapQP : QP.map eP.toMonoidHom = commutator (StatedSp 2 F) := by
    rw [show QP = ⁅(⊤ : Subgroup ↥P), ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eP.surjective, commutator_def]
  have hQe : QP ≃* alternatingGroup (Fin 6) :=
    ((eP.subgroupMap QP).trans (MulEquiv.subgroupCongr hmapQP)).trans
      (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hncard)
  have hQPQ : QP ≃* Q :=
    Subgroup.equivMapOfInjective QP P.subtype (Subgroup.subtype_injective P)
  have hA6 : CFSG.Open.IsQuasisimple ↥(alternatingGroup (Fin 6)) :=
    CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup (by norm_num)
  have hQq : CFSG.Open.IsQuasisimple ↥Q := hA6.of_mulEquiv (hQPQ.symm.trans hQe)
  have hQcard : Nat.card ↥Q = 360 := by
    rw [Nat.card_congr (hQPQ.symm.trans hQe).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hpne3 : p ≠ 3 := by
    intro h3
    subst h3
    have h2 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord 3 1 = 2 := by
      rw [CFSG.LocalAnalysis.GLTheoremA.rk2Ord, pow_one]
      exact CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_three
    rw [hn1, h2] at hm0
    omega
  have hpStated : p ∣ Nat.card (StatedSp 2 F) := by
    rwa [Nat.card_congr eP.toEquiv] at hpP
  have hp5 : p = 5 :=
    prime_dvd_card_statedSp_two_eq_five hp hp2 hpne3 hncard hpStated
  have hpQ : p ∣ Nat.card ↥Q := by
    rw [hQcard, hp5]
    norm_num
  exact ⟨Q, hQJ, hQz, hQn, hQq, hpQ⟩

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
