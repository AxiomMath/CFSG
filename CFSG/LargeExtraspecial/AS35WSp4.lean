module

public import CFSG.LargeExtraspecial.AS35WCheck
public import CFSG.LargeExtraspecial.AS35WList
public import CFSG.LargeExtraspecial.AS35WQP45Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Certificate21296
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public import CFSG.Fischer.NoF25.Local
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8CBFSect
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

namespace AS35W

theorem orderOf_mem_of_pow {G : Type} [Group G] {p : G}
    (h : p = 1 ∨ p ^ 2 = 1 ∨ p ^ 3 = 1) : orderOf p ∈ ({1, 2, 3} : Set ℕ) := by
  rcases h with h | h | h
  · simp [h]
  · have := orderOf_dvd_of_pow_eq_one h
    have : orderOf p = 1 ∨ orderOf p = 2 := (Nat.dvd_prime Nat.prime_two).1 this
    rcases this with h1 | h1 <;> simp [h1]
  · have := orderOf_dvd_of_pow_eq_one h
    have : orderOf p = 1 ∨ orderOf p = 3 := (Nat.dvd_prime Nat.prime_three).1 this
    rcases this with h1 | h1 <;> simp [h1]

theorem toA_mem_enumA {g : Equiv.Perm (Fin 45)}
    (hg : g ∈ QP45.originalSubgroup) : toA g ∈ enumA QP45 := by
  rw [enumA_eq]
  exact List.mem_map.2 ⟨g, (mem_elemsT QP45 QP45_ok g).2 hg, rfl⟩

theorem eq_toA_of_mem_enumA {a : Array Nat}
    (ha : a ∈ enumA QP45) : ∃ g ∈ QP45.originalSubgroup, a = toA g := by
  rw [enumA_eq] at ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
  exact ⟨g, (mem_elemsT QP45 QP45_ok g).1 hg, rfl⟩

theorem w2Good_QP45 :
    W2Good QP45.originalSubgroup := by
  intro z hz
  have hQ := QP45_ok
  obtain ⟨hInv, hProd⟩ := Certificates.certificate21296
  unfold qp45InvCheck qp45InvCheckL at hInv
  unfold qp45ProdCheck qp45ProdCheckL at hProd
  set s : Equiv.Perm (Fin 45) := (z : Equiv.Perm (Fin 45))
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz.orderOf_eq, sq] at this
    exact congrArg Subtype.val this
  have hs1 : s ≠ 1 := fun h => by
    have : z = 1 := Subtype.ext h
    have h2 := hz.orderOf_eq
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hrs := rep_toA s
  have hinv : invA45 (toA s) = true := by
    unfold invA45
    rw [Bool.and_eq_true, eqA_iff (rep_compA hrs hrs) rep_idA, Bool.not_eq_true',
      Bool.eq_false_iff, Ne, eqA_iff hrs rep_idA]
    exact ⟨hs2, hs1⟩
  have h1 := List.all_eq_true.1 hInv _ (toA_mem_enumA z.2)
  rw [hinv, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h1
  rcases h1 with ⟨gA, hgA, hgs⟩ | h64
  · obtain ⟨g, hgQ, rfl⟩ := eq_toA_of_mem_enumA hgA
    have hgx : g * x45 = s * g := (eqA_iff (rep_compA (rep_toA g) (rep_toA x45))
      (rep_compA hrs (rep_toA g))).1 hgs
    have hgs' : g * x45 * g⁻¹ = s := by rw [hgx]; group
    intro g₁ g₂
    set a : Equiv.Perm (Fin 45) := (g₁ : Equiv.Perm (Fin 45)) * g
    set b : Equiv.Perm (Fin 45) := (g₂ : Equiv.Perm (Fin 45)) * g
    have haQ : a ∈ QP45.originalSubgroup := QP45.originalSubgroup.mul_mem g₁.2 hgQ
    have hbQ : b ∈ QP45.originalSubgroup := QP45.originalSubgroup.mul_mem g₂.2 hgQ
    set h := a⁻¹ * b
    have hh : h ∈ QP45.originalSubgroup :=
      QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem haQ) hbQ
    have h2 := List.all_eq_true.1 hProd _ (toA_mem_enumA hh)
    rw [Bool.and_eq_true] at h2
    obtain ⟨hi, ho⟩ := h2
    have hri := rep_inv_of_isInvA (rep_toA h) hi
    have hc := rep_compA (rep_toA x45) (rep_compA (rep_compA (rep_toA h) (rep_toA x45)) hri)
    set p : Equiv.Perm (Fin 45) := x45 * (h * x45 * h⁻¹)
    have hp : p = 1 ∨ p ^ 2 = 1 ∨ p ^ 3 = 1 := by
      unfold ord123A45 at ho
      rw [Bool.or_eq_true, Bool.or_eq_true] at ho
      rcases ho with (ho | ho) | ho
      · exact Or.inl ((eqA_iff hc rep_idA).1 ho)
      · exact Or.inr (Or.inl (by rw [sq]; exact (eqA_iff (rep_compA hc hc) rep_idA).1 ho))
      · refine Or.inr (Or.inr ?_)
        have := (eqA_iff (rep_compA hc (rep_compA hc hc)) rep_idA).1 ho
        rw [pow_succ, sq, mul_assoc]
        exact this
    rw [← Subgroup.orderOf_coe]
    have e : ((g₁ * z * g₁⁻¹ * (g₂ * z * g₂⁻¹) : QP45.originalSubgroup) : Equiv.Perm (Fin 45)) =
        a * p * a⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (z : Equiv.Perm (Fin 45)) = g * x45 * g⁻¹ from hgs'.symm]
      simp only [a, b, p, h]
      group
    rw [e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact orderOf_mem_of_pow hp
  · exfalso
    have hcard : Nat.card (centralizer ({z} : Set QP45.originalSubgroup)) =
        ((enumA QP45).filter fun g => eqA 45 (compA 45 g (toA s)) (compA 45 (toA s) g)).length := by
      have hpred : ∀ g ∈ elemsT QP45, decide (g * s = s * g) =
          ((fun a => eqA 45 (compA 45 a (toA s)) (compA 45 (toA s) a)) ∘ toA) g := by
        intro g _
        simp only [Function.comp_apply]
        rw [eqA_eq_decide (rep_compA (rep_toA g) hrs) (rep_compA hrs (rep_toA g))]
      rw [card_centralizer_subtype z.2, card_inf_centralizer QP45 hQ, enumA_eq, List.filter_map,
        List.length_map, List.filter_congr hpred]
    have h6 := hz.pow_dvd (k := 6) (by rw [card_group QP45 hQ, QP45_valid.2]; norm_num)
    rw [hcard] at h6
    exact h64 h6

end AS35W

end CFSG.LargeExtraspecial
