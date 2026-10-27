module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.HardMathSupport.Dickson.Bal207.UniLift
import CFSG.HardMathSupport.Dickson.Bal207.UniOrder
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Dickson.Bal207.Uni

theorem fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (t : G) :
    Solomon.Coordinator.fixSubgroup (MulAut.conj t) = Subgroup.centralizer ({t} : Set G) := by
  ext g
  rw [Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_lift_orderOf_three (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {t : ProjOrthDerived Q} (ht : orderOf t = 3) :
    ∃ x : orthDerived Q, piOrth Q x = t ∧ orderOf x = 3 := by
  obtain ⟨x, rfl⟩ := piOrth_surjective (Q := Q) t
  exact ⟨x, rfl, (orderOf_injective _ (piOrth_injective hQ) x).symm.trans ht⟩

theorem su38_image_eq_componentImage {Y : Type} [Group Y] [Finite Y]
    (hF : Nat.card K = 2 ∨ Nat.card K = 8) (hQ : (polarBilin Q).Nondegenerate)
    {L : Subgroup Y} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* ProjOrthDerived Q) {a : Y}
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (x : orthDerived Q) (hx3 : orderOf x = 3)
    (hax : uniAut e ⟨a, ha⟩ = MulAut.conj (piOrth Q x))
    (hlay : PerfectInLayer (MulAut.conj (piOrth Q x))) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set Y)) J) (hsu : IsSU38Comp J) :
    CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({a} : Set Y)) ∧ Nat.card K = 8 ∧
      (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
      primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) = 3 ∧
      (J.comap L.subtype).map (uniMap e) = componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1) := by
  obtain ⟨hcomp, hJc, -⟩ := uni_component e Nat.prime_three hL hZ ha (hax ▸ hlay) hJ
  rw [hax, fixSubgroup_conj_eq_centralizer] at hJc
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  obtain ⟨eq⟩ := LieComp.nonempty_centralQuotient_mulEquiv hcomp.2.2.1 (uniRestr e hJL)
    (uniRestr_surjective e hJL) (ker_uniRestr_le_center e hJL)
  have hcard : Nat.card (↥((J.comap L.subtype).map (uniMap e)) ⧸
      Subgroup.center ↥((J.comap L.subtype).map (uniMap e))) = 5515776 := by
    rw [← Nat.card_congr eq.toEquiv, uni_card_su38 hsu]
  obtain ⟨h8, hΦ, hm, hEq⟩ := eq_componentImage_of_card hF hQ x hx3 hJc hcard
  exact ⟨hcomp, h8, hΦ, hm, hEq⟩

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
