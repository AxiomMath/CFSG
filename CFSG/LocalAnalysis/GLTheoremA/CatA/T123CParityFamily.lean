module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityCore
public import CFSG.RankThree.PartOne.K159.FamilyConj
import CFSG.RankThree.PartOne.K159.FamilySL4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped Pointwise

variable {J : Type} [Group J]

theorem parityCoreAt_of_family {p : ℕ} (hp : p.Prime) (Pi : Set (Subgroup J))
    (hcard : ¬ p ∣ Nat.card Pi) (hstab : ∀ α : MulAut J, ∀ M ∈ Pi, M.map α.toMonoidHom ∈ Pi)
    (hS : ∀ M ∈ Pi, ∃ S : Subgroup J, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ α : MulAut J, M.map α.toMonoidHom = M → S.map α.toMonoidHom = S) :
    ParityCoreAt p J := by
  intro A hA
  have : Fact p.Prime := ⟨hp⟩
  let sub : SubMulAction A (Subgroup J) :=
    { carrier := Pi
      smul_mem' := fun a M hM => hstab a M hM }
  have hcard' : ¬ p ∣ Nat.card sub := hcard
  obtain ⟨Mfix, hMfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card sub hcard'
  have hMe : ∀ a : A, (Mfix : Subgroup J).map (a : MulAut J).toMonoidHom = Mfix := fun a =>
    congrArg (fun P : sub => (P : Subgroup J)) (MulAction.mem_fixedPoints.1 hMfix a)
  obtain ⟨S, hS1, hS2, hSinv⟩ := hS Mfix Mfix.2
  refine ⟨S, hS1, hS2, fun α hα u hu => ?_⟩
  rw [← hSinv α (hMe ⟨α, hα⟩)]
  exact Subgroup.mem_map_of_mem _ hu

theorem parityCoreAt_of_pCoreOf_family [Finite J] {p : ℕ} (hp : p.Prime)
    (Pi : Set (Subgroup J)) (hcard : ¬ p ∣ Nat.card Pi)
    (hstab : ∀ α : MulAut J, ∀ M ∈ Pi, M.map α.toMonoidHom ∈ Pi)
    (hcore : ∀ M ∈ Pi, pCoreOf 2 M ≠ ⊥) : ParityCoreAt p J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine parityCoreAt_of_family hp Pi hcard hstab fun M hM => ⟨pCoreOf 2 M, hcore M hM,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, fun α hα => ?_⟩
  have := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 α M
  rw [hα] at this
  exact this.symm

theorem parityCoreAt_of_familyFactsGrp [Finite J] {p : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartOne.K159.FamilyFactsGrp p J) : ParityCoreAt p J := by
  obtain ⟨Pi, hcard, hstab, hM⟩ := h
  refine parityCoreAt_of_family hp Pi hcard hstab fun M hMPi => ?_
  obtain ⟨hpM, S, -, hS2, hSinv, hcent⟩ := hM M hMPi
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) p hpM
  obtain ⟨t, htS, hne⟩ := hcent x x.2 (by rw [Subgroup.orderOf_coe, hx])
  refine ⟨S, fun hbot => hne ?_, hS2, hSinv⟩
  rw [hbot, Subgroup.mem_bot] at htS
  rw [htS, mul_one, one_mul]

theorem parityCoreL4_holds : ParityCoreL4 := by
  intro p k K _ _ hp hp2 _ hpk hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := k) (by rw [Fintype.card_eq_nat_card, hK])
  have : Finite (projectiveSL 4 K) := inferInstance
  exact parityCoreAt_of_familyFactsGrp hp
    (CFSG.RankThree.PartOne.K159.FamilyFactsGrp.of_mulEquiv
      CFSG.RankThree.PartOne.K159.slEquivProj
      (CFSG.RankThree.PartOne.K159.familyFactsGrp_specialLinear_four hp hp2
        (by rw [hK]; exact hpk)))

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
