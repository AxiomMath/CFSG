module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Main
import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RD
import CFSG.ClassicalInvolution.Q3.TL4G23Inner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section U3


theorem oddCore_centralizer_eq_bot_of_u33 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 3 3 1) {z : X} (hz : z * z = 1) (hz1 : z ≠ 1) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ :=
  oddCore_eq_bot_of_oddCoreIn ((TL4.E3S3O.simple_oddFree_of_lieModel
    (Or.inr (Or.inr (Or.inl rfl))) hX).2 z (orderOf_eq_prime (by rw [pow_two]; exact hz) hz1))

end U3

section M12


theorem oddCore_centralizer_eq_bot_of_m12 {X : Type} [Group X]
    (hX : CFSG.Blueprint.NativeSporadic.IsSporadic X .M12) {z : X} (hz : z * z = 1)
    (hz1 : z ≠ 1) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨e⟩ := hX
  let e' : X ≃* CFSG.Blueprint.NativeSporadic.M12 := e
  refine oddCore_centralizer_eq_bot_of_mulEquiv e' ?_
  have h2 : orderOf (e' z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  exact CFSG.Sporadic.Schreier.m12_inner_oddCore (e' z) h2

end M12

section G23


theorem oddCore_centralizer_eq_bot_of_g23 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .G2 0 3 1) {z : X} (hz : z * z = 1) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have hK3 : Nat.card K = 3 := by simpa using hcard
  let e' : X ≃* ↥(adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)
  have hz2 : e' z * e' z = 1 := by rw [← map_mul, hz, map_one]
  exact oddCore_eq_bot_of_oddCoreIn (oddCoreIn_centralizer_eq_bot_of_mulEquiv e' z
    (TL4.oddCoreIn_centralizer_adjoint_three (Or.inl rfl) hK3 hz2))

end G23

section All


theorem rowCentralizerFacts_proved : RowCentralizerFacts :=
  ⟨fun _ _ _ hX _ hz hz1 => oddCore_centralizer_eq_bot_of_u33 hX hz hz1,
    fun _ _ _ hX _ hz hz1 => oddCore_centralizer_eq_bot_of_m12 hX hz hz1,
    fun _ _ _ hX _ hz _ => oddCore_centralizer_eq_bot_of_g23 hX hz⟩

theorem thm3RTwoOrbit_proved (m : ℕ) : Thm3RTwoOrbit m :=
  thm3RTwoOrbit_of_rowFacts rowCentralizerFacts_proved m

end All

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
