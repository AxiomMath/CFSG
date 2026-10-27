module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7Comm
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7Levi
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7Tw
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcGFE
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Split
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.Burgoyne.E2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.AlgebraicGroups (signMaskTuple)

theorem innerDiagCoreInput_E7_holds :
    InnerDiagCoreInput .E7 := by
  intro K _ _ hodd α hα2 hα1 g a hga
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hK] at hodd
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' n.ne_zero).2 even_two)
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow hcard
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hZ : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot_field .E7 K
  have hcomm : ∀ c d : MulAut (adjointGroup .E7 K), Odd (orderOf c) → Odd (orderOf d) →
      c * d * c⁻¹ * d⁻¹ ∈
        (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    fun c d _ _ => commutator_mem_range_conj_E7 hodd c d
  have hαo : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hαeq : α = MulAut.conj g * rootDiagAut .E7 K a := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hga x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_rootDiagAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  rw [hαeq] at hαo ⊢
  by_cases hsplit : ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ ∃ ψ : MulAut (adjointGroup .E7 K),
      ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ =
        rootDiagAut .E7 K (signMaskTuple .E7 K m)
  · obtain ⟨m, hm, ψ, hψ⟩ := hsplit
    refine outerCoreAt_of_conj hψ ?_
    rcases hm with rfl | rfl | rfl
    · rw [signMaskTuple_one]
      exact outerCoreAt_of_pPrimeCore hZ (fun _ => Iff.rfl) (burgCoreFor_E7_t1 hK2).1 hcomm
    · rw [signMaskTuple_two]
      exact outerCoreAt_of_pPrimeCore hZ (fun _ => Iff.rfl) (burgCoreFor_E7_t4 hK2).1 hcomm
    · rw [signMaskTuple_three]
      obtain ⟨n', hn'⟩ := exists_conj_rootDiagAut_three (K := K) hK2
      rw [hn']
      exact outerCoreAt_of_conj (ψ := (MulAut.conj n')⁻¹) (by group) (outerCoreAt_t7 hp hp2 hK)
  · push Not at hsplit
    by_cases hcore : pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) = ⊥
    · exact outerCoreAt_of_pPrimeCore hZ (fun _ => Iff.rfl) hcore hcomm
    · have : CharP (AlgebraicClosure K) p :=
        charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
      rcases TwE7.twisted_core_or_mask_three hp2 n.pos hK (AlgebraicClosure K) hαo hsplit with
        h | ⟨-, r, hr, h3, g₁, hg₁G, hconj, hcoc⟩
      · exact absurd h hcore
      · exact outerCoreAt_twisted_three hp2 n.pos hK (AlgebraicClosure K) hr h3 hg₁G hconj hcoc

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7
