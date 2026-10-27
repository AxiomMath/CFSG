module

public import CFSG.ClassicalInvolution.Asc77.AscC25W4
public import CFSG.ClassicalInvolution.Asc77.AscC25W3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem c25_9_of_residuals (hM6 : C25Y.Layer6Cen4 p f) (h5 : Layer5Sq p f) (hExt : CentExt p f) :
    C25_9 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  by_cases hA : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z
  · have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 2 := by
      rw [hA, Nat.card_zpowers, hz2']
    exact ⟨by omega, fun h4 => by omega⟩
  · obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := T7U.exists_normal_four_bad hyp hA
    have hA0 := fourExhausts_of_centExt hExt (hyp := hyp) haA ha2 ha1 haz hconj hbad
    have haz' : a * z = z * a := hyp.hzS a haA.1
    have hFD : FourData hyp a := ⟨ha2, ha1, haz, haA, hconj, hA0⟩
    have hAeq : Subgroup.closure ({a, z} : Set G) =
        (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      refine le_antisymm ?_ fun b hb =>
        (inFour_iff_mem_closure ha2 hz2 haz').mp (hA0 b hb)
      rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact haA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hzA
    have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz haz'
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
      rw [← hAeq, hE.1]
      norm_num
    refine ⟨hcard.le, fun _ => ⟨a, hAeq, hbad, fun hgood => ?_⟩⟩
    exact no_mixed hM6 h5 hFD hbad hgood

end Assembly

end C25W

end CFSG.ClassicalInvolution.Asc77
