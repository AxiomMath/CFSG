module

public import CFSG.Quasithin.EmptyFaithful.S146zRSL2Set
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise MatrixGroups

section EightMain

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H PQ : Subgroup G}

theorem q_relIndex_eq_eight_F4 (h12 : Stage14612PartP_F4) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ 3) (hmax : PMaximal T M 3) :
    (pCoreOf 2 H).relIndex T = 8 := by
  classical
  obtain ⟨-, H₀, H₁, H₂, t, hdec⟩ := h12 G T M S H PQ 3 hred hmax
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hred.isHTM.1.1
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hred.isHTM
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp (pCoreOf_isPGroup 2 H)
  have h1 := hdec.card_H₀
  have h2 := hdec.relIndex_eq_two_of_p_three S hred
  have h3 := Subgroup.relIndex_mul_card H₀ H
  rw [inf_eq_left.mpr hdec.le, h2, h1, hb] at h3
  have hHcard : Nat.card H = 9 * 2 ^ (b + 3) := by rw [← h3]; ring
  have hSyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 S.hyp.sylow hTH
  have hT := q_card_of_isSylowTwoOf hSyl
  rw [hHcard, q_factorization_two_mul 9 (b + 3) (by norm_num)] at hT
  have h4 := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
  rw [inf_eq_left.mpr hQT, hT, hb] at h4
  have hpos : 0 < 2 ^ b := pow_pos two_pos b
  have : (pCoreOf 2 H).relIndex T * 2 ^ b = 8 * 2 ^ b := by rw [h4]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end EightMain

end CFSG.Quasithin
