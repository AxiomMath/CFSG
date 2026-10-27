module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHeNine
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Nine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open

section He


open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (fixGen_of_ex27Check he_check
  heP_eq_closure_gens factorization_card_heP)
open CFSG.Sporadic.HeldB (heP heEquivP card_heP rep_heGen)

theorem glbCore_one_eq_top_He (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .He).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 2) : GLBCore 3 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  let φ : K ≃* heP := (e₁.trans e₂.symm).trans heEquivP
  have : Finite heP := Nat.finite_of_card_ne_zero (by rw [card_heP]; norm_num)
  have h9 : Nat.card (A.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
    norm_num
  exact glbCore_one_eq_top_of_fixGen_map Nat.prime_three φ hA
    (fixGen_of_ex27Check (rep_heGen (k := 0) (by norm_num)) (rep_heGen (k := 1) (by norm_num))
      heP_eq_closure_gens factorization_card_heP he_check _ h9)

end He

section J4


open CFSG.Blueprint (NativeSporadic.Carrier NativeSporadic.J4)
open CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine (fixGen_j4)
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm (factorization_three_pow_mul)

theorem glbCore_one_eq_top_J4 (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 2) : GLBCore 3 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have e₂' : NativeSporadic.Carrier .J4 ≃* (TauCeti.CFSGIndex.sporadic .J4).Group := e₂
  let φ : K ≃* NativeSporadic.Carrier .J4 := e₁.trans e₂'.symm
  have hcard : Nat.card NativeSporadic.J4 = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
  have : Finite NativeSporadic.J4 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hL : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
    rw [hcard, show (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 by norm_num,
      factorization_three_pow_mul 3 (by norm_num)]
  have h9 : Nat.card (A.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
    norm_num
  exact glbCore_one_eq_top_of_fixGen_map Nat.prime_three φ hA (fixGen_j4 hL _ h9)

end J4

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
