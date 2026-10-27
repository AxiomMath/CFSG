module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanC0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanLag
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanFull

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem closure_sqMap_perp_eq_top {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup K} (hΛ : 4 ≤ Nat.card Λ) (hRu : ¬ (a = 1 ∧ Nat.card Λ = 4)) {c e : K}
    {x : K × K × K} (hr : x.2.1 ≠ 0) (hQ : sqMap a c e x = 0) :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  by_cases hc : c = 0
  · subst hc
    by_cases hu : x.1 = 0
    · exact closure_eq_top_c_eq_zero_u_eq_zero hK hu
    by_cases hs : x.2.2 = 0
    · exact closure_eq_top_c_eq_zero_s_eq_zero hu hs hQ
    · exact closure_eq_top_c_eq_zero_s_ne_zero ha hK hs
  by_cases hu : x.1 = 0
  · by_cases hs : x.2.2 = 0
    · exact closure_eq_top_c_ne_zero_u_eq_zero_s_eq_zero ha hK (by omega) hc hu hs hr
    · exact closure_eq_top_c_ne_zero_u_eq_zero_s_ne_zero ha hK (by omega) hc hu hs hr
  by_cases ha2 : 2 ≤ a
  · exact closure_eq_top_c_ne_zero_u_ne_zero ha2 hK hc hu
  have ha1 : a = 1 := by omega
  have hcardK : Nat.card K = 8 := by rw [Nat.card_eq_fintype_card, hK, ha1]; norm_num
  have hdvd : Nat.card Λ ∣ 8 := hcardK ▸ AddSubgroup.card_addSubgroup_dvd_card Λ
  have h8 : Nat.card Λ = 8 := by
    have hle : Nat.card Λ ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have h4 : Nat.card Λ ≠ 4 := fun h => hRu ⟨ha1, h⟩
    interval_cases h : Nat.card Λ <;> omega
  have htop : Λ = ⊤ := AddSubgroup.eq_top_of_card_eq Λ (by rw [h8, hcardK])
  exact closure_eq_top_of_eq_top ha hK htop

end CFSG.ComponentClassification.GMS78.VLike
