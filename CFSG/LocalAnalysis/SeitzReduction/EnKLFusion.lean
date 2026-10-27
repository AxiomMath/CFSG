module

public import CFSG.LocalAnalysis.SeitzReduction.EnKLOrderSix
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.GF2n.Stroth80

variable {K : Type} [Field K]


theorem exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE6 [CharP K 2] {x : adjointGroup .E6 K}
    (hx : x ∈ innerRepsE6 K) (hθ : x ≠ pinnedElt .E6 (highRoot .E6) 1) :
    ∃ g : adjointGroup .E6 K, orderOf (x * (g⁻¹ * x * g)) = 6 := by
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact absurd rfl hθ
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E6) (Or.inl rfl)
      (d := ![-1, -1, -1, -2, -1, 0]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E6) (Or.inl rfl)
      (d := ![-1, -1, -1, -1, -1, -1]) (by decide +kernel)

theorem exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE7 [CharP K 2] {x : adjointGroup .E7 K}
    (hx : x ∈ innerRepsE7 K) (hθ : x ≠ pinnedElt .E7 (highRoot .E7) 1) :
    ∃ g : adjointGroup .E7 K, orderOf (x * (g⁻¹ * x * g)) = 6 := by
  simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hθ
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E7) (Or.inr (Or.inl rfl))
      (d := ![-1, -2, -2, -3, -2, -1, -1]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E7) (Or.inr (Or.inl rfl))
      (d := ![-1, -1, -1, -2, -2, -2, -1]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E7) (Or.inr (Or.inl rfl))
      (d := ![-1, -1, -2, -2, -1, 0, 0]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E7) (Or.inr (Or.inl rfl))
      (d := ![0, 0, -1, -1, -1, -1, 0]) (by decide +kernel)

theorem exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE8 [CharP K 2] {x : adjointGroup .E8 K}
    (hx : x ∈ innerRepsE8 K) (hθ : x ≠ pinnedElt .E8 (highRoot .E8) 1) :
    ∃ g : adjointGroup .E8 K, orderOf (x * (g⁻¹ * x * g)) = 6 := by
  simp only [innerRepsE8, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact absurd rfl hθ
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E8) (Or.inr (Or.inr rfl))
      (d := ![-1, -3, -3, -5, -4, -3, -2, -1]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E8) (Or.inr (Or.inr rfl))
      (d := ![-1, -2, -3, -4, -3, -2, -1, -1]) (by decide +kernel)
  · exact exists_orderOf_frame_mul_conj_eq_six (τ := .E8) (Or.inr (Or.inr rfl))
      (d := ![-1, -1, -2, -3, -3, -2, -1, -1]) (by decide +kernel)

theorem exists_conj_eq_pinnedElt_highRoot_E6 [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    {a : ℕ} (h : IsStrothInvolution t a) :
    ∃ g : adjointGroup .E6 K, g * t * g⁻¹ = pinnedElt .E6 (highRoot .E6) 1 :=
  h.exists_conj_eq_of_orderOf_mul_conj_eq_six exists_conj_mem_innerRepsE6
    fun _ hx hθ => exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE6 hx hθ

theorem exists_conj_eq_pinnedElt_highRoot_E7 [Finite K] [CharP K 2] {t : adjointGroup .E7 K}
    {a : ℕ} (h : IsStrothInvolution t a) :
    ∃ g : adjointGroup .E7 K, g * t * g⁻¹ = pinnedElt .E7 (highRoot .E7) 1 :=
  h.exists_conj_eq_of_orderOf_mul_conj_eq_six exists_conj_mem_innerRepsE7
    fun _ hx hθ => exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE7 hx hθ

theorem exists_conj_eq_pinnedElt_highRoot_E8 [Finite K] [CharP K 2] {t : adjointGroup .E8 K}
    {a : ℕ} (h : IsStrothInvolution t a) :
    ∃ g : adjointGroup .E8 K, g * t * g⁻¹ = pinnedElt .E8 (highRoot .E8) 1 :=
  h.exists_conj_eq_of_orderOf_mul_conj_eq_six classListE8_exists_conj_mem_innerRepsE8
    fun _ hx hθ => exists_orderOf_mul_conj_eq_six_of_mem_innerRepsE8 hx hθ

end CFSG.SeitzReduction.EPilot
