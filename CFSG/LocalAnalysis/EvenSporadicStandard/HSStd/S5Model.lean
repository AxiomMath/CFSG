module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SylowConj

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

structure HS100Model : Prop where
  aut : ∃ e : ↥hs100R ≃* MulAut ↥hs100P, ∀ (x : ↥hs100R) (p : ↥hs100P),
    ((e x p : ↥hs100P) : Equiv.Perm (Fin 100)) =
      (x : Equiv.Perm (Fin 100)) * p * (x : Equiv.Perm (Fin 100))⁻¹
  card : Nat.card ↥hs100R = 2 * Nat.card ↥hs100P
  outer : ∃ u : ↥hs100R, u ∉ (Subgroup.inclusion hs100P_le_R).range ∧ u * u = 1
  count : ∀ Sw : Subgroup ↥hs100R, IsPGroup 2 Sw → ¬ 2 ∣ Sw.index → ∀ zw ∈
      (Subgroup.inclusion hs100P_le_R).range, orderOf zw = 2 →
      centralizer ((Sw ⊓ (Subgroup.inclusion hs100P_le_R).range : Subgroup ↥hs100R) :
        Set ↥hs100R) ⊓ (Subgroup.inclusion hs100P_le_R).range = zpowers zw →
      Nat.card {y : Sw // y.1 ∉ (Subgroup.inclusion hs100P_le_R).range ∧ y.1 * y.1 = 1} ≠
        Nat.card {y : Sw // y.1 ∉ (Subgroup.inclusion hs100P_le_R).range ∧ y.1 * y.1 = zw}
  equiv : ∀ (Y : Type) [Group Y], IsSporadic Y .HS → Nonempty (Y ≃* ↥hs100P)
  center_eq_bot : ∀ (Y : Type) [Group Y], IsSporadic Y .HS → center Y = ⊥

theorem hs100Model :
    HS100Model where
  aut := by
    obtain ⟨-, -, ⟨e, he, -⟩, -⟩ := automorphism_model_of hs100R_eq_sup hs100U_sq
      hs100U_not_mem_P (fun p hp => hs100U_conj_mem hp) centralizer_hs100P outer_card_hs100P
    exact ⟨e, he⟩
  card := by rw [card_hs100R, card_hs100P]
  outer := by
    refine ⟨⟨hs100U, hs100U_mem_R⟩, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      have h1 : (x : Equiv.Perm (Fin 100)) = hs100U := congrArg Subtype.val hx
      exact hs100U_not_mem_P (h1 ▸ x.2)
    · refine Subtype.ext ?_
      show hs100U * hs100U = 1
      rw [← sq]
      exact hs100U_sq
  count := by
    classical
    obtain ⟨S₀, z₀, hS₀R, hS₀c, hz₀P, -, hz₀1, hz₀c, hc1, hcZ⟩ := s5_sylow_spec
    set Q : Subgroup ↥hs100R := (Subgroup.inclusion hs100P_le_R).range with hQ
    have hQn : Q.Normal := by
      rw [hQ, Subgroup.inclusion_range]
      exact hs100P_normal_R
    set S₀' : Subgroup ↥hs100R := S₀.subgroupOf hs100R with hS₀'
    have hcard : Nat.card S₀' = 2 ^ 10 := by
      rw [hS₀', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀R).toEquiv, hS₀c]
      norm_num
    have hp : IsPGroup 2 S₀' := IsPGroup.of_card hcard
    have hidx : ¬ 2 ∣ S₀'.index := by
      have h := Subgroup.card_mul_index S₀'
      rw [hcard, card_hs100R] at h
      omega
    have hmemQ : ∀ x : ↥hs100R, x ∈ Q ↔ (x : Equiv.Perm (Fin 100)) ∈ hs100P := by
      intro x
      rw [hQ, Subgroup.inclusion_range, mem_subgroupOf]
    refine hcount_of_one_sylow Q S₀' hp hidx ⟨z₀, hs100P_le_R hz₀P⟩
      ((hmemQ _).2 hz₀P) (fun h => hz₀1 (congrArg Subtype.val h)) ?_ ?_
    · rintro x ⟨hxS, hxQ⟩
      exact Subtype.ext (hz₀c x.1 hxS ((hmemQ x).1 hxQ))
    · let e : S₀' ≃ S₀ :=
        { toFun := fun y => ⟨y.1.1, y.2⟩
          invFun := fun x => ⟨⟨x.1, hS₀R x.2⟩, x.2⟩
          left_inv := fun y => rfl
          right_inv := fun x => rfl }
      have h1 : Nat.card {y : S₀' // y.1 ∉ Q ∧ y.1 * y.1 = 1} = 104 := by
        rw [← hc1]
        refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
        simp only [hmemQ]
        exact and_congr Iff.rfl ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      have h2 : Nat.card {y : S₀' // y.1 ∉ Q ∧ y.1 * y.1 = ⟨z₀, hs100P_le_R hz₀P⟩} = 40 := by
        rw [← hcZ]
        refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
        simp only [hmemQ]
        exact and_congr Iff.rfl ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      rw [h1, h2]
      norm_num
  equiv Y _ h := by
    obtain ⟨e₀⟩ := h
    exact ⟨(e₀ : Y ≃* NativeSporadic.HS).trans hs100Equiv⟩
  center_eq_bot Y _ h := center_eq_bot_of_isSporadic_hs h

end CFSG.EvenSporadicStandard.HSStd
