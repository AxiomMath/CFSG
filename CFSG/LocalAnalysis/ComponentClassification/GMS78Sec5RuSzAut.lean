module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem card_Sz_eq (a : ℕ) :
    Nat.card (Sz a) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  obtain ⟨E⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  rw [Nat.card_congr E.toEquiv]
  exact CFSG.LieType.Ree.suzuki_order (GaloisField.card 2 (2 * a + 1) (by omega))

theorem card_Sz_one : Nat.card (Sz 1) = 29120 := by
  rw [card_Sz_eq]
  norm_num

theorem card_Sz_zero_eq : Nat.card (Sz 0) = 20 := by
  rw [card_Sz_eq]
  norm_num

theorem card_outer_eq_three {Q : Type} [Group Q] (e : Q ≃* Sz 1) :
    Nat.card (Outer Q) = 3 := by
  obtain ⟨E⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup 1
  have h := (CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting 1 le_rfl
    (GaloisField 2 (2 * 1 + 1)) (GaloisField.card 2 (2 * 1 + 1) (by omega))).2.2.2.2.2.1
  rw [Nat.card_congr (equivalence (e.trans E)).toEquiv, h]

theorem mem_inner_of_card_eight {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Sz 1) (β : MulAut Q) {A : Subgroup Q} (hA : Nat.card A = 8)
    (hβ : ∀ a ∈ A, β a = a) : β ∈ inner Q := by
  by_contra hβin
  have h3 : Nat.card (Outer Q) = 3 := card_outer_eq_three e
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set b := (QuotientGroup.mk β : Outer Q) with hb
  have hb1 : b ≠ 1 := fun h => hβin ((QuotientGroup.eq_one_iff _).mp h)
  have hbo : orderOf b = 3 := by
    have hdvd : orderOf b ∣ 3 := h3 ▸ _root_.orderOf_dvd_natCard b
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hβ0 : orderOf β ≠ 0 := (orderOf_pos β).ne'
  obtain ⟨k, m, hm3, hβm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hβ0 3 (by norm_num)
  set β' := β ^ m with hβ'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβm
    exact hβ0 hβm
  have hβ'o : orderOf β' = 3 ^ k := by
    rw [hβ', orderOf_pow_of_dvd hm0 (by rw [hβm]; exact dvd_mul_left m _), hβm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hb' : (QuotientGroup.mk β' : Outer Q) ≠ 1 := by
    intro h
    rw [hβ', QuotientGroup.mk_pow, ← hb] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hbo] at this
    exact hm3 this
  have hβ'1 : β' ≠ 1 := fun h => hb' (by rw [h]; rfl)
  set f := MulAut.congr e β' with hf
  have hfo : orderOf f = 3 ^ k := by
    rw [hf, MulEquiv.orderOf_eq, hβ'o]
  have hcop : Nat.Coprime (2 * 1 + 1) (Nat.card (Sz 1)) := by
    rw [card_Sz_one]
    norm_num
  have hP : IsPGroup 3 (zpowers f) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hfo]
  have hdvd := CFSG.SignalizerFunctorTheorem.NearModels.sz_card_pSubgroup_dvd 1 (by norm_num) hcop
    (zpowers f) hP
  rw [Nat.card_zpowers] at hdvd
  have hfo3 : orderOf f = 2 * 1 + 1 := by
    rcases (Nat.dvd_prime (by norm_num : (2 * 1 + 1).Prime)).mp hdvd with h | h
    · exfalso
      apply hβ'1
      have hf1 : f = 1 := orderOf_eq_one_iff.mp h
      rw [hf] at hf1
      exact (MulAut.congr e).injective (by rw [hf1, map_one])
    · exact h
  obtain ⟨φ⟩ := CFSG.SignalizerFunctorTheorem.NearModels.sz_fixedSubgroup_mulEquiv 1 (by norm_num)
    hcop f hfo3
  have hle : A.map e.toMonoidHom ≤ signalizerFixedSubgroup f := by
    rintro _ ⟨a, ha, rfl⟩
    change f (e a) = e a
    have hpow : ∀ j : ℕ, (β ^ j) a = a := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, MulAut.mul_apply, hβ a ha, ih]
    rw [hf, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hβ', hpow m]
  have h8 : Nat.card (A.map e.toMonoidHom) = 8 := by
    rw [card_map_of_injective e.injective, hA]
  have h20 : Nat.card (signalizerFixedSubgroup f) = 20 := by
    rw [Nat.card_congr φ.toEquiv, card_Sz_zero_eq]
  have := card_dvd_of_le hle
  rw [h8, h20] at this
  norm_num at this

theorem isPGroup_centralizer_of_sz_one {Q : Type} [Group Q]
    (e : Q ≃* Sz 1) {t : Q} (ht : orderOf t = 2) : IsPGroup 2 (centralizer ({t} : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup 1
  set ψ := e.trans E with hψ
  have hψt : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  obtain ⟨S, hS⟩ := UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow
    (GaloisField.card 2 (2 * 1 + 1) (by omega)) (ψ t) hψt
  have hC : IsPGroup 2 (centralizer ({ψ t} : Set (suzukiGroup 1 (GaloisField 2 (2 * 1 + 1))))) := by
    rw [← hS]
    exact S.isPGroup'
  intro x
  obtain ⟨k, hk⟩ := hC ⟨ψ x, by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp x.2]⟩
  refine ⟨k, Subtype.ext (ψ.injective ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

end CFSG.ComponentClassification.GMS78
