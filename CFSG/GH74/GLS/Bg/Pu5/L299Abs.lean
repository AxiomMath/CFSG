module

public import CFSG.GH74.GLS.C3.Layer1.P34QShape
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU CFSG.GH74.GLS

theorem isNonabelianMaximalClassTwoGroup_of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    (h : IsNonabelianMaximalClassTwoGroup P) : IsNonabelianMaximalClassTwoGroup P' := by
  obtain ⟨hp, hnc, hnil, hcard⟩ := h
  have : Group.IsNilpotent P := hnil
  have hp' : IsPGroup 2 P' := hp.of_surjective e.toMonoidHom e.surjective
  have hnc' : ¬ IsMulCommutative P' := by
    intro hc
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    apply e.injective
    simp only [map_mul]
    exact hc.is_comm.comm (e a) (e b)
  have hnil' : Group.IsNilpotent P' := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  refine ⟨hp', hnc', hnil', ?_⟩
  have : Group.IsNilpotent P' := hnil'
  have h1 : Group.nilpotencyClass P' ≤ Group.nilpotencyClass P :=
    Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
  have h2 : Group.nilpotencyClass P ≤ Group.nilpotencyClass P' :=
    Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  rw [← Nat.card_congr e.toEquiv, hcard, le_antisymm h1 h2]

theorem exists_central_involution {X : Type*} [Group X] [Finite X] [Nontrivial X] (hX : IsPGroup 2 X) :
    ∃ x : X, orderOf x = 2 ∧ ∀ y : X, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZnt : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center X) := hX.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center X) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.1 h).1 (not_subsingleton _)
    · exact h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2 hdvd
  refine ⟨(c : X), (Subgroup.orderOf_coe c).trans hc, fun y => ?_⟩
  exact (Subgroup.mem_center_iff.1 c.2 y).symm

theorem qShape_of_index_two {X : Type} [Group X] [Finite X]
    (hX : P34.IsMaximalClassTwoGroup X) (Q : Subgroup X) (hQ : Q.index = 2) :
    IsCyclic ↥Q ∨ (Nat.card ↥Q = 4 ∧ ¬ IsCyclic ↥Q) ∨ IsNonabelianMaximalClassTwoGroup ↥Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup 2 X := hX.1
  have hcardX : Nat.card X = Nat.card Q * 2 := by
    have := Subgroup.card_mul_index Q
    rw [hQ] at this
    exact this.symm
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hnt : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨x, hx2, hxc⟩ := exists_central_involution hXp
  have hQp : IsPGroup 2 ↥Q := hXp.to_subgroup Q
  rcases P34.QShape.classify hx2 hxc (Or.inr hX) with hcyc | ⟨h4, -⟩ | ⟨a, hmd⟩
  · left
    have := hcyc
    infer_instance
  · left
    have hQ2 : Nat.card ↥Q = 2 := by omega
    exact isCyclic_of_prime_card hQ2
  · set A := zpowers a with hAdef
    have hA : A.index = 2 := hmd.index_two
    have hcardA : Nat.card X = Nat.card ↥A * 2 := by
      have := Subgroup.card_mul_index A
      rw [hA] at this
      exact this.symm
    have hQA : Nat.card ↥Q = Nat.card ↥A := by omega
    have hA4 : 4 ≤ Nat.card ↥A := by
      rw [hAdef, Nat.card_zpowers]
      exact hmd.order_ge
    by_cases hQeq : Q = A
    · left
      rw [hQeq]
      infer_instance
    · have hnle : ¬ Q ≤ A := fun hle => hQeq (Subgroup.eq_of_le_of_card_ge hle (by omega))
      obtain ⟨g, hgQ, hgA⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
      have hcen : ∀ y : X, y * g = g * y → y = 1 ∨ y = x ∨ y = g ∨ y = g * x := by
        intro y hyg
        by_cases hyA : y ∈ A
        · have hyc : ∀ h, y * h = h * y := hmd.central_of_centralizes hgA hyA hyg
          rcases hmd.center_eq y hyc with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · have hgy : g⁻¹ * y ∈ A := by
            rw [Subgroup.mul_mem_iff_of_index_two hA, inv_mem_iff]
            exact iff_of_false hgA hyA
          have hcom : (g⁻¹ * y) * g = g * (g⁻¹ * y) := by
            calc (g⁻¹ * y) * g = g⁻¹ * (y * g) := mul_assoc _ _ _
              _ = g⁻¹ * (g * y) := by rw [hyg]
              _ = y := inv_mul_cancel_left _ _
              _ = g * (g⁻¹ * y) := (mul_inv_cancel_left _ _).symm
          have hyc : ∀ h, (g⁻¹ * y) * h = h * (g⁻¹ * y) := hmd.central_of_centralizes hgA hgy hcom
          rcases hmd.center_eq _ hyc with h | h
          · right; right; left
            exact (inv_mul_eq_one.1 h).symm
          · right; right; right
            exact inv_mul_eq_iff_eq_mul.1 h
      have hc4 : Nat.card ↥(centralizer ({(⟨g, hgQ⟩ : ↥Q)} : Set ↥Q)) ≤ 2 ^ 2 := by
        have hmem : ∀ y : ↥(centralizer ({(⟨g, hgQ⟩ : ↥Q)} : Set ↥Q)),
            ((y : ↥Q) : X) ∈ ({1, x, g, g * x} : Finset X) := by
          intro y
          have hy := Subgroup.mem_centralizer_iff.1 y.2 ⟨g, hgQ⟩ rfl
          have h1 : ((y : ↥Q) : X) * g = g * ((y : ↥Q) : X) := (congrArg Subtype.val hy).symm
          rcases hcen _ h1 with h | h | h | h <;> simp [h]
        have hinj : Function.Injective (fun y : ↥(centralizer ({(⟨g, hgQ⟩ : ↥Q)} : Set ↥Q)) =>
            (⟨((y : ↥Q) : X), hmem y⟩ : ↥({1, x, g, g * x} : Finset X))) := by
          intro y y' h
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h')
        have hfin : Nat.card ↥({1, x, g, g * x} : Finset X) = ({1, x, g, g * x} : Finset X).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        have hle := Nat.card_le_card_of_injective _ hinj
        rw [hfin] at hle
        have h4' : ({1, x, g, g * x} : Finset X).card ≤ 4 := Finset.card_le_four
        norm_num
        omega
      by_cases h8 : 8 ≤ Nat.card ↥Q
      · obtain ⟨m, hm, hl⟩ := SU1.b_maximalClass_of_small_centralizer 2 Nat.prime_two ↥Q hQp
          (by norm_num; exact h8) ⟨g, hgQ⟩ hc4
        have hm3 : 3 ≤ m := by
          by_contra hcon
          push Not at hcon
          have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hnab : ¬ IsMulCommutative ↥Q := by
          intro hcomm
          have : Group.IsNilpotent ↥Q := hQp.isNilpotent
          have h1 : Group.nilpotencyClass ↥Q ≤ 1 := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hcomm
          apply hl
          rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
          omega
        right; right
        exact Stage1.Thm3.Sec6.B.maxClass_of_lcs ↥Q hQp hnab m hm hl
      · have hQ4 : Nat.card ↥Q = 4 := by
          obtain ⟨n, hn⟩ := hQp.exists_card_eq
          have hn3 : n < 3 := by
            by_contra hcon
            push Not at hcon
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hcon
            norm_num at this
            omega
          have hn2 : 2 ≤ n := by
            by_contra hcon
            push Not at hcon
            have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show n ≤ 1 by omega)
            norm_num at this
            omega
          have : n = 2 := by omega
          rw [hn, this]
          norm_num
        by_cases hcyc : IsCyclic ↥Q
        · left; exact hcyc
        · right; left; exact ⟨hQ4, hcyc⟩

end CFSG.GH74.GLS.Bg.Pu5
