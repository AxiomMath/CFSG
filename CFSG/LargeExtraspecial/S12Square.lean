module

public import CFSG.LargeExtraspecial.S12Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem closure_Dbar12_le_Mbar : closure S.Dbar12 ≤ S.Mbar :=
  (closure_le _).mpr fun _ h => h.1

theorem Mbar_le_normalizer_closure_Dbar12 :
    S.Mbar ≤ normalizer (closure S.Dbar12 : Set S.O) := by
  intro m hm
  refine mem_normalizer_of_conj_le
    (conj_mem_closure_of_conj_mem fun y hy => conj_mem_Dbar12 hm hy)
    (conj_mem_closure_of_conj_mem fun y hy => conj_mem_Dbar12 (S.Mbar.inv_mem hm) hy)

theorem inv_eq_of_mem_Dbar12 {x : S.O} (hx : x ∈ S.Dbar12) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (Subtype.ext hx.2.2.2.1)

theorem conj_mem_comp12_of_mem_Dbar12 {τ x y : S.O} (hτ : τ ∈ S.Dbar12) (hx : x ∈ S.Dbar12)
    (hy : y ∈ S.comp12 τ) : x * y * x⁻¹ ∈ S.comp12 τ := by
  have hyD := mem_Dbar12_of_mem_comp12 hτ hy
  by_cases hxy : x * y = y * x
  · rw [hxy, mul_inv_cancel_right]
    exact hy
  by_cases hxc : x ∈ S.comp12 τ
  ·
    have hxi := inv_eq_of_mem_Dbar12 hx
    have hne : x * (x * y * x⁻¹) ≠ (x * y * x⁻¹) * x := by
      intro h
      apply hxy
      rw [hxi] at h
      have hxx : x * x = 1 := Subtype.ext hx.2.2.2.1
      have h' : y * x = x * y := by
        calc y * x = x * x * y * x := by rw [hxx, one_mul]
          _ = x * (x * y * x) := by group
          _ = x * y * x * x := h
          _ = x * y := by rw [mul_assoc (x * y) x x, hxx, mul_one]
      exact h'.symm
    exact Relation.ReflTransGen.tail hxc ⟨hx, conj_mem_Dbar12 hx.1 hyD, hne⟩
  · exact absurd (commute_of_not_mem_comp12 hy hτ hx hxc).symm hxy

theorem closure_Dbar12_le_normalizer_closure_comp12 {τ : S.O} (hτ : τ ∈ S.Dbar12) :
    closure S.Dbar12 ≤ normalizer (closure (S.comp12 τ) : Set S.O) := by
  rw [closure_le]
  intro x hx
  refine mem_normalizer_of_conj_le
    (conj_mem_closure_of_conj_mem fun y hy => conj_mem_comp12_of_mem_Dbar12 hτ hx hy)
    (conj_mem_closure_of_conj_mem fun y hy => ?_)
  rw [inv_eq_of_mem_Dbar12 hx]
  exact conj_mem_comp12_of_mem_Dbar12 hτ hx hy

theorem noNormalTwo_closure_comp12 {τ : S.O} (hτ : τ ∈ S.Dbar12) :
    S12NoNormalTwo (closure (S.comp12 τ)) := by
  have hD : S12NoNormalTwo (closure S.Dbar12) :=
    S.s12_noNormalTwo_Mbar.of_normal closure_Dbar12_le_Mbar Mbar_le_normalizer_closure_Dbar12
  exact hD.of_normal (closure_mono (comp12_subset_Dbar12 hτ))
    (closure_Dbar12_le_normalizer_closure_comp12 hτ)

theorem sq_mem_comp12 {d e : S.O} (hd : d ∈ S.Dbar12) (he : e ∈ S.comp12 d)
    (h4 : orderOf (d * e) = 4) : (d * e) ^ 2 ∈ S.comp12 d := by
  have heD := mem_Dbar12_of_mem_comp12 hd he
  have hfD := Dbar12_rootInvolution.2 d hd e heD h4
  by_contra hf
  have hcomm : ∀ c ∈ S.comp12 d, c * (d * e) ^ 2 = (d * e) ^ 2 * c := fun c hc =>
    commute_of_not_mem_comp12 hc hd hfD hf
  have hf2 : orderOf ((d * e) ^ 2) = 2 := orderOf_eq_two_of_isTypeA' hfD.2
  have hP : zpowers ((d * e) ^ 2) = ⊥ := by
    refine noNormalTwo_closure_comp12 hd _ ?_ ?_ ?_
    · rw [zpowers_le]
      exact pow_mem (mul_mem (subset_closure (mem_comp12_self d)) (subset_closure he)) 2
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
    · intro y hy
      have hyc : Commute y ((d * e) ^ 2) := by
        have hle : closure (S.comp12 d) ≤ centralizer ({(d * e) ^ 2} : Set S.O) := by
          rw [closure_le]
          intro c hc
          rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
          exact hcomm c hc
        exact mem_centralizer_singleton_iff.mp (hle hy)
      exact mem_normalizer_of_commute fun p hp => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hp
        exact (hyc.zpow_right k).eq
  have h1 : (d * e) ^ 2 ∈ zpowers ((d * e) ^ 2) := mem_zpowers _
  rw [hP, mem_bot] at h1
  rw [h1, orderOf_one] at hf2
  exact absurd hf2 (by norm_num)

theorem sq_mem_Ebar12 (hRI : RootInvolutionComponentsInput.{u}) {g : G} {d e : S.O}
    (hd : d ∈ S.Ebar12 g) (he : e ∈ S.Ebar12 g) (h4 : orderOf (d * e) = 4) :
    (d * e) ^ 2 ∈ S.Ebar12 g := by
  have hdD := Ebar12_subset_Dbar12 hd
  have heD := Ebar12_subset_Dbar12 he
  have hdd : d * d = 1 := Subtype.ext hdD.2.2.2.1
  have hee : e * e = 1 := Subtype.ext heD.2.2.2.1
  have hde : d * e ≠ e * d := by
    intro h
    have h2 : (d * e) ^ 2 = 1 := by
      calc (d * e) ^ 2 = d * (e * d) * e := by rw [pow_two]; group
        _ = d * (d * e) * e := by rw [h]
        _ = (d * d) * (e * e) := by group
        _ = 1 := by rw [hdd, hee, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hec : e ∈ S.comp12 d := Relation.ReflTransGen.single ⟨hdD, heD, hde⟩
  exact comp12_subset_Ebar12 hRI hd (sq_mem_comp12 hdD hec h4)

end Setting

end CFSG.LargeExtraspecial
