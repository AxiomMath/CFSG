module

public import CFSG.CGT.Timmesfeld75.Sec76
public import CFSG.CGT.Timmesfeld75.Sec77Stmt

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem orderOf_mul_eq_two_of_comm {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hne : a * b ≠ 1) : orderOf (a * b) = 2 := by
  have h2 : (a * b) ^ 2 = 1 := by
    rw [(show Commute a b from hab).mul_pow, pow_two, pow_two, ha, hb, one_mul]
  exact orderOf_eq_prime h2 hne

theorem conj_conj_pair_eq {g h y z u : G} (hz : g * y * g⁻¹ = z) (hu : h * y * h⁻¹ = u) :
    (h * g⁻¹) * z * (h * g⁻¹)⁻¹ = u := by
  subst hz hu
  group

theorem orderOf_mul_swap {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    orderOf (a * b) = orderOf (b * a) := by
  have h : b * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  rw [h, orderOf_inv]

theorem Sec6Ctx.order_cases_of_comm (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {a b e : G} (ha : a ∈ classD T) (hb : b ∈ classD T)
    (he : e ∈ classD T) (hea : e * a = a * e) (heb : e * b = b * e) (heb1 : e * b ≠ 1) :
    orderOf (a * b) = 2 ∨ orderOf (a * b) = 4 ∨ Odd (orderOf (a * b)) := by
  have hTab := hc.hy.pair.wc.1
  have he2 : e * e = 1 := mul_self_eq_one_of_mem_classD hTab he
  have hb2 : b * b = 1 := mul_self_eq_one_of_mem_classD hTab hb
  rcases (hc.sec73 h1 h62 h63 h66 hA8 hnat ha hb).1 with h4 | hodd | ⟨s, hs, hs2⟩
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr hodd)
  · by_cases hs1 : s = 1
    · exact Or.inl (by rw [hs2, hs1])
    · exfalso
      have hs3 : 3 ≤ s := by
        obtain ⟨t, ht⟩ := hs
        omega
      have h76 := (sec76_of h66 h1 h62 h63) G T T₁ n m hc hnat hn3 hA8 a ha b hb s hs hs3 hs2 e he
        hea
      exact h76.1 (orderOf_mul_eq_two_of_comm he2 hb2 heb heb1)

theorem Sec6Ctx.comm_of_commuting_config (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62)
    (h63 : Sec63) (h77 : Sec77) (hc : Sec6Ctx T T₁ n m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1))
    {x z a u : G} (hxD : x ∈ classD T) (hzD : z ∈ classD T) (haD : a ∈ classD T)
    (huD : u ∈ classD T) (hxz : x * z = z * x) (hxz1 : x * z ≠ 1) (hxzD : x * z ∉ classD T)
    (hac : a * (x * z) = (x * z) * a) (hua : u * a = a * u) (hux : u * x = x * u)
    (huz : u * z = z * u) (hux1 : u * x ≠ 1) (huz1 : u * z ≠ 1) (haz : a ≠ z) :
    a * x = x * a ∧ a * z = z * a := by
  have hTab := hc.hy.pair.wc.1
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hxD
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_classD hTab hzD
  have ha2 : a * a = 1 := mul_self_eq_one_of_mem_classD hTab haD
  have hz_cases := hc.order_cases_of_comm h66 h1 h62 h63 hnat hn3 hA8 haD hzD huD hua huz huz1
  have hx_cases := hc.order_cases_of_comm h66 h1 h62 h63 hnat hn3 hA8 haD hxD huD hua hux hux1
  have hcord : orderOf (x * z) = 2 := orderOf_mul_eq_two_of_comm hx2 hz2 hxz hxz1
  have hcz : Commute (x * z) z := by
    show (x * z) * z = z * (x * z)
    rw [← mul_assoc, ← hxz]
  have hcx : Commute (x * z) x := by
    show (x * z) * x = x * (x * z)
    rw [mul_assoc, ← hxz]
  have hca : Commute (x * z) a := hac.symm
  have hform1 : a * x = (a * z) * (x * z) := by
    calc a * x = a * (z * z) * x := by rw [hz2, mul_one]
      _ = (a * z) * (z * x) := by group
      _ = (a * z) * (x * z) := by rw [hxz]
  have hform2 : a * z = (a * x) * (x * z) := by
    calc a * z = a * (x * x) * z := by rw [hx2, mul_one]
      _ = (a * x) * (x * z) := by group
  have hnotodd : ¬ Odd (orderOf (a * z)) := by
    intro hodd
    have hord : orderOf (a * x) = orderOf (a * z) * 2 := by
      rw [hform1, (show Commute (a * z) (x * z) from
        (hca.mul_right hcz).symm).orderOf_mul_eq_mul_orderOf_of_coprime
          (by rw [hcord]; exact Nat.coprime_two_right.2 hodd), hcord]
    rcases hx_cases with h2 | h4 | hoddx
    · have h1' : orderOf (a * z) = 1 := by omega
      exact haz (by
        have hz1 : a * z = 1 := orderOf_eq_one_iff.1 h1'
        rw [eq_inv_of_mul_eq_one_left hz1, inv_eq_of_mul_eq_one_right hz2])
    · obtain ⟨t, ht⟩ := hodd
      omega
    · obtain ⟨t, ht⟩ := hoddx
      omega
  have hz24 : orderOf (a * z) = 2 ∨ orderOf (a * z) = 4 := by
    rcases hz_cases with h2 | h4 | hodd
    · exact Or.inl h2
    · exact Or.inr h4
    · exact absurd hodd hnotodd
  by_cases hxodd : Odd (orderOf (a * x))
  ·
    have hord : orderOf (a * z) = orderOf (a * x) * 2 := by
      rw [hform2, (show Commute (a * x) (x * z) from
        (hca.mul_right hcx).symm).orderOf_mul_eq_mul_orderOf_of_coprime
          (by rw [hcord]; exact Nat.coprime_two_right.2 hxodd), hcord]
    have h1' : orderOf (a * x) = 1 := by
      obtain ⟨t, ht⟩ := hxodd
      rcases hz24 with h2 | h4 <;> omega
    have hax1 : a * x = 1 := orderOf_eq_one_iff.1 h1'
    have hax : a = x := by
      rw [eq_inv_of_mul_eq_one_left hax1, inv_eq_of_mul_eq_one_right hx2]
    subst hax
    exact ⟨rfl, hxz⟩
  · have hx24 : orderOf (a * x) = 2 ∨ orderOf (a * x) = 4 := by
      rcases hx_cases with h2 | h4 | hodd
      · exact Or.inl h2
      · exact Or.inr h4
      · exact absurd hodd hxodd
    have hzx1 : z * x ≠ 1 := by rw [← hxz]; exact hxz1
    have hzxD : z * x ∉ classD T := by rw [← hxz]; exact hxzD
    have hac' : a * (z * x) = (z * x) * a := by rw [← hxz]; exact hac
    have h7x := h77 G T T₁ n m hc hnat hn3 hA8 x hxD z hzD hxz hxz1 hxzD a haD hac
    have h7z := h77 G T T₁ n m hc hnat hn3 hA8 z hzD x hxD hxz.symm hzx1 hzxD a haD hac'
    have hax2 : orderOf (a * x) = 2 := by
      rcases hx24 with h2 | h4
      · exact h2
      · exact absurd ((orderOf_mul_swap ha2 hx2).symm.trans h4) h7x
    have haz2 : orderOf (a * z) = 2 := by
      rcases hz24 with h2 | h4
      · exact h2
      · exact absurd ((orderOf_mul_swap ha2 hz2).symm.trans h4) h7z
    exact ⟨(orderOf_mul_dvd_two_iff_commute ha2 hx2).1 (dvd_of_eq hax2),
      (orderOf_mul_dvd_two_iff_commute ha2 hz2).1 (dvd_of_eq haz2)⟩

end CFSG.CGT.Timmesfeld75
