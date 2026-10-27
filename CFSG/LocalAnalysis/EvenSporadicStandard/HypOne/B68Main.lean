module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Delta

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

open Subgroup

variable {G : Type} [Group G] [Finite G] {N sz : Fin 4 → ℕ}

theorem no_order_four (hA : Arith N sz) (hT3 : TableIII (G := G) N) (hT4 : TableIV (G := G) N sz)
    (hCap : Cap (G := G) N) (h2A : ∃ c : G, Inv N 0 c) {x n : G} (hx : orderOf x = 17)
    (hn : orderOf n = 4) (hnx : n * x = x * n) : False := by
  have hn4 : n ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hn
    omega
  have ha : orderOf (n * n) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hn]; norm_num), hn]
  have hax : n * n * x = x * (n * n) := commute_mul_of_commute hnx hnx
  have hnn : n * (n * n) = n * n * n := (mul_assoc n n n).symm
  obtain ⟨k, hk⟩ := hT3.1 (n * n) ha
  rcases hA.class_of_commute hx hax.symm hk with rfl | rfl
  ·
    have haD : n * n ∈ Del N x := ⟨hk, hax⟩
    obtain ⟨v, hvD, hva⟩ := exists_partner hA hT4 hx haD
    have hav := (del_commute hA hT4 hx haD hvD hva.symm).1
    obtain ⟨S, hS5, hS4, hSn⟩ := exists_five_of_order_four hn hvD.1.mul_self hvD.1.ne_one hva
    have hxT : x ∈ (centralizer ({n * n} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      ⟨mem_centralizer_singleton_iff.2 hax.symm, mem_centralizer_singleton_iff.2 rfl⟩
    have hnT : n ∈ (centralizer ({n * n} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      ⟨mem_centralizer_singleton_iff.2 hnn, mem_centralizer_singleton_iff.2 hnx⟩
    have hvT : v ∈ (centralizer ({n * n} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      ⟨mem_centralizer_singleton_iff.2 hav.symm, mem_centralizer_singleton_iff.2 hvD.2⟩
    have hSsub : S ⊆ (centralizer ({n * n} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
      intro g hg
      rcases hSn g hg with h | rfl
      · exact (Subgroup.zpowers_le.2 hnT) h
      · exact hvT
    have h4 := ncard_le_four_of_pow_four hxT (fun t ht => mem_centralizer_singleton_iff.1 ht.2) hx
      (hCap hk hx hax) hSsub hS4
    omega
  ·
    obtain ⟨c, hcD, e, heD, hce⟩ := exists_pair hA hT3 hT4 h2A hx hax.symm hk
    have hne : c ≠ e := by
      intro h
      subst h
      exact hk.ne_one (hce.symm.trans hcD.1.mul_self)
    have hcom := (del_commute hA hT4 hx hcD heD hne).1
    have hall : ∀ w ∈ Del N x, w = c ∨ w = e := fun w hw => by
      rcases del_three hA hT4 hCap hx hcD heD hw with h | h | h
      · exact absurd h hne
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hcn : c ≠ n := by
      rintro rfl
      have := hcD.1.1
      rw [hn] at this
      omega
    have hc' : n * c * n⁻¹ ∈ Del N x :=
      ⟨Inv.of_isConj hcD.1 (isConj_iff.2 ⟨n, rfl⟩), commute_conj_of_commute hnx hcD.2⟩
    rcases hall _ hc' with hcc | hce'
    ·
      have hnc : n * c = c * n := mul_inv_eq_iff_eq_mul.1 hcc
      have hea : e ≠ n * n := by
        intro h
        have heC : Inv N 3 e := by rw [h]; exact hk
        exact absurd (Inv.unique hA.inj heD.1 heC) (by decide)
      obtain ⟨S, hS5, hS4, hSn⟩ := exists_five_of_order_four hn heD.1.mul_self heD.1.ne_one hea
      have hxT : x ∈ (centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
        ⟨mem_centralizer_singleton_iff.2 hcD.2.symm, mem_centralizer_singleton_iff.2 rfl⟩
      have hnT : n ∈ (centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
        ⟨mem_centralizer_singleton_iff.2 hnc, mem_centralizer_singleton_iff.2 hnx⟩
      have heT : e ∈ (centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
        ⟨mem_centralizer_singleton_iff.2 hcom.symm, mem_centralizer_singleton_iff.2 heD.2⟩
      have hSsub : S ⊆ (centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
        intro g hg
        rcases hSn g hg with h | rfl
        · exact (Subgroup.zpowers_le.2 hnT) h
        · exact heT
      have h4 := ncard_le_four_of_pow_four hxT (fun t ht => mem_centralizer_singleton_iff.1 ht.2)
        hx (hCap hcD.1 hx hcD.2) hSsub hS4
      omega
    ·
      have hnce : n * c * n⁻¹ = e := hce'
      have hww : c * n * (c * n) = 1 := by
        calc c * n * (c * n) = c * (n * c * n⁻¹) * (n * n) := by group
          _ = c * e * (n * n) := by rw [hnce]
          _ = 1 := by rw [hce]; exact hk.mul_self
      have hw1 : c * n ≠ 1 := by
        intro h
        apply hcn
        exact (mul_left_cancel (h.trans hcD.1.mul_self.symm : c * n = c * c)).symm
      have hwo : orderOf (c * n) = 2 :=
        orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hww) hw1
      have hwx : c * n * x = x * (c * n) := commute_mul_of_commute hcD.2 hnx
      obtain ⟨k', hk'⟩ := hT3.1 (c * n) hwo
      rcases hA.class_of_commute hx hwx.symm hk' with rfl | rfl
      ·
        rcases hall _ ⟨hk', hwx⟩ with hwc | hwe
        · exact hn4 (mul_left_cancel (hwc.trans (mul_one c).symm : c * n = c * 1))
        · have h1 : c * (c * n) = n * n := by rw [hwe, hce]
          rw [← mul_assoc, hcD.1.mul_self, one_mul] at h1
          exact hn4 (mul_left_cancel ((mul_one n).trans h1)).symm
      ·
        obtain ⟨c₂, hc₂, e₂, he₂, hce₂⟩ := exists_pair hA hT3 hT4 h2A hx hwx.symm hk'
        have hc₂e₂ : c₂ ≠ e₂ := by
          intro h
          subst h
          exact hk'.ne_one (hce₂.symm.trans hc₂.1.mul_self)
        have key : c * n = n * n → False := fun h => hcn (mul_right_cancel h)
        rcases hall c₂ hc₂ with h1 | h1 <;> rcases hall e₂ he₂ with h2 | h2
        · exact hc₂e₂ (h1.trans h2.symm)
        · rw [h1, h2] at hce₂
          exact key (hce₂.symm.trans hce)
        · rw [h1, h2] at hce₂
          exact key (hce₂.symm.trans (hcom.symm.trans hce))
        · exact hc₂e₂ (h1.trans h2.symm)

theorem no_order_sixtyEight (hA : Arith N sz) (hT3 : TableIII (G := G) N)
    (hT4 : TableIV (G := G) N sz) (hCap : Cap (G := G) N) (h2A : ∃ c : G, Inv N 0 c) :
    ∀ g : G, orderOf g ≠ 68 := by
  intro g hg
  have hx : orderOf (g ^ 4) = 17 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hn : orderOf (g ^ 17) = 4 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  refine no_order_four hA hT3 hT4 hCap h2A hx hn ?_
  rw [← pow_add, ← pow_add, add_comm]

end CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68
