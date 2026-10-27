module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218c

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Subgroup

theorem card_fixE_conj {E : Type} [CommGroup E] (a d : MulAut E) :
    Nat.card (fixE (d * a * d⁻¹)) = Nat.card (fixE a) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (d⁻¹).toEquiv ?_
  intro e
  rw [mem_fixE, mem_fixE]
  simp only [MulAut.mul_apply]
  show d (a (d⁻¹ e)) = e ↔ a (d⁻¹ e) = d⁻¹ e
  constructor
  · intro h
    have := congrArg (fun z => d⁻¹ z) h
    simpa using this
  · intro h
    rw [h]
    simp

section Main

variable {E : Type} [CommGroup E] [Finite E] {X : Subgroup (MulAut E)} {S : Sylow 2 ↥X}

theorem Ctx.free_of_inv (c : Ctx E X S) {x : ↥X} (hx : x ∈ (S : Subgroup ↥X)) (hx1 : x ≠ 1)
    (hcon : ∀ a b : ↥X, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → IsConj a b)
    {s : ↥X} (hs1 : s ≠ 1) (hs2 : s * s = 1) : Nat.card (fixE (s : MulAut E)) = 4 := by
  obtain ⟨d, hd⟩ := isConj_iff.mp (hcon x s hx1 (c.hS2 x hx) hs1 hs2)
  have : (s : MulAut E) = (d : MulAut E) * (x : MulAut E) * (d : MulAut E)⁻¹ := by
    rw [← hd]; rfl
  rw [this, card_fixE_conj]
  exact c.free hx hx1

end Main

theorem sylow_card_prime {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (h1 : p ∣ Nat.card G) (h2 : ¬ p ^ 2 ∣ Nat.card G) : Nat.card P = p := by
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  have hidx := Subgroup.card_mul_index (P : Subgroup G)
  have hnd := P.not_dvd_index
  rw [hk] at hidx
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · exfalso
      apply hnd
      rw [pow_zero, one_mul] at hidx
      rw [hidx]
      exact h1
    · simpa using hk
  · exfalso
    apply h2
    rw [← hidx]
    exact Dvd.dvd.mul_right (pow_dvd_pow p hk2) _

theorem no_Y84 {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    {X : Subgroup (MulAut E)}
    (hfree : ∀ s : ↥X, s ≠ 1 → s * s = 1 → Nat.card (fixE (s : MulAut E)) = 4)
    (Y : Subgroup ↥X) (hY : Nat.card Y = 84) : False := by
  classical
  have h7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 ↥Y) := inferInstance
  have hP7 : Nat.card P = 7 :=
    sylow_card_prime P (by rw [hY]; norm_num) (by rw [hY]; norm_num)
  have hsub : Subsingleton (Sylow 7 ↥Y) := by
    have hmod := card_sylow_modEq_one 7 ↥Y
    have hdvd := P.card_dvd_index
    have hidx := Subgroup.card_mul_index (P : Subgroup ↥Y)
    rw [hP7, hY] at hidx
    have hi : (P : Subgroup ↥Y).index = 12 := by omega
    rw [hi] at hdvd
    have hn : Nat.card (Sylow 7 ↥Y) = 1 := by
      have hmem : Nat.card (Sylow 7 ↥Y) ∈ Nat.divisors 12 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
      rw [h12] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h | h | h <;>
        first | exact h | (rw [h] at hmod; exact absurd hmod (by decide))
    exact (Nat.card_eq_one_iff_unique.mp hn).1
  have hPn : (P : Subgroup ↥Y).Normal := Sylow.normal_of_subsingleton P
  let θ : ↥Y →* MulAut (P : Subgroup ↥Y) := MulAut.conjNormal
  have hcyc : IsCyclic (P : Subgroup ↥Y) := isCyclic_of_prime_card (p := 7) hP7
  have hMA : Nat.card (MulAut (P : Subgroup ↥Y)) = 6 := by
    rw [IsCyclic.card_mulAut, hP7, Nat.totient_prime h7.out]
  have hr : Nat.card θ.range ∣ 6 := hMA ▸ Subgroup.card_subgroup_dvd_card θ.range
  have hprod : Nat.card θ.ker * Nat.card θ.range = 84 := by
    have h1 : Nat.card ↥Y = Nat.card (↥Y ⧸ θ.ker) * Nat.card θ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    have h2' : Nat.card (↥Y ⧸ θ.ker) = Nat.card θ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
    rw [h2', hY] at h1
    rw [h1]; ring
  have hker2 : 2 ∣ Nat.card θ.ker := by
    have hle : Nat.card θ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hr
    interval_cases h : Nat.card θ.range <;> omega
  obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' 2 hker2
  have h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s₁ : ↥Y := (s₀ : ↥Y)
  let s : ↥X := (s₁ : ↥X)
  have hs : orderOf s = 2 := by
    show orderOf ((s₁ : ↥X)) = 2
    rw [Subgroup.orderOf_coe]
    show orderOf (s₀ : ↥Y) = 2
    rw [Subgroup.orderOf_coe]; exact hs₀
  have hs2 : s * s = 1 := by rw [← pow_two]; exact hs ▸ pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hs₁ker : s₁ ∈ θ.ker := s₀.2
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' 7 (show 7 ∣ Nat.card P by rw [hP7])
  let c₁ : ↥Y := (c₀ : ↥Y)
  let cx : ↥X := (c₁ : ↥X)
  have hcx : orderOf cx = 7 := by
    show orderOf ((c₁ : ↥X)) = 7
    rw [Subgroup.orderOf_coe]
    show orderOf (c₀ : ↥Y) = 7
    rw [Subgroup.orderOf_coe]; exact hc₀
  have hcomm₁ : s₁ * c₁ = c₁ * s₁ := by
    have h1 : θ s₁ c₀ = c₀ := by rw [MonoidHom.mem_ker.mp hs₁ker]; rfl
    have h2' : (↑(θ s₁ c₀) : ↥Y) = s₁ * c₁ * s₁⁻¹ := MulAut.conjNormal_apply s₁ c₀
    rw [h1] at h2'
    have h3 : c₁ = s₁ * c₁ * s₁⁻¹ := h2'
    calc s₁ * c₁ = (s₁ * c₁ * s₁⁻¹) * s₁ := by group
      _ = c₁ * s₁ := by rw [← h3]
  have hcomm : cx * s = s * cx := by
    show (c₁ : ↥X) * (s₁ : ↥X) = (s₁ : ↥X) * (c₁ : ↥X)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm₁]
  let σ : MulAut E := (s : MulAut E)
  let g : MulAut E := (cx : MulAut E)
  have hσσ : σ * σ = 1 := congrArg Subtype.val hs2
  have hgs : g * σ = σ * g := congrArg Subtype.val hcomm
  have hg7 : g ^ 7 = 1 := by
    have : cx ^ 7 = 1 := by rw [← hcx]; exact pow_orderOf_eq_one cx
    exact congrArg Subtype.val this
  have hD : Nat.card (fixE σ) = 4 := hfree s hs1 hs2
  obtain ⟨hdvd, hmod⟩ := fix_card_cases σ g hgs 7 hg7 hD
  have hc4 : Nat.card ↥(fixE σ ⊓ fixE g) = 4 := by
    have hmem : Nat.card ↥(fixE σ ⊓ fixE g) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h] at hmod; exact absurd hmod (by decide)
    · rw [h] at hmod; exact absurd hmod (by decide)
    · exact h
  have hle : fixE σ ⊓ fixE g = fixE σ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc4, hD])
  have hfix : ∀ e, σ e = e → g e = e := by
    intro e he
    have : e ∈ fixE σ ⊓ fixE g := by rw [hle]; exact he
    exact (mem_fixE g e).mp this.2
  have hgg := lemmaG h2 σ g hσσ hgs hfix
  have hg1 : g = 1 := by
    have : g ^ 7 = g := by
      calc g ^ 7 = (g * g) ^ 3 * g := by rw [← pow_two, ← pow_mul, ← pow_succ]
        _ = g := by rw [hgg, one_pow, one_mul]
    rw [← this, hg7]
  have hcx1 : cx = 1 := Subtype.ext hg1
  rw [hcx1, orderOf_one] at hcx
  omega

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
