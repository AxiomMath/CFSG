module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step3

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem exists_conj_of_mul_mem {G : Type} [Group G] [Finite G] {N : Subgroup G} {b u u' : G}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbN : b ∈ N)
    (hN : ∀ X : Subgroup G, X ≤ N → IsPGroup 2 X → Nat.card X ≤ 2)
    (hcN : ∀ n ∈ N, n * b = b * n) (hu2 : u * u = 1) (hu'2 : u' * u' = 1)
    (hu'N : u' ∈ normalizer (N : Set G)) (hu'b : u' * b = b * u') (hmem : u'⁻¹ * u ∈ N)
    (hu'n : u' ∉ N) (hu1 : u ≠ 1) (hub : u ≠ b) :
    ∃ y : G, y * u * y⁻¹ = u' ∨ y * u * y⁻¹ = u' * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := N ⊔ zpowers u' with hY
  have hcases : ∀ y ∈ Y, y ∈ N ∨ ∃ n ∈ N, y = n * u' := by
    intro y hy
    have hy' : y ∈ ((Y : Subgroup G) : Set G) := hy
    rw [hY, coe_mul_of_right_le_normalizer_left N (zpowers u') (zpowers_le.mpr hu'N)] at hy'
    obtain ⟨n, hn, w, hw, hnw⟩ := hy'
    beta_reduce at hnw
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hu'2 hw with rfl | rfl
    · left; rw [← hnw, mul_one]; exact hn
    · right; exact ⟨n, hn, hnw.symm⟩
  have hbY : ∀ y ∈ Y, y * b = b * y := by
    intro y hy
    rcases hcases y hy with h1 | ⟨n, hn, rfl⟩
    · exact hcN y h1
    · rw [mul_assoc, hu'b, ← mul_assoc, hcN n hn, mul_assoc]
  have hmax : ∀ X : Subgroup G, X ≤ Y → IsPGroup 2 X → Nat.card X ≤ 4 := by
    intro X hXY hX
    have h1 := Eight.card_le_two_mul_card_inf (A := X) (K := N) fun y hy y' hy' hyN hy'N => by
      rcases hcases y (hXY hy) with h | ⟨n, hn, rfl⟩
      · exact absurd h hyN
      rcases hcases y' (hXY hy') with h | ⟨n', hn', rfl⟩
      · exact absurd h hy'N
      have h2 := (mem_normalizer_iff.mp (inv_mem hu'N) (n⁻¹ * n')).mp (mul_mem (inv_mem hn) hn')
      rwa [show (n * u')⁻¹ * (n' * u') = u'⁻¹ * (n⁻¹ * n') * u'⁻¹⁻¹ by group]
    have h2 := hN (X ⊓ N) inf_le_right (hX.to_le inf_le_left)
    omega
  have hu'1 : u' ≠ 1 := fun h1 => hu'n (h1 ▸ one_mem N)
  have hu'b' : u' ≠ b := fun h1 => hu'n (h1 ▸ hbN)
  have hub' : u * b = b * u := by
    have hn := hcN _ hmem
    calc u * b = u' * ((u'⁻¹ * u) * b) := by group
      _ = u' * (b * (u'⁻¹ * u)) := by rw [hn]
      _ = (u' * b) * (u'⁻¹ * u) := by group
      _ = b * u := by rw [hu'b]; group
  obtain ⟨hc₁, -⟩ := card_sup_zpowers_of_inv hu'2 hb2 hu'1 hb1 hu'b' hu'b
  obtain ⟨hc₂, -⟩ := card_sup_zpowers_of_inv hu2 hb2 hu1 hb1 hub hub'
  have huY : u ∈ Y := by
    rw [show u = u' * (u'⁻¹ * u) by group]
    exact mul_mem (mem_sup_right (mem_zpowers u')) (mem_sup_left hmem)
  have hE₁Y : zpowers u' ⊔ zpowers b ≤ Y :=
    sup_le le_sup_right ((zpowers_le.mpr hbN).trans le_sup_left)
  have hE₂Y : zpowers u ⊔ zpowers b ≤ Y :=
    sup_le (zpowers_le.mpr huY) ((zpowers_le.mpr hbN).trans le_sup_left)
  have hE₁2 : IsPGroup 2 ↥(zpowers u' ⊔ zpowers b) :=
    IsPGroup.of_card (n := 2) (by rw [hc₁]; norm_num)
  have hE₂2 : IsPGroup 2 ↥(zpowers u ⊔ zpowers b) :=
    IsPGroup.of_card (n := 2) (by rw [hc₂]; norm_num)
  have hS := sylow_of_card_ge hE₁Y hE₁2 fun A hAY hA => (hmax A hAY hA).trans hc₁.ge
  obtain ⟨l, hlY, hl⟩ := exists_conjugate_le_of_sylow hS hE₂Y hE₂2
  have hlu : l⁻¹ * u * l ∈ zpowers u' ⊔ zpowers b := by
    refine hl ?_
    rw [mem_conjugate_iff, show l * (l⁻¹ * u * l) * l⁻¹ = u by group]
    exact mem_sup_left (mem_zpowers u)
  have hcomm : ∀ x ∈ zpowers u', ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hu'b i j).eq
  obtain ⟨x, hx, w, hw, hxw⟩ := Eight.exists_mul_of_mem_sup₂ hcomm hlu
  have hlb : l⁻¹ * b * l = b := by
    rw [mul_assoc, ← hbY l hlY, inv_mul_cancel_left]
  refine ⟨l⁻¹, ?_⟩
  rw [inv_inv]
  rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hu'2 hx with hx1 | hx1 <;>
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hb2 hw with hw1 | hw1 <;>
    rw [hx1, hw1] at hxw
  · exfalso; apply hu1
    calc u = l * (l⁻¹ * u * l) * l⁻¹ := by group
      _ = 1 := by rw [hxw]; group
  · exfalso; apply hub
    calc u = l * (l⁻¹ * u * l) * l⁻¹ := by group
      _ = l * (l⁻¹ * b * l) * l⁻¹ := by rw [hxw, hlb, one_mul]
      _ = b := by group
  · left; rw [hxw, mul_one]
  · right; exact hxw

theorem exists_cycle_pow_two_pow {G : Type*} [Group G] {θ e₁ e₂ : G}
    (h1 : θ * e₁ * θ⁻¹ = e₂) (h2 : θ * e₂ * θ⁻¹ = e₁ * e₂) (he₁ : e₁ * e₁ = 1)
    (he₂ : e₂ * e₂ = 1) (hc : e₁ * e₂ = e₂ * e₁) (m : ℕ) :
    ∃ f : G, (f = e₂ ∨ f = e₁ * e₂) ∧ θ ^ 2 ^ m * e₁ * (θ ^ 2 ^ m)⁻¹ = f ∧
      θ ^ 2 ^ m * f * (θ ^ 2 ^ m)⁻¹ = e₁ * f := by
  induction m with
  | zero => exact ⟨e₂, Or.inl rfl, by simpa using h1, by simpa using h2⟩
  | succ m ih =>
    obtain ⟨f, hf, hf1, hf2⟩ := ih
    set ψ := θ ^ 2 ^ m with hψ
    have hsq : θ ^ 2 ^ (m + 1) = ψ * ψ := by rw [pow_succ, pow_mul, sq]
    have hff : f * f = 1 ∧ e₁ * f = f * e₁ := by
      rcases hf with rfl | rfl
      · exact ⟨he₂, hc⟩
      · refine ⟨?_, ?_⟩
        · rw [show e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ by group, ← hc,
            show e₁ * (e₁ * e₂) * e₂ = (e₁ * e₁) * (e₂ * e₂) by group, he₁, he₂, one_mul]
        · rw [mul_assoc e₁ e₂ e₁, ← hc]
    refine ⟨e₁ * f, ?_, ?_, ?_⟩
    · rcases hf with rfl | rfl
      · exact Or.inr rfl
      · left; rw [← mul_assoc, he₁, one_mul]
    · rw [hsq, mul_inv_rev, show ψ * ψ * e₁ * (ψ⁻¹ * ψ⁻¹) = ψ * (ψ * e₁ * ψ⁻¹) * ψ⁻¹ by group,
        hf1, hf2]
    · rw [hsq, mul_inv_rev]
      have h3 : ψ * (e₁ * f) * ψ⁻¹ = f * (e₁ * f) := by
        rw [show ψ * (e₁ * f) * ψ⁻¹ = (ψ * e₁ * ψ⁻¹) * (ψ * f * ψ⁻¹) by group, hf1, hf2]
      have h4 : f * (e₁ * f) = e₁ := by
        rw [← mul_assoc, ← hff.2, mul_assoc, hff.1, mul_one]
      rw [show ψ * ψ * (e₁ * f) * (ψ⁻¹ * ψ⁻¹) = ψ * (ψ * (e₁ * f) * ψ⁻¹) * ψ⁻¹ by group, h3, h4,
        hf1, ← mul_assoc, he₁, one_mul]

theorem exists_odd_orderOf_pow {G : Type*} [Group G] [Finite G] (θ : G) :
    ∃ m : ℕ, Odd (orderOf (θ ^ 2 ^ m)) := by
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos θ).ne'
  refine ⟨k, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨r, hkr⟩, hkr,
    Nat.mul_div_cancel_left r (pow_pos two_pos k)]
  exact hr

theorem pow_eq_one_of_odd {x : Equiv.Perm (Fin 8)} (hx : Odd (orderOf x)) : x ^ 315 = 1 := by
  have h1 : orderOf x ∣ 2 ^ 7 * 315 := by
    have := orderOf_dvd_card (x := x)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  exact orderOf_dvd_iff_pow_eq_one.mp
    ((Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hx)).dvd_of_dvd_mul_left h1)

end CFSG.ComponentClassification.GSThmB.A8
