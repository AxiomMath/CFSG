module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2YKey

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

section Three

variable {Y : Type} [Group Y] [Finite Y] {Sb Rb L₁ L₂ : Subgroup Y} {r₁ r₂ : ℕ}

omit [Finite Y] in
theorem Pair.mem_inf_of_sq_left {Lk Lk' : Subgroup Y} {r r' : ℕ} (h : Pair Lk Lk' r r') {a : Y}
    (ha : a ∈ Lk) (ha2 : a * a = 1) : a ∈ Lk ⊓ Lk' := by
  by_cases ha1 : a = 1
  · rw [ha1]; exact (Lk ⊓ Lk').one_mem
  · obtain ⟨-, huniq⟩ := sl2_model_center_inv h.odd h.hm
    have hne : ∃ w ∈ Lk ⊓ Lk', w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card ↥(Lk ⊓ Lk') = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨1⟩⟩
        rw [hcon x x.2, hcon y y.2]
      rw [h.inf] at this
      omega
    obtain ⟨w, hw, hw1⟩ := hne
    have hww : w * w = 1 := h.sq_of_mem_inf hw
    have ho : ∀ x : Y, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
      orderOf_eq_prime (by rw [← sq] at hx; exact hx) hx1
    have := huniq a ha w hw.1 (ho a ha2 ha1) (ho w hww hw1)
    rw [this]
    exact hw


theorem ykey_three (f₁ : Factor Sb Rb L₁ L₂ r₁ 3) (hn₂ : L₂.Normal)
    {Wb : Subgroup Y} (hWbn : Wb.Normal) (hWbL : Wb ≤ L₂) (hWbc : Nat.card ↥Wb = 8)
    (hW4 : ∀ x ∈ L₂, x ^ 4 = 1 → x ∈ Wb) (hF : generalizedFitting Y ≤ L₁ ⊔ Wb)
    {t e : Y} (ht : t ∈ L₁ ⊔ L₂) (ht2 : t * t = 1) (htI : t ∉ L₁ ⊓ L₂)
    (he2 : e * e = 1) (het : e * t = t * e) (heI : e ∉ L₁ ⊓ L₂) (hetI : e * t ∉ L₁ ⊓ L₂)
    {Bb : Subgroup Y} (hBodd : Odd (Nat.card ↥Bb)) (hBt : ∀ b ∈ Bb, b * t = t * b)
    (hBn : ∀ m : Y, m * t = t * m → ∀ b ∈ Bb, m * b * m⁻¹ ∈ Bb)
    (hBe : ∀ b ∈ Bb, e * b = b * e) : Bb = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ : L₁.Normal := f₁.normal
  have p₁ := f₁.toPair
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := p₁.exists_mul ht
  have hc12 : a₁ * a₂ = a₂ * a₁ := p₁.comm a₁ ha₁ a₂ ha₂
  have hprod : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hc12]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := ht2
  have hI : a₁ * a₁ ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.mul_mem ha₁ ha₁, ?_⟩
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this]; exact L₂.inv_mem (L₂.mul_mem ha₂ ha₂)
  have hsq : a₁ * a₁ = a₂ * a₂ := by
    have h1 := p₁.sq_of_mem_inf hI
    have : a₂ * a₂ = (a₁ * a₁)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [this]; exact (inv_eq_of_mul_eq_one_right h1).symm
  have ha₁2 : a₁ * a₁ ≠ 1 := by
    intro h1
    apply htI
    have h2 : a₂ * a₂ = 1 := by rw [← hsq]; exact h1
    have h3 : a₂ ∈ L₁ ⊓ L₂ := p₁.mem_inf_of_sq ha₂ h2
    have h4 : a₁ ∈ L₁ ⊓ L₂ := p₁.mem_inf_of_sq_left ha₁ h1
    exact (L₁ ⊓ L₂).mul_mem h4 h3
  have ha₂2 : a₂ * a₂ ≠ 1 := by rw [← hsq]; exact ha₁2
  have hsq₁ : ∀ c ∈ L₁, c * (a₁ * a₁) = (a₁ * a₁) * c := fun c hc => p₁.comm c hc _ hI.2
  have hcen : ∀ m ∈ centralizer ({a₁ * a₂} : Set Y), m * (a₁ * a₂) = (a₁ * a₂) * m := fun m hm =>
    (Subgroup.mem_centralizer_iff.1 hm _ rfl).symm
  obtain ⟨W, hWB, hWne, hWab, hWn⟩ := exists_abelian_normalized hBodd hne
    (centralizer ({a₁ * a₂} : Set Y)) (fun m hm b hb => hBn m (hcen m hm) b hb)
  have hWM : W ≤ centralizer ({a₁ * a₂} : Set Y) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hBt w (hWB hw)).symm
  have hWodd : Odd (Nat.card ↥W) := hBodd.of_dvd_nat (Subgroup.card_dvd_of_le hWB)
  have hkM : ∀ {k : Y}, (k * (a₁ * a₂) = (a₁ * a₂) * k) → k ∈ centralizer ({a₁ * a₂} : Set Y) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hk.symm
  have hfit₁ := fit_factor (Lk := L₁) (r := r₁) p₁.odd p₁.gt p₁.hm ha₁ ha₁2 hsq₁
    (centralizer ({a₁ * a₂} : Set Y))
    (fun m hm c hc => p₁.comm c hc _ (p₁.conj_div_mem hn₁ hn₂ ha₁ ha₂ (hcen m hm)))
    W hWM hWodd hWab
    (fun k hk _ hka => ⟨k, hkM (p₁.comm_prod ha₂ hk hka), fun x _ => rfl,
      fun w hw => hWn k (hkM (p₁.comm_prod ha₂ hk hka)) w hw⟩)
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hWne (eq_bot_iff.2 fun x hx => by simpa using hcon x hx)
  obtain ⟨k₁, hk₁, hk₁o, hk₁a, hk₁act⟩ := hfit₁ w hwW
  have hr₁ : e * k₁ * e⁻¹ = k₁⁻¹ :=
    f₁.reflect' hn₂ ha₁ ha₂ ha₁2 hsq₁ hsq.symm he2 het heI hetI k₁ hk₁ hk₁o hk₁a
  have hwt : w * (a₁ * a₂) = (a₁ * a₂) * w := hBt w (hWB hwW)
  have hwa₁ : w * a₁ = a₁ * w := by
    have h1 := hk₁act a₁ ha₁
    have h2 : k₁ * a₁ * k₁⁻¹ = a₁ := by rw [hk₁a]; group
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hwa₂ : w * a₂ = a₂ * w := by
    have h1 : a₁ * (w * a₂) = a₁ * (a₂ * w) := by
      calc a₁ * (w * a₂) = (a₁ * w) * a₂ := by group
        _ = (w * a₁) * a₂ := by rw [hwa₁]
        _ = w * (a₁ * a₂) := by group
        _ = (a₁ * a₂) * w := hwt
        _ = a₁ * (a₂ * w) := by group
    exact mul_left_cancel h1
  have hwa₂' : w * a₂ * w⁻¹ = a₂ := mul_inv_eq_iff_eq_mul.2 hwa₂
  have ha₂4 : a₂ ^ 4 = 1 := by
    have : a₂ ^ 4 = (a₂ * a₂) * (a₂ * a₂) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, ← hsq]; exact p₁.sq_of_mem_inf hI
  have ha₂W : a₂ ∈ Wb := hW4 a₂ ha₂ ha₂4
  have ha₂ord : orderOf a₂ = 4 := by
    have h1 : orderOf a₂ = 2 ^ (1 + 1) := orderOf_eq_prime_pow (p := 2) (n := 1)
      (by intro h; apply ha₂2; simpa [pow_two] using h) (by norm_num; exact ha₂4)
    simpa using h1
  have hwodd : Odd (orderOf w) := hBodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Bb (hWB hwW))
  have hfix := fixes_of_odd_of_card_eight hWbc ha₂W ha₂ord hwodd
    (fun x hx => hWbn.conj_mem x hx w) hwa₂'
  have hwk₁ : w * k₁ * w⁻¹ = k₁ := by rw [hk₁act k₁ hk₁]; group
  have hwk₁' : w * k₁ = k₁ * w := mul_inv_eq_iff_eq_mul.1 hwk₁
  set u := k₁⁻¹ * w with hu
  have hu1 : ∀ x ∈ L₁, u * x = x * u := by
    intro x hx
    have h1 := hk₁act x hx
    have h3 : w * x = k₁ * x * k₁⁻¹ * w := by
      calc w * x = (w * x * w⁻¹) * w := by group
        _ = k₁ * x * k₁⁻¹ * w := by rw [h1]
    calc k₁⁻¹ * w * x = k₁⁻¹ * (w * x) := by group
      _ = k₁⁻¹ * (k₁ * x * k₁⁻¹ * w) := by rw [h3]
      _ = x * (k₁⁻¹ * w) := by group
  have hu2 : ∀ x ∈ Wb, u * x = x * u := by
    intro x hx
    have h1 : w * x = x * w := mul_inv_eq_iff_eq_mul.1 (hfix x hx)
    have h2 : k₁⁻¹ * x = x * k₁⁻¹ :=
      (Commute.inv_left (show Commute k₁ x from p₁.comm k₁ hk₁ x (hWbL hx))).eq
    calc k₁⁻¹ * w * x = k₁⁻¹ * (w * x) := by group
      _ = k₁⁻¹ * (x * w) := by rw [h1]
      _ = (k₁⁻¹ * x) * w := by group
      _ = (x * k₁⁻¹) * w := by rw [h2]
      _ = x * (k₁⁻¹ * w) := by group
  have hLW : ∀ a ∈ L₁, ∀ b ∈ Wb, a * b = b * a := fun a ha b hb => p₁.comm a ha b (hWbL hb)
  have hucen : u ∈ centralizer ((L₁ ⊔ Wb : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := L26.exists_mul_of_mem_sup_of_commute hLW hx
    calc x₁ * x₂ * u = x₁ * (x₂ * u) := by group
      _ = x₁ * (u * x₂) := by rw [← hu2 x₂ hx₂]
      _ = (x₁ * u) * x₂ := by group
      _ = (u * x₁) * x₂ := by rw [← hu1 x₁ hx₁]
      _ = u * (x₁ * x₂) := by group
  have huF : u ∈ generalizedFitting Y :=
    CFSG.centralizer_generalizedFitting_le Y (Subgroup.centralizer_le hF hucen)
  have huLW : u ∈ L₁ ⊔ Wb := hF huF
  obtain ⟨l, hl, b, hb, hulb⟩ := L26.exists_mul_of_mem_sup_of_commute hLW huLW
  have hlcen : ∀ c ∈ L₁, c * l = l * c := by
    intro c hc
    have h1 : l = u * b⁻¹ := by rw [hulb]; group
    have hb' : Commute c b⁻¹ := Commute.inv_right (show Commute c b from hLW c hc b hb)
    calc c * l = c * (u * b⁻¹) := by rw [← h1]
      _ = (c * u) * b⁻¹ := by group
      _ = (u * c) * b⁻¹ := by rw [← hu1 c hc]
      _ = u * (c * b⁻¹) := by group
      _ = u * (b⁻¹ * c) := by rw [hb'.eq]
      _ = (u * b⁻¹) * c := by group
      _ = l * c := by rw [← h1]
  have hlI : l ∈ L₁ ⊓ L₂ := ⟨hl, p₁.cen hl hlcen⟩
  have hlW : l ∈ Wb := by
    rcases p₁.inf_cases hI ha₁2 hlI with h | h
    · rw [h]; exact Wb.one_mem
    · rw [h, hsq]; exact Wb.mul_mem ha₂W ha₂W
  have huW : u ∈ Wb := by rw [hulb]; exact Wb.mul_mem hlW hb
  have huo : Odd (orderOf u) := by
    refine odd_orderOf_mul_of_commute (Commute.inv_left (show Commute k₁ w from hwk₁'.symm)) ?_ hwodd
    rw [orderOf_inv]; exact hk₁o
  have hu_one : u = 1 := by
    have h1 : orderOf u ∣ 8 := hWbc ▸ Subgroup.orderOf_dvd_natCard Wb huW
    have h2 : Nat.Coprime (orderOf u) (2 ^ 3) := (Nat.coprime_two_right.2 huo).pow_right 3
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h2 (by simpa using h1))
  have hwk : w = k₁ := (inv_mul_eq_one.1 hu_one).symm
  have hew : e * w = w * e := hBe w (hWB hwW)
  have hk₁sq : k₁ * k₁ = 1 := by
    have h1 : e * k₁ * e⁻¹ = k₁ := by rw [← hwk, hew]; group
    rw [h1] at hr₁
    exact mul_eq_one_iff_eq_inv.2 hr₁
  exact hw1 (hwk.trans (eq_one_of_mul_self_of_odd hk₁sq hk₁o))

end Three

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
