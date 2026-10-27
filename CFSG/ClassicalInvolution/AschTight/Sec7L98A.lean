module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem eq_one_of_sq_of_pow_odd {d : G} (hd : d * d = 1) {m : ℕ} (hm : Odd m)
    (hdm : d ^ m = 1) : d = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : d ^ 2 = 1 := by rw [pow_two]; exact hd
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hdm
  exact hdm

theorem conj_eq_of_odd {A : Subgroup G} (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : IsPGroup 2 A) {g : G} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hg : Odd (orderOf g))
    (h1 : ∀ a ∈ A, a * a = 1 → g * a * g⁻¹ = a) : ∀ a ∈ A, g * a * g⁻¹ = a := by
  have key : ∀ n : ℕ, ∀ a ∈ A, a ^ (2 ^ n) = 1 → g * a * g⁻¹ = a := by
    intro n
    induction n with
    | zero =>
      intro a _ ha
      rw [pow_zero, pow_one] at ha
      rw [ha]
      group
    | succ n ih =>
      intro a haA ha
      have ha2 : g * (a * a) * g⁻¹ = a * a := by
        refine ih (a * a) (A.mul_mem haA haA) ?_
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact ha
      have ha'A : g * a * g⁻¹ ∈ A := hgA a haA
      have hsq : (g * a * g⁻¹) * (g * a * g⁻¹) = a * a := by
        calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = a * a := ha2
      have hdA : g * a * g⁻¹ * a⁻¹ ∈ A := A.mul_mem ha'A (A.inv_mem haA)
      have hd2 : (g * a * g⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) = 1 := by
        have hc : a⁻¹ * (g * a * g⁻¹) = (g * a * g⁻¹) * a⁻¹ := hAab _ (A.inv_mem haA) _ ha'A
        calc (g * a * g⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹)
            = (g * a * g⁻¹) * (a⁻¹ * (g * a * g⁻¹)) * a⁻¹ := by group
          _ = (g * a * g⁻¹) * ((g * a * g⁻¹) * a⁻¹) * a⁻¹ := by rw [hc]
          _ = ((g * a * g⁻¹) * (g * a * g⁻¹)) * (a * a)⁻¹ := by group
          _ = 1 := by rw [hsq, mul_inv_cancel]
      set d := g * a * g⁻¹ * a⁻¹ with hd
      have hgd : g * d * g⁻¹ = d := h1 d hdA hd2
      have hda : g * a * g⁻¹ = d * a := by rw [hd]; group
      have hpow : ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = d ^ k * a := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
                rw [pow_succ']; group
            _ = g * (d ^ k * a) * g⁻¹ := by rw [ihk]
            _ = (g * d * g⁻¹) ^ k * (g * a * g⁻¹) := by rw [conj_pow]; group
            _ = d ^ k * (d * a) := by rw [hgd, hda]
            _ = d ^ (k + 1) * a := by rw [pow_succ]; group
      have hm := hpow (orderOf g)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
      have hdm : d ^ orderOf g = 1 := by
        have h' : d ^ orderOf g * a * a⁻¹ = a * a⁻¹ := by rw [← hm]
        simpa using h'
      have hd1 : d = 1 := eq_one_of_sq_of_pow_odd hd2 hg hdm
      rw [hda, hd1, one_mul]
  intro a ha
  obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
  refine key n a ha ?_
  have := congrArg Subtype.val hn
  simpa using this

theorem exists_mul_conj_inv_eq [Finite G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {b : G} (hbA : ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hfp : ∀ a ∈ A, b * a * b⁻¹ = a → a = 1) :
    ∀ w ∈ A, ∃ w' ∈ A, w' * (b * w' * b⁻¹)⁻¹ = w := by
  let f : ↥A → ↥A := fun x => ⟨(x : G) * (b * x * b⁻¹)⁻¹,
    A.mul_mem x.2 (A.inv_mem (hbA x x.2))⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (x : G) * (b * x * b⁻¹)⁻¹ = (y : G) * (b * y * b⁻¹)⁻¹ := congrArg Subtype.val hxy
    have hyx : (y : G)⁻¹ * x ∈ A := A.mul_mem (A.inv_mem y.2) x.2
    have hfix : b * ((y : G)⁻¹ * x) * b⁻¹ = (y : G)⁻¹ * x := by
      have hc1 : (b * x * b⁻¹) * (y : G)⁻¹ = (y : G)⁻¹ * (b * x * b⁻¹) :=
        hAab _ (hbA x x.2) _ (A.inv_mem y.2)
      have h2 : (y : G)⁻¹ * x = (b * y * b⁻¹)⁻¹ * (b * x * b⁻¹) := by
        have h3 : (y : G)⁻¹ * ((y : G) * (b * y * b⁻¹)⁻¹) * (b * x * b⁻¹) =
            (y : G)⁻¹ * ((x : G) * (b * x * b⁻¹)⁻¹) * (b * x * b⁻¹) := by rw [h]
        have h4 : (y : G)⁻¹ * ((x : G) * (b * x * b⁻¹)⁻¹) * (b * x * b⁻¹) =
            (y : G)⁻¹ * x := by group
        rw [h4] at h3
        rw [← h3]
        group
      calc b * ((y : G)⁻¹ * x) * b⁻¹ = (b * y * b⁻¹)⁻¹ * (b * x * b⁻¹) := by group
        _ = (y : G)⁻¹ * x := h2.symm
    have h1 := hfp _ hyx hfix
    apply Subtype.ext
    have : (x : G) = y * ((y : G)⁻¹ * x) := by group
    rw [this, h1, mul_one]
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨x, hx⟩ := hsurj ⟨w, hw⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem exists_fixed_mul_of_odd [Finite G] {H O : Subgroup G} (hH : IsPGroup 2 H)
    (hO : Odd (Nat.card O)) (hHO : H ≤ Subgroup.normalizer (O : Set G)) {b : G}
    (hb : ∀ h ∈ H, b⁻¹ * (h * b * h⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ h ∈ H, h * (b * o) * h⁻¹ = b * o := by
  let _inst : MulAction ↥H ↥O :=
    { smul := fun h o => ⟨b⁻¹ * ((h : G) * b * (h : G)⁻¹) * ((h : G) * o * (h : G)⁻¹),
        O.mul_mem (hb h h.2) ((Subgroup.mem_normalizer_iff.mp (hHO h.2) o).mp o.2)⟩
      one_smul := fun o => by
        apply Subtype.ext
        change b⁻¹ * ((1 : G) * b * (1 : G)⁻¹) * ((1 : G) * o * (1 : G)⁻¹) = o
        group
      mul_smul := fun h₁ h₂ o => by
        apply Subtype.ext
        change b⁻¹ * (((h₁ : G) * h₂) * b * ((h₁ : G) * h₂)⁻¹) *
            (((h₁ : G) * h₂) * o * ((h₁ : G) * h₂)⁻¹) =
          b⁻¹ * ((h₁ : G) * b * (h₁ : G)⁻¹) * ((h₁ : G) *
            (b⁻¹ * ((h₂ : G) * b * (h₂ : G)⁻¹) * ((h₂ : G) * o * (h₂ : G)⁻¹)) * (h₁ : G)⁻¹)
        group }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := hH.card_modEq_card_fixedPoints (↥O)
  have h0 : Nat.card ↑(MulAction.fixedPoints ↥H ↥O) ≠ 0 := by
    intro h0
    rw [h0] at hcard
    have h1 : Nat.card ↥O % 2 = 0 := hcard
    obtain ⟨k, hk⟩ := hO
    omega
  obtain ⟨⟨o, ho⟩⟩ := (Nat.card_ne_zero.mp h0).1
  refine ⟨o, o.2, fun h hh => ?_⟩
  have h1 : (⟨h, hh⟩ : ↥H) • o = o := ho ⟨h, hh⟩
  have hval : b⁻¹ * (h * b * h⁻¹) * (h * (o : G) * h⁻¹) = o := congrArg Subtype.val h1
  calc h * (b * o) * h⁻¹ = b * (b⁻¹ * (h * b * h⁻¹) * (h * (o : G) * h⁻¹)) := by group
    _ = b * o := by rw [hval]

theorem mem_of_dihedral {A D : Subgroup G}
    (hDA : ∀ d ∈ D, d ∉ A → ∀ w ∈ A, d * w * d⁻¹ = w⁻¹) {w₀ : G} (hw₀ : w₀ ∈ A)
    (hw₀2 : w₀ * w₀ ≠ 1) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a * b = b * a)
    (hb2 : b * b ≠ 1) (hab2 : (a * b) * (a * b) ≠ 1) : a ∈ A := by
  by_contra haA
  by_cases hbA : b ∈ A
  · have h1 := hDA a ha haA b hbA
    have h2 : a * b * a⁻¹ = b := by rw [hab]; group
    rw [h2] at h1
    apply hb2
    calc b * b = b * b⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel b
  · have habD : a * b ∈ D := D.mul_mem ha hb
    have hcent : ∀ w ∈ A, (a * b) * w * (a * b)⁻¹ = w := by
      intro w hw
      have h1 := hDA b hb hbA w hw
      have h2 := hDA a ha haA (w⁻¹) (A.inv_mem hw)
      calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
        _ = a * w⁻¹ * a⁻¹ := by rw [h1]
        _ = w⁻¹⁻¹ := h2
        _ = w := inv_inv w
    have habA : a * b ∈ A := by
      by_contra habA
      have h3 := hDA _ habD habA w₀ hw₀
      rw [hcent w₀ hw₀] at h3
      apply hw₀2
      calc w₀ * w₀ = w₀ * w₀⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel w₀
    have h4 := hDA a ha haA _ habA
    have h5 : a * (a * b) * a⁻¹ = a * b := by
      calc a * (a * b) * a⁻¹ = a * (b * a) * a⁻¹ := by rw [hab]
        _ = a * b := by group
    rw [h5] at h4
    apply hab2
    calc (a * b) * (a * b) = (a * b) * (a * b)⁻¹ := by rw [← h4]
      _ = 1 := mul_inv_cancel _

theorem eq_inv_of_conj_mul {A : Subgroup G} {b x c : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) (hbo : Odd (orderOf b))
    (hxc : b⁻¹ * x * b = x * c) (hc : ∀ w ∈ A, c * w * c⁻¹ = w⁻¹) : ∀ w ∈ A, w = w⁻¹ := by
  have key : ∀ k : ℕ, ∀ w ∈ A, ((b ^ k)⁻¹ * x * b ^ k) * w * ((b ^ k)⁻¹ * x * b ^ k)⁻¹ =
      x * w ^ ((-1 : ℤ) ^ k) * x⁻¹ := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hbw : b * w * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hb w).mp hw
      have e1 : (b ^ (k + 1))⁻¹ * x * b ^ (k + 1) = b⁻¹ * ((b ^ k)⁻¹ * x * b ^ k) * b := by
        rw [pow_succ]; group
      rw [e1]
      calc b⁻¹ * ((b ^ k)⁻¹ * x * b ^ k) * b * w * (b⁻¹ * ((b ^ k)⁻¹ * x * b ^ k) * b)⁻¹
          = b⁻¹ * (((b ^ k)⁻¹ * x * b ^ k) * (b * w * b⁻¹) *
              ((b ^ k)⁻¹ * x * b ^ k)⁻¹) * b := by group
        _ = b⁻¹ * (x * (b * w * b⁻¹) ^ ((-1 : ℤ) ^ k) * x⁻¹) * b := by rw [ih _ hbw]
        _ = (b⁻¹ * x * b) * w ^ ((-1 : ℤ) ^ k) * (b⁻¹ * x * b)⁻¹ := by rw [conj_zpow]; group
        _ = (x * c) * w ^ ((-1 : ℤ) ^ k) * (x * c)⁻¹ := by rw [hxc]
        _ = x * (c * w ^ ((-1 : ℤ) ^ k) * c⁻¹) * x⁻¹ := by group
        _ = x * (c * w * c⁻¹) ^ ((-1 : ℤ) ^ k) * x⁻¹ := by rw [conj_zpow]
        _ = x * (w⁻¹) ^ ((-1 : ℤ) ^ k) * x⁻¹ := by rw [hc w hw]
        _ = x * w ^ ((-1 : ℤ) ^ (k + 1)) * x⁻¹ := by rw [inv_zpow', pow_succ, mul_neg_one]
  intro w hw
  have h := key (orderOf b) w hw
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one, Odd.neg_one_pow hbo, zpow_neg,
    zpow_one] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem eq_inv_of_conj_inv {A : Subgroup G} {b g : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) (hbo : Odd (orderOf b))
    (hinv : ∀ w ∈ A, (g * b * g⁻¹ * b) * w * (g * b * g⁻¹ * b)⁻¹ = w⁻¹) :
    ∀ w ∈ A, w = w⁻¹ := by
  have hbi : b⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hb
  obtain ⟨y, hyd⟩ : ∃ y : G, g * b * g⁻¹ = y := ⟨_, rfl⟩
  have hy : ∀ w ∈ A, y * w * y⁻¹ = (b⁻¹ * w * b)⁻¹ := by
    intro w hw
    have hw' : b⁻¹ * w * b ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp hbi w).mp hw
      rwa [inv_inv] at this
    have h1 := hinv _ hw'
    rw [hyd] at h1
    calc y * w * y⁻¹ = (y * b) * (b⁻¹ * w * b) * (y * b)⁻¹ := by group
      _ = (b⁻¹ * w * b)⁻¹ := h1
  have hpowA : ∀ k : ℕ, ∀ w ∈ A, (b ^ k)⁻¹ * w * b ^ k ∈ A := by
    intro k w hw
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hbi k) w).mp hw
    rwa [inv_pow, inv_inv] at this
  have key : ∀ k : ℕ, ∀ w ∈ A, y ^ k * w * (y ^ k)⁻¹ =
      ((b ^ k)⁻¹ * w * b ^ k) ^ ((-1 : ℤ) ^ k) := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      calc y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = y * ((b ^ k)⁻¹ * w * b ^ k) ^ ((-1 : ℤ) ^ k) * y⁻¹ := by rw [ih w hw]
        _ = (y * ((b ^ k)⁻¹ * w * b ^ k) * y⁻¹) ^ ((-1 : ℤ) ^ k) := by rw [conj_zpow]
        _ = ((b⁻¹ * ((b ^ k)⁻¹ * w * b ^ k) * b)⁻¹) ^ ((-1 : ℤ) ^ k) := by
              rw [hy _ (hpowA k w hw)]
        _ = ((b ^ (k + 1))⁻¹ * w * b ^ (k + 1)) ^ ((-1 : ℤ) ^ (k + 1)) := by
              rw [inv_zpow', pow_succ (-1 : ℤ), mul_neg_one, pow_succ b]
              congr 1
              group
  intro w hw
  have h := key (orderOf b) w hw
  have hy1 : y ^ orderOf b = 1 := by
    rw [← hyd, conj_pow, pow_orderOf_eq_one]; group
  simp only [hy1, pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h
  rw [Odd.neg_one_pow hbo, zpow_neg, zpow_one] at h
  exact h

theorem isSylow2In_sup_of_sylow [Finite G] {N C Q V : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hQ : IsSylow2In Q N) (hV : IsSylow2In V C)
    (hVQ : V ≤ Subgroup.normalizer (Q : Set G)) (hVN : V ⊓ N ≤ Q) :
    IsSylow2In (Q ⊔ V) (N ⊔ C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQV2 : IsPGroup 2 ↥(Q ⊔ V) := IsPGroup.to_sup_of_normal_left' hQ.2.1 hV.2.1 hVQ
  refine ⟨sup_le (hQ.1.trans le_sup_left) (hV.1.trans le_sup_right), hQV2,
    fun T hT hT2 hle => ?_⟩
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hT.trans (sup_le Subgroup.le_normalizer hCN)
  have e1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hTN
  have e2 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hCN
  have e3 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hVQ
  have hdvd : Nat.card ↥(T ⊔ N) ∣ Nat.card ↥(C ⊔ N) :=
    Subgroup.card_dvd_of_le (sup_le (hT.trans (by rw [sup_comm])) le_sup_right)
  have hTNle : Nat.card ↥(T ⊓ N) ≤ Nat.card Q := hQ.natCard_le (hT2.to_le inf_le_left) inf_le_right
  have hVNeq : V ⊓ Q = V ⊓ N := le_antisymm (inf_le_inf_left V hQ.1) (le_inf inf_le_left hVN)
  rw [hVNeq] at e3
  have hVC := AscL62.natCard_eq_pow_of_isSylow2In hV
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  set m := Nat.card C / 2 ^ (Nat.card C).factorization 2 with hm
  have hCm : Nat.card C = Nat.card V * m := by
    rw [hVC, hm]; exact (Nat.ordProj_mul_ordCompl_eq_self (Nat.card C) 2).symm
  have hmodd : Odd m := by
    have := Nat.coprime_ordCompl Nat.prime_two hC0
    exact Nat.coprime_two_left.mp this
  obtain ⟨k, hk⟩ : Nat.card ↥(V ⊓ N) ∣ Nat.card ↥(C ⊓ N) :=
    Subgroup.card_dvd_of_le (inf_le_inf_right N hV.1)
  obtain ⟨q, hq⟩ := hdvd
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have h1 : Nat.card T * q * Nat.card ↥(C ⊓ N) = Nat.card C * Nat.card ↥(T ⊓ N) := by
    have h2 : Nat.card ↥(T ⊔ N) * Nat.card ↥(T ⊓ N) * q * Nat.card ↥(C ⊓ N) =
        Nat.card C * Nat.card N * Nat.card ↥(T ⊓ N) := by
      rw [← e2, hq]; ring
    rw [e1] at h2
    have h3 : Nat.card N * (Nat.card T * q * Nat.card ↥(C ⊓ N)) =
        Nat.card N * (Nat.card C * Nat.card ↥(T ⊓ N)) := by
      calc Nat.card N * (Nat.card T * q * Nat.card ↥(C ⊓ N))
          = Nat.card T * Nat.card N * q * Nat.card ↥(C ⊓ N) := by ring
        _ = Nat.card C * Nat.card N * Nat.card ↥(T ⊓ N) := h2
        _ = Nat.card N * (Nat.card C * Nat.card ↥(T ⊓ N)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hN0 h3
  obtain ⟨t, ht⟩ := hT2.exists_card_eq
  obtain ⟨s, hs⟩ := (hV.2.1.to_le (inf_le_left : V ⊓ N ≤ V)).exists_card_eq
  have h4 : Nat.card T * Nat.card ↥(V ⊓ N) ∣ (Nat.card V * Nat.card ↥(T ⊓ N)) * m := by
    refine ⟨q * k, ?_⟩
    have : Nat.card T * q * (Nat.card ↥(V ⊓ N) * k) =
        Nat.card V * m * Nat.card ↥(T ⊓ N) := by rw [← hk, h1, hCm]
    calc Nat.card V * Nat.card ↥(T ⊓ N) * m = Nat.card V * m * Nat.card ↥(T ⊓ N) := by ring
      _ = Nat.card T * q * (Nat.card ↥(V ⊓ N) * k) := this.symm
      _ = Nat.card T * Nat.card ↥(V ⊓ N) * (q * k) := by ring
  have hcop : Nat.Coprime (Nat.card T * Nat.card ↥(V ⊓ N)) m := by
    rw [ht, hs, ← pow_add]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd)
  have h5 := hcop.dvd_of_dvd_mul_right h4
  have h6 : Nat.card T * Nat.card ↥(V ⊓ N) ≤ Nat.card ↥(Q ⊔ V) * Nat.card ↥(V ⊓ N) := by
    calc Nat.card T * Nat.card ↥(V ⊓ N) ≤ Nat.card V * Nat.card ↥(T ⊓ N) :=
          Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) h5
      _ ≤ Nat.card V * Nat.card Q := Nat.mul_le_mul_left _ hTNle
      _ = Nat.card ↥(Q ⊔ V) * Nat.card ↥(V ⊓ N) := by rw [sup_comm, e3]
  have h7 : Nat.card T ≤ Nat.card ↥(Q ⊔ V) := Nat.le_of_mul_le_mul_right h6 Nat.card_pos
  exact (Subgroup.eq_of_le_of_card_ge hle h7).symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
