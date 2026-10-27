module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512D
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512C

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_odd_char_L512 {K O : Subgroup G} (hOK : O ≤ K) (hOodd : Odd (Nat.card O))
    (hOchar : ∀ k ∈ K, Odd (orderOf k) → k ∈ O) {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) {o : G}
    (ho : o ∈ O) : g * o * g⁻¹ ∈ O := by
  apply hOchar _ (hg o (hOK ho))
  have h1 : orderOf (g * o * g⁻¹) = orderOf o := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h2 : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  rw [h1]
  exact Odd.of_dvd_nat hOodd h2

theorem mem_O_of_conj_eq_L512 {Wa Wb O : Subgroup G} (hWasq : ∀ w ∈ Wa, w * w = 1)
    (hWb4 : Nat.card Wb = 4) (hWbsq : ∀ w ∈ Wb, w * w = 1)
    (hWab : ∀ a ∈ Wa, ∀ b ∈ Wb, a * b = b * a) {a b : G}
    (haO : a ∈ normalizer (O : Set G)) (hbO : b ∈ normalizer (O : Set G))
    (hWaO : ∀ w ∈ Wa, w ∈ normalizer (O : Set G)) (hWbO : ∀ w ∈ Wb, w ∈ normalizer (O : Set G))
    (hbWa : ∀ w ∈ Wa, b * w = w * b) (hbWb : ∀ w ∈ Wb, b * w * b⁻¹ ∈ Wb)
    (hbfix : ∀ w ∈ Wb, b * w * b⁻¹ = w → w = 1) (hb3 : b ^ 3 ∈ O) {x y o : G} (hx : x ∈ Wa)
    (hy : y ∈ Wb) (ho : o ∈ O) (hab : a * b * a⁻¹ = x * y * o * b) : x ∈ O := by
  have hconj : ∀ g ∈ normalizer (O : Set G), ∀ u ∈ O, g⁻¹ * u * g ∈ O := fun g hg u hu => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hg) u).mp hu
    rwa [inv_inv] at h1
  set y' := x * y * b with hy'
  have hy'N : y' ∈ normalizer (O : Set G) :=
    mul_mem (mul_mem (hWaO x hx) (hWbO y hy)) hbO
  have ho₁ : b⁻¹ * o * b ∈ O := hconj b hbO o ho
  have h1 : x * y * o * b = y' * (b⁻¹ * o * b) := by rw [hy']; group
  have h2 := pow_mul_mem_coset_L512 (hconj y' hy'N) 1 3 ho₁
  rw [one_mul, pow_one, ← h1, ← hab, conj_pow] at h2
  have h3 : a * b ^ 3 * a⁻¹ ∈ O := (mem_normalizer_iff.mp haO _).mp hb3
  have hy'3 : y' ^ 3 ∈ O := by
    have h4 := mul_mem h3 (inv_mem h2)
    rwa [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at h4
  have hxb : x * (y * b) = (y * b) * x := by
    rw [← mul_assoc, hWab x hx y hy, mul_assoc, ← hbWa x hx, ← mul_assoc]
  have hcube := (conj_cube_of_fpf_L512 hWb4 hWbsq hbWb hbfix hy).2
  have hyb3 : (y * b) ^ 3 = b ^ 3 := by
    calc (y * b) ^ 3 = y * b * (y * b) * (y * b) := by rw [pow_succ, sq]
      _ = y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹) * b ^ 3 := by group
      _ = b ^ 3 := by rw [hcube, one_mul]
  have hx3 : x ^ 3 = x := by
    rw [pow_succ, sq, hWasq x hx, one_mul]
  have h5 : y' ^ 3 = x * b ^ 3 := by
    rw [hy', mul_assoc, (Commute.mul_pow hxb 3), hx3, hyb3]
  rw [h5] at hy'3
  have h6 := mul_mem hy'3 (inv_mem hb3)
  rwa [mul_inv_cancel_right] at h6

theorem commutator_mem_of_fpf_L512 {W₁ W₂ K O P : Subgroup G} (hW₁4 : Nat.card W₁ = 4)
    (hW₂4 : Nat.card W₂ = 4) (hW₁sq : ∀ w ∈ W₁, w * w = 1) (hW₂sq : ∀ w ∈ W₂, w * w = 1)
    (hW₁₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a)
    (hK : ∀ k, k ∈ K ↔ (∀ w ∈ W₁, k * w = w * k) ∧ ∀ w ∈ W₂, k * w = w * k)
    (hOK : O ≤ K) (hOodd : Odd (Nat.card O)) (hOchar : ∀ k ∈ K, Odd (orderOf k) → k ∈ O)
    (hdec : ∀ k ∈ K, ∃ o ∈ O, ∃ q ∈ P, k = o * q) {p₀ : G} (hp₀ : p₀ ∈ K) {e : ℕ}
    (he : p₀ ^ 2 ^ e = 1) (hcyc : ∀ q ∈ P, ∃ j : ℕ, ∃ w ∈ W₁ ⊔ W₂, q = p₀ ^ j * w) {h₁ h₂ : G}
    (h₁W₁ : ∀ w ∈ W₁, h₁ * w * h₁⁻¹ ∈ W₁) (h₁fix : ∀ w ∈ W₁, h₁ * w * h₁⁻¹ = w → w = 1)
    (h₁W₂ : ∀ w ∈ W₂, h₁ * w = w * h₁) (h₁odd : Odd (orderOf h₁))
    (h₂W₂ : ∀ w ∈ W₂, h₂ * w * h₂⁻¹ ∈ W₂) (h₂fix : ∀ w ∈ W₂, h₂ * w * h₂⁻¹ = w → w = 1)
    (h₂W₁ : ∀ w ∈ W₁, h₂ * w = w * h₂) (h₂odd : Odd (orderOf h₂)) :
    h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈ O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWmem : ∀ w ∈ W₁ ⊔ W₂, ∃ a ∈ W₁, ∃ b ∈ W₂, w = a * b := fun w hw => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_commute hW₁₂ hw
    exact ⟨a, ha, b, hb, rfl⟩
  have hKW : ∀ k ∈ K, ∀ w ∈ W₁ ⊔ W₂, k * w = w * k := by
    intro k hk w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWmem w hw
    rw [← mul_assoc, ((hK k).mp hk).1 a ha, mul_assoc, ((hK k).mp hk).2 b hb, mul_assoc]
  have hOW : ∀ w ∈ W₁ ⊔ W₂, ∀ o ∈ O, w * o = o * w := fun w hw o ho =>
    (hKW o (hOK ho) w hw).symm
  have hOn : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) → ∀ o ∈ O, g * o * g⁻¹ ∈ O :=
    fun g hg o ho => conj_mem_of_odd_char_L512 hOK hOodd hOchar hg ho
  have hKK : ∀ g ∈ K, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk =>
    mul_mem (mul_mem hg hk) (inv_mem hg)
  have hW₁K : ∀ w ∈ W₁, w ∈ K := fun w hw => (hK w).mpr
    ⟨fun v hv => commute_of_mul_sq_L512 (hW₁sq w hw) (hW₁sq v hv) (hW₁sq _ (mul_mem hw hv)),
      fun v hv => hW₁₂ w hw v hv⟩
  have hW₂K : ∀ w ∈ W₂, w ∈ K := fun w hw => (hK w).mpr
    ⟨fun v hv => (hW₁₂ v hv w hw).symm,
      fun v hv => commute_of_mul_sq_L512 (hW₂sq w hw) (hW₂sq v hv) (hW₂sq _ (mul_mem hw hv))⟩
  have hinvN : ∀ {g : G} {V : Subgroup G}, (∀ w ∈ V, g * w * g⁻¹ ∈ V) →
      ∀ w ∈ V, g⁻¹ * w * g ∈ V := by
    intro g V hg w hw
    have h1 := mem_normalizer_of_conj_mem_L512 hg
    have h2 := (mem_normalizer_iff.mp (inv_mem h1) w).mp hw
    rwa [inv_inv] at h2
  have hKconj : ∀ g : G, (∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁) → (∀ w ∈ W₂, g * w * g⁻¹ ∈ W₂) →
      ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg₁ hg₂ k hk
    refine (hK _).mpr ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have h1 := ((hK k).mp hk).1 _ (hinvN hg₁ w hw)
      calc g * k * g⁻¹ * w = g * (k * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * k) * g⁻¹ := by rw [h1]
        _ = w * (g * k * g⁻¹) := by group
    · have h1 := ((hK k).mp hk).2 _ (hinvN hg₂ w hw)
      calc g * k * g⁻¹ * w = g * (k * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * k) * g⁻¹ := by rw [h1]
        _ = w * (g * k * g⁻¹) := by group
  have hcent : ∀ {g : G} {V : Subgroup G}, (∀ w ∈ V, g * w = w * g) →
      ∀ w ∈ V, g * w * g⁻¹ ∈ V := fun hg w hw => by rw [hg w hw, mul_inv_cancel_right]; exact hw
  have hK₁ := hKconj h₁ h₁W₁ (hcent h₁W₂)
  have hK₂ := hKconj h₂ (hcent h₂W₁) h₂W₂
  set U := (W₁ ⊔ W₂) ⊔ O with hUdef
  have hUmem : ∀ u ∈ U, ∃ w ∈ W₁ ⊔ W₂, ∃ o ∈ O, u = w * o := fun u hu => by
    obtain ⟨w, hw, o, ho, rfl⟩ := exists_mul_of_mem_sup_commute hOW hu
    exact ⟨w, hw, o, ho, rfl⟩
  have hUconj : ∀ g : G, (∀ w ∈ W₁ ⊔ W₂, g * w * g⁻¹ ∈ W₁ ⊔ W₂) →
      (∀ o ∈ O, g * o * g⁻¹ ∈ O) → ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hgW hgO u hu
    obtain ⟨w, hw, o, ho, rfl⟩ := hUmem u hu
    rw [show g * (w * o) * g⁻¹ = (g * w * g⁻¹) * (g * o * g⁻¹) by group]
    exact mul_mem (mem_sup_left (hgW w hw)) (mem_sup_right (hgO o ho))
  have hUK : ∀ g ∈ K, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg =>
    hUconj g (fun w hw => by rw [hKW g hg w hw, mul_inv_cancel_right]; exact hw)
      (hOn g (hKK g hg))
  have hWconj : ∀ g : G, (∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁) → (∀ w ∈ W₂, g * w * g⁻¹ ∈ W₂) →
      ∀ w ∈ W₁ ⊔ W₂, g * w * g⁻¹ ∈ W₁ ⊔ W₂ := by
    intro g hg₁ hg₂ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWmem w hw
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact mul_mem (mem_sup_left (hg₁ a ha)) (mem_sup_right (hg₂ b hb))
  have hU₁ := hUconj h₁ (hWconj h₁ h₁W₁ (hcent h₁W₂)) (hOn h₁ hK₁)
  have hcycK : ∀ k ∈ K, ∃ j : ℕ, ∃ u ∈ U, k = p₀ ^ j * u := by
    intro k hk
    obtain ⟨o, ho, q, hq, rfl⟩ := hdec k hk
    obtain ⟨j, w, hw, rfl⟩ := hcyc q hq
    have h1 : (p₀ ^ j)⁻¹ * o * p₀ ^ j ∈ O := by
      have h2 := hOn _ (hKK _ (inv_mem (pow_mem hp₀ j))) o ho
      rwa [inv_inv] at h2
    refine ⟨j, (p₀ ^ j)⁻¹ * o * p₀ ^ j * w, mul_mem (mem_sup_right h1) (mem_sup_left hw), ?_⟩
    group
  have he' : p₀ ^ 2 ^ e ∈ U := by rw [he]; exact one_mem _
  have hact : ∀ k ∈ K, k⁻¹ * (h₁ * k * h₁⁻¹) ∈ U := fun k hk =>
    conj_mem_of_cyclic_mod (M := K) (U := U) hUK hp₀ hcycK he' hK₁ hU₁ h₁odd
      (pow_orderOf_eq_one h₁) hk
  set c := h₁ * h₂ * h₁⁻¹ * h₂⁻¹ with hc
  have hN₁ := mem_normalizer_of_conj_mem_L512 h₁W₁
  have hN₂ := mem_normalizer_of_conj_mem_L512 h₂W₂
  have hfK : ∀ r : ℕ, h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹ ∈ K := by
    intro r
    have hr1 : ∀ w ∈ W₁, (h₁ ^ r)⁻¹ * w * h₁ ^ r ∈ W₁ := fun w hw => by
      have h1 := (mem_normalizer_iff.mp (inv_mem (pow_mem hN₁ r)) w).mp hw
      rwa [inv_inv] at h1
    have hr2 : ∀ w ∈ W₂, h₁ ^ r * w = w * h₁ ^ r := fun w hw =>
      (Commute.pow_left (h₁W₂ w hw) r).eq
    refine (hK _).mpr ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have hc1 : h₂⁻¹ * w * h₂ = w := by
        rw [mul_assoc, ← h₂W₁ w hw, ← mul_assoc, inv_mul_cancel, one_mul]
      have hc2 : h₂ * ((h₁ ^ r)⁻¹ * w * h₁ ^ r) * h₂⁻¹ = (h₁ ^ r)⁻¹ * w * h₁ ^ r := by
        rw [h₂W₁ _ (hr1 w hw), mul_inv_cancel_right]
      have h3 : h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹ * w * (h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹)⁻¹ = w := by
        calc _ = h₁ ^ r * (h₂ * ((h₁ ^ r)⁻¹ * (h₂⁻¹ * w * h₂) * h₁ ^ r) * h₂⁻¹) * (h₁ ^ r)⁻¹ := by
              group
          _ = w := by rw [hc1, hc2]; group
      exact (mul_inv_eq_iff_eq_mul.mp h3)
    · have hw' : h₂⁻¹ * w * h₂ ∈ W₂ := hinvN h₂W₂ w hw
      have hc3 : (h₁ ^ r)⁻¹ * (h₂⁻¹ * w * h₂) * h₁ ^ r = h₂⁻¹ * w * h₂ := by
        rw [mul_assoc, ← hr2 _ hw', ← mul_assoc, inv_mul_cancel, one_mul]
      have h3 : h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹ * w * (h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹)⁻¹ = w := by
        calc _ = h₁ ^ r * (h₂ * ((h₁ ^ r)⁻¹ * (h₂⁻¹ * w * h₂) * h₁ ^ r) * h₂⁻¹) * (h₁ ^ r)⁻¹ := by
              group
          _ = h₁ ^ r * w * (h₁ ^ r)⁻¹ := by rw [hc3]; group
          _ = w := by rw [hr2 w hw, mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp h3)
  have hcK : c ∈ K := by
    have h1 := hfK 1
    rwa [pow_one] at h1
  have hfe : ∀ r : ℕ, (c ^ r)⁻¹ * (h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹) ∈ U := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      set f := h₁ ^ r * h₂ * (h₁ ^ r)⁻¹ * h₂⁻¹ with hf
      have h1 : h₁ ^ (r + 1) * h₂ * (h₁ ^ (r + 1))⁻¹ * h₂⁻¹ = h₁ * f * h₁⁻¹ * c := by
        rw [hf, hc, pow_succ']
        group
      have h2 := hact f (hfK r)
      rw [h1, show (c ^ (r + 1))⁻¹ * (h₁ * f * h₁⁻¹ * c) =
        c⁻¹ * ((c ^ r)⁻¹ * f * (f⁻¹ * (h₁ * f * h₁⁻¹))) * c⁻¹⁻¹ by rw [pow_succ]; group]
      exact hUK _ (inv_mem hcK) _ (mul_mem ih h2)
  have hcm : c ^ orderOf h₁ ∈ U := by
    have h1 := hfe (orderOf h₁)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, mul_inv_cancel, mul_one] at h1
    simpa using inv_mem h1
  have hc2 : c ^ 2 ^ e ∈ U := by
    obtain ⟨j, u, hu, hju⟩ := hcycK c hcK
    have hpU : ∀ v ∈ U, p₀⁻¹ * v * p₀ ∈ U := fun v hv => by
      have h1 := hUK _ (inv_mem hp₀) v hv
      rwa [inv_inv] at h1
    have h1 := pow_mul_mem_coset_L512 hpU j (2 ^ e) hu
    rw [mul_comm, pow_mul, he, one_pow, inv_one, one_mul, ← hju] at h1
    exact h1
  have hcU : c ∈ U := mem_of_pow_odd_mem h₁odd hcm hc2
  obtain ⟨w, hw, o, ho, hwo⟩ := hUmem c hcU
  obtain ⟨x, hx, y, hy, rfl⟩ := hWmem w hw
  have hON : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) → g ∈ normalizer (O : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem_L512 (hOn g hg)
  have hpow3 : ∀ {g : G} {Va Vb : Subgroup G}, Nat.card Vb = 4 → (∀ v ∈ Vb, v * v = 1) →
      (∀ w ∈ Vb, g * w * g⁻¹ ∈ Vb) → (∀ w ∈ Vb, g * w * g⁻¹ = w → w = 1) →
      (∀ w ∈ Va, g * w = w * g) →
      (∀ k, k ∈ K ↔ (∀ w ∈ Va, k * w = w * k) ∧ ∀ w ∈ Vb, k * w = w * k) →
      Odd (orderOf g) → g ^ 3 ∈ O := by
    intro g Va Vb hVb4 hVbsq hgVb hgfix hgVa hK' hgodd
    refine hOchar _ ((hK' _).mpr ⟨fun w hw => (Commute.pow_left (hgVa w hw) 3).eq,
      fun w hw => ?_⟩) (Odd.of_dvd_nat hgodd (orderOf_pow_dvd 3))
    have h1 := (conj_cube_of_fpf_L512 hVb4 hVbsq hgVb hgfix hw).1
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hb₂ : h₂ ^ 3 ∈ O := hpow3 hW₂4 hW₂sq h₂W₂ h₂fix h₂W₁ hK h₂odd
  have hb₁ : h₁ ^ 3 ∈ O := hpow3 hW₁4 hW₁sq h₁W₁ h₁fix h₁W₂
    (fun k => by rw [hK k, and_comm]) h₁odd
  have hW₁O : ∀ w ∈ W₁, w ∈ normalizer (O : Set G) := fun w hw => hON w (hKK w (hW₁K w hw))
  have hW₂O : ∀ w ∈ W₂, w ∈ normalizer (O : Set G) := fun w hw => hON w (hKK w (hW₂K w hw))
  have hP₁ : IsPGroup 2 W₁ := IsPGroup.of_card (n := 2) (by rw [hW₁4]; norm_num)
  have hP₂ : IsPGroup 2 W₂ := IsPGroup.of_card (n := 2) (by rw [hW₂4]; norm_num)
  have hx1 : x = 1 := by
    have h1 : h₁ * h₂ * h₁⁻¹ = x * y * o * h₂ := by
      rw [← hwo, hc]
      group
    exact eq_one_of_mem_of_odd hP₁ hOodd hx (mem_O_of_conj_eq_L512 hW₁sq hW₂4 hW₂sq hW₁₂
      (hON h₁ hK₁) (hON h₂ hK₂) hW₁O hW₂O h₂W₁ h₂W₂ h₂fix hb₂ hx hy ho h1)
  have hy1 : y = 1 := by
    have h1 : h₂ * h₁ * h₂⁻¹ = y⁻¹ * x⁻¹ * o⁻¹ * h₁ := by
      have h2 : y⁻¹ * x⁻¹ * o⁻¹ = (x * y * o)⁻¹ := by
        have hyx : y⁻¹ * x⁻¹ ∈ W₁ ⊔ W₂ :=
          mul_mem (mem_sup_right (inv_mem hy)) (mem_sup_left (inv_mem hx))
        rw [hOW _ hyx _ (inv_mem ho)]
        group
      rw [h2, ← hwo, hc]
      group
    have h3 := mem_O_of_conj_eq_L512 hW₂sq hW₁4 hW₁sq (fun a ha b hb => (hW₁₂ b hb a ha).symm)
      (hON h₂ hK₂) (hON h₁ hK₁) hW₂O hW₁O h₁W₂ h₁W₁ h₁fix hb₁ (inv_mem hy) (inv_mem hx)
      (inv_mem ho) h1
    have h4 := eq_one_of_mem_of_odd hP₂ hOodd (inv_mem hy) h3
    rwa [inv_eq_one] at h4
  rw [hwo, hx1, hy1, one_mul, one_mul]
  exact ho

end CFSG.ComponentClassification.Foote5
