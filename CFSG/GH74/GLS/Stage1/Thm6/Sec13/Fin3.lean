module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ClassCard
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Final
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L131b

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem conj_x_eq {H₀ : Subgroup G} {x : G} (hinv : ∀ h ∈ H₀, x * h * x⁻¹ = h⁻¹) {h : G}
    (hh : h ∈ H₀) : h * x * h⁻¹ = (h * h) * x := by
  have h1 : x * h⁻¹ * x⁻¹ = h := by
    have := hinv h⁻¹ (H₀.inv_mem hh)
    rw [this, inv_inv]
  calc h * x * h⁻¹ = h * (x * h⁻¹ * x⁻¹) * x := by group
    _ = (h * h) * x := by rw [h1]

theorem conj_x_mem_Vx [Finite G] {S H₀ V : Subgroup G} {a b x y₀ : G} (z4 : Z4Data H₀ a b)
    (hS : Nat.card S = 64) (hH₀S : H₀ ≤ S) (hxS : x ∈ S)
    (hinv : ∀ h ∈ H₀, x * h * x⁻¹ = h⁻¹) (hV4 : Nat.card V = 4)
    (hVsub : ∀ v ∈ V, v = 1 ∨ v = a ^ 2 ∨ v = b ^ 2 ∨ v = a ^ 2 * b ^ 2)
    (hCS : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) = 16) (hy₀S : y₀ ∈ S) :
    ∃ v ∈ V, y₀ * x * y₀⁻¹ = v * x := by
  have hcard := card_cls_mul S hxS
  rw [hCS, hS] at hcard
  have h4 : Nat.card (cls S x) = 4 := by omega
  have hab2 : (a * b) * (a * b) = a ^ 2 * b ^ 2 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← z4.hab]
      _ = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
  have hsub : (fun v => v * x) '' (V : Set G) ⊆ cls S x := by
    rintro _ ⟨v, hv, rfl⟩
    rcases hVsub v hv with rfl | rfl | rfl | rfl
    · exact ⟨1, S.one_mem, by simp⟩
    · refine ⟨a, hH₀S z4.a_mem, ?_⟩
      rw [conj_x_eq hinv z4.a_mem, pow_two]
    · refine ⟨b, hH₀S z4.b_mem, ?_⟩
      rw [conj_x_eq hinv z4.b_mem, pow_two]
    · refine ⟨a * b, hH₀S (H₀.mul_mem z4.a_mem z4.b_mem), ?_⟩
      rw [conj_x_eq hinv (H₀.mul_mem z4.a_mem z4.b_mem), hab2]
  have hnc : ((fun v => v * x) '' (V : Set G)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective x), ← Nat.card_coe_set_eq]
    exact hV4
  have hle : (cls S x).ncard ≤ ((fun v => v * x) '' (V : Set G)).ncard := by
    rw [hnc, ← Nat.card_coe_set_eq, h4]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hmem : y₀ * x * y₀⁻¹ ∈ cls S x := ⟨y₀, hy₀S, rfl⟩
  rw [← heq] at hmem
  obtain ⟨v, hv, hvx⟩ := hmem
  exact ⟨v, hv, hvx.symm⟩

theorem exists_y1 [Finite G] {S H₀ V : Subgroup G} {a b x y₀ : G} (z4 : Z4Data H₀ a b)
    (hS : Nat.card S = 64) (hH₀S : H₀ ≤ S) (hxS : x ∈ S)
    (hinv : ∀ h ∈ H₀, x * h * x⁻¹ = h⁻¹) (hV4 : Nat.card V = 4)
    (hVsub : ∀ v ∈ V, v = 1 ∨ v = a ^ 2 ∨ v = b ^ 2 ∨ v = a ^ 2 * b ^ 2)
    (hCS : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) = 16) (hy₀S : y₀ ∈ S) (hy₀ : y₀ * y₀ = 1)
    (hya : y₀ * a * y₀⁻¹ = b) (hyb : y₀ * b * y₀⁻¹ = a) :
    ∃ k ∈ H₀, (k * y₀ * k⁻¹) * x = x * (k * y₀ * k⁻¹) := by
  obtain ⟨v, hv, hvx⟩ := conj_x_mem_Vx z4 hS hH₀S hxS hinv hV4 hVsub hCS hy₀S
  have hya2 : y₀ * a ^ 2 * y₀⁻¹ = b ^ 2 := by
    calc y₀ * a ^ 2 * y₀⁻¹ = (y₀ * a * y₀⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = b ^ 2 := by rw [hya]
  have hyb2 : y₀ * b ^ 2 * y₀⁻¹ = a ^ 2 := by
    calc y₀ * b ^ 2 * y₀⁻¹ = (y₀ * b * y₀⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = a ^ 2 := by rw [hyb]
  have hrel : x = (y₀ * v * y₀⁻¹) * (v * x) := by
    have h1 : y₀⁻¹ * y₀⁻¹ = 1 := by rw [← mul_inv_rev, hy₀, inv_one]
    calc x = (y₀ * y₀) * x * (y₀⁻¹ * y₀⁻¹) := by rw [hy₀, h1]; group
      _ = y₀ * (y₀ * x * y₀⁻¹) * y₀⁻¹ := by group
      _ = y₀ * (v * x) * y₀⁻¹ := by rw [hvx]
      _ = (y₀ * v * y₀⁻¹) * (y₀ * x * y₀⁻¹) := by group
      _ = (y₀ * v * y₀⁻¹) * (v * x) := by rw [hvx]
  rcases hVsub v hv with rfl | rfl | rfl | rfl
  · refine ⟨1, H₀.one_mem, ?_⟩
    have : y₀ * x * y₀⁻¹ = x := by rw [hvx]; group
    simpa using mul_inv_eq_iff_eq_mul.1 this
  · exfalso
    rw [hya2] at hrel
    have h2 : (b ^ 2 * a ^ 2) * x = 1 * x := by rw [mul_assoc, one_mul]; exact hrel.symm
    have h3 := mul_right_cancel h2
    rw [z4.tab_ba] at h3
    exact z4.z_ne_one h3
  · exfalso
    rw [hyb2] at hrel
    have h2 : (a ^ 2 * b ^ 2) * x = 1 * x := by rw [mul_assoc, one_mul]; exact hrel.symm
    exact z4.z_ne_one (mul_right_cancel h2)
  · refine ⟨a, z4.a_mem, ?_⟩
    have hax : x * a = a⁻¹ * x := mul_inv_eq_iff_eq_mul.1 (hinv a z4.a_mem)
    have hax2 : a⁻¹ * x * a = x * a ^ 2 := by
      calc a⁻¹ * x * a = (a⁻¹ * x) * a := rfl
        _ = (x * a) * a := by rw [← hax]
        _ = x * a ^ 2 := by rw [pow_two, mul_assoc]
    have hax' : x * a⁻¹ = a * x := by
      have := hinv a⁻¹ (H₀.inv_mem z4.a_mem)
      rw [inv_inv] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    have hxb2 : x * b ^ 2 = b ^ 2 * x := by
      have h1 := hinv (b ^ 2) z4.b2_mem
      rw [inv_eq_of_mul_eq_one_right z4.tab_bb] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have h4 : a * (a ^ 2 * 1) * a = 1 := by
      rw [mul_one]
      calc a * a ^ 2 * a = a ^ 4 := by group
        _ = 1 := z4.ha
    have key : (a * y₀ * a⁻¹) * x * (a * y₀ * a⁻¹)⁻¹ = x := by
      calc (a * y₀ * a⁻¹) * x * (a * y₀ * a⁻¹)⁻¹
          = a * y₀ * (a⁻¹ * x * a) * y₀⁻¹ * a⁻¹ := by group
        _ = a * y₀ * (x * a ^ 2) * y₀⁻¹ * a⁻¹ := by rw [hax2]
        _ = a * ((y₀ * x * y₀⁻¹) * (y₀ * a ^ 2 * y₀⁻¹)) * a⁻¹ := by group
        _ = a * (((a ^ 2 * b ^ 2) * x) * b ^ 2) * a⁻¹ := by rw [hvx, hya2]
        _ = a * ((a ^ 2 * b ^ 2) * (x * b ^ 2)) * a⁻¹ := by group
        _ = a * ((a ^ 2 * b ^ 2) * (b ^ 2 * x)) * a⁻¹ := by rw [hxb2]
        _ = a * (a ^ 2 * b ^ 2 * b ^ 2) * (x * a⁻¹) := by group
        _ = a * (a ^ 2 * b ^ 2 * b ^ 2) * (a * x) := by rw [hax']
        _ = (a * (a ^ 2 * (b ^ 2 * b ^ 2)) * a) * x := by group
        _ = x := by rw [z4.tab_bb, h4, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 key

theorem m12data_of_y1 [Finite G] {S H₀ : Subgroup G} {a b x y₁ : G} (z4 : Z4Data H₀ a b)
    (hS : Nat.card S = 64) (hH₀S : H₀ ≤ S) (hxS : x ∈ S) (hy₁S : y₁ ∈ S)
    (hxx : x * x = 1) (hyy : y₁ * y₁ = 1) (hyx : y₁ * x = x * y₁)
    (hya : y₁ * a * y₁⁻¹ = b) (hyb : y₁ * b * y₁⁻¹ = a)
    (hinv : ∀ h ∈ H₀, x * h * x⁻¹ = h⁻¹)
    (hxH : x ∉ H₀) (hy₁H : y₁ ∉ H₀) (hxy : x ∉ H₀ ⊔ zpowers y₁) :
    M12Data S a b y₁ x := by
  refine ⟨z4.ha, z4.hb, z4.hab, hyy, hxx, hyx, hya, hyb, hinv a z4.a_mem, hinv b z4.b_mem, ?_, hS⟩
  have haS : a ∈ S := hH₀S z4.a_mem
  have hbS : b ∈ S := hH₀S z4.b_mem
  have hle : Subgroup.closure ({a, b, y₁, x} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  set C' := Subgroup.closure ({a, b, y₁, x} : Set G) with hC'
  have hH₀C' : H₀ ≤ C' := by
    rw [← z4.gen]
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl <;> simp
  have hxC' : x ∈ C' := Subgroup.subset_closure (by simp)
  have hy₁C' : y₁ ∈ C' := Subgroup.subset_closure (by simp)
  have hN : ∀ q ∈ H₀, x * q * x⁻¹ ∈ H₀ := fun q hq => by rw [hinv q hq]; exact H₀.inv_mem hq
  set C'' := H₀ ⊔ zpowers x with hC''
  have hC''C' : C'' ≤ C' := sup_le hH₀C' ((zpowers_le).2 hxC')
  have hH₀C'' : H₀ < C'' := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hxH
    rw [h]
    exact Subgroup.mem_sup_right (mem_zpowers x)
  have hC''C'lt : C'' < C' := by
    refine lt_of_le_of_ne hC''C' ?_
    intro h
    have : y₁ ∈ C'' := h ▸ hy₁C'
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_invol hxx hN).1 this
    · exact hy₁H (h1 ▸ hq)
    · apply hxy
      have : x = q⁻¹ * y₁ := by rw [h1]; group
      rw [this]
      exact (H₀ ⊔ zpowers y₁).mul_mem (Subgroup.mem_sup_left (H₀.inv_mem hq))
        (Subgroup.mem_sup_right (mem_zpowers y₁))
  have h1 := Subgroup.card_lt_of_lt hH₀C''
  have h2 := Subgroup.card_lt_of_lt hC''C'lt
  have h3 : Nat.card H₀ ∣ Nat.card C'' := Subgroup.card_dvd_of_le hH₀C''.le
  have h4 : Nat.card C' ∣ Nat.card S := Subgroup.card_dvd_of_le hle
  have h5 : Nat.card C'' ≤ Nat.card S := Subgroup.card_le_of_le (hC''C'.trans hle)
  rw [z4.card] at h1 h3
  rw [hS] at h4 h5
  have h6 : 32 ≤ Nat.card C'' := by
    obtain ⟨c, hc⟩ := h3
    have : 2 ≤ c := by
      by_contra hcon
      push Not at hcon
      interval_cases c <;> omega
    omega
  have h7 : Nat.card C' = 64 := by
    obtain ⟨m, hm⟩ := h4
    have hm1 : 1 ≤ m := by
      by_contra hcon
      push Not at hcon
      interval_cases m
      simp at hm
    have : m < 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    interval_cases m
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hS, h7])

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
