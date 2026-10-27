module

public import CFSG.CGT.Foote81L6.TStruct.Lemma2Two
public import CFSG.CGT.Foote81L6.TStruct.TypeT

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem comm_b₀_of_mem_T₁ {y : G} (hy : y ∈ D.T₁) : y * D.b₀ = D.b₀ * y := by
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hy
  have h1 := D.A_comm_B α hα D.b₀ D.b₀_mem_B
  have h2 := D.b₀_comm_B₀B₁ hw
  calc α * w * D.b₀ = α * (D.b₀ * w) := by rw [mul_assoc, h2]
    _ = D.b₀ * (α * w) := by rw [← mul_assoc, h1, mul_assoc]

theorem comm_b₁_of_mem_T₁ {y : G} (hy : y ∈ D.T₁) : y * D.b₁ = D.b₁ * y := by
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hy
  have h1 := D.A_comm_B α hα D.b₁ D.b₁_mem_B
  have h2 := D.b₁_comm_B₀B₁ hw
  calc α * w * D.b₁ = α * (D.b₁ * w) := by rw [mul_assoc, h2]
    _ = D.b₁ * (α * w) := by rw [← mul_assoc, h1, mul_assoc]

theorem conj_b₀_of_mul_t_mem_T₁ {x : G} (hx : x * D.t ∈ D.T₁) : x * D.b₀ * x⁻¹ = D.b₁ := by
  have h' : D.t⁻¹ * D.b₀ * D.t = D.b₁ := by
    have h := D.conj_t_b₀
    rw [D.t_inv] at h ⊢
    exact h
  calc x * D.b₀ * x⁻¹ = (x * D.t) * (D.t⁻¹ * D.b₀ * D.t) * (x * D.t)⁻¹ := by group
    _ = (x * D.t) * D.b₁ * (x * D.t)⁻¹ := by rw [h']
    _ = D.b₁ := by rw [D.comm_b₁_of_mem_T₁ hx, mul_inv_cancel_right]

theorem exists_moved_B₀ {E : Subgroup G} (hE : IsE64 T E) {w : G}
    (hw : w ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) (hwE : w ∉ E) :
    ∃ v ∈ E ⊓ D.B₀, w * v * w⁻¹ = v * D.b₀ := by
  obtain ⟨e⟩ := D.B₀_iso
  obtain ⟨v, hv, hvw⟩ := exists_conj_of_not_mem_four e D.one_le_n_sub_one (D.E64_decomp hE).2.2.1
    hw fun h => hwE (mem_inf.1 h).1
  rw [symm_zc_eq e D.two_le_n_sub_one D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy] at hvw
  exact ⟨v, hv, hvw⟩

theorem exists_moved_B₁ {E : Subgroup G} (hE : IsE64 T E) {w : G}
    (hw : w ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) (hwE : w ∉ E) :
    ∃ v ∈ E ⊓ D.B₁, w * v * w⁻¹ = v * D.b₁ := by
  obtain ⟨e⟩ := D.B₁_iso
  obtain ⟨v, hv, hvw⟩ := exists_conj_of_not_mem_four e D.one_le_n_sub_one (D.E64_decomp hE).2.2.2
    hw fun h => hwE (mem_inf.1 h).1
  rw [symm_zc_eq e D.two_le_n_sub_one D.b₁_mem D.b₁_ne_one fun y hy => D.b₁_comm y hy] at hvw
  exact ⟨v, hv, hvw⟩

theorem exists_moved_A (hm : 3 ≤ m) {E : Subgroup G} (hE : IsE64 T E) {w : G}
    (hw : w ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) (hwE : w ∉ E) :
    ∃ u ∈ E ⊓ D.A, w * u * w⁻¹ = u * D.a := by
  obtain ⟨e⟩ := D.A_iso
  obtain ⟨u, hu, huw⟩ := exists_conj_of_not_mem_four e (by omega) (D.E64_decomp hE).2.1 hw
    fun h => hwE (mem_inf.1 h).1
  rw [symm_zc_eq e (by omega) D.a_mem D.a_ne_one fun y hy => D.a_comm_A hy] at huw
  exact ⟨u, hu, huw⟩

theorem transvection_E64_center {E : Subgroup G} (hE : IsE64 T E) {x c : G} (hx : x ∈ T)
    (hxN : x ∈ normalizer (E : Set G)) (htv : ∀ v ∈ E, x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * c)
    (hmove : ∃ v ∈ E, x * v * x⁻¹ ≠ v) :
    (∃ α ∈ D.A, x * α⁻¹ ∈ E ∧ c = D.a) ∨ (∃ β ∈ D.B₀, x * β⁻¹ ∈ E ∧ c = D.b₀) ∨
      (∃ β ∈ D.B₁, x * β⁻¹ ∈ E ∧ c = D.b₁) := by
  classical
  obtain ⟨-, hA, hB₀, -⟩ := D.E64_decomp hE
  have hc : ∀ v ∈ E, ∀ w : G, x * v * x⁻¹ = v * w → w ≠ 1 → c = w := by
    intro v hv w hw hw1
    rcases htv v hv with h | h
    · exact absurd (mul_left_cancel ((hw.symm.trans h).trans (mul_one v).symm)) hw1
    · exact mul_left_cancel (h.symm.trans hw)
  have hb₀b₁ : D.b₀⁻¹ * D.b₁ ≠ 1 := fun h => D.b₀_ne_b₁ (inv_mul_eq_one.1 h)
  have hx0 : x ∈ D.T₀ := by
    by_contra hx0
    have hxt := D.mul_t_mem_T₁_of_mem_normalizer hE hx hx0 hxN
    obtain ⟨u, hu, hux⟩ : ∃ u ∈ E ⊓ D.A, x * u ≠ u * x := by
      by_contra hno
      apply hx0
      refine D.mem_T₀_of_comm_four hA hx fun u hu => ?_
      by_contra h
      exact hno ⟨u, hu, h⟩
    have huA := (mem_inf.1 hu).2
    have hcu : c = u⁻¹ * (x * u * x⁻¹) := by
      refine hc u (mem_inf.1 hu).1 _ (by group) fun h1 => hux ?_
      have h2 : x * u * x⁻¹ = u := by
        calc x * u * x⁻¹ = u * (u⁻¹ * (x * u * x⁻¹)) := by group
          _ = u := by rw [h1, mul_one]
      calc x * u = x * u * x⁻¹ * x := by group
        _ = u * x := by rw [h2]
    have hcb : c = D.b₀⁻¹ * D.b₁ :=
      hc D.b₀ (D.b₀_mem_E64 hE) _ (by rw [D.conj_b₀_of_mul_t_mem_T₁ hxt]; group) hb₀b₁
    have hcA : c ∈ D.A := by
      rw [hcu]
      exact mul_mem (inv_mem huA) (D.A_normal_T hx u huA)
    have hcB : c ∈ D.B := by
      rw [hcb]
      exact mul_mem (inv_mem D.b₀_mem_B) D.b₁_mem_B
    have hcAB : c ∈ D.A ⊓ D.B := mem_inf.2 ⟨hcA, hcB⟩
    rw [D.A_inf_B, mem_bot] at hcAB
    exact hb₀b₁ (hcb ▸ hcAB)
  have hx1 : x ∈ D.T₁ := by
    by_contra hx1
    have hcb : c = D.b₀⁻¹ * D.b₁ :=
      hc D.b₀ (D.b₀_mem_E64 hE) _ (by rw [D.conj_b₀_of_not_mem_T₁ hx0 hx1]; group) hb₀b₁
    obtain ⟨v, hv, hv1, hvb⟩ : ∃ v ∈ E ⊓ D.B₀, v ≠ 1 ∧ v ≠ D.b₀ := by
      by_contra hno
      have hsub : ∀ y ∈ E ⊓ D.B₀, y ∈ ({1, D.b₀} : Finset G) := by
        intro y hy
        by_contra hy'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy'
        exact hno ⟨y, hy, hy'.1, hy'.2⟩
      have h1 := card_le_of_forall_mem_finset' _ hsub
      rw [hB₀.2.2] at h1
      have h2 : ({1, D.b₀} : Finset G).card ≤ 2 := Finset.card_le_two
      omega
    have hvB := (mem_inf.1 hv).2
    have hxv : x * v * x⁻¹ ∈ D.B₁ := by
      have hxs : x * D.s ∈ D.T₁ := (D.mem_T₁_or_mul_s_mem_T₁ hx0).resolve_left hx1
      have e : x * v * x⁻¹ = (x * D.s) * (D.s * v * D.s⁻¹) * (x * D.s)⁻¹ := by
        calc x * v * x⁻¹ = (x * D.s) * (D.s⁻¹ * v * D.s) * (x * D.s)⁻¹ := by group
          _ = (x * D.s) * (D.s * v * D.s⁻¹) * (x * D.s)⁻¹ := by rw [D.s_inv]
      rw [e]
      exact D.B₁_normal_T₁ hxs _ (D.conj_s_mem_B₁ hvB)
    rcases htv v (mem_inf.1 hv).1 with h | h
    · rw [h] at hxv
      have h2 : v ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨hvB, hxv⟩
      rw [D.B₀_inf_B₁, mem_bot] at h2
      exact hv1 h2
    · rw [h, hcb] at hxv
      have h2 : v * D.b₀⁻¹ ∈ D.B₀ ⊓ D.B₁ := by
        refine mem_inf.2 ⟨mul_mem hvB (inv_mem D.b₀_mem), ?_⟩
        have h3 := mul_mem hxv (inv_mem D.b₁_mem)
        rwa [show v * (D.b₀⁻¹ * D.b₁) * D.b₁⁻¹ = v * D.b₀⁻¹ by group] at h3
      rw [D.B₀_inf_B₁, mem_bot] at h2
      exact hvb (mul_inv_eq_one.1 h2)
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx1
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  obtain ⟨hαR, hw₀R, hw₁R⟩ := D.mem_R_of_mem_normalizer hE hα hw₀ hw₁ hxN
  have hcA : α ∉ E → c = D.a := by
    intro hαE
    have hm : 3 ≤ m := by
      by_contra hm
      exact hαE (D.A_le_E64 (by have := D.two_le_m; omega) hE hα)
    obtain ⟨u, hu, hux⟩ := D.exists_moved_A hm hE hαR hαE
    exact hc u (mem_inf.1 hu).1 D.a (by rw [D.conj_mul_of_mem_A hw₀ hw₁ (mem_inf.1 hu).2, hux])
      D.a_ne_one
  have hcB₀ : w₀ ∉ E → c = D.b₀ := by
    intro hwE
    obtain ⟨v, hv, hvx⟩ := D.exists_moved_B₀ hE hw₀R hwE
    exact hc v (mem_inf.1 hv).1 D.b₀
      (by rw [D.conj_mul_of_mem_B₀ hα hw₀ hw₁ (mem_inf.1 hv).2, hvx]) D.b₀_ne_one
  have hcB₁ : w₁ ∉ E → c = D.b₁ := by
    intro hwE
    obtain ⟨v, hv, hvx⟩ := D.exists_moved_B₁ hE hw₁R hwE
    exact hc v (mem_inf.1 hv).1 D.b₁
      (by rw [D.conj_mul_of_mem_B₁ hα hw₀ hw₁ (mem_inf.1 hv).2, hvx]) D.b₁_ne_one
  have haB : D.a ∉ D.B := fun h => by
    have h2 : D.a ∈ D.A ⊓ D.B := mem_inf.2 ⟨D.a_mem, h⟩
    rw [D.A_inf_B, mem_bot] at h2
    exact D.a_ne_one h2
  have ha0 : D.a ≠ D.b₀ := fun h => haB (by rw [h]; exact D.b₀_mem_B)
  have ha1 : D.a ≠ D.b₁ := fun h => haB (by rw [h]; exact D.b₁_mem_B)
  by_cases hαE : α ∈ E
  · by_cases hw₀E : w₀ ∈ E
    · by_cases hw₁E : w₁ ∈ E
      · exfalso
        obtain ⟨v, hv, hvx⟩ := hmove
        apply hvx
        have hxE : α * (w₀ * w₁) ∈ E := mul_mem hαE (mul_mem hw₀E hw₁E)
        rw [comm_of_mul_self hE.mul_self hxE hv, mul_inv_cancel_right]
      · refine Or.inr (Or.inr ⟨w₁, hw₁, ?_, hcB₁ hw₁E⟩)
        rw [show α * (w₀ * w₁) * w₁⁻¹ = α * w₀ by group]
        exact mul_mem hαE hw₀E
    · have hc0 := hcB₀ hw₀E
      have hw₁E : w₁ ∈ E := by
        by_contra h
        exact D.b₀_ne_b₁ (hc0.symm.trans (hcB₁ h))
      refine Or.inr (Or.inl ⟨w₀, hw₀, ?_, hc0⟩)
      have hc01 : w₀ * w₁ = w₁ * w₀ := D.B₀_comm_B₁ w₀ hw₀ w₁ hw₁
      rw [show α * (w₀ * w₁) * w₀⁻¹ = α * w₁ by rw [hc01]; group]
      exact mul_mem hαE hw₁E
  · have hca := hcA hαE
    have hw₀E : w₀ ∈ E := by
      by_contra h
      exact ha0 (hca.symm.trans (hcB₀ h))
    have hw₁E : w₁ ∈ E := by
      by_contra h
      exact ha1 (hca.symm.trans (hcB₁ h))
    refine Or.inl ⟨α, hα, ?_, hca⟩
    have hcw : α * (w₀ * w₁) = (w₀ * w₁) * α :=
      D.A_comm_B₀B₁ α hα _ (mul_mem (mem_sup_left hw₀) (mem_sup_right hw₁))
    rw [hcw, mul_inv_cancel_right]
    exact mul_mem hw₀E hw₁E

theorem transvection_E64 {E : Subgroup G} (hE : IsE64 T E) {x c : G} (hx : x ∈ T)
    (hxN : x ∈ normalizer (E : Set G)) (htv : ∀ v ∈ E, x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * c)
    (hmove : ∃ v ∈ E, x * v * x⁻¹ ≠ v) :
    (∃ α ∈ D.A, x * α⁻¹ ∈ E) ∨ (∃ β ∈ D.B₀, x * β⁻¹ ∈ E) ∨ (∃ β ∈ D.B₁, x * β⁻¹ ∈ E) := by
  rcases D.transvection_E64_center hE hx hxN htv hmove with ⟨α, hα, h, -⟩ | ⟨β, hβ, h, -⟩ |
    ⟨β, hβ, h, -⟩
  · exact Or.inl ⟨α, hα, h⟩
  · exact Or.inr (Or.inl ⟨β, hβ, h⟩)
  · exact Or.inr (Or.inr ⟨β, hβ, h⟩)

end FooteCore

end CFSG.CGT.Foote81L6
