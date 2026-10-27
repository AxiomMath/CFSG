module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A V : Subgroup G} {a₁ b₁ a₂ b₂ z : G}

private theorem y7a_exists_mul_of_mem_sup {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let Q : Subgroup G :=
    { carrier := {x : G | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      mul_mem' := by
        rintro x y ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        exact ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, by
          calc (h1 * h2) * (k1 * k2) = h1 * (h2 * k1) * k2 := by group
            _ = h1 * (k1 * h2) * k2 := by rw [hc h2 hh2 k1 hk1]
            _ = (h1 * k1) * (h2 * k2) := by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by
          rw [mul_inv_rev, hc h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)]⟩ }
  have hHQ : H ≤ Q := fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩
  have hKQ : K ≤ Q := fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩
  have hxQ : x ∈ Q := mem_of_le_of_mem (sup_le hHQ hKQ) hx
  change ∃ h ∈ H, ∃ k ∈ K, h * k = x at hxQ
  exact hxQ

private theorem y7a_commute_A_of_gens {x : G}
    (h1 : x * a₁ = a₁ * x) (h2 : x * b₁ = b₁ * x)
    (h3 : x * a₂ = a₂ * x) (h4 : x * b₂ = b₂ * x) :
    ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), x * b = b * x := by
  intro b hb
  refine Subgroup.closure_induction (p := fun b _ => x * b = b * x) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]
  · simp
  · intro y y' _ _ ih1 ih2
    calc x * (y * y') = (x * y) * y' := (mul_assoc x y y').symm
      _ = (y * x) * y' := by rw [ih1]
      _ = y * (x * y') := mul_assoc y x y'
      _ = y * (y' * x) := by rw [ih2]
      _ = (y * y') * x := (mul_assoc y y' x).symm
  · intro y _ ih
    calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
      _ = y⁻¹ * (x * y) * y⁻¹ := by rw [← ih]
      _ = y⁻¹ * x := by group

private theorem y7a_mem_W_of_comm (hrel : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hAc : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) {a : G}
    (ha : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hcomm : ∀ u ∈ (closure {a₁, b₁} : Subgroup G), a * u = u * a) :
    a ∈ (closure {a₂, b₂} : Subgroup G) := by
  obtain ⟨u, hu, w, hw, rfl⟩ := y6q8_A_elems hrel a ha
  have huu : ∀ t ∈ (closure {a₁, b₁} : Subgroup G), u * t = t * u := by
    intro t ht
    have hat : (u * w) * t = t * (u * w) := hcomm t ht
    have hwt : w * t = t * w := (y6q8_commUW hrel t ht w hw).eq.symm
    have h2 : (u * t) * w = (t * u) * w := by
      calc (u * t) * w = u * (t * w) := by group
        _ = u * (w * t) := by rw [← hwt]
        _ = (u * w) * t := by group
        _ = t * (u * w) := hat
        _ = (t * u) * w := by group
    exact mul_right_cancel h2
  have hucen : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), u * b = b * u :=
    y7a_commute_A_of_gens (huu a₁ (Subgroup.subset_closure (by simp)))
      (huu b₁ (Subgroup.subset_closure (by simp)))
      ((y6q8_commUW hrel u hu a₂ (Subgroup.subset_closure (by simp))).eq)
      ((y6q8_commUW hrel u hu b₂ (Subgroup.subset_closure (by simp))).eq)
  have huZ : u = 1 ∨ u = z := y6q8_cen hrel hz hAc u (y6q8_U_le_A hu) hucen
  have hzW : z ∈ (closure {a₂, b₂} : Subgroup G) := by
    rw [← hrel.a2_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  rcases huZ with hu1 | huz
  · rw [hu1, one_mul]
    exact hw
  · rw [huz]
    exact mul_mem hzW hw

private theorem y7a_mem_U_of_comm (hrel : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hAc : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) {a : G}
    (ha : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hcomm : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), a * w = w * a) :
    a ∈ (closure {a₁, b₁} : Subgroup G) := by
  obtain ⟨u, hu, w, hw, rfl⟩ := y6q8_A_elems hrel a ha
  have hww : ∀ t ∈ (closure {a₂, b₂} : Subgroup G), w * t = t * w := by
    intro t ht
    have hat : (u * w) * t = t * (u * w) := hcomm t ht
    have hut : u * t = t * u := (y6q8_commUW hrel u hu t ht).eq
    have h2 : u * (w * t) = u * (t * w) := by
      calc u * (w * t) = (u * w) * t := by group
        _ = t * (u * w) := hat
        _ = (t * u) * w := by group
        _ = (u * t) * w := by rw [← hut]
        _ = u * (t * w) := by group
    exact mul_left_cancel h2
  have hwcen : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), w * b = b * w :=
    y7a_commute_A_of_gens
      ((y6q8_commUW hrel a₁ (Subgroup.subset_closure (by simp)) w hw).symm.eq)
      ((y6q8_commUW hrel b₁ (Subgroup.subset_closure (by simp)) w hw).symm.eq)
      (hww a₂ (Subgroup.subset_closure (by simp)))
      (hww b₂ (Subgroup.subset_closure (by simp)))
  have hwZ : w = 1 ∨ w = z := y6q8_cen hrel hz hAc w (y6q8_W_le_A hw) hwcen
  have hzU : z ∈ (closure {a₁, b₁} : Subgroup G) := by
    rw [← hrel.a1_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  rcases hwZ with hw1 | hwz
  · rw [hw1, mul_one]
    exact hu
  · rw [hwz]
    exact mul_mem hu hzU

theorem y7a_cent_UV (hA : A = closure {a₁, b₁, a₂, b₂}) (hrel : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : z ≠ 1) (hA32 : Nat.card ↥A = 32) (hVA : A ⊓ V = zpowers z)
    (hVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hVab : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v) :
    ∀ x ∈ A ⊔ V, ((∀ y ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V, x * y = y * x) ↔
      x ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V) := by
  have hAc : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    simpa only [hA] using hA32
  have hUA : (closure {a₁, b₁} : Subgroup G) ≤ A := by rw [hA]; exact y6q8_U_le_A
  have hWA : (closure {a₂, b₂} : Subgroup G) ≤ A := by rw [hA]; exact y6q8_W_le_A
  have hUV : ∀ u ∈ (closure {a₁, b₁} : Subgroup G), ∀ v ∈ V, u * v = v * u :=
    fun u hu v hv => hVc u (hUA hu) v hv
  have hWV : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), ∀ v ∈ V, w * v = v * w :=
    fun w hw v hv => hVc w (hWA hw) v hv
  intro x hx
  constructor
  · intro hcomm
    obtain ⟨a, ha, v, hv, rfl⟩ := y7a_exists_mul_of_mem_sup hVc hx
    have haA : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by simpa only [hA] using ha
    have hau : ∀ u ∈ (closure {a₁, b₁} : Subgroup G), a * u = u * a := by
      intro u hu
      have h1 : (a * v) * u = u * (a * v) := hcomm u (Subgroup.mem_sup_left hu)
      have hvu : u * v = v * u := hVc u (hUA hu) v hv
      have h2 : (a * u) * v = (u * a) * v := by
        calc (a * u) * v = a * (u * v) := by group
          _ = a * (v * u) := by rw [hvu]
          _ = (a * v) * u := by group
          _ = u * (a * v) := h1
          _ = (u * a) * v := by group
      exact mul_right_cancel h2
    have haW : a ∈ (closure {a₂, b₂} : Subgroup G) := y7a_mem_W_of_comm hrel hz hAc haA hau
    exact Subgroup.mul_mem_sup haW hv
  · intro hxW y hy
    obtain ⟨w, hw, v, hv, rfl⟩ := y7a_exists_mul_of_mem_sup hWV hxW
    obtain ⟨u, hu, v', hv', rfl⟩ := y7a_exists_mul_of_mem_sup hUV hy
    have hwu : Commute w u := (y6q8_commUW hrel u hu w hw).symm
    have hwv : Commute w v := (hVc w (hWA hw) v hv)
    have hwv' : Commute w v' := (hVc w (hWA hw) v' hv')
    have hvu : Commute v u := ((hVc u (hUA hu) v hv)).symm
    have hvv' : Commute v v' := (hVab v hv v' hv')
    exact ((hwu.mul_right hwv').mul_left (hvu.mul_right hvv')).eq

theorem y7a_cent_WV (hA : A = closure {a₁, b₁, a₂, b₂}) (hrel : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : z ≠ 1) (hA32 : Nat.card ↥A = 32) (hVA : A ⊓ V = zpowers z)
    (hVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hVab : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v) :
    ∀ x ∈ A ⊔ V, ((∀ y ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V, x * y = y * x) ↔
      x ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V) := by
  have hAc : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    simpa only [hA] using hA32
  have hUA : (closure {a₁, b₁} : Subgroup G) ≤ A := by rw [hA]; exact y6q8_U_le_A
  have hWA : (closure {a₂, b₂} : Subgroup G) ≤ A := by rw [hA]; exact y6q8_W_le_A
  have hUV : ∀ u ∈ (closure {a₁, b₁} : Subgroup G), ∀ v ∈ V, u * v = v * u :=
    fun u hu v hv => hVc u (hUA hu) v hv
  have hWV : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), ∀ v ∈ V, w * v = v * w :=
    fun w hw v hv => hVc w (hWA hw) v hv
  intro x hx
  constructor
  · intro hcomm
    obtain ⟨a, ha, v, hv, rfl⟩ := y7a_exists_mul_of_mem_sup hVc hx
    have haA : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by simpa only [hA] using ha
    have haw : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), a * w = w * a := by
      intro w hw
      have h1 : (a * v) * w = w * (a * v) := hcomm w (Subgroup.mem_sup_left hw)
      have hwv : w * v = v * w := hVc w (hWA hw) v hv
      have h2 : (a * w) * v = (w * a) * v := by
        calc (a * w) * v = a * (w * v) := by group
          _ = a * (v * w) := by rw [hwv]
          _ = (a * v) * w := by group
          _ = w * (a * v) := h1
          _ = (w * a) * v := by group
      exact mul_right_cancel h2
    have haU : a ∈ (closure {a₁, b₁} : Subgroup G) := y7a_mem_U_of_comm hrel hz hAc haA haw
    exact Subgroup.mul_mem_sup haU hv
  · intro hxU y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := y7a_exists_mul_of_mem_sup hUV hxU
    obtain ⟨w, hw, v', hv', rfl⟩ := y7a_exists_mul_of_mem_sup hWV hy
    have huw : Commute u w := y6q8_commUW hrel u hu w hw
    have huv : Commute u v := (hVc u (hUA hu) v hv)
    have huv' : Commute u v' := (hVc u (hUA hu) v' hv')
    have hwv : Commute w v := (hVc w (hWA hw) v hv)
    have hvv' : Commute v v' := (hVab v hv v' hv')
    exact ((huw.mul_right huv').mul_left ((hwv.symm).mul_right hvv')).eq

end CFSG.OddStandard.HigherRank.YamadaG23
