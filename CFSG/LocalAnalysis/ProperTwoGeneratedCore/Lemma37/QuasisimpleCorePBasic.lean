module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePQuaternion
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {G : Type} [Group G]

structure PartC (T Q P₁ : Subgroup G) (e u : G) : Prop where
  isPGroup : IsPGroup 2 T
  left_le : Q ≤ T
  right_le : P₁ ≤ T
  quaternion : Nonempty (Q ≃* QuaternionGroup 2)
  commute : ∀ q ∈ Q, ∀ p ∈ P₁, q * p = p * q
  mem_inf : ∀ x ∈ Q, x ∈ P₁ → x = 1 ∨ x = e
  order : orderOf e = 2
  center : e ∈ Subgroup.center G
  mem_left : e ∈ Q
  mem_right : e ∈ P₁
  self_mem : u ∈ P₁
  sq : u * u = e
  unique : ∀ p ∈ P₁, orderOf p = 2 → p = e
  normal_left : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q
  normal_right : ∀ t ∈ T, ∀ p ∈ P₁, t * p * t⁻¹ ∈ P₁
  involution_mem : ∀ t ∈ T, orderOf t = 2 → t ∈ Q ⊔ P₁
  inv_mul_mem : ∀ a ∈ T, ∀ b ∈ T, a ∉ Q ⊔ P₁ → b ∉ Q ⊔ P₁ → a⁻¹ * b ∈ Q ⊔ P₁
  outer : ∀ y ∈ T, y ∉ Q ⊔ P₁ → ∃ m ∈ Q, y * m * y⁻¹ ≠ m ∧ y * m * y⁻¹ ≠ m * e

namespace PartC

variable {T Q P₁ : Subgroup G} {e u : G}

theorem commute_centralElt (hc : PartC T Q P₁ e u) (g : G) : g * e = e * g :=
  Subgroup.mem_center_iff.mp hc.center g

theorem centralElt_mul_self (hc : PartC T Q P₁ e u) : e * e = 1 := by
  rw [← pow_two, ← hc.order, pow_orderOf_eq_one]

theorem centralElt_inv (hc : PartC T Q P₁ e u) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right hc.centralElt_mul_self

theorem centralElt_ne_one (hc : PartC T Q P₁ e u) : e ≠ 1 := fun h => by
  have h2 := hc.order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem mul_centralElt_mul_centralElt (hc : PartC T Q P₁ e u) (x : G) : x * e * e = x := by
  rw [mul_assoc, hc.centralElt_mul_self, mul_one]

theorem conj_centralElt (hc : PartC T Q P₁ e u) (y : G) : y * e * y⁻¹ = e := by
  rw [hc.commute_centralElt y, mul_inv_cancel_right]

theorem le_normalizer (hc : PartC T Q P₁ e u) : Q ≤ Subgroup.normalizer (P₁ : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    rw [hc.commute q hq p hp, mul_inv_cancel_right]
    exact hp
  · intro hp
    have h := hc.commute q hq _ hp
    have hpx : p = q * p * q⁻¹ := by
      calc p = q⁻¹ * ((q * p * q⁻¹) * q) := by group
        _ = q⁻¹ * (q * (q * p * q⁻¹)) := by rw [h]
        _ = q * p * q⁻¹ := by group
    rw [hpx]
    exact hp

theorem mem_sup_iff (hc : PartC T Q P₁ e u) {x : G} :
    x ∈ Q ⊔ P₁ ↔ ∃ q ∈ Q, ∃ p ∈ P₁, q * p = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q P₁ hc.le_normalizer,
    Set.mem_mul]
  rfl

theorem mul_mem_sup {q p : G} (hq : q ∈ Q) (hp : p ∈ P₁) : q * p ∈ Q ⊔ P₁ :=
  (Q ⊔ P₁).mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hp)

theorem sup_le (hc : PartC T Q P₁ e u) : Q ⊔ P₁ ≤ T :=
  _root_.sup_le hc.left_le hc.right_le

theorem mul_self_mem_sup (hc : PartC T Q P₁ e u) {y : G} (hyT : y ∈ T) : y * y ∈ Q ⊔ P₁ := by
  by_cases hy : y ∈ Q ⊔ P₁
  · exact (Q ⊔ P₁).mul_mem hy hy
  · have h := hc.inv_mul_mem y⁻¹ (T.inv_mem hyT) y hyT
      (fun h => hy (by simpa using (Q ⊔ P₁).inv_mem h)) hy
    rwa [inv_inv] at h

theorem mul_not_mem_sup {y q : G} (hy : y ∉ Q ⊔ P₁) (hq : q ∈ Q) : y * q ∉ Q ⊔ P₁ :=
  fun h => hy (by simpa using (Q ⊔ P₁).mul_mem h ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_left hq)))

theorem mul_self_of_ne (hc : PartC T Q P₁ e u) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1)
    (hxe : x ≠ e) : x * x = e :=
  quaternion_mul_self_of_ne hc.quaternion.some hc.mem_left hc.order hx hx1 hxe

theorem anticomm (hc : PartC T Q P₁ e u) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxx : x * x = e) (hyy : y * y = e) (hyx : y ≠ x) (hyxe : y ≠ x * e) :
    x * y = y * x * e :=
  quaternion_anticomm hc.quaternion.some hc.mem_left hc.order hx hy hxx hyy hyx hyxe

theorem enum (hc : PartC T Q P₁ e u) {x y w : G} (hx : x ∈ Q) (hy : y ∈ Q) (hw : w ∈ Q)
    (hxx : x * x = e) (hyy : y * y = e) (hyx : y ≠ x) (hyxe : y ≠ x * e) :
    w = 1 ∨ w = e ∨ w = x ∨ w = x * e ∨ w = y ∨ w = y * e ∨ w = x * y ∨ w = x * y * e :=
  quaternion_enum hc.quaternion.some hc.mem_left hc.order hx hy hw hxx hyy hyx hyxe

theorem moved_facts (hc : PartC T Q P₁ e u) {y m : G} (hyT : y ∈ T) (hm : m ∈ Q)
    (hm1 : y * m * y⁻¹ ≠ m) :
    m * m = e ∧ y * m * y⁻¹ ∈ Q ∧ y * m * y⁻¹ * (y * m * y⁻¹) = e := by
  have hb := hc.normal_left y hyT m hm
  have hm1' : m ≠ 1 := fun h => hm1 (by rw [h, mul_one, mul_inv_cancel])
  have hme : m ≠ e := fun h => hm1 (by rw [h, hc.conj_centralElt])
  have hb1 : y * m * y⁻¹ ≠ 1 := fun h => hm1' (by
    rw [mul_inv_eq_one, mul_eq_left] at h
    exact h)
  have hbe : y * m * y⁻¹ ≠ e := fun h => hme (by
    rw [← hc.conj_centralElt y] at h
    exact mul_left_cancel (mul_right_cancel h))
  exact ⟨hc.mul_self_of_ne hm hm1' hme, hb, hc.mul_self_of_ne hb hb1 hbe⟩

theorem exists_mul_mul_self_mem (hc : PartC T Q P₁ e u) {y : G} (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) : ∃ q ∈ Q, y * q ∉ Q ⊔ P₁ ∧ y * q * (y * q) ∈ P₁ := by
  obtain ⟨q₀, hq₀, p₀, hp₀, hy2⟩ := hc.mem_sup_iff.mp (hc.mul_self_mem_sup hyT)
  by_cases hq₀Z : q₀ = 1 ∨ q₀ = e
  · refine ⟨1, Q.one_mem, by simpa using hy, ?_⟩
    rw [mul_one, ← hy2]
    rcases hq₀Z with rfl | rfl
    · simpa using hp₀
    · exact P₁.mul_mem hc.mem_right hp₀
  push Not at hq₀Z
  obtain ⟨m, hm, hm1, hm2⟩ := hc.outer y hyT hy
  obtain ⟨hmm, hb, hbb⟩ := hc.moved_facts hyT hm hm1
  set b := y * m * y⁻¹ with hbdef
  have hq₀q₀ := hc.mul_self_of_ne hq₀ hq₀Z.1 hq₀Z.2
  have hb₀ : y * q₀ * y⁻¹ = q₀ ∨ y * q₀ * y⁻¹ = q₀ * e := by
    have hp₀' := hc.normal_right y hyT p₀ hp₀
    have hc₀ : (y * q₀ * y⁻¹) * (y * p₀ * y⁻¹) = q₀ * p₀ := by
      calc (y * q₀ * y⁻¹) * (y * p₀ * y⁻¹) = y * (q₀ * p₀) * y⁻¹ := by group
        _ = y * (y * y) * y⁻¹ := by rw [hy2]
        _ = y * y := by group
        _ = q₀ * p₀ := hy2.symm
    have hmem : q₀⁻¹ * (y * q₀ * y⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq₀)
      (hc.normal_left y hyT q₀ hq₀)
    have hmem' : q₀⁻¹ * (y * q₀ * y⁻¹) ∈ P₁ := by
      have h1 : q₀⁻¹ * (y * q₀ * y⁻¹) = p₀ * (y * p₀ * y⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, hc₀]
        group
      rw [h1]
      exact P₁.mul_mem hp₀ (P₁.inv_mem hp₀')
    rcases hc.mem_inf _ hmem hmem' with h | h
    · left
      rw [inv_mul_eq_one] at h
      exact h.symm
    · right
      rw [inv_mul_eq_iff_eq_mul] at h
      exact h
  have hconj_inj : ∀ a c : G, y * a * y⁻¹ = y * c * y⁻¹ → a = c := fun a c h =>
    mul_left_cancel (mul_right_cancel h)
  have hconj_e : ∀ a : G, y * (a * e) * y⁻¹ = y * a * y⁻¹ * e := fun a => by
    calc y * (a * e) * y⁻¹ = y * a * (e * y⁻¹) := by group
      _ = y * a * (y⁻¹ * e) := by rw [hc.commute_centralElt y⁻¹]
      _ = y * a * y⁻¹ * e := by group
  have hq₀m : q₀ ≠ m := by
    rintro rfl
    rcases hb₀ with h | h
    · exact hm1 h
    · exact hm2 h
  have hq₀me : q₀ ≠ m * e := by
    rintro rfl
    rcases hb₀ with h | h
    · rw [hconj_e] at h
      exact hm1 (mul_right_cancel h)
    · rw [hconj_e, hc.mul_centralElt_mul_centralElt] at h
      exact hm2 (by
        calc b = b * e * e := (hc.mul_centralElt_mul_centralElt b).symm
          _ = m * e := by rw [hbdef, h])
  have hbq : b = m * q₀ ∨ b = m * q₀ * e := by
    have hbq₀ : b ≠ q₀ := by
      intro h
      rcases hb₀ with h' | h'
      · exact hq₀m (hconj_inj _ _ (h'.trans h.symm))
      · exact hq₀me (hconj_inj _ _ (by rw [h', hconj_e, ← h]))
    have hbq₀e : b ≠ q₀ * e := by
      intro h
      have hq₀b : q₀ = b * e := by rw [h, hc.mul_centralElt_mul_centralElt]
      rcases hb₀ with h' | h'
      · exact hq₀me (hconj_inj _ _ (by rw [h', hconj_e, ← hq₀b]))
      · exact hq₀m (hconj_inj _ _ (by
          rw [h', hq₀b, hc.mul_centralElt_mul_centralElt]))
    rcases hc.enum hm hq₀ hb hmm hq₀q₀ hq₀m hq₀me with h | h | h | h | h | h | h | h
    · exact absurd (h ▸ hbb) (by rw [mul_one]; exact (hc.centralElt_ne_one).symm)
    · exact absurd (h ▸ hbb) (by rw [hc.centralElt_mul_self]; exact (hc.centralElt_ne_one).symm)
    · exact absurd h hm1
    · exact absurd h hm2
    · exact absurd h hbq₀
    · exact absurd h hbq₀e
    · exact Or.inl h
    · exact Or.inr h
  have hpm : m * p₀ = p₀ * m := hc.commute m hm p₀ hp₀
  refine ⟨m, hm, mul_not_mem_sup hy hm, ?_⟩
  have hsq : y * m * (y * m) = b * q₀ * m * p₀ := by
    calc y * m * (y * m) = b * (y * y) * m := by rw [hbdef]; group
      _ = b * (q₀ * p₀) * m := by rw [hy2]
      _ = b * q₀ * (m * p₀) := by rw [hpm]; group
      _ = b * q₀ * m * p₀ := by group
  rw [hsq]
  refine P₁.mul_mem ?_ hp₀
  rcases hbq with h | h
  · rw [h, show m * q₀ * q₀ * m = m * (q₀ * q₀) * m by group, hq₀q₀,
      hc.commute_centralElt m, mul_assoc, hmm, hc.centralElt_mul_self]
    exact P₁.one_mem
  · have h' : m * q₀ * e * q₀ * m = m * (q₀ * q₀) * e * m := by
      calc m * q₀ * e * q₀ * m = m * q₀ * (e * q₀) * m := by group
        _ = m * q₀ * (q₀ * e) * m := by rw [hc.commute_centralElt q₀]
        _ = m * (q₀ * q₀) * e * m := by group
    rw [h, h', hq₀q₀, hc.mul_centralElt_mul_centralElt, hmm]
    exact hc.mem_right

theorem exists_mul_self_mem (hc : PartC T Q P₁ e u) (hT : ¬ T ≤ Q ⊔ P₁) :
    ∃ y ∈ T, y ∉ Q ⊔ P₁ ∧ y * y ∈ P₁ := by
  obtain ⟨y, hyT, hy⟩ := Set.not_subset.mp hT
  obtain ⟨q, hq, hyq, hsq⟩ := hc.exists_mul_mul_self_mem hyT hy
  exact ⟨y * q, T.mul_mem hyT (hc.left_le hq), hyq, hsq⟩

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
