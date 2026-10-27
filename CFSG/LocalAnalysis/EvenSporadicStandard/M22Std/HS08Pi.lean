module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08AutDef

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

structure AutHyp (Y : Type*) [Group Y] (S J : Subgroup (MulAut Y)) : Prop where
  data : HS08AutData Y S J
  card_S : Nat.card S = 256
  J_le : J ≤ S
  J_comm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a
  J_sq : ∀ a ∈ J, a * a = 1
  card_J : Nat.card J = 32
  J_unique : ∀ E : Subgroup (MulAut Y), E ≤ S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    (∀ a ∈ E, a * a = 1) → 32 ≤ Nat.card E → E = J
  center_S : ∃ ζ ∈ S, ζ ≠ 1 ∧ ζ * ζ = 1 ∧ ζ ∈ innerImage Y ⊤ ∧
    ∀ α ∈ S, (∀ β ∈ S, β * α = α * β) ↔ (α = 1 ∨ α = ζ)
  card_A : Nat.card (MulAut Y) = 887040
  not_inner : ¬ S ≤ innerImage Y ⊤

structure PiData {Hh : Type*} [Group Hh] {Y : Type*} [Group Y] (π : Hh →* MulAut Y) (t : Hh) :
    Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_central : ∀ x, t * x = x * t
  surj : Function.Surjective π
  ker : ∀ x, π x = 1 ↔ (x = 1 ∨ x = t)
  lift_sq : ∀ x, π x ∈ innerImage Y ⊤ → π x * π x = 1 → x * x = 1
  sq_of_lift : ∀ u, π u ∈ innerImage Y ⊤ → π u * π u = 1 → π u ≠ 1 → ∃ w, w * w = u
  exists_outer : ∃ y, π y ∉ innerImage Y ⊤ ∧ y * y = 1

theorem inn_conj_mem {Y : Type*} [Group Y] (a b : MulAut Y) (hb : b ∈ innerImage Y ⊤) :
    a * b * a⁻¹ ∈ innerImage Y ⊤ := by
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hb
  refine Subgroup.mem_map.2 ⟨a y, Subgroup.mem_top _, ?_⟩
  ext z
  simp [MulAut.conj_apply]

namespace AutHyp

variable {Y : Type*} [Group Y] {S J : Subgroup (MulAut Y)} (A : AutHyp Y S J)
include A

theorem outer_mul_inner {α β : MulAut Y} (hα : α ∈ J) (hβ : β ∈ J)
    (hαo : α ∉ innerImage Y ⊤) (hβo : β ∉ innerImage Y ⊤) : α⁻¹ * β ∈ innerImage Y ⊤ := by
  set K : Subgroup J := (J ⊓ innerImage Y ⊤).subgroupOf J with hK
  have hKcard : Nat.card K = 16 := by
    rw [← A.data.card_inner]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      J ⊓ innerImage Y ⊤ ≤ J)).toEquiv
  have hidx : K.index = 2 := by
    have := K.card_mul_index
    rw [A.card_J, hKcard] at this
    omega
  have hmem : ∀ γ : MulAut Y, ∀ hγ : γ ∈ J, (⟨γ, hγ⟩ : J) ∈ K ↔ γ ∈ innerImage Y ⊤ := by
    intro γ hγ
    rw [hK, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hγ, h⟩⟩
  have h1 : (⟨α, hα⟩ : J)⁻¹ * ⟨β, hβ⟩ ∈ K := (Subgroup.mul_mem_iff_of_index_two hidx).2 (by
    rw [inv_mem_iff, hmem α hα, hmem β hβ]
    simp [hαo, hβo])
  exact (hmem (α⁻¹ * β) (J.mul_mem (J.inv_mem hα) hβ)).1 h1

end AutHyp

namespace PiData

variable {Hh : Type*} [Group Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  (h : PiData π t)

include h

theorem pi_t : π t = 1 := (h.ker t).2 (Or.inr rfl)

theorem eq_or_eq_mul_t {x y : Hh} (hxy : π x = π y) : x = y ∨ x = y * t := by
  have h1 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rcases (h.ker _).1 h1 with h2 | h2
  · left
    exact (inv_mul_eq_one.1 h2).symm
  · right
    calc x = y * (y⁻¹ * x) := by group
      _ = y * t := by rw [h2]

theorem t_comm (x : Hh) : x * t = t * x := (h.t_central x).symm

theorem commutes_of_mem {c : Hh} (hc : c = 1 ∨ c = t) (g : Hh) : c * g = g * c := by
  rcases hc with rfl | rfl
  · simp
  · exact h.t_central g

def cm (x a : Hh) : Hh := x * a * x⁻¹ * a⁻¹

theorem cm_mul {x a b : Hh} (hb : cm x b = 1 ∨ cm x b = t) :
    cm x (a * b) = cm x a * cm x b := by
  have hc := h.commutes_of_mem hb
  have e1 : x * a * x⁻¹ = cm x a * a := by simp only [cm]; group
  have e2 : x * b * x⁻¹ = cm x b * b := by simp only [cm]; group
  calc cm x (a * b) = (x * a * x⁻¹) * (x * b * x⁻¹) * b⁻¹ * a⁻¹ := by simp only [cm]; group
    _ = (cm x a * a) * (cm x b * b) * b⁻¹ * a⁻¹ := by rw [e1, e2]
    _ = cm x a * (a * cm x b * a⁻¹) := by group
    _ = cm x a * cm x b := by rw [← hc a]; group

theorem cm_t (x : Hh) : cm x t = 1 := by
  simp only [cm]
  rw [h.t_comm x]
  group

theorem cm_inv_conj {x a : Hh} (hx : cm x a = 1 ∨ cm x a = t) (n : Hh) :
    n * cm x a * n⁻¹ = cm x a := by
  have := h.commutes_of_mem hx n
  rw [← this]
  group

end PiData

namespace PiData

variable {Hh : Type*} [Group Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  {S J : Subgroup (MulAut Y)} (h : PiData π t) (A : AutHyp Y S J)
include h A

theorem inner_sq_comm {a b : Hh} (ha : π a ∈ J ⊓ innerImage Y ⊤)
    (hb : π b ∈ J ⊓ innerImage Y ⊤) : a * a = 1 ∧ a * b = b * a := by
  have haa : a * a = 1 := h.lift_sq a ha.2 (A.J_sq _ ha.1)
  have hbb : b * b = 1 := h.lift_sq b hb.2 (A.J_sq _ hb.1)
  have hab : a * b * (a * b) = 1 := by
    refine h.lift_sq (a * b) ?_ ?_
    · rw [map_mul]
      exact ((J ⊓ innerImage Y ⊤).mul_mem ha hb).2
    · rw [map_mul]
      exact A.J_sq _ (J.mul_mem ha.1 hb.1)
  refine ⟨haa, ?_⟩
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]

theorem cm_mem {x a : Hh} (hx : π x ∈ J) (ha : π a ∈ J) : cm x a = 1 ∨ cm x a = t := by
  refine (h.ker _).1 ?_
  simp only [cm, map_mul, map_inv]
  have := A.J_comm _ hx _ ha
  calc π x * π a * (π x)⁻¹ * (π a)⁻¹ = (π a * π x) * (π x)⁻¹ * (π a)⁻¹ := by rw [this]
    _ = 1 := by group

theorem cm_conj {x a n : Hh} (hx : π x ∈ J) (hxo : π x ∉ innerImage Y ⊤)
    (hn : π n ∈ normalizer (J : Set (MulAut Y))) (ha : π a ∈ J ⊓ innerImage Y ⊤) :
    cm x (n * a * n⁻¹) = cm x a := by
  have hnorm := Subgroup.mem_normalizer_iff.1 hn
  have hx'' : π (n⁻¹ * x * n) ∈ J := by
    rw [map_mul, map_mul, map_inv]
    refine (hnorm _).2 ?_
    have : π n * ((π n)⁻¹ * π x * π n) * (π n)⁻¹ = π x := by group
    rw [this]
    exact hx
  have hx''o : π (n⁻¹ * x * n) ∉ innerImage Y ⊤ := by
    intro hin
    apply hxo
    have := inn_conj_mem (π n) _ hin
    rw [map_mul, map_mul, map_inv] at this
    simpa [mul_assoc] using this
  have hb : π (x⁻¹ * (n⁻¹ * x * n)) ∈ J ⊓ innerImage Y ⊤ := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_inv]
      exact J.mul_mem (J.inv_mem hx) hx''
    · rw [map_mul, map_inv]
      exact A.outer_mul_inner hx hx'' hxo hx''o
  have hcomm := (h.inner_sq_comm A hb ha).2
  have h1 : cm (n⁻¹ * x * n) a = cm x a := by
    have hxb : n⁻¹ * x * n = x * (x⁻¹ * (n⁻¹ * x * n)) := by group
    rw [hxb]
    simp only [cm]
    calc x * (x⁻¹ * (n⁻¹ * x * n)) * a * (x * (x⁻¹ * (n⁻¹ * x * n)))⁻¹ * a⁻¹
        = x * ((x⁻¹ * (n⁻¹ * x * n)) * a) * (x⁻¹ * (n⁻¹ * x * n))⁻¹ * x⁻¹ * a⁻¹ := by group
      _ = x * (a * (x⁻¹ * (n⁻¹ * x * n))) * (x⁻¹ * (n⁻¹ * x * n))⁻¹ * x⁻¹ * a⁻¹ := by rw [hcomm]
      _ = x * a * x⁻¹ * a⁻¹ := by group
  have h2 : cm x (n * a * n⁻¹) = n * cm (n⁻¹ * x * n) a * n⁻¹ := by
    simp only [cm]; group
  rw [h2, h1]
  exact h.cm_inv_conj (h.cm_mem A hx ha.1) n

theorem cm_eq_of_ne_one {x a₁ a₂ : Hh} (hx : π x ∈ J) (hxo : π x ∉ innerImage Y ⊤)
    (h1 : π a₁ ∈ J ⊓ innerImage Y ⊤) (h2 : π a₂ ∈ J ⊓ innerImage Y ⊤) (h1n : π a₁ ≠ 1)
    (h2n : π a₂ ≠ 1) : cm x a₁ = cm x a₂ := by
  obtain ⟨d, hd, hda⟩ := A.data.trans_inner (π a₁) h1 h1n (π a₂) h2 h2n
  obtain ⟨n, rfl⟩ := h.surj d
  have hπ : π (n * a₁ * n⁻¹) = π a₂ := by rw [map_mul, map_mul, map_inv]; exact hda
  have hc := h.cm_conj A hx hxo hd h1
  rcases h.eq_or_eq_mul_t hπ with h3 | h3
  · rw [← hc, h3]
  · rw [← hc, h3, h.cm_mul (h.cm_t x |>.symm ▸ Or.inl rfl), h.cm_t x, mul_one]

omit h A in
theorem exists_ne_two {G : Type*} [Group G] {K : Subgroup G} (hK : 3 ≤ Nat.card K) (a : G) :
    ∃ b ∈ K, b ≠ 1 ∧ b ≠ a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hlt : ({1, a} : Set G).ncard < (K : Set G).ncard := by
    have h1 : ({1, a} : Set G).ncard ≤ 2 := by
      calc ({1, a} : Set G).ncard ≤ ({a} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h2 : (K : Set G).ncard = Nat.card K := (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨b, hbK, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  exact ⟨b, hbK, hb.1, hb.2⟩

theorem outer_comm_inner {x a : Hh} (hx : π x ∈ J) (hxo : π x ∉ innerImage Y ⊤)
    (ha : π a ∈ J ⊓ innerImage Y ⊤) : x * a = a * x := by
  have hcard : 3 ≤ Nat.card ↥(J ⊓ innerImage Y ⊤) := by rw [A.data.card_inner]; norm_num
  obtain ⟨α₁, hα₁, hα₁1⟩ : ∃ α₁ ∈ J ⊓ innerImage Y ⊤, α₁ ≠ 1 := by
    obtain ⟨b, hb, hb1, -⟩ := exists_ne_two (K := J ⊓ innerImage Y ⊤) hcard 1
    exact ⟨b, hb, hb1⟩
  obtain ⟨α₂, hα₂, hα₂1, hα₂ne⟩ := exists_ne_two (K := J ⊓ innerImage Y ⊤) hcard α₁
  obtain ⟨a₁, rfl⟩ := h.surj α₁
  obtain ⟨a₂, rfl⟩ := h.surj α₂
  have hα₁α₂ : π (a₁ * a₂) ∈ J ⊓ innerImage Y ⊤ := by
    rw [map_mul]; exact (J ⊓ innerImage Y ⊤).mul_mem hα₁ hα₂
  have hne12 : π (a₁ * a₂) ≠ 1 := by
    rw [map_mul]
    intro h1
    apply hα₂ne
    have hsq := A.J_sq _ hα₁.1
    calc π a₂ = (π a₁)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      _ = π a₁ := inv_eq_of_mul_eq_one_right hsq
  have e1 := h.cm_eq_of_ne_one A hx hxo hα₁ hα₂ hα₁1 hα₂1
  have e2 := h.cm_eq_of_ne_one A hx hxo hα₁ hα₁α₂ hα₁1 hne12
  have e3 : cm x (a₁ * a₂) = cm x a₁ * cm x a₂ := h.cm_mul (h.cm_mem A hx hα₂.1)
  have hc0 : cm x a₁ = 1 := by
    have : cm x a₁ = cm x a₁ * cm x a₁ := by
      calc cm x a₁ = cm x (a₁ * a₂) := e2
        _ = cm x a₁ * cm x a₂ := e3
        _ = cm x a₁ * cm x a₁ := by rw [e1]
    exact (mul_left_cancel (a := cm x a₁) (by rw [mul_one]; exact this)).symm
  by_cases hna : π a = 1
  · rcases (h.ker a).1 hna with rfl | rfl
    · simp
    · exact h.t_comm x
  · have := h.cm_eq_of_ne_one A hx hxo hα₁ ha hα₁1 hna
    rw [hc0] at this
    simp only [cm] at this
    calc x * a = (x * a * x⁻¹ * a⁻¹) * a * x := by group
      _ = a * x := by rw [← this]; group

omit h in
theorem outer_inv_mul_inner {x x' : Hh} (hx : π x ∈ J) (hxo : π x ∉ innerImage Y ⊤)
    (hx' : π x' ∈ J) (hx'o : π x' ∉ innerImage Y ⊤) :
    π (x⁻¹ * x') ∈ J ⊓ innerImage Y ⊤ := by
  rw [map_mul, map_inv]
  exact ⟨J.mul_mem (J.inv_mem hx) hx', A.outer_mul_inner hx hx' hxo hx'o⟩

theorem outer_sq {x : Hh} (hx : π x ∈ J) (hxo : π x ∉ innerImage Y ⊤) : x * x = 1 := by
  obtain ⟨y₀, hy₀o, hy₀sq⟩ := h.exists_outer
  have hy₀π : π y₀ * π y₀ = 1 := by rw [← map_mul, hy₀sq, map_one]
  obtain ⟨a, ha⟩ := A.data.outer_involution (π y₀) hy₀π hy₀o
  obtain ⟨n, rfl⟩ := h.surj a
  set y' : Hh := n * y₀ * n⁻¹ with hy'
  have hy'J : π y' ∈ J := by rw [hy', map_mul, map_mul, map_inv]; exact ha
  have hy'o : π y' ∉ innerImage Y ⊤ := by
    intro hin
    apply hy₀o
    have := inn_conj_mem (π n)⁻¹ _ hin
    rw [hy', map_mul, map_mul, map_inv] at this
    simpa [mul_assoc] using this
  have hy'sq : y' * y' = 1 := by
    rw [hy']
    calc n * y₀ * n⁻¹ * (n * y₀ * n⁻¹) = n * (y₀ * y₀) * n⁻¹ := by group
      _ = 1 := by rw [hy₀sq]; group
  have hb := PiData.outer_inv_mul_inner A hy'J hy'o hx hxo
  have hcomm := h.outer_comm_inner A hy'J hy'o hb
  have hbb := (h.inner_sq_comm A hb hb).1
  set b : Hh := y'⁻¹ * x with hbdef
  have hxb : x = y' * b := by rw [hbdef]; group
  rw [hxb]
  calc y' * b * (y' * b) = y' * (b * y') * b := by group
    _ = y' * (y' * b) * b := by rw [← hcomm]
    _ = (y' * y') * (b * b) := by group
    _ = 1 := by rw [hy'sq, hbb, one_mul]

theorem mul_self_of_pi_sq (x : Hh) (hx : π x * π x = 1) : x * x = 1 := by
  by_cases hin : π x ∈ innerImage Y ⊤
  · exact h.lift_sq x hin hx
  · obtain ⟨a, ha⟩ := A.data.outer_involution (π x) hx hin
    obtain ⟨n, rfl⟩ := h.surj a
    have hJ : π (n * x * n⁻¹) ∈ J := by rw [map_mul, map_mul, map_inv]; exact ha
    have ho : π (n * x * n⁻¹) ∉ innerImage Y ⊤ := by
      intro hin'
      apply hin
      have := inn_conj_mem (π n)⁻¹ _ hin'
      rw [map_mul, map_mul, map_inv] at this
      simpa [mul_assoc] using this
    have h1 := h.outer_sq A hJ ho
    calc x * x = n⁻¹ * (n * x * n⁻¹ * (n * x * n⁻¹)) * n := by group
      _ = 1 := by rw [h1]; group

theorem sq_of_mem_J {x : Hh} (hx : π x ∈ J) : x * x = 1 :=
  h.mul_self_of_pi_sq A x (A.J_sq _ hx)

theorem comm_of_mem_J {x y : Hh} (hx : π x ∈ J) (hy : π y ∈ J) : x * y = y * x := by
  by_cases hxi : π x ∈ innerImage Y ⊤ <;> by_cases hyi : π y ∈ innerImage Y ⊤
  · exact (h.inner_sq_comm A ⟨hx, hxi⟩ ⟨hy, hyi⟩).2
  · exact (h.outer_comm_inner A hy hyi ⟨hx, hxi⟩).symm
  · exact h.outer_comm_inner A hx hxi ⟨hy, hyi⟩
  · set b : Hh := x⁻¹ * y with hb
    have hbJ := PiData.outer_inv_mul_inner A hx hxi hy hyi
    have hxb : y = x * b := by rw [hb]; group
    rw [hxb]
    have := h.outer_comm_inner A hx hxi hbJ
    calc x * (x * b) = x * x * b := by group
      _ = x * (b * x) := by rw [mul_assoc, ← this]
      _ = x * b * x := by group

end PiData

end CFSG.EvenSporadicStandard.M22Std
