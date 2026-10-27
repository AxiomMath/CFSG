module

public import CFSG.LargeExtraspecial.DWSm77Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

section Swap

variable {u x : G} (hux : u * S.z * u⁻¹ = x) (hxu : u * x * u⁻¹ = S.z) (hxA : x ∈ D.A)
  (hxz : x ≠ S.z)

include hxu hxA in
theorem conj_B_le_M_of_swap : (D.conj u).B ≤ S.M := by
  intro b hb
  rw [S.mem_M_iff]
  have hc := D.comm x hxA _ (D.mem_conj_B.mp hb)
  calc b * S.z = b * (u * x * u⁻¹) := by rw [hxu]
    _ = u * (u⁻¹ * b * u * x) * u⁻¹ := by group
    _ = u * (x * (u⁻¹ * b * u)) * u⁻¹ := by rw [← hc]
    _ = u * x * u⁻¹ * b := by group
    _ = S.z * b := by rw [hxu]

include hxu hxA in
theorem z_mem_conj_A_of_swap : S.z ∈ (D.conj u).A := by
  rw [← hxu]
  exact conj_mem_map_conj u hxA

omit [Finite G] in
include hux in
theorem mem_conjBy_M_of_swap {m : G} : m ∈ (S.conjBy u).M ↔ m * x = x * m := by
  rw [(S.conjBy u).mem_M_iff, Setting.conjBy_z, hux]

omit [Finite G] in
theorem x_ne_one_of_swap (hux : u * S.z * u⁻¹ = x) : x ≠ 1 := by
  rintro rfl
  apply S.z_ne_one
  calc S.z = u⁻¹ * (u * S.z * u⁻¹) * u := by group
    _ = 1 := by rw [hux]; group

include hux hxu hxA hxz in
theorem eq_one_of_mem_B_conj_B_of_swap {t : G} (htB : t ∈ D.B) (htB' : t ∈ (D.conj u).B) :
    t = 1 := by
  by_contra ht1
  have hN : ∀ b ∈ (D.conj u).B, ∀ s ∈ D.B, b * s * b⁻¹ ∈ D.B := fun b hb s hs =>
    D.conj_B b (D.conj_B_le_M_of_swap hxu hxA hb) s hs
  have hxB : (S.conjBy u).z ∈ D.B := (D.conj u).z_mem_of_normalized hN htB htB' ht1
  rw [Setting.conjBy_z, hux] at hxB
  rcases D.inter x hxA hxB with h | h
  exacts [x_ne_one_of_swap hux h, hxz h]

include hux hxu hxA hxz in
theorem comm_B_conj_B_of_swap {b b' : G} (hb : b ∈ D.B) (hb' : b' ∈ (D.conj u).B) :
    b * b' = b' * b := by
  have hb'M := D.conj_B_le_M_of_swap hxu hxA hb'
  have hbM : b ∈ (S.conjBy u).M :=
    (mem_conjBy_M_of_swap hux).mpr (D.comm x hxA b hb).symm
  have h1 : b * b' * b⁻¹ * b'⁻¹ ∈ D.B := by
    have := D.conj_B b' hb'M b⁻¹ (D.B.inv_mem hb)
    rw [show b * b' * b⁻¹ * b'⁻¹ = b * (b' * b⁻¹ * b'⁻¹) by group]
    exact D.B.mul_mem hb this
  have h2 : b * b' * b⁻¹ * b'⁻¹ ∈ (D.conj u).B :=
    (D.conj u).B.mul_mem ((D.conj u).conj_B b hbM b' hb') ((D.conj u).B.inv_mem hb')
  have h3 := D.eq_one_of_mem_B_conj_B_of_swap hux hxu hxA hxz h1 h2
  calc b * b' = b * b' * b⁻¹ * b'⁻¹ * (b' * b) := by group
    _ = b' * b := by rw [h3, one_mul]

variable {a : G} (haA : a ∈ D.A) (hax : a * x * a⁻¹ = x * S.z)

omit hux hxu hxA hxz in
theorem mem_conj_mul_B_iff {y : G} : y ∈ (D.conj (a * u)).B ↔ a⁻¹ * y * a ∈ (D.conj u).B := by
  rw [mem_conj_B, mem_conj_B]
  constructor <;> intro h <;> convert h using 1 <;> group

include hux in
theorem commute_x_of_mem_conj_B {b : G} (hb : b ∈ (D.conj u).B) : b * x = x * b := by
  have := (S.conjBy u).QG_le_M ((D.conj u).B_le hb)
  rwa [mem_conjBy_M_of_swap hux] at this

include hux hax in
theorem commute_xz_of_mem_conj_mul_B {b : G} (hb : b ∈ (D.conj (a * u)).B) :
    b * (x * S.z) = x * S.z * b := by
  have := (S.conjBy (a * u)).QG_le_M ((D.conj (a * u)).B_le hb)
  rwa [(S.conjBy (a * u)).mem_M_iff, Setting.conjBy_z,
    show a * u * S.z * (a * u)⁻¹ = a * (u * S.z * u⁻¹) * a⁻¹ by group, hux, hax] at this

include hxu hxA haA in
theorem conj_mul_B_le_M {b : G} (hb : b ∈ (D.conj (a * u)).B) : b ∈ S.M := by
  have h := D.conj_B_le_M_of_swap hxu hxA ((D.mem_conj_mul_B_iff).mp hb)
  have e : b = a * (a⁻¹ * b * a) * a⁻¹ := by group
  rw [e]
  have haM : a ∈ S.M := S.QG_le_M (D.A_le haA)
  exact S.M.mul_mem (S.M.mul_mem haM h) (S.M.inv_mem haM)

include hux hxu hxA hax in
theorem conj_mem_conj_mul_B {b s : G} (hb : b ∈ (D.conj u).B) (hs : s ∈ (D.conj (a * u)).B) :
    b * s * b⁻¹ ∈ (D.conj (a * u)).B := by
  refine (D.conj (a * u)).conj_B b ?_ s hs
  rw [(S.conjBy (a * u)).mem_M_iff, Setting.conjBy_z,
    show a * u * S.z * (a * u)⁻¹ = a * (u * S.z * u⁻¹) * a⁻¹ by group, hux, hax]
  have h1 := D.commute_x_of_mem_conj_B hux hb
  have h2 := S.z_comm (D.conj_B_le_M_of_swap hxu hxA hb)
  calc b * (x * S.z) = x * (b * S.z) := by rw [← mul_assoc, h1, mul_assoc]
    _ = x * S.z * b := by rw [h2, mul_assoc]

include hux hxu hxA haA hax in
theorem conj_mem_conj_B_of_mem_conj_mul_B {b s : G} (hb : b ∈ (D.conj (a * u)).B)
    (hs : s ∈ (D.conj u).B) : b * s * b⁻¹ ∈ (D.conj u).B := by
  refine (D.conj u).conj_B b ?_ s hs
  rw [mem_conjBy_M_of_swap hux]
  have h1 := D.commute_xz_of_mem_conj_mul_B hux hax hb
  have h2 := S.z_comm (D.conj_mul_B_le_M hxu hxA haA hb)
  calc b * x = b * (x * S.z) * S.z := by rw [mul_assoc, mul_assoc, S.z_mul_z, mul_one]
    _ = x * S.z * (b * S.z) := by rw [h1, mul_assoc]
    _ = x * S.z * (S.z * b) := by rw [h2]
    _ = x * b := by rw [mul_assoc, ← mul_assoc S.z, S.z_mul_z, one_mul]

include hux hxu hxA hxz haA hax in
theorem eq_one_of_mem_conj_B_conj_mul_B {t : G} (ht : t ∈ (D.conj u).B)
    (ht' : t ∈ (D.conj (a * u)).B) : t = 1 := by
  by_contra ht1
  have hN : ∀ b ∈ (D.conj u).B, ∀ s ∈ (D.conj (a * u)).B, b * s * b⁻¹ ∈ (D.conj (a * u)).B :=
    fun b hb s hs => D.conj_mem_conj_mul_B hux hxu hxA hax hb hs
  have hN' : ∀ b ∈ (D.conj (a * u)).B, ∀ s ∈ (D.conj u).B, b * s * b⁻¹ ∈ (D.conj u).B :=
    fun b hb s hs => D.conj_mem_conj_B_of_mem_conj_mul_B hux hxu hxA haA hax hb hs
  have hx : (S.conjBy u).z ∈ (D.conj (a * u)).B :=
    (D.conj u).z_mem_of_normalized hN ht' ht ht1
  have hxz' : (S.conjBy (a * u)).z ∈ (D.conj u).B :=
    (D.conj (a * u)).z_mem_of_normalized hN' ht ht' ht1
  rw [Setting.conjBy_z, hux] at hx
  rw [Setting.conjBy_z, show a * u * S.z * (a * u)⁻¹ = a * (u * S.z * u⁻¹) * a⁻¹ by group, hux,
    hax] at hxz'
  have hxB : x ∈ (D.conj u).B := by
    have := (D.conj u).z_mem_B
    rwa [Setting.conjBy_z, hux] at this
  have hzB : S.z ∈ (D.conj u).B := by
    have e : S.z = x⁻¹ * (x * S.z) := by group
    rw [e]
    exact (D.conj u).B.mul_mem ((D.conj u).B.inv_mem hxB) hxz'
  rcases (D.conj u).inter S.z (D.z_mem_conj_A_of_swap hxu hxA) hzB with h | h
  · exact S.z_ne_one h
  · rw [Setting.conjBy_z, hux] at h
    exact hxz h.symm

include hux hxu hxA hxz haA hax in
theorem conj_B_inf_QG_of_swap {t : G} (ht : t ∈ (D.conj u).B) (htQ : t ∈ S.QG) :
    t = 1 ∨ t = x := by
  have hat : a * t * a⁻¹ ∈ (D.conj (a * u)).B := by
    rw [D.mem_conj_mul_B_iff]
    convert ht using 1
    group
  rcases S.mul_comm_or (D.A_le haA) htQ with h | h
  · left
    refine D.eq_one_of_mem_conj_B_conj_mul_B hux hxu hxA hxz haA hax ht ?_
    convert hat using 1
    rw [h]
    group
  · right
    have htz : t * S.z ∈ (D.conj (a * u)).B := by
      convert hat using 1
      rw [h, (S.z_comm (S.QG_le_M htQ))]
      group
    have hxz' : x * S.z ∈ (D.conj (a * u)).B := by
      have := (D.conj (a * u)).z_mem_B
      rwa [Setting.conjBy_z,
        show a * u * S.z * (a * u)⁻¹ = a * (u * S.z * u⁻¹) * a⁻¹ by group, hux, hax] at this
    have hxB : x ∈ (D.conj u).B := by
      have := (D.conj u).z_mem_B
      rwa [Setting.conjBy_z, hux] at this
    have h1 : t * x⁻¹ ∈ (D.conj (a * u)).B := by
      have e : t * x⁻¹ = t * S.z * (x * S.z)⁻¹ := by group
      rw [e]
      exact (D.conj (a * u)).B.mul_mem htz ((D.conj (a * u)).B.inv_mem hxz')
    have h2 : t * x⁻¹ ∈ (D.conj u).B := (D.conj u).B.mul_mem ht ((D.conj u).B.inv_mem hxB)
    have h3 := D.eq_one_of_mem_conj_B_conj_mul_B hux hxu hxA hxz haA hax h2 h1
    calc t = t * x⁻¹ * x := by group
      _ = x := by rw [h3, one_mul]

include hux hxu hxA hxz haA hax in
theorem two_mul_card_B_le_of_swap : 2 * Nat.card D.B ≤ Nat.card D.A := by
  have hdis : ∀ t ∈ (D.conj u).B, t ∈ (D.conj (a * u)).B → t = 1 := fun t ht ht' =>
    D.eq_one_of_mem_conj_B_conj_mul_B hux hxu hxA hxz haA hax ht ht'
  have hcomm : ∀ p ∈ (D.conj u).B, ∀ r ∈ (D.conj (a * u)).B, p * r = r * p := by
    intro p hp r hr
    have h1 : p * r * p⁻¹ * r⁻¹ ∈ (D.conj (a * u)).B :=
      (D.conj (a * u)).B.mul_mem (D.conj_mem_conj_mul_B hux hxu hxA hax hp hr)
        ((D.conj (a * u)).B.inv_mem hr)
    have h2 : p * r * p⁻¹ * r⁻¹ ∈ (D.conj u).B := by
      rw [show p * r * p⁻¹ * r⁻¹ = p * (r * p⁻¹ * r⁻¹) by group]
      exact (D.conj u).B.mul_mem hp
        (D.conj_mem_conj_B_of_mem_conj_mul_B hux hxu hxA haA hax hr ((D.conj u).B.inv_mem hp))
    have h3 := hdis _ h2 h1
    calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
      _ = r * p := by rw [h3, one_mul]
  have huniq : ∀ p ∈ (D.conj u).B, ∀ p' ∈ (D.conj u).B, ∀ r ∈ (D.conj (a * u)).B,
      ∀ r' ∈ (D.conj (a * u)).B, r * p = r' * p' → r = r' ∧ p = p' := by
    intro p hp p' hp' r hr r' hr' h
    have e : r'⁻¹ * r = p' * p⁻¹ := by
      calc r'⁻¹ * r = r'⁻¹ * (r * p) * p⁻¹ := by group
        _ = p' * p⁻¹ := by rw [h]; group
    have h1 : r'⁻¹ * r ∈ (D.conj u).B := by
      rw [e]
      exact (D.conj u).B.mul_mem hp' ((D.conj u).B.inv_mem hp)
    have h2 := hdis _ h1 ((D.conj (a * u)).B.mul_mem ((D.conj (a * u)).B.inv_mem hr') hr)
    have hrr : r = r' := by
      calc r = r' * (r'⁻¹ * r) := by group
        _ = r' := by rw [h2, mul_one]
    refine ⟨hrr, ?_⟩
    rw [hrr] at h
    exact mul_left_cancel h
  have hBM := D.conj_B_le_M_of_swap hxu hxA
  have hmemA : ∀ b ∈ (D.conj u).B, a * b * a⁻¹ * b⁻¹ ∈ D.A := fun b hb => by
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact D.A.mul_mem haA (D.conj_A b (hBM hb) a⁻¹ (D.A.inv_mem haA))
  have haB : ∀ b ∈ (D.conj u).B, a * b * a⁻¹ ∈ (D.conj (a * u)).B := fun b hb => by
    rw [D.mem_conj_mul_B_iff]
    convert hb using 1
    group
  have hxB : x ∈ (D.conj u).B := by
    have := (D.conj u).z_mem_B
    rwa [Setting.conjBy_z, hux] at this
  let φ : (D.conj u).B ⊕ (D.conj u).B → D.A := fun s => match s with
    | Sum.inl b => ⟨a * (b : G) * a⁻¹ * (b : G)⁻¹, hmemA b b.2⟩
    | Sum.inr b => ⟨x * (a * (b : G) * a⁻¹ * (b : G)⁻¹), D.A.mul_mem hxA (hmemA b b.2)⟩
  have hx' : ∀ b ∈ (D.conj u).B, x * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * (x * b⁻¹) :=
    fun b hb => by
      rw [← mul_assoc, hcomm x hxB _ (haB b hb)]
      group
  have hconj : ∀ b c : G, a * b * a⁻¹ = a * c * a⁻¹ → b = c := fun b c h => by
    have := congrArg (fun y => a⁻¹ * y * a) h
    simpa [mul_assoc] using this
  have hφ : Function.Injective φ := by
    rintro (b | b) (c | c) h <;> simp only [φ, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext (hconj _ _ (huniq _ (inv_mem b.2) _ (inv_mem c.2) _
        (haB b b.2) _ (haB c c.2) (by simpa [mul_assoc] using h)).1))
    · exfalso
      rw [hx' c c.2] at h
      obtain ⟨h1, h2⟩ := huniq _ (inv_mem b.2) _ ((D.conj u).B.mul_mem hxB (inv_mem c.2)) _
        (haB b b.2) _ (haB c c.2) (by simpa [mul_assoc] using h)
      have hbc := hconj _ _ h1
      rw [hbc] at h2
      exact x_ne_one_of_swap hux (by simpa using h2.symm)
    · exfalso
      rw [hx' b b.2] at h
      obtain ⟨h1, h2⟩ := huniq _ ((D.conj u).B.mul_mem hxB (inv_mem b.2)) _ (inv_mem c.2) _
        (haB b b.2) _ (haB c c.2) (by simpa [mul_assoc] using h)
      have hbc := hconj _ _ h1
      rw [hbc] at h2
      exact x_ne_one_of_swap hux (by simpa using h2)
    · rw [hx' b b.2, hx' c c.2] at h
      exact congrArg Sum.inr (Subtype.ext (hconj _ _ (huniq _
        ((D.conj u).B.mul_mem hxB (inv_mem b.2)) _ ((D.conj u).B.mul_mem hxB (inv_mem c.2)) _
        (haB b b.2) _ (haB c c.2) (by simpa [mul_assoc] using h)).1))
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_sum, D.card_conj_B u] at h
  omega

end Swap

section General

variable {g : G} (hxA : g * S.z * g⁻¹ ∈ D.A) (hxz : g * S.z * g⁻¹ ≠ S.z)

include hxA hxz

theorem exists_swap_of_mem_A :
    ∃ u : G, u * S.z * u⁻¹ = g * S.z * g⁻¹ ∧ u * (g * S.z * g⁻¹) * u⁻¹ = S.z := by
  obtain ⟨u, -, h1, h2⟩ := S.exists_swap rfl (D.A_le hxA) hxz
  exact ⟨u, h1, h2⟩

theorem conj_B_le_M : (D.conj g).B ≤ S.M := by
  obtain ⟨u, h1, h2⟩ := D.exists_swap_of_mem_A hxA hxz
  rw [D.conj_B_eq h1.symm]
  exact D.conj_B_le_M_of_swap h2 hxA

theorem z_mem_conj_A : S.z ∈ (D.conj g).A := by
  obtain ⟨u, h1, h2⟩ := D.exists_swap_of_mem_A hxA hxz
  rw [D.conj_A_eq h1.symm]
  exact D.z_mem_conj_A_of_swap h2 hxA

theorem comm_B_conj_B {b b' : G} (hb : b ∈ D.B) (hb' : b' ∈ (D.conj g).B) :
    b * b' = b' * b := by
  obtain ⟨u, h1, h2⟩ := D.exists_swap_of_mem_A hxA hxz
  rw [D.conj_B_eq h1.symm] at hb'
  exact D.comm_B_conj_B_of_swap h1 h2 hxA hxz hb hb'

theorem conj_B_inf_QG {t : G} (ht : t ∈ (D.conj g).B) (htQ : t ∈ S.QG) :
    t = 1 ∨ t = g * S.z * g⁻¹ := by
  obtain ⟨u, h1, h2⟩ := D.exists_swap_of_mem_A hxA hxz
  rw [D.conj_B_eq h1.symm] at ht
  obtain ⟨a, haA, hax⟩ := D.exists_conj_eq_mul_z_A hxA (x_ne_one_of_swap h1) hxz
  exact D.conj_B_inf_QG_of_swap h1 h2 hxA hxz haA hax ht htQ

theorem two_mul_card_B_le : 2 * Nat.card D.B ≤ Nat.card D.A := by
  obtain ⟨u, h1, h2⟩ := D.exists_swap_of_mem_A hxA hxz
  obtain ⟨a, haA, hax⟩ := D.exists_conj_eq_mul_z_A hxA (x_ne_one_of_swap h1) hxz
  exact D.two_mul_card_B_le_of_swap h1 h2 hxA hxz haA hax

end General

theorem not_mem_B_of_mem_A {g h : G} (hxA : g * S.z * g⁻¹ ∈ D.A) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hyB : h * S.z * h⁻¹ ∈ D.B) (hyz : h * S.z * h⁻¹ ≠ S.z) : False := by
  have h1 := D.two_mul_card_B_le hxA hxz
  have h2 := D.swap.two_mul_card_B_le (g := h) hyB hyz
  have h3 : 0 < Nat.card D.A := Nat.card_pos
  simp only [swap_A, swap_B] at h2
  omega

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
