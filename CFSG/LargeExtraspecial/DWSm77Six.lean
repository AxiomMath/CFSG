module

public import CFSG.LargeExtraspecial.DWSm77Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

section Closure

variable {H : Type*} [Group H]

theorem mul_self_eq_one_of_mem_closure {s : Set H} (hcomm : s.Pairwise Commute)
    (hs : ∀ a ∈ s, a * a = 1) {a : H} (ha : a ∈ closure s) : a * a = 1 := by
  have hc := Subgroup.isMulCommutative_closure hcomm
  induction ha using closure_induction with
  | mem a ha => exact hs a ha
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := by
      have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, iha, one_mul, ihb]
  | inv a _ iha =>
    rw [← mul_inv_rev, iha, inv_one]

end Closure

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

section Six

variable (hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z) (h8 : 8 < Nat.card D.A)
  (hB8 : 8 < Nat.card D.B ∨ ∀ b ∈ D.B, b ^ 2 = 1 → b = 1 ∨ b = S.z)

include hB h8 hB8

theorem commutator_mem_QG_of_commute {g₁ g₂ : G} (hx₁A : g₁ * S.z * g₁⁻¹ ∈ D.A)
    (hx₁z : g₁ * S.z * g₁⁻¹ ≠ S.z) (hx₂A : g₂ * S.z * g₂⁻¹ ∈ D.A)
    (hx12 : g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹) = g₂ * S.z * g₂⁻¹ * (g₁ * S.z * g₁⁻¹))
    {b₁ b₂ : G} (hb₁ : b₁ ∈ (D.conj g₁).B) (hb₂ : b₂ ∈ (D.conj g₂).B) :
    b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ S.QG := by
  have hx₂A' := D.mem_conj_A_of_commute hB h8 hB8 hx₁A hx₁z hx₂A hx12
  by_cases he : g₂ * S.z * g₂⁻¹ = g₁ * S.z * g₁⁻¹
  · rw [D.conj_B_eq he] at hb₂
    rcases (S.conjBy g₁).commutator_eq_one_or_z ((D.conj g₁).B_le hb₁)
      ((D.conj g₁).B_le hb₂) with h | h
    · rw [h]
      exact S.QG.one_mem
    · rw [h]
      exact D.A_le hx₁A
  · have hk : g₂ * g₁⁻¹ * (S.conjBy g₁).z * (g₂ * g₁⁻¹)⁻¹ = g₂ * S.z * g₂⁻¹ := by
      rw [Setting.conjBy_z]
      group
    have hkA : g₂ * g₁⁻¹ * (S.conjBy g₁).z * (g₂ * g₁⁻¹)⁻¹ ∈ (D.conj g₁).A := by
      rw [hk]
      exact hx₂A'
    have hkz : g₂ * g₁⁻¹ * (S.conjBy g₁).z * (g₂ * g₁⁻¹)⁻¹ ≠ (S.conjBy g₁).z := by
      rw [hk, Setting.conjBy_z]
      exact he
    have hb₂' : b₂ ∈ ((D.conj g₁).conj (g₂ * g₁⁻¹)).B := by
      rw [Decomp.mem_conj_B, Decomp.mem_conj_B]
      rw [Decomp.mem_conj_B] at hb₂
      convert hb₂ using 1
      group
    have h := (D.conj g₁).comm_B_conj_B hkA hkz hb₁ hb₂'
    rw [show b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = 1 by rw [h]; group]
    exact S.QG.one_mem

theorem exists_not_commute_conj {g : G} (hxA : g * S.z * g⁻¹ ∈ D.A)
    (hxz : g * S.z * g⁻¹ ≠ S.z) :
    ∃ h₁ h₂ : G, h₁ * S.z * h₁⁻¹ ∈ D.A ∧ h₂ * S.z * h₂⁻¹ ∈ D.A ∧
      h₁ * S.z * h₁⁻¹ * (h₂ * S.z * h₂⁻¹) ≠ h₂ * S.z * h₂⁻¹ * (h₁ * S.z * h₁⁻¹) := by
  by_contra hall
  push Not at hall
  have hmA : ∀ m ∈ S.M, m * g * S.z * (m * g)⁻¹ ∈ D.A := fun m hm => by
    have := D.conj_A m hm _ hxA
    convert this using 1
    group
  have hmz : ∀ m ∈ S.M, m * g * S.z * (m * g)⁻¹ ≠ S.z := fun m hm h => by
    apply hxz
    have e : m * (g * S.z * g⁻¹) * m⁻¹ = S.z := by
      calc m * (g * S.z * g⁻¹) * m⁻¹ = m * g * S.z * (m * g)⁻¹ := by group
        _ = S.z := h
    calc g * S.z * g⁻¹ = m⁻¹ * (m * (g * S.z * g⁻¹) * m⁻¹) * m := by group
      _ = m⁻¹ * S.z * m := by rw [e]
      _ = S.z := by rw [S.z_comm (S.M.inv_mem hm)]; group
  have hcommB : ∀ m₁ ∈ S.M, ∀ m₂ ∈ S.M, ∀ b₁ ∈ (D.conj (m₁ * g)).B,
      ∀ b₂ ∈ (D.conj (m₂ * g)).B, b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ S.QG :=
    fun m₁ hm₁ m₂ hm₂ b₁ hb₁ b₂ hb₂ => D.commutator_mem_QG_of_commute hB h8 hB8 (hmA m₁ hm₁)
      (hmz m₁ hm₁) (hmA m₂ hm₂) (hall _ _ (hmA m₁ hm₁) (hmA m₂ hm₂)) hb₁ hb₂
  set s : Set S.M := {m | (m : G) ∈ S.QG ∨ ∃ m' ∈ S.M, (m : G) ∈ (D.conj (m' * g)).B} with hs
  have hRn : (closure s).Normal := by
    constructor
    intro r hr n
    induction hr using closure_induction with
    | mem r hr =>
      apply Subgroup.subset_closure
      rcases hr with h | ⟨m', hm', h⟩
      · exact Or.inl (S.conj_mem_QG n.2 h)
      · refine Or.inr ⟨n * m', S.M.mul_mem n.2 hm', ?_⟩
        rw [Decomp.mem_conj_B] at h ⊢
        convert h using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : n * (a * b) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hsQ : ∀ a ∈ s, ((a * a : S.M) : G) ∈ S.QG := by
    rintro a (h | ⟨m', hm', h⟩)
    · exact S.QG.mul_mem h h
    · rcases (S.conjBy (m' * g)).sq_eq_one_or_z ((D.conj (m' * g)).B_le h) with e | e
      · rw [Subgroup.coe_mul, ← pow_two, e]
        exact S.QG.one_mem
      · rw [Subgroup.coe_mul, ← pow_two, e]
        exact D.A_le (hmA m' hm')
  have hρs : ∀ a ∈ s, ∀ b ∈ s, S.ρ a * S.ρ b = S.ρ b * S.ρ a := by
    intro a ha b hb
    rcases ha with ha | ⟨m₁, hm₁, ha⟩
    · rw [(S.ρ_eq_one_iff a).mpr ha, one_mul, mul_one]
    rcases hb with hb | ⟨m₂, hm₂, hb⟩
    · rw [(S.ρ_eq_one_iff b).mpr hb, one_mul, mul_one]
    have h1 : S.ρ (a * b * a⁻¹ * b⁻¹) = 1 := (S.ρ_eq_one_iff _).mpr (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcommB m₁ hm₁ m₂ hm₂ _ ha _ hb)
    simp only [map_mul, map_inv] at h1
    calc S.ρ a * S.ρ b = S.ρ a * S.ρ b * (S.ρ a)⁻¹ * (S.ρ b)⁻¹ * (S.ρ b * S.ρ a) := by group
      _ = S.ρ b * S.ρ a := by rw [h1, one_mul]
  have hsq : ∀ r ∈ closure s, S.ρ r * S.ρ r = 1 := by
    intro r hr
    have hr' : S.ρ r ∈ closure (S.ρ '' s) := by
      rw [← MonoidHom.map_closure]
      exact mem_map_of_mem _ hr
    refine mul_self_eq_one_of_mem_closure ?_ ?_ hr'
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
      exact hρs a ha b hb
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      exact (S.ρ_eq_one_iff _).mpr (hsQ a ha)
  have hR2 : IsPGroup 2 (closure s) := by
    intro r
    refine ⟨3, ?_⟩
    have h1 : S.ρ ((r : S.M) * r) = 1 := by
      rw [map_mul]
      exact hsq r r.2
    have h2 := S.pow_four_eq_one ((S.ρ_eq_one_iff _).mp h1)
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one] at h2 ⊢
    calc ((r : S.M) : G) ^ 2 ^ 3 = (((r : S.M) : G) * ((r : S.M) : G)) ^ 4 := by
          rw [← pow_two, ← pow_mul]
          norm_num
      _ = 1 := h2
  have hRQ := S.le_of_normal _ hRn hR2
  obtain ⟨b, hb, hb1, hbx⟩ := (D.conj g).ne_B
  have hbM : b ∈ S.M := D.conj_B_le_M hxA hxz hb
  have hbs : (⟨b, hbM⟩ : S.M) ∈ s := Or.inr ⟨1, S.M.one_mem, by rw [one_mul]; exact hb⟩
  have hbQ : b ∈ S.QG := ⟨⟨b, hbM⟩, hRQ (Subgroup.subset_closure hbs), rfl⟩
  rcases D.conj_B_inf_QG hxA hxz hb hbQ with h | h
  · exact hb1 h
  · exact hbx h

theorem mul_conj_of_commute {g h : G} (hxA : g * S.z * g⁻¹ ∈ D.A) (hyA : h * S.z * h⁻¹ ∈ D.A)
    (hne : g * S.z * g⁻¹ ≠ h * S.z * h⁻¹)
    (hxy : g * S.z * g⁻¹ * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * (g * S.z * g⁻¹)) :
    ∃ k : G, g * S.z * g⁻¹ * (h * S.z * h⁻¹) = k * S.z * k⁻¹ := by
  have hx1 : g * S.z * g⁻¹ ≠ 1 := (S.conjBy g).z_ne_one
  have hy1 : h * S.z * h⁻¹ ≠ 1 := (S.conjBy h).z_ne_one
  by_cases hxz : g * S.z * g⁻¹ = S.z
  · have hyz : h * S.z * h⁻¹ ≠ S.z := fun e => hne (hxz.trans e.symm)
    obtain ⟨a, haA, ha⟩ := D.exists_conj_eq_mul_z_A hyA hy1 hyz
    refine ⟨a * h, ?_⟩
    rw [hxz, ← S.z_comm_QG (D.A_le hyA)]
    calc h * S.z * h⁻¹ * S.z = a * (h * S.z * h⁻¹) * a⁻¹ := ha.symm
      _ = a * h * S.z * (a * h)⁻¹ := by group
  by_cases hyz : h * S.z * h⁻¹ = S.z
  · obtain ⟨a, haA, ha⟩ := D.exists_conj_eq_mul_z_A hxA hx1 hxz
    refine ⟨a * g, ?_⟩
    rw [hyz]
    calc g * S.z * g⁻¹ * S.z = a * (g * S.z * g⁻¹) * a⁻¹ := ha.symm
      _ = a * g * S.z * (a * g)⁻¹ := by group
  have hyAx := D.mem_conj_A_of_commute hB h8 hB8 hxA hxz hyA hxy
  obtain ⟨a, -, ha⟩ := (D.conj g).exists_conj_eq_mul_z_A hyAx hy1 (by
    rw [Setting.conjBy_z]
    exact hne.symm)
  refine ⟨a * h, ?_⟩
  rw [hxy]
  calc h * S.z * h⁻¹ * (g * S.z * g⁻¹) = a * (h * S.z * h⁻¹) * a⁻¹ := by
        rw [ha, Setting.conjBy_z]
    _ = a * h * S.z * (a * h)⁻¹ := by group

end Six

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
