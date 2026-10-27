module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Background.G118S3
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace ShortComm

section Dihedral

variable {G : Type*} [Group G]

@[expose] def InE (z z' e : G) : Prop := e = 1 ∨ e = z ∨ e = z' ∨ e = z * z'

structure DihData (V : Subgroup G) (s s' z z' : G) : Prop where
  hz : z ∈ V
  hz' : z' ∈ V
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq : ∀ a ∈ V, a * a = 1
  s_cases : ∀ v ∈ V, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = v * z
  s'_cases : ∀ v ∈ V, s' * v * s'⁻¹ = v ∨ s' * v * s'⁻¹ = v * z'
  sz : s * z * s⁻¹ = z
  s'z' : s' * z' * s'⁻¹ = z'
  sz' : s * z' * s⁻¹ = z' * z
  s'z : s' * z * s'⁻¹ = z * z'

namespace DihData

variable {V : Subgroup G} {s s' z z' : G} (h : DihData V s s' z z')
include h

theorem zz'_comm : z * z' = z' * z := h.comm z h.hz z' h.hz'

theorem z_sq : z * z = 1 := h.sq z h.hz

theorem z'_sq : z' * z' = 1 := h.sq z' h.hz'

theorem u_z : s * s' * z * (s * s')⁻¹ = z' := by
  have e : s * s' * z * (s * s')⁻¹ = s * (s' * z * s'⁻¹) * s⁻¹ := by group
  rw [e, h.s'z]
  have e2 : s * (z * z') * s⁻¹ = (s * z * s⁻¹) * (s * z' * s⁻¹) := by group
  rw [e2, h.sz, h.sz']
  calc z * (z' * z) = (z * z') * z := by group
    _ = (z' * z) * z := by rw [h.zz'_comm]
    _ = z' * (z * z) := by group
    _ = z' := by rw [h.z_sq, mul_one]

theorem u_z' : s * s' * z' * (s * s')⁻¹ = z * z' := by
  have e : s * s' * z' * (s * s')⁻¹ = s * (s' * z' * s'⁻¹) * s⁻¹ := by group
  rw [e, h.s'z', h.sz', h.zz'_comm]

theorem u_zz' : s * s' * (z * z') * (s * s')⁻¹ = z := by
  have e : s * s' * (z * z') * (s * s')⁻¹ =
      (s * s' * z * (s * s')⁻¹) * (s * s' * z' * (s * s')⁻¹) := by group
  rw [e, h.u_z, h.u_z']
  calc z' * (z * z') = (z' * z) * z' := by group
    _ = (z * z') * z' := by rw [h.zz'_comm]
    _ = z * (z' * z') := by group
    _ = z := by rw [h.z'_sq, mul_one]

theorem u_act {v : G} (hv : v ∈ V) : ∃ e, InE z z' e ∧ s * s' * v * (s * s')⁻¹ = v * e := by
  have hu : s * s' * v * (s * s')⁻¹ = s * (s' * v * s'⁻¹) * s⁻¹ := by group
  rw [hu]
  rcases h.s'_cases v hv with h1 | h1
  · rw [h1]
    rcases h.s_cases v hv with h2 | h2
    · exact ⟨1, Or.inl rfl, by rw [h2, mul_one]⟩
    · exact ⟨z, Or.inr (Or.inl rfl), h2⟩
  · rw [h1]
    have e1 : s * (v * z') * s⁻¹ = (s * v * s⁻¹) * (s * z' * s⁻¹) := by group
    rw [e1, h.sz']
    rcases h.s_cases v hv with h2 | h2
    · rw [h2]
      exact ⟨z * z', Or.inr (Or.inr (Or.inr rfl)), by rw [h.zz'_comm]⟩
    · rw [h2]
      refine ⟨z', Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      calc v * z * (z' * z) = v * (z * (z' * z)) := by group
        _ = v * ((z * z') * z) := by group
        _ = v * ((z' * z) * z) := by rw [h.zz'_comm]
        _ = v * (z' * (z * z)) := by group
        _ = v * z' := by rw [h.z_sq, mul_one]

theorem commutator_mem_E {v : G} (hv : v ∈ V) : InE z z' (v⁻¹ * (s * s' * v * (s * s')⁻¹)) := by
  obtain ⟨e, he, hve⟩ := h.u_act hv
  rw [hve, inv_mul_cancel_left]
  exact he

theorem zz'_sq : z * z' * (z * z') = 1 := by
  calc z * z' * (z * z') = z * (z' * z) * z' := by group
    _ = z * (z * z') * z' := by rw [← h.zz'_comm]
    _ = (z * z) * (z' * z') := by group
    _ = 1 := by rw [h.z_sq, h.z'_sq, mul_one]

theorem cube_E {e : G} (he : InE z z' e) :
    e * (s * s' * e * (s * s')⁻¹) * (s * s' * (s * s' * e * (s * s')⁻¹) * (s * s')⁻¹) = 1 := by
  rcases he with he | he | he | he <;> rw [he]
  · simp
  · rw [h.u_z, h.u_z']
    exact h.zz'_sq
  · rw [h.u_z', h.u_zz']
    calc z' * (z * z') * z = (z' * z) * (z' * z) := by group
      _ = (z * z') * (z * z') := by rw [← h.zz'_comm]
      _ = 1 := h.zz'_sq
  · rw [h.u_zz', h.u_z]
    calc z * z' * z * z' = (z * z') * (z * z') := by group
      _ = 1 := h.zz'_sq

theorem u_cube {v : G} (hv : v ∈ V) : (s * s') ^ 3 * v * ((s * s') ^ 3)⁻¹ = v := by
  obtain ⟨e, he, hve⟩ := h.u_act hv
  have hc : ∀ a b : G, s * s' * (a * b) * (s * s')⁻¹ =
      (s * s' * a * (s * s')⁻¹) * (s * s' * b * (s * s')⁻¹) := fun a b => by group
  have h1 : s * s' * v * (s * s')⁻¹ = v * e := hve
  have h2 : s * s' * (s * s' * v * (s * s')⁻¹) * (s * s')⁻¹ =
      v * e * (s * s' * e * (s * s')⁻¹) := by
    rw [h1, hc]; rw [h1]
  have h3 : s * s' * (s * s' * (s * s' * v * (s * s')⁻¹) * (s * s')⁻¹) * (s * s')⁻¹ =
      v * e * (s * s' * e * (s * s')⁻¹) *
        (s * s' * (s * s' * e * (s * s')⁻¹) * (s * s')⁻¹) := by
    rw [h2, hc, hc, h1]
  have h4 : ∀ u : G, u ^ 3 * v * (u ^ 3)⁻¹ = u * (u * (u * v * u⁻¹) * u⁻¹) * u⁻¹ :=
    fun u => by
      have : u ^ 3 = u * u * u := by rw [pow_succ, pow_two]
      rw [this]; group
  rw [h4, h3]
  calc v * e * (s * s' * e * (s * s')⁻¹) * (s * s' * (s * s' * e * (s * s')⁻¹) * (s * s')⁻¹)
      = v * (e * (s * s' * e * (s * s')⁻¹) *
          (s * s' * (s * s' * e * (s * s')⁻¹) * (s * s')⁻¹)) := by group
    _ = v := by rw [h.cube_E he, mul_one]

theorem u_ne (hz1 : z ≠ 1) : s * s' * z' * (s * s')⁻¹ ≠ z' := by
  rw [h.u_z']
  intro e
  apply hz1
  have : z * z' = 1 * z' := by rw [one_mul]; exact e
  exact mul_right_cancel this

end DihData

end Dihedral

section Perfect

variable {G : Type*} [Group G]

theorem centralizes_of_perfect_of_card_le_four {L E : Subgroup G} [Finite E] (hperf : ⁅L, L⁆ = L)
    (hN : L ≤ Subgroup.normalizer (E : Set G)) (hcard : Nat.card E ≤ 4) :
    ∀ l ∈ L, ∀ e ∈ E, l * e * l⁻¹ = e := by
  classical
  let θ : ↥L →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hsolvP : Group.IsSolvable (Equiv.Perm ↥E) := Equiv.Perm.isSolvable hcard
  have hsolv : Group.IsSolvable (MulAut ↥E) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥E) (fun a b hab => MulEquiv.toEquiv_injective hab)
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hperfR : Group.IsPerfect ↥θ.range := Group.IsPerfect.range θ
  have hsub : Subsingleton ↥θ.range := by
    by_contra hns
    have : Nontrivial ↥θ.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable ↥θ.range inferInstance
  intro l hl e he
  have h1 : θ ⟨l, hl⟩ = 1 := by
    have := hsub.elim (⟨θ ⟨l, hl⟩, ⟨_, rfl⟩⟩ : ↥θ.range) 1
    exact congrArg Subtype.val this
  have h2 : ((θ ⟨l, hl⟩ ⟨e, he⟩ : ↥E) : G) = l * e * l⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe E (Subgroup.inclusion hN ⟨l, hl⟩) ⟨e, he⟩
  rw [← h2, h1]
  rfl

theorem eq_bot_of_perfect_of_isPGroup [Finite G] {P : Subgroup G} (hperf : ⁅P, P⁆ = P)
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  have : Finite ↥P := inferInstance
  have hnil : Group.IsNilpotent ↥P := h2.isNilpotent
  have hperfP : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isNilpotent ↥P hnil

end Perfect

section Perm3

open Equiv in
theorem perm3_cases : ∀ p R : Perm (Fin 3), R ^ 3 = 1 → R ≠ 1 → p ≠ 1 →
    p = R ∨ p = R⁻¹ ∨ p * R * p⁻¹ * R⁻¹ = R ∨ p * R * p⁻¹ * R⁻¹ = R⁻¹ := by decide

open Equiv in
theorem perm3_conj_ne_one : ∀ A R : Perm (Fin 3), A * A = 1 → A ≠ 1 → R ^ 3 = 1 → R ≠ 1 →
    R * A * R⁻¹ ≠ 1 := by decide

open Equiv in
theorem perm3_conj_ne_self : ∀ A R : Perm (Fin 3), A * A = 1 → A ≠ 1 → R ^ 3 = 1 → R ≠ 1 →
    R * A * R⁻¹ ≠ A := by decide

theorem card_perm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem eq_one_of_pow_three_of_pow_two_pow {H : Type*} [Group H] {a : H} (h3 : a ^ 3 = 1) {k : ℕ}
    (h2 : a ^ 2 ^ k = 1) : a = 1 := by
  have := (pow_gcd_eq_one (a := a) (m := 3) (n := 2 ^ k)).mpr ⟨h3, h2⟩
  have hg : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rwa [hg, pow_one] at this

section TwoInvolutions

theorem card_le_ncard_of_forall_mem' {Q : Type*} [Finite Q] {S : Set Q} (h : ∀ q, q ∈ S) :
    Nat.card Q ≤ S.ncard := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard fun q _ => h q

theorem nonempty_mulEquiv_perm_three_of_involutions' {Q : Type*} [Group Q] [Finite Q] {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) (ha1 : a ≠ 1)
    (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤) (hnot : ¬ ∀ q : Q, ∃ n : ℕ, q ^ 2 ^ n = 1) :
    Nonempty (Q ≃* Equiv.Perm (Fin 3)) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hx2 : a * b * (a * b) = b * a := by
    have h3 : a * b * (a * b) * (a * b) = 1 := by rw [← pow_three']; exact hab
    calc a * b * (a * b) = a * b * (a * b) * (a * b) * (a * b)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h3, one_mul]
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hbab : b * a * b = a * b * a := by
    calc b * a * b = a * b * (a * b) * b := by rw [hx2]
      _ = a * b * a * (b * b) := by simp only [mul_assoc]
      _ = a * b * a := by rw [hb, mul_one]
  have r4 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have r6 : a * (a * b * a) = b * a := by rw [← mul_assoc, ← mul_assoc, ha, one_mul]
  have r10 : b * (a * b) = a * b * a := by rw [← mul_assoc, hbab]
  have r11 : b * (b * a) = a := by rw [← mul_assoc, hb, one_mul]
  have r12 : b * (a * b * a) = a * b := by
    calc b * (a * b * a) = b * a * b * a := by simp only [mul_assoc]
      _ = a * b * a * a := by rw [hbab]
      _ = a * b := by rw [mul_assoc (a * b) a a, ha, mul_one]
  have hstep : ∀ x ∈ ({a, b} : Set Q), ∀ y ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q),
      x * y ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q) := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy | hy | hy | hy | hy <;> subst x <;> subst y
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl r4))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mul_assoc _ _ _).symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r6))))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r10))))
    · exact Or.inr (Or.inl r11)
    · exact Or.inr (Or.inr (Or.inr (Or.inl r12)))
  have hall : ∀ q : Q, q ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q) := by
    intro q
    have hq : q ∈ Subgroup.closure ({a, b} : Set Q) := by rw [hgen]; exact Subgroup.mem_top q
    induction hq using Subgroup.closure_induction_left with
    | one => exact Or.inl rfl
    | mul_left x hx y _ ih => exact hstep x hx y ih
    | inv_mul_cancel x hx y _ ih =>
      have hxinv : x⁻¹ = x := by
        rcases hx with hx | hx
        · rw [hx, ha']
        · rw [Set.mem_singleton_iff.1 hx, hb']
      rw [hxinv]
      exact hstep x hx y ih
  have h6 : Nat.card Q ≤ 6 := by
    refine (card_le_ncard_of_forall_mem' hall).trans ?_
    have h1 := Set.ncard_insert_le (1 : Q) ({a, b, a * b, b * a, a * b * a} : Set Q)
    have h2 := Set.ncard_insert_le a ({b, a * b, b * a, a * b * a} : Set Q)
    have h3 := Set.ncard_insert_le b ({a * b, b * a, a * b * a} : Set Q)
    have h4 := Set.ncard_insert_le (a * b) ({b * a, a * b * a} : Set Q)
    have h5 := Set.ncard_insert_le (b * a) ({a * b * a} : Set Q)
    have h6 := Set.ncard_singleton (a * b * a)
    omega
  have h2dvd : 2 ∣ Nat.card Q := by
    have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
    rw [← hord]
    exact orderOf_dvd_natCard a
  have hne : ∀ n : ℕ, Nat.card Q ≠ 2 ^ n := by
    intro n hn
    exact hnot fun q => ⟨n, by rw [← hn]; exact pow_card_eq_one'⟩
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hc6 : Nat.card Q = 6 := by
    have h2 : Nat.card Q ≠ 2 := by simpa using hne 1
    have h4 : Nat.card Q ≠ 4 := by simpa using hne 2
    obtain ⟨m, hm⟩ := h2dvd
    omega
  have hc1 : a * b ≠ 1 := by
    intro h1
    have hba : b = a := by rw [eq_inv_of_mul_eq_one_right h1, ha']
    have hall2 : ∀ q : Q, q ∈ ({1, a} : Set Q) := by
      intro q
      rcases hall q with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr (h.trans hba)
      · exact Or.inl (h.trans h1)
      · exact Or.inl (h.trans (by rw [hba, ha]))
      · exact Or.inr (h.trans (by rw [h1, one_mul]))
    have h2 := card_le_ncard_of_forall_mem' hall2
    have h3 := Set.ncard_insert_le (1 : Q) ({a} : Set Q)
    have h4 := Set.ncard_singleton a
    omega
  exact CFSG.Quasithin.G11.G118.g118_mulEquiv_perm_three hc6 ha ha1 hab hc1
    (by rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul])

end TwoInvolutions

end Perm3

end ShortComm

end CFSG.HardMathSupport.Cooperstein.StructureLie
