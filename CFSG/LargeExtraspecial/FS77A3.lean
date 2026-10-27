module

public import CFSG.LargeExtraspecial.FS77A1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup

theorem conj_mul_inv_mem_of_mem {G : Type*} [Group G] {K : Subgroup G} {y m : G}
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hym : y * m * y⁻¹ * m⁻¹ ∈ K) {g : G} (hg : g * m⁻¹ ∈ K) :
    y * g * y⁻¹ * m⁻¹ ∈ K := by
  have h := mul_mem (hyK _ hg) hym
  have e : y * (g * m⁻¹) * y⁻¹ * (y * m * y⁻¹ * m⁻¹) = y * g * y⁻¹ * m⁻¹ := by group
  rwa [e] at h

theorem exists_commute_mul_of_isPGroup {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsPGroup 2 K) {y : G} {e : ℕ} (hy : orderOf y = 3 ^ e)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) {m : G} (hym : y * m * y⁻¹ * m⁻¹ ∈ K) :
    ∃ k ∈ K, y * (k * m) * y⁻¹ = k * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ n : ℕ, ∀ g : G, g * m⁻¹ ∈ K → y ^ n * g * (y ^ n)⁻¹ * m⁻¹ ∈ K := by
    intro n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih =>
      intro g hg
      have h1 := conj_mul_inv_mem_of_mem hyK hym (ih g hg)
      have e1 : y * (y ^ n * g * (y ^ n)⁻¹) * y⁻¹ = y ^ (n + 1) * g * (y ^ (n + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e1] at h1
  have hmem : ∀ h ∈ zpowers y, ∀ g : G, g * m⁻¹ ∈ K → h * g * h⁻¹ * m⁻¹ ∈ K := by
    intro h hh g hg
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff h y).mp (mem_powers_iff_mem_zpowers.mpr hh)
    exact hpow n g hg
  let α := {g : G // g * m⁻¹ ∈ K}
  let act : MulAction (zpowers y) α :=
    { smul := fun h g => ⟨(h : G) * g.1 * (h : G)⁻¹, hmem h h.2 g.1 g.2⟩
      one_smul := fun g => Subtype.ext (show (1 : G) * g.1 * (1 : G)⁻¹ = g.1 by group)
      mul_smul := fun h₁ h₂ g => Subtype.ext
        (show (h₁ : G) * h₂ * g.1 * ((h₁ : G) * h₂)⁻¹ =
          (h₁ : G) * ((h₂ : G) * g.1 * (h₂ : G)⁻¹) * (h₁ : G)⁻¹ by group) }
  have hY : IsPGroup 3 (zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers, hy])
  have hα : Nat.card α = Nat.card K := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1 * m⁻¹, g.2⟩
        invFun := fun k => ⟨k.1 * m, by simp⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  obtain ⟨c, hc⟩ := hK.exists_card_eq
  have hmod := hY.card_modEq_card_fixedPoints α
  rw [hα, hc] at hmod
  have hne : (MulAction.fixedPoints (zpowers y) α).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : Nat.card (MulAction.fixedPoints (zpowers y) α) = 0 := by
      rw [h]
      exact Nat.card_of_isEmpty
    rw [h0] at hmod
    have h3 : 3 ∣ 2 ^ c := Nat.dvd_of_mod_eq_zero hmod
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  obtain ⟨⟨g, hg⟩, hfix⟩ := hne
  refine ⟨g * m⁻¹, hg, ?_⟩
  have h1 := congrArg Subtype.val (hfix ⟨y, mem_zpowers y⟩)
  simp only [inv_mul_cancel_right]
  exact h1

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

variable (D : CaseA S)

@[expose] def IsCycle (w : G) : Prop := w * S.z * w⁻¹ = D.a * S.z ∧ w * D.a * w⁻¹ = S.z

theorem a_mul_z_mul_z : D.a * S.z * S.z = D.a := by rw [mul_assoc, S.z_mul_z, mul_one]

theorem IsCycle.conj_az {w : G} (hw : D.IsCycle w) : w * (D.a * S.z) * w⁻¹ = D.a := by
  have : w * (D.a * S.z) * w⁻¹ = (w * D.a * w⁻¹) * (w * S.z * w⁻¹) := by group
  rw [this, hw.1, hw.2, ← mul_assoc, ← S.z_comm (D.a_mem_M), D.a_mul_z_mul_z]

omit [Finite G] in
theorem conj_pow_succ (w x : G) (n : ℕ) :
    w ^ (n + 1) * x * (w ^ (n + 1))⁻¹ = w * (w ^ n * x * (w ^ n)⁻¹) * w⁻¹ := by
  rw [pow_succ']
  group

theorem IsCycle.pow {w : G} (hw : D.IsCycle w) (n : ℕ) :
    (n % 3 = 0 → w ^ n * S.z * (w ^ n)⁻¹ = S.z ∧ w ^ n * D.a * (w ^ n)⁻¹ = D.a) ∧
    (n % 3 = 1 → w ^ n * S.z * (w ^ n)⁻¹ = D.a * S.z ∧ w ^ n * D.a * (w ^ n)⁻¹ = S.z) ∧
    (n % 3 = 2 → w ^ n * S.z * (w ^ n)⁻¹ = D.a ∧ w ^ n * D.a * (w ^ n)⁻¹ = D.a * S.z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [conj_pow_succ, conj_pow_succ]
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
    · obtain ⟨h1, h2⟩ := ih.1 h
      have h' : (n + 1) % 3 = 1 := by omega
      refine ⟨fun h0 => by omega, fun _ => ?_, fun h0 => by omega⟩
      rw [h1, h2]
      exact ⟨hw.1, hw.2⟩
    · obtain ⟨h1, h2⟩ := ih.2.1 h
      refine ⟨fun h0 => by omega, fun h0 => by omega, fun _ => ?_⟩
      rw [h1, h2]
      exact ⟨hw.conj_az D, hw.1⟩
    · obtain ⟨h1, h2⟩ := ih.2.2 h
      refine ⟨fun _ => ?_, fun h0 => by omega, fun h0 => by omega⟩
      rw [h1, h2]
      exact ⟨hw.2, hw.conj_az D⟩

theorem az_ne_z : D.a * S.z ≠ S.z := by
  intro h
  apply D.a_ne_one
  calc D.a = D.a * S.z * S.z := D.a_mul_z_mul_z.symm
    _ = 1 := by rw [h, S.z_mul_z]

theorem IsCycle.pow_of_mod {w : G} (hw : D.IsCycle w) {n : ℕ} (hn : n % 3 = 1) :
    D.IsCycle (w ^ n) :=
  (hw.pow D n).2.1 hn

theorem exists_isCycle_pow_three {w : G} (hw : D.IsCycle w) :
    ∃ j : ℕ, D.IsCycle (w ^ j) ∧ ∃ e : ℕ, orderOf (w ^ j) = 3 ^ e := by
  have ho : orderOf w ≠ 0 := (orderOf_pos w).ne'
  obtain ⟨e, m', hm', hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hom
    exact ho hom
  have h1 : orderOf (w ^ m') = 3 ^ e := by
    rw [orderOf_pow_of_dvd hm'0 ⟨3 ^ e, by rw [hom, mul_comm]⟩, hom,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm'0)]
  rcases (show m' % 3 = 0 ∨ m' % 3 = 1 ∨ m' % 3 = 2 by omega) with h3 | h3 | h3
  · exact absurd (Nat.dvd_of_mod_eq_zero h3) hm'
  · exact ⟨m', hw.pow_of_mod D h3, e, h1⟩
  · refine ⟨m' * 2, ?_, e, ?_⟩
    · exact hw.pow_of_mod D (by omega)
    · rw [pow_mul, orderOf_pow' _ (by norm_num), h1]
      have hc : Nat.Coprime (3 ^ e) 2 := Nat.Coprime.pow_left e (by norm_num)
      rw [hc.gcd_eq_one, Nat.div_one]

theorem exists_cycle : ∃ w : G, D.IsCycle w := by
  obtain ⟨u, -, hu1, hu2⟩ := S.exists_swap (t := D.a) rfl D.haQ D.hne
  obtain ⟨r, hrQ, hr⟩ := S.exists_conj_eq_mul_z D.a_mem_QG D.a_ne_one D.a_ne_z
  have hrz : r * S.z * r⁻¹ = S.z := by
    rw [S.z_comm (S.QG_le_M hrQ)]
    group
  refine ⟨r * u, ?_, ?_⟩
  · calc r * u * S.z * (r * u)⁻¹ = r * (u * S.z * u⁻¹) * r⁻¹ := by group
      _ = D.a * S.z := by rw [hu1, hr]
  · calc r * u * D.a * (r * u)⁻¹ = r * (u * D.a * u⁻¹) * r⁻¹ := by group
      _ = S.z := by rw [hu2, hrz]

theorem IsCycle.conj_mem_X {w : G} (hw : D.IsCycle w) {x : G} (hx : x ∈ D.X) :
    w * x * w⁻¹ ∈ D.X := by
  obtain ⟨hxz, hxa⟩ := D.mem_X.mp hx
  have hxaz : x * (D.a * S.z) = (D.a * S.z) * x :=
    calc x * (D.a * S.z) = (x * D.a) * S.z := (mul_assoc _ _ _).symm
      _ = (D.a * x) * S.z := by rw [hxa]
      _ = D.a * (x * S.z) := mul_assoc _ _ _
      _ = D.a * (S.z * x) := by rw [hxz]
      _ = (D.a * S.z) * x := (mul_assoc _ _ _).symm
  have hc : ∀ t : G, x * t = t * x →
      (w * x * w⁻¹) * (w * t * w⁻¹) = (w * t * w⁻¹) * (w * x * w⁻¹) :=
    fun t ht => by
      calc (w * x * w⁻¹) * (w * t * w⁻¹) = w * (x * t) * w⁻¹ := by group
        _ = w * (t * x) * w⁻¹ := by rw [ht]
        _ = (w * t * w⁻¹) * (w * x * w⁻¹) := by group
  refine D.mem_X.mpr ⟨?_, ?_⟩
  · have := hc D.a hxa
    rwa [hw.2] at this
  · have := hc (D.a * S.z) hxaz
    rwa [hw.conj_az D] at this

theorem IsCycle.pow_three_mem_X {w : G} (hw : D.IsCycle w) : w ^ 3 ∈ D.X := by
  obtain ⟨h1, h2⟩ := (hw.pow D 3).1 (by norm_num)
  refine D.mem_X.mpr ⟨?_, ?_⟩
  · calc w ^ 3 * S.z = w ^ 3 * S.z * (w ^ 3)⁻¹ * w ^ 3 := by group
      _ = S.z * w ^ 3 := by rw [h1]
  · calc w ^ 3 * D.a = w ^ 3 * D.a * (w ^ 3)⁻¹ * w ^ 3 := by group
      _ = D.a * w ^ 3 := by rw [h2]

theorem IsCycle.mul_mem_X {w : G} (hw : D.IsCycle w) {x : G} (hx : x ∈ D.X) :
    D.IsCycle (x * w) := by
  obtain ⟨hxz, hxa⟩ := D.mem_X.mp hx
  have hxaz : x * (D.a * S.z) * x⁻¹ = D.a * S.z :=
    calc x * (D.a * S.z) * x⁻¹ = (x * D.a) * S.z * x⁻¹ := by rw [← mul_assoc]
      _ = (D.a * x) * S.z * x⁻¹ := by rw [hxa]
      _ = D.a * (x * S.z) * x⁻¹ := by rw [mul_assoc D.a]
      _ = D.a * (S.z * x) * x⁻¹ := by rw [hxz]
      _ = D.a * S.z := by rw [← mul_assoc, mul_assoc _ x, mul_inv_cancel, mul_one]
  refine ⟨?_, ?_⟩
  · calc x * w * S.z * (x * w)⁻¹ = x * (w * S.z * w⁻¹) * x⁻¹ := by group
      _ = D.a * S.z := by rw [hw.1, hxaz]
  · calc x * w * D.a * (x * w)⁻¹ = x * (w * D.a * w⁻¹) * x⁻¹ := by group
      _ = S.z := by rw [hw.2, hxz]; group

end CaseA

end CFSG.LargeExtraspecial.FS77
