module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Local.CentralCommutatorPowers
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.LinearCombination

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open scoped commutatorElement Pointwise

variable {R : Type*} [Group R]

theorem commutatorElement_mul_left_of_mem_center {a b c : R}
    (h₁ : ⁅a, c⁆ ∈ Subgroup.center R) (h₂ : ⁅b, c⁆ ∈ Subgroup.center R) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    show a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ from by rw [Subgroup.mem_center_iff.mp h₂ a]; group]
  exact Subgroup.mem_center_iff.mp h₁ ⁅b, c⁆

theorem commutatorElement_mul_right_of_mem_center {a b c : R}
    (h : ⁅a, c⁆ ∈ Subgroup.center R) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    show ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) from by group,
    show b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ from by rw [Subgroup.mem_center_iff.mp h b]; group]

theorem commutatorElement_mul_mul_of_mem_center {a b c d : R}
    (hac : ⁅a, c⁆ ∈ Subgroup.center R) (had : ⁅a, d⁆ ∈ Subgroup.center R)
    (hbc : ⁅b, c⁆ ∈ Subgroup.center R) (hbd : ⁅b, d⁆ ∈ Subgroup.center R) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅a, d⁆ * (⁅b, c⁆ * ⁅b, d⁆) := by
  rw [commutatorElement_mul_left_of_mem_center
      (by rw [commutatorElement_mul_right_of_mem_center had]; exact mul_mem hac had)
      (by rw [commutatorElement_mul_right_of_mem_center hbd]; exact mul_mem hbc hbd),
    commutatorElement_mul_right_of_mem_center had,
    commutatorElement_mul_right_of_mem_center hbd]

private def commutatorRightHom {H : Subgroup R} (u : R)
    (h : ∀ w ∈ H, ⁅u, w⁆ ∈ Subgroup.center R) : H →* R where
  toFun w := ⁅u, (w : R)⁆
  map_one' := by simp
  map_mul' w₁ w₂ := commutatorElement_mul_right_of_mem_center (h w₂ w₂.2)

private def commutatorLeftHom {H : Subgroup R} (v : R)
    (h : ∀ w ∈ H, ⁅w, v⁆ ∈ Subgroup.center R) : H →* R where
  toFun w := ⁅(w : R), v⁆
  map_one' := by simp
  map_mul' w₁ w₂ := commutatorElement_mul_left_of_mem_center (h w₁ w₁.2) (h w₂ w₂.2)

theorem commutatorElement_zpow_right {H : Subgroup R} {u : R}
    (h : ∀ w ∈ H, ⁅u, w⁆ ∈ Subgroup.center R) {v : R} (hv : v ∈ H) (J : ℤ) :
    ⁅u, v ^ J⁆ = ⁅u, v⁆ ^ J :=
  map_zpow (commutatorRightHom u h) (⟨v, hv⟩ : H) J

theorem commutatorElement_zpow_left {H : Subgroup R} {v : R}
    (h : ∀ w ∈ H, ⁅w, v⁆ ∈ Subgroup.center R) {u : R} (hu : u ∈ H) (I : ℤ) :
    ⁅u ^ I, v⁆ = ⁅u, v⁆ ^ I :=
  map_zpow (commutatorLeftHom v h) (⟨u, hu⟩ : H) I

theorem commutatorElement_zpow_zpow {H : Subgroup R}
    (hH : ∀ u ∈ H, ∀ v ∈ H, ⁅u, v⁆ ∈ Subgroup.center R) {u v : R} (hu : u ∈ H) (hv : v ∈ H)
    (I J : ℤ) : ⁅u ^ I, v ^ J⁆ = ⁅u, v⁆ ^ (I * J) := by
  have hright : ∀ w ∈ H, ⁅w, v ^ J⁆ = ⁅w, v⁆ ^ J := fun w hw =>
    commutatorElement_zpow_right (fun w' hw' => hH w hw w' hw') hv J
  have hcen : ∀ w ∈ H, ⁅w, v ^ J⁆ ∈ Subgroup.center R := fun w hw => by
    rw [hright w hw]; exact zpow_mem (hH w hw v hv) J
  rw [commutatorElement_zpow_left hcen hu I, hright u hu, ← zpow_mul, mul_comm J I]

theorem commutatorElement_pow_pow {H : Subgroup R}
    (hH : ∀ u ∈ H, ∀ v ∈ H, ⁅u, v⁆ ∈ Subgroup.center R) {u v : R} (hu : u ∈ H) (hv : v ∈ H)
    (m n : ℕ) : ⁅u ^ m, v ^ n⁆ = ⁅u, v⁆ ^ (m * n) := by
  have h := commutatorElement_zpow_zpow hH hu hv (m : ℤ) (n : ℤ)
  rw [← Nat.cast_mul, zpow_natCast, zpow_natCast, zpow_natCast] at h
  exact h

theorem commutatorElement_pow_pow_of_central (hc : ∀ u v : R, ⁅u, v⁆ ∈ Subgroup.center R)
    (u v : R) (m n : ℕ) : ⁅u ^ m, v ^ n⁆ = ⁅u, v⁆ ^ (m * n) :=
  commutatorElement_pow_pow (H := ⊤) (fun a _ b _ => hc a b) (Subgroup.mem_top u)
    (Subgroup.mem_top v) m n

theorem commutatorElement_mul_mul_of_central (hc : ∀ u v : R, ⁅u, v⁆ ∈ Subgroup.center R)
    (a b c d : R) : ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅a, d⁆ * (⁅b, c⁆ * ⁅b, d⁆) :=
  commutatorElement_mul_mul_of_mem_center (hc a c) (hc a d) (hc b c) (hc b d)

theorem sup_zpowers_eq_of_card {p : ℕ} (hp : p.Prime) [Finite R] {K H : Subgroup R}
    (hHK : H ≤ K) (hcard : Nat.card ↥K = p * Nat.card ↥H) {g : R} (hgK : g ∈ K) (hgH : g ∉ H) :
    Subgroup.zpowers g ⊔ H = K := by
  set S : Subgroup R := Subgroup.zpowers g ⊔ H with hS
  have hSK : S ≤ K := sup_le (Subgroup.zpowers_le.2 hgK) hHK
  have hHS : H ≤ S := le_sup_right
  have hgS : g ∈ S := (le_sup_left : Subgroup.zpowers g ≤ S) (Subgroup.mem_zpowers g)
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hHS
  have hdvd : Nat.card ↥H * d ∣ Nat.card ↥H * p := by
    rw [← hd, mul_comm (Nat.card ↥H) p, ← hcard]
    exact Subgroup.card_dvd_of_le hSK
  have hpos : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have hdp : d ∣ p := (mul_dvd_mul_iff_left hpos).1 hdvd
  rcases (Nat.dvd_prime hp).1 hdp with h | h
  · refine absurd ?_ hgH
    have heq : H = S := Subgroup.eq_of_le_of_card_ge hHS (le_of_eq (by rw [hd, h, mul_one]))
    rw [heq]; exact hgS
  · exact Subgroup.eq_of_le_of_card_ge hSK (le_of_eq (by rw [hcard, hd, h, mul_comm]))

theorem exists_pow_mul_eq {N : Subgroup R} [N.Normal] {g : R} (hg : IsOfFinOrder g)
    {K : Subgroup R} (hsup : Subgroup.zpowers g ⊔ N = K) {b : R} (hb : b ∈ K) :
    ∃ (m : ℕ) (u : R), u ∈ N ∧ b = g ^ m * u := by
  rw [← hsup] at hb
  have hb' : b ∈ ((Subgroup.zpowers g : Set R) * (N : Set R)) := by
    rw [← Subgroup.mul_normal]; exact hb
  obtain ⟨v, hv, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  obtain ⟨m, hm⟩ := hg.mem_powers_iff_mem_zpowers.2 hv
  exact ⟨m, u, hu, by rw [← hm]⟩

theorem exists_mem_pow_mul_eq_pow_mul {N : Subgroup R} (hN : N.Normal) (g : R) {t : R}
    (ht : t ∈ N) (n : ℕ) : ∃ u ∈ N, (g * t) ^ n = g ^ n * u := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨u, hu, hun⟩ := ih
    refine ⟨g⁻¹ * u * g * t, N.mul_mem (by simpa using hN.conj_mem' u hu g) ht, ?_⟩
    rw [pow_succ, hun, pow_succ]
    group

theorem orderOf_eq_of_card_eq_prime {p : ℕ} (hp : p.Prime) {N : Subgroup R}
    (hN : Nat.card ↥N = p) {u : R} (hu : u ∈ N) (hu1 : u ≠ 1) : orderOf u = p := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (⟨u, hu⟩ : ↥N) ^ p = 1 := by rw [← hN]; exact pow_card_eq_one'
  exact orderOf_eq_prime (by simpa using congrArg Subtype.val h) hu1

theorem natCast_eq_natCast_of_pow_eq {p : ℕ} {g : R} (hg : orderOf g = p) {m n : ℕ}
    (h : g ^ m = g ^ n) : (m : ZMod p) = (n : ZMod p) := by
  rw [ZMod.natCast_eq_natCast_iff]
  have h2 := pow_eq_pow_iff_modEq.mp h
  rwa [hg] at h2

theorem pow_eq_pow_of_natCast_eq {p : ℕ} {g : R} (hg : orderOf g = p) {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) : g ^ m = g ^ n := by
  rw [pow_eq_pow_iff_modEq, hg]
  exact (ZMod.natCast_eq_natCast_iff m n p).1 h

theorem dvd_of_zpow_mem {p : ℕ} (hp : p.Prime) {N : Subgroup R} {g : R} (hg : orderOf g = p)
    (hgN : g ∉ N) {m : ℤ} (hm : g ^ m ∈ N) : (p : ℤ) ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  have hfin : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hle : Subgroup.zpowers g ⊓ N ≤ Subgroup.zpowers g := inf_le_left
  have hbot : Subgroup.zpowers g ⊓ N = ⊥ := by
    rcases (Nat.dvd_prime hp).1 (hcard ▸ Subgroup.card_dvd_of_le hle) with h | h
    · exact Subgroup.card_eq_one.1 h
    · have heq : Subgroup.zpowers g ⊓ N = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h])
      exact absurd (Subgroup.mem_inf.1 (heq ▸ Subgroup.mem_zpowers g)).2 hgN
  have h1 : g ^ m = 1 := by
    have : g ^ m ∈ Subgroup.zpowers g ⊓ N := ⟨⟨m, rfl⟩, hm⟩
    simpa [hbot] using this
  rw [← hg]
  exact orderOf_dvd_iff_zpow_eq_one.2 h1

theorem natCast_eq_natCast_of_mul_inv_mem {p : ℕ} (hp : p.Prime) {N : Subgroup R} {g : R}
    (hg : orderOf g = p) (hgN : g ∉ N) {m n : ℕ} (h : g ^ m * (g ^ n)⁻¹ ∈ N) :
    (m : ZMod p) = (n : ZMod p) := by
  have h2 : g ^ ((m : ℤ) - (n : ℤ)) ∈ N := by
    rw [zpow_sub, zpow_natCast, zpow_natCast]; exact h
  have h3 := dvd_of_zpow_mem hp hg hgN h2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  push_cast at h3
  exact sub_eq_zero.1 h3

theorem apply_eq_pow_of_mem_zpowers {φ : MulAut R} {g : R} {i : ℕ} (hφ : φ g = g ^ i) {u : R}
    (hu : u ∈ Subgroup.zpowers g) : φ u = u ^ i := by
  obtain ⟨c, rfl⟩ := hu
  rw [map_zpow, hφ, ← zpow_natCast (g ^ c) i, ← zpow_natCast g i, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem not_isInvariantSubgroup_of_closure_displacement_eq_top
    {p : ℕ} (hp : p.Prime) (_hodd : Odd p) [Finite R]
    {B Z T X : Subgroup R} [B.Characteristic]
    (hBcard : Nat.card ↥B = p ^ 3) (hBnab : ¬ IsMulCommutative ↥B)
    (hBexp : ∀ b ∈ B, b ^ p = 1)
    (hZ : Z = B ⊓ Subgroup.centralizer (B : Set R))
    (hT : T = ⁅(⊤ : Subgroup R), B⁆) (hTcard : Nat.card ↥T = p ^ 2)
    (hZT : Z ≤ T) (hRT : ⁅(⊤ : Subgroup R), T⁆ ≤ Z)
    (hXT : X ≤ Subgroup.centralizer (T : Set R)) (hXcyc : IsCyclic ↥X)
    (hBX : B ⊔ X = ⊤) (hBXZ : B ⊓ X = Z)
    {A : Type*} [Group A] [Finite A] (hAodd : Odd (Nat.card A))
    (ρ : A →* MulAut R) (hXinv : IsInvariantSubgroup ρ X)
    (hRA : Subgroup.closure {g : R | ∃ (a : A) (r : R), r⁻¹ * ρ a r = g} = ⊤) :
    False := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hTB : T ≤ B := hT ▸ Subgroup.commutator_le_right _ _
  have hTnorm : T.Normal := hT ▸ Subgroup.commutator_normal _ _
  have hZB : Z ≤ B := hZ ▸ inf_le_left
  have hZX : Z ≤ X := hBXZ ▸ inf_le_right
  have hZmem : ∀ u : R, u ∈ Z ↔ (u ∈ B ∧ ∀ b ∈ B, b * u = u * b) := by
    intro u
    rw [hZ]
    simp [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  have hZmap : Subgroup.map B.subtype (Subgroup.center ↥B) = Z := by
    ext u
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, hZmem]
    refine ⟨?_, ?_⟩
    · rintro ⟨b', hb', rfl⟩
      exact ⟨b'.2, fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp hb' ⟨g, hg⟩)⟩
    · rintro ⟨hu, hc⟩
      exact ⟨⟨u, hu⟩, Subgroup.mem_center_iff.mpr (fun b => Subtype.ext (hc b b.2)), rfl⟩
  have hZcard : Nat.card ↥Z = p := by
    rw [← hZmap, Subgroup.card_map_of_injective B.subtype_injective]
    exact card_center_of_card_eq_prime_cube hp hBcard hBnab
  have hcommB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ⁅b₁, b₂⁆ ∈ Z := by
    intro b₁ h₁ b₂ h₂
    rw [← hZmap]
    refine ⟨⁅(⟨b₁, h₁⟩ : ↥B), (⟨b₂, h₂⟩ : ↥B)⁆, ?_, ?_⟩
    · rw [← commutator_eq_center_of_card_eq_prime_cube hp hBcard hBnab, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · simp [commutatorElement_def]
  obtain ⟨x, hx⟩ := X.isCyclic_iff_exists_zpowers_eq_top.mp hXcyc
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hXab : IsMulCommutative ↥X := IsCyclic.isMulCommutative
  have hTab : IsMulCommutative ↥T := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hTcard
  have hXpow : ∀ s ∈ X, ∃ m : ℕ, s = x ^ m := fun s hs => by
    obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite x).mem_powers_iff_mem_zpowers.2 (hx ▸ hs)
    exact ⟨m, hm.symm⟩
  have hRdecomp : ∀ r : R, ∃ b ∈ B, ∃ m : ℕ, r = b * x ^ m := by
    intro r
    have hr : r ∈ ((B : Set R) * (X : Set R)) := by
      rw [← Subgroup.normal_mul, hBX, Subgroup.coe_top]; trivial
    obtain ⟨b, hb, s, hs, rfl⟩ := Set.mem_mul.1 hr
    obtain ⟨m, rfl⟩ := hXpow s hs
    exact ⟨b, hb, m, rfl⟩
  have hZcenter : Z ≤ Subgroup.center R := by
    intro u hu
    obtain ⟨huB, huC⟩ := (hZmem u).1 hu
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨b, hb, m, rfl⟩ := hRdecomp g
    have h1 : u * x ^ m = x ^ m * u := setLike_mul_comm (hZX hu) (X.pow_mem hxX m)
    calc b * x ^ m * u = b * (x ^ m * u) := by rw [mul_assoc]
      _ = b * (u * x ^ m) := by rw [h1]
      _ = b * u * x ^ m := by rw [mul_assoc]
      _ = u * b * x ^ m := by rw [huC b hb]
      _ = u * (b * x ^ m) := by rw [mul_assoc]
  have hZnorm : Z.Normal := by
    constructor
    intro u hu g
    have h : g * u * g⁻¹ = u := by
      rw [Subgroup.mem_center_iff.mp (hZcenter hu) g]; group
    rw [h]; exact hu
  have hZone : ∀ g : R, g ∈ Z ↔ QuotientGroup.mk' Z g = 1 := fun g => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hBcentT : ∀ b ∈ B, ∀ r : R, ⁅b, r⁆ ∈ T := by
    intro b hb r
    rw [hT, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hb (Subgroup.mem_top r)
  have hcenT : ∀ b ∈ B, ∀ g : R ⧸ T, Commute (QuotientGroup.mk' T b) g := by
    intro b hb g
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective T g
    refine (?_ : QuotientGroup.mk' T b * QuotientGroup.mk' T r
      = QuotientGroup.mk' T r * QuotientGroup.mk' T b)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      show (b * r)⁻¹ * (r * b) = ⁅r⁻¹, b⁻¹⁆ from by rw [commutatorElement_def]; group,
      ← commutatorElement_inv]
    exact T.inv_mem (hBcentT b⁻¹ (B.inv_mem hb) r⁻¹)
  have hRcomm : ∀ r₁ r₂ : R, ⁅r₁, r₂⁆ ∈ T := by
    have hcomm : ∀ u v : R, Commute (QuotientGroup.mk' T u) (QuotientGroup.mk' T v) := by
      intro u v
      obtain ⟨b₁, hb₁, m₁, rfl⟩ := hRdecomp u
      obtain ⟨b₂, hb₂, m₂, rfl⟩ := hRdecomp v
      rw [map_mul, map_mul, map_pow, map_pow]
      exact ((hcenT b₁ hb₁ _).mul_right (hcenT b₁ hb₁ _)).mul_left
        (((hcenT b₂ hb₂ _).symm).mul_right ((Commute.refl _).pow_pow m₁ m₂))
    intro r₁ r₂
    have h : QuotientGroup.mk' T ⁅r₁, r₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hcomm r₁ r₂
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hQcen : ∀ U V : R ⧸ Z, ⁅U, V⁆ ∈ Subgroup.center (R ⧸ Z) := by
    intro U V
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Z U
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective Z V
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Z g
    rw [← map_commutatorElement, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq,
      show (w * ⁅u, v⁆)⁻¹ * (⁅u, v⁆ * w) = ⁅⁅u, v⁆⁻¹, w⁻¹⁆ from by
        rw [commutatorElement_def]; group,
      ← commutatorElement_inv]
    exact Z.inv_mem
      (hRT (Subgroup.commutator_mem_commutator (Subgroup.mem_top w⁻¹) (T.inv_mem (hRcomm u v))))
  have hρB : ∀ a : A, ∀ b ∈ B, ρ a b ∈ B := by
    intro a b hb
    have h : Subgroup.map (ρ a).toMonoidHom B = B :=
      Subgroup.characteristic_iff_map_eq.mp ‹B.Characteristic› (ρ a)
    rw [← h]; exact ⟨b, hb, rfl⟩
  have hρT : ∀ a : A, ∀ t ∈ T, ρ a t ∈ T := by
    intro a t ht
    have h : Subgroup.map (ρ a).toMonoidHom T = T := by
      rw [hT, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (ρ a).surjective,
        Subgroup.characteristic_iff_map_eq.mp ‹B.Characteristic› (ρ a)]
    rw [← h]; exact ⟨t, ht, rfl⟩
  have hstepA : ∃ (a : A) (y : R), y ∈ B ∧ y⁻¹ * ρ a y ∉ T := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : Subgroup.closure {g : R | ∃ (a : A) (r : R), r⁻¹ * ρ a r = g} ≤ T ⊔ X := by
      rw [Subgroup.closure_le]
      rintro g ⟨a, r, rfl⟩
      obtain ⟨b, hb, m, rfl⟩ := hRdecomp r
      rw [show (b * x ^ m)⁻¹ * ρ a (b * x ^ m)
          = (x ^ m)⁻¹ * (b⁻¹ * ρ a b) * ρ a (x ^ m) from by rw [map_mul]; group]
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact (le_sup_right : X ≤ T ⊔ X) (X.inv_mem (X.pow_mem hxX m))
      · exact (le_sup_left : T ≤ T ⊔ X) (hcon a b hb)
      · exact (le_sup_right : X ≤ T ⊔ X) (hXinv.apply_mem a (X.pow_mem hxX m))
    rw [hRA, top_le_iff] at hsub
    have hBT : B ≤ T := by
      intro b hb
      have hb2 : b ∈ ((T : Set R) * (X : Set R)) := by
        rw [← Subgroup.normal_mul, hsub, Subgroup.coe_top]; trivial
      obtain ⟨t, ht, s, hs, rfl⟩ := Set.mem_mul.1 hb2
      have hsB : s ∈ B := by
        have h : t⁻¹ * (t * s) ∈ B := B.mul_mem (B.inv_mem (hTB ht)) hb
        simpa using h
      exact T.mul_mem ht (hZT (hBXZ ▸ Subgroup.mem_inf.2 ⟨hsB, hs⟩))
    have hd := Subgroup.card_dvd_of_le hBT
    rw [hBcard, hTcard] at hd
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd
    omega
  obtain ⟨a, y, hyB, hyd⟩ := hstepA
  have hyT : y ∉ T := fun h => hyd (T.mul_mem (T.inv_mem h) (hρT a y h))
  have hy1 : y ≠ 1 := fun h => hyT (h ▸ T.one_mem)
  have hyord : orderOf y = p := orderOf_eq_prime (hBexp y hyB) hy1
  have hByT : Subgroup.zpowers y ⊔ T = B :=
    sup_zpowers_eq_of_card hp hTB (by rw [hBcard, hTcard]; ring) hyB hyT
  obtain ⟨j, t, htT, hjt⟩ := exists_pow_mul_eq (isOfFinOrder_of_finite y) hByT (hρB a y hyB)
  have hjne : (j : ZMod p) ≠ 1 := by
    intro hj1
    refine hyd ?_
    rw [hjt, ← mul_assoc,
      pow_eq_pow_of_natCast_eq (n := 1) hyord (by simpa using hj1), pow_one, inv_mul_cancel,
      one_mul]
    exact htT
  have hiter : ∀ m : ℕ, ∃ u ∈ T, ρ (a ^ m) y = y ^ (j ^ m) * u := by
    intro m
    induction m with
    | zero => exact ⟨1, T.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨u, hu, hum⟩ := ih
      have h1 : ρ (a ^ (m + 1)) y = (y ^ j * t) ^ (j ^ m) * ρ a u := by
        rw [pow_succ', map_mul, MulAut.mul_apply, hum, map_mul, map_pow (ρ a) y (j ^ m), hjt]
      obtain ⟨v, hv, hveq⟩ := exists_mem_pow_mul_eq_pow_mul hTnorm (y ^ j) htT (j ^ m)
      have h2 : (y ^ j) ^ (j ^ m) = y ^ (j ^ (m + 1)) := by rw [← pow_mul, ← pow_succ']
      exact ⟨v * ρ a u, T.mul_mem hv (hρT a u hu), by rw [h1, hveq, h2, mul_assoc]⟩
  obtain ⟨u₀, hu₀, hueq⟩ := hiter (orderOf a)
  rw [pow_orderOf_eq_one, map_one, MulAut.one_apply] at hueq
  have hJn : (j : ZMod p) ^ orderOf a = 1 := by
    have h4 : y ^ (j ^ orderOf a) * (y ^ 1)⁻¹ ∈ T := by
      rw [show y ^ (j ^ orderOf a) * (y ^ 1)⁻¹
          = y ^ (j ^ orderOf a) * u₀ * u₀⁻¹ * (y ^ 1)⁻¹ from by group,
        ← hueq, pow_one]
      exact hTnorm.conj_mem u₀⁻¹ (T.inv_mem hu₀) y
    have h := natCast_eq_natCast_of_mul_inv_mem hp hyord hyT h4
    push_cast at h
    exact h
  have hoddn : Odd (orderOf a) := by
    rw [Nat.odd_iff] at hAodd ⊢
    rcases Nat.even_or_odd (orderOf a) with he | ho
    · exfalso
      obtain ⟨c, hc⟩ := (he.two_dvd).trans (orderOf_dvd_natCard (G := A) a)
      omega
    · exact Nat.odd_iff.1 ho
  have hzT : ⁅x, y⁆ ∈ T := by
    rw [hT]; exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hyB
  have hcen : ∀ u ∈ B, ∀ v ∈ B, ⁅u, v⁆ ∈ Subgroup.center R := fun u hu v hv =>
    hZcenter (hcommB u hu v hv)
  have hzZ : ⁅x, y⁆ ∉ Z := by
    intro hzZ
    have hσz : QuotientGroup.mk' Z ⁅x, y⁆ = 1 := (hZone _).1 hzZ
    have hTZ : T ≤ Z := by
      rw [hT, Subgroup.commutator_le]
      intro r _ b hb
      obtain ⟨b₁, hb₁, m, rfl⟩ := hRdecomp r
      obtain ⟨s, t', ht', rfl⟩ := exists_pow_mul_eq (isOfFinOrder_of_finite y) hByT hb
      have e1 : ⁅QuotientGroup.mk' Z b₁, QuotientGroup.mk' Z y ^ s⁆ = 1 := by
        rw [← map_pow, ← map_commutatorElement, ← hZone]
        exact hcommB b₁ hb₁ (y ^ s) (B.pow_mem hyB s)
      have e2 : ⁅QuotientGroup.mk' Z b₁, QuotientGroup.mk' Z t'⁆ = 1 := by
        rw [← map_commutatorElement, ← hZone]
        exact hcommB b₁ hb₁ t' (hTB ht')
      have e3 : ⁅QuotientGroup.mk' Z x ^ m, QuotientGroup.mk' Z y ^ s⁆ = 1 := by
        rw [commutatorElement_pow_pow_of_central hQcen, ← map_commutatorElement, hσz, one_pow]
      have e4 : ⁅QuotientGroup.mk' Z x ^ m, QuotientGroup.mk' Z t'⁆ = 1 := by
        rw [commutatorElement_pow_left_of_mem_center (hQcen _ _), ← map_commutatorElement,
          show ⁅x, t'⁆ = 1 from commutatorElement_eq_one_iff_commute.2
            (Subgroup.mem_centralizer_iff.mp (hXT hxX) t' ht').symm, map_one, one_pow]
      have key : ⁅QuotientGroup.mk' Z (b₁ * x ^ m), QuotientGroup.mk' Z (y ^ s * t')⁆ = 1 := by
        rw [map_mul, map_mul, map_pow, map_pow, commutatorElement_mul_mul_of_central hQcen]
        simp only [e1, e2, e3, e4, mul_one]
      rw [hZone, map_commutatorElement]
      exact key
    have heq : T = Z := le_antisymm hTZ hZT
    rw [heq, hZcard] at hTcard
    have h3 : p * 1 = p * p := by rw [mul_one, ← pow_two]; exact hTcard
    have h4 := Nat.eq_of_mul_eq_mul_left hp.pos h3
    have h5 := hp.one_lt
    omega
  have hTzZ : Subgroup.zpowers ⁅x, y⁆ ⊔ Z = T :=
    sup_zpowers_eq_of_card hp hZT (by rw [hTcard, hZcard]; ring) hzT hzZ
  obtain ⟨k, w, hwZ, hkw⟩ :=
    exists_pow_mul_eq (isOfFinOrder_of_finite ⁅x, y⁆) hTzZ (hρT a _ hzT)
  obtain ⟨i, hi⟩ := hXpow (ρ a x) (hXinv.apply_mem a hxX)
  have hyz : ⁅y, ⁅x, y⁆⁆ ≠ 1 := by
    intro hcom
    have hcz : Commute y ⁅x, y⁆ := commutatorElement_eq_one_iff_commute.1 hcom
    have hyT' : ∀ v ∈ T, Commute y v := by
      intro v hv
      obtain ⟨c, v', hv'Z, hcv⟩ := exists_pow_mul_eq (isOfFinOrder_of_finite ⁅x, y⁆) hTzZ hv
      rw [hcv]
      exact (hcz.pow_right c).mul_right
        (Subgroup.mem_center_iff.mp (hZcenter hv'Z) y : y * v' = v' * y)
    refine hBnab (le_centralizer_iff_isMulCommutative.1 ?_)
    intro u hu
    obtain ⟨s, tt, httT, hst⟩ := exists_pow_mul_eq (isOfFinOrder_of_finite y) hByT hu
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    obtain ⟨s', t', ht'T, hst'⟩ := exists_pow_mul_eq (isOfFinOrder_of_finite y) hByT hv
    rw [hst, hst']
    have c1 : Commute (y ^ s') tt := (hyT' tt httT).pow_left s'
    have c2 : Commute (y ^ s) t' := (hyT' t' ht'T).pow_left s
    have c3 : Commute tt t' := setLike_mul_comm httT ht'T
    have c4 : Commute (y ^ s) (y ^ s') := (Commute.refl y).pow_pow s s'
    exact ((c4.symm.mul_right c1).mul_left (c2.symm.mul_right c3.symm)).eq
  have hcZ : ⁅y, ⁅x, y⁆⁆ ∈ Z := hcommB y hyB _ (hTB hzT)
  have hcord : orderOf ⁅y, ⁅x, y⁆⁆ = p := orderOf_eq_of_card_eq_prime hp hZcard hcZ hyz
  have hρc : ρ a ⁅y, ⁅x, y⁆⁆ = ⁅y, ⁅x, y⁆⁆ ^ i :=
    apply_eq_pow_of_mem_zpowers hi (by rw [hx]; exact hZX hcZ)
  have heq1 : ⁅y, ⁅x, y⁆⁆ ^ i = ⁅y, ⁅x, y⁆⁆ ^ (j * k) := by
    have ew : ⁅y ^ j, w⁆ = 1 := commutatorElement_eq_one_iff_commute.2
      (Subgroup.mem_center_iff.mp (hZcenter hwZ) (y ^ j))
    have etz : ⁅t, ⁅x, y⁆ ^ k⁆ = 1 := commutatorElement_eq_one_iff_commute.2
      (Commute.pow_right (setLike_mul_comm htT hzT : Commute t ⁅x, y⁆) k)
    have etw : ⁅t, w⁆ = 1 := commutatorElement_eq_one_iff_commute.2
      (Subgroup.mem_center_iff.mp (hZcenter hwZ) t)
    rw [← hρc, map_commutatorElement, hjt, hkw,
      commutatorElement_mul_mul_of_mem_center
        (hcen _ (B.pow_mem hyB j) _ (B.pow_mem (hTB hzT) k))
        (hcen _ (B.pow_mem hyB j) _ (hZB hwZ))
        (hcen _ (hTB htT) _ (B.pow_mem (hTB hzT) k))
        (hcen _ (hTB htT) _ (hZB hwZ)),
      commutatorElement_pow_pow (H := B) (fun u hu v hv => hcen u hu v hv) hyB (hTB hzT) j k,
      ew, etz, etw]
    simp
  have hik : (i : ZMod p) = ((j * k : ℕ) : ZMod p) := natCast_eq_natCast_of_pow_eq hcord heq1
  have hσz1 : QuotientGroup.mk' Z ⁅x, y⁆ ≠ 1 := fun h => hzZ ((hZone _).2 h)
  have hσzord : orderOf (QuotientGroup.mk' Z ⁅x, y⁆) = p :=
    orderOf_eq_prime (by rw [← map_pow, hBexp _ (hTB hzT), map_one]) hσz1
  have heq2 : (QuotientGroup.mk' Z ⁅x, y⁆) ^ k = (QuotientGroup.mk' Z ⁅x, y⁆) ^ (i * j) := by
    have hl : QuotientGroup.mk' Z (ρ a ⁅x, y⁆) = (QuotientGroup.mk' Z ⁅x, y⁆) ^ k := by
      rw [hkw, map_mul, map_pow, (hZone w).1 hwZ, mul_one]
    have hσt : ⁅QuotientGroup.mk' Z x ^ i, QuotientGroup.mk' Z t⁆ = 1 := by
      rw [commutatorElement_pow_left_of_mem_center (hQcen _ _), ← map_commutatorElement,
        show ⁅x, t⁆ = 1 from commutatorElement_eq_one_iff_commute.2
          (Subgroup.mem_centralizer_iff.mp (hXT hxX) t htT).symm, map_one, one_pow]
    rw [← hl, map_commutatorElement, hi, hjt, map_commutatorElement, map_mul, map_pow, map_pow,
      commutatorElement_mul_right_of_mem_center (hQcen _ _), hσt, mul_one,
      commutatorElement_pow_pow_of_central hQcen, ← map_commutatorElement]
  have hkij : ((k : ℕ) : ZMod p) = ((i * j : ℕ) : ZMod p) :=
    natCast_eq_natCast_of_pow_eq hσzord heq2
  have hI : (i : ZMod p) ≠ 0 := by
    intro h0
    have hpi : p ∣ i := by
      have h1 : ((i : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by rw [h0]; simp
      exact (Nat.modEq_zero_iff_dvd).1 ((ZMod.natCast_eq_natCast_iff i 0 p).1 h1)
    have h2 : ⁅y, ⁅x, y⁆⁆ ^ i = 1 := by
      rw [← hcord] at hpi
      exact orderOf_dvd_iff_pow_eq_one.1 hpi
    rw [← hρc] at h2
    exact hyz ((ρ a).injective (h2.trans (map_one (ρ a)).symm))
  push_cast at hik hkij
  have hsq : (j : ZMod p) ^ 2 = 1 := by
    have h1 : (i : ZMod p) = (i : ZMod p) * (j : ZMod p) ^ 2 := by
      linear_combination hik + (j : ZMod p) * hkij
    have h2 : (i : ZMod p) * ((j : ZMod p) ^ 2 - 1) = 0 := by
      rw [mul_sub, mul_one, ← h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hI
    · exact sub_eq_zero.1 h
  obtain ⟨q, hq⟩ := hoddn
  refine hjne ?_
  calc (j : ZMod p) = ((j : ZMod p) ^ 2) ^ q * (j : ZMod p) := by rw [hsq, one_pow, one_mul]
    _ = (j : ZMod p) ^ orderOf a := by rw [hq]; ring
    _ = 1 := hJn

end CFSG.FeitThompson
