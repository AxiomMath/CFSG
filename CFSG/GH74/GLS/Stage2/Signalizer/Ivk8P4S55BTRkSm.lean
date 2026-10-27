module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkSm

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem center_eq_bot {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h : ¬ (Nat.card Y).Prime) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ a b : Y, a * b = b * a := fun a b =>
      mem_center_iff.1 (h0 ▸ mem_top b) a
    let _ : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
    exact h (IsSimpleGroup.prime_card (α := Y))

theorem conj_injective {Y : Type} [Group Y] (hc : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ center Y := by
    rw [mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut Y => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hc, mem_bot] at hx'
  exact hx'

theorem finite_mulAut {Y : Type} [Group Y] [Finite Y] : Finite (MulAut Y) :=
  Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective

theorem card_mulAut {Y : Type} [Group Y] (hc : center Y = ⊥) :
    Nat.card (MulAut Y) = Nat.card Y * Nat.card (Outer Y) := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (inner Y)
  have h2 : Nat.card (inner Y) = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective hc)).toEquiv).symm
  rw [h1, h2, mul_comm]

theorem isPGroup_of_sq {A : Type} [Group A] {E : Subgroup A} (hE : ∀ y ∈ E, y ^ 2 = 1) :
    IsPGroup 2 ↥E :=
  fun y => ⟨1, Subtype.ext (by simpa using hE y y.2)⟩

theorem exists_card_pow {A : Type} [Group A] [Finite A] {E : Subgroup A} (hE : IsPGroup 2 ↥E) :
    ∃ n : ℕ, Nat.card E = 2 ^ n ∧ 2 ^ n ∣ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hE
  exact ⟨n, hn, hn ▸ card_subgroup_dvd_card E⟩

theorem lt_of_pow_dvd {n k m : ℕ} (h : 2 ^ n ∣ m) (hk : ¬ 2 ^ k ∣ m) : n < k := by
  by_contra hnk
  exact hk ((pow_dvd_pow 2 (not_lt.mp hnk)).trans h)

theorem card_le_eight_of_not_dvd {A : Type} [Group A] [Finite A] (h16 : ¬ 16 ∣ Nat.card A)
    (E : Subgroup A) (hE : ∀ y ∈ E, y ^ 2 = 1) : Nat.card E ≤ 8 := by
  obtain ⟨n, hn, hdvd⟩ := exists_card_pow (isPGroup_of_sq hE)
  have hn3 := lt_of_pow_dvd hdvd (k := 4) (by norm_num; exact h16)
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 8 := by norm_num

theorem mem_smul_sylow_iff {A : Type} [Group A] {p : ℕ} (P : Sylow p A) (g y : A) :
    y ∈ (g • P : Sylow p A) ↔ g⁻¹ * y * g ∈ P := by
  change y ∈ ((g • P : Sylow p A) : Subgroup A) ↔ g⁻¹ * y * g ∈ (P : Subgroup A)
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem card_le_eight_of_order_four {A : Type} [Group A] [Finite A] (h32 : ¬ 32 ∣ Nat.card A)
    {x : A} (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1) (E : Subgroup A) (hE : ∀ y ∈ E, y ^ 2 = 1) :
    Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp := isPGroup_of_sq hE
  obtain ⟨n, hn, hdvd⟩ := exists_card_pow hEp
  have hn4 := lt_of_pow_dvd hdvd (k := 5) (by norm_num; exact h32)
  by_contra hgt
  have hn4' : n = 4 := by
    by_contra hne
    apply hgt
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  subst hn4'
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨m, hm, hmd⟩ := exists_card_pow P.isPGroup'
  have hm4 := lt_of_pow_dvd hmd (k := 5) (by norm_num; exact h32)
  have hEPeq : E = P := by
    refine eq_of_le_of_card_ge hEP ?_
    rw [hn, hm]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxo : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hx4)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxo
  have hxp : IsPGroup 2 ↥(zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hxQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq A P Q
  have hx : g⁻¹ * x * g ∈ E := by
    rw [hEPeq]
    exact (mem_smul_sylow_iff P g x).mp (hxQ (mem_zpowers x))
  have h2 := hE _ hx
  apply hx2
  have e : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, ← map_pow]
    simp
  rw [e] at h2
  calc x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem admRank3_of_sq {k : Stage12.Kind} {Y : Type} [Group Y]
    (h : ∀ E : Subgroup (MulAut Y), (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 8) : AdmRank3 k Y := by
  intro E hE _
  exact h E fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := E) x hx

theorem bound_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z) {m : ℕ}
    (hZ : ∀ E : Subgroup Z, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ m) (E : Subgroup Y)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ m := by
  have h := hZ (E.map e.toMonoidHom) (by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE y hy, map_one])
  rwa [card_map_of_injective e.injective] at h

theorem card_le_of_inner {Y : Type} [Group Y] (hc : center Y = ⊥)
    (hodd : Odd (Nat.card (Outer Y))) {m : ℕ}
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ m) (E : Subgroup (MulAut Y))
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ m := by
  have hle : E ≤ inner Y := by
    intro x hx
    have h1 : ((x : Outer Y)) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, hE x hx, QuotientGroup.mk_one]
    have h2 : ((x : Outer Y)) ^ Nat.card (Outer Y) = 1 := pow_card_eq_one'
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), pow_one] at h3
    exact (QuotientGroup.eq_one_iff (N := inner Y) x).mp h3
  have hinj := conj_injective hc
  have h := hY (E.comap MulAut.conj) (fun y hy => hinj (by
    rw [map_pow, map_one]
    exact hE _ hy))
  have hmap : (E.comap MulAut.conj).map MulAut.conj = E := map_comap_eq_self hle
  rwa [← card_map_of_injective hinj, hmap] at h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkSm
