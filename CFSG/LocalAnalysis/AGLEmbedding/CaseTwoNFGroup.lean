module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped Pointwise

variable {X : Type*} [Group X]

theorem eq_one_of_pow_p_pow {p : ℕ} {L : Subgroup X}
    (hZ : ∀ ζ ∈ L, ζ ∈ Subgroup.centralizer (L : Set X) → ζ ^ p = 1 → ζ = 1) :
    ∀ k : ℕ, ∀ ζ ∈ L, ζ ∈ Subgroup.centralizer (L : Set X) → ζ ^ p ^ k = 1 → ζ = 1 := by
  intro k
  induction k with
  | zero => intro ζ _ _ h; simpa using h
  | succ k ih =>
    intro ζ hζL hζC h
    have h1 : ζ ^ p ^ k = 1 := hZ _ (L.pow_mem hζL _) (Subgroup.pow_mem _ hζC _) (by
      rw [← pow_mul, ← pow_succ]; exact h)
    exact ih ζ hζL hζC h1

theorem rep_unique_p {p : ℕ} {L : Subgroup X}
    (hZ : ∀ ζ ∈ L, ζ ∈ Subgroup.centralizer (L : Set X) → ζ ^ p = 1 → ζ = 1) {u l l' : X}
    (hl : l ∈ L) (hl' : l' ∈ L) {k k' : ℕ} (hlk : l ^ p ^ k = 1) (hlk' : l' ^ p ^ k' = 1)
    (hc : l⁻¹ * u ∈ Subgroup.centralizer (L : Set X))
    (hc' : l'⁻¹ * u ∈ Subgroup.centralizer (L : Set X)) : l = l' := by
  have hζC : l⁻¹ * l' ∈ Subgroup.centralizer (L : Set X) := by
    have := Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')
    simpa [mul_assoc] using this
  have hζL : l⁻¹ * l' ∈ L := L.mul_mem (L.inv_mem hl) hl'
  have hcomm : Commute l (l⁻¹ * l') := Subgroup.mem_centralizer_iff.mp hζC l hl
  have hcomm' : Commute l⁻¹ l' := by
    have h2 : Commute l⁻¹ (l⁻¹ * l') := hcomm.inv_left
    have h3 : l' = l * (l⁻¹ * l') := by group
    rw [h3]
    exact (Commute.inv_left (Commute.refl l)).mul_right h2
  have hpow : (l⁻¹ * l') ^ p ^ (k + k') = 1 := by
    rw [hcomm'.mul_pow, inv_pow]
    have e1 : l ^ p ^ (k + k') = 1 := by rw [pow_add, pow_mul, hlk, one_pow]
    have e2 : l' ^ p ^ (k + k') = 1 := by rw [pow_add, mul_comm, pow_mul, hlk', one_pow]
    rw [e1, e2, inv_one, one_mul]
  exact inv_mul_eq_one.mp (eq_one_of_pow_p_pow hZ _ _ hζL hζC hpow)

theorem rep_pow_p {p : ℕ} {L : Subgroup X}
    (hZ : ∀ ζ ∈ L, ζ ∈ Subgroup.centralizer (L : Set X) → ζ ^ p = 1 → ζ = 1) {u r : X}
    (hr : r ∈ L) {k : ℕ} (hrk : r ^ p ^ k = 1) (hup : u ^ p = 1) (hru : Commute r u)
    (hc : r⁻¹ * u ∈ Subgroup.centralizer (L : Set X)) : r ^ p = 1 := by
  have hC : r ^ p ∈ Subgroup.centralizer (L : Set X) := by
    have h1 : (r⁻¹ * u) ^ p = (r ^ p)⁻¹ := by
      rw [(hru.inv_left).mul_pow, hup, mul_one, inv_pow]
    have h2 := Subgroup.pow_mem _ hc p
    rw [h1] at h2
    simpa using Subgroup.inv_mem _ h2
  refine eq_one_of_pow_p_pow hZ k _ (L.pow_mem hr p) hC ?_
  rw [← pow_mul, mul_comm, pow_mul, hrk, one_pow]

theorem zpowers_inf_eq_bot_of_not_mem' {p : ℕ} (hp : p.Prime) {D : Subgroup X} {w : X}
    (hw : orderOf w = p) (hwD : w ∉ D) : Subgroup.zpowers w ⊓ D = ⊥ := by
  have : Finite (Subgroup.zpowers w) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers, hw]
    exact hp.ne_zero
  have hdvd : Nat.card (Subgroup.zpowers w ⊓ D : Subgroup X) ∣ p := by
    rw [← hw, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · have heq : Subgroup.zpowers w ⊓ D = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hw])
    have hle : Subgroup.zpowers w ≤ D := by
      rw [← heq]
      exact inf_le_right
    exact (hwD (hle (Subgroup.mem_zpowers w))).elim

theorem card_sup_zpowers {p : ℕ} (hp : p.Prime) {A D : Subgroup X} {w : X} (hAD : A ≤ D)
    (hw : orderOf w = p) (hwD : w ∉ D)
    (hAw : A ≤ Subgroup.centralizer (Subgroup.zpowers w : Set X)) :
    Nat.card (A ⊔ Subgroup.zpowers w : Subgroup X) = Nat.card A * p := by
  have hwA : Subgroup.zpowers w ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.le_centralizer_iff.mp hAw).trans (Subgroup.centralizer_le_normalizer _)
  have h0 : A ⊓ Subgroup.zpowers w = ⊥ := by
    rw [inf_comm, eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem' hp hw hwD]
    exact inf_le_inf_left _ hAD
  have h1 := card_sup_mul_card_inf_eq_of_le_normalizer hwA
  rw [h0, Subgroup.card_bot, mul_one, Nat.card_zpowers, hw] at h1
  exact h1

theorem card_sup_zpowers_le [Finite X] {p : ℕ} {w z : X} (hwo : orderOf w = p)
    (hzo : orderOf z = p) (hwz : Commute w z) :
    Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers z : Subgroup X) ≤ p * p := by
  have hzw : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers w : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hwz.zpow_left n).eq
  have h1 := card_sup_mul_card_inf_eq_of_le_normalizer hzw
  rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hzo] at h1
  have h3 := Nat.card_pos (α := (Subgroup.zpowers w ⊓ Subgroup.zpowers z : Subgroup X))
  nlinarith

theorem isElemAbelian_zpowers_three {w : X} (hw : w ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers w) := CFSG.Open.isElemAbelian_zpowers hw

theorem exists_zpow_of_mem_sup {a b c v : X} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c)
    (hv : v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c) :
    ∃ i j k : ℤ, v = a ^ i * b ^ j * c ^ k := by
  have hC1 : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hab.zpow_right n).eq.symm
  have hC2 : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set X) := by
    have hcen : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
        Subgroup.centralizer ({c} : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]; exact hac.eq
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]; exact hbc.eq
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)).symm
      n)).eq
  have hv' : v ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) : Set X) *
      (Subgroup.zpowers c : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hC2]; exact hv
  obtain ⟨x, hx, y, hy, rfl⟩ := hv'
  have hx' : x ∈ (Subgroup.zpowers a : Set X) * (Subgroup.zpowers b : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hC1]; exact hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx₁
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx₂
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨i, j, k, rfl⟩

theorem conj_mem_centralizer_map {B : Subgroup X} {g x : X}
    (hx : x ∈ Subgroup.centralizer (B : Set X)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup X) :
      Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  rintro _ ⟨b, hb, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have := hx b hb
  calc g * b * g⁻¹ * (g * x * g⁻¹) = g * (b * x) * g⁻¹ := by group
    _ = g * (x * b) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * (g * b * g⁻¹) := by group

theorem mem_normalizer_centralizer {B : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (B : Set X)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set X) : Set X) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _) hx

theorem mem_zpowers_sq {y : X} {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    y ∈ Subgroup.zpowers (y ^ 2) := by
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  refine Subgroup.mem_zpowers_iff.mpr ⟨(m + 1 : ℕ), ?_⟩
  rw [zpow_natCast, ← pow_mul]
  have e : 2 * (m + 1) = 3 ^ k + 1 := by omega
  rw [e, pow_succ, hy, one_mul]

theorem zpow_mod_three {x : X} (hx : orderOf x = 3) (n : ℤ) : x ^ (n % 3) = x ^ n := by
  have := zpow_mod_orderOf x n
  rw [hx] at this
  exact_mod_cast this

theorem exists_mul_pow_mem_zpowers {w z r : X} (hwo : orderOf w = 3) (hzo : orderOf z = 3)
    (hwz : Commute w z) {a b : ℤ} (hr : r = w ^ a * z ^ b) (hb : b % 3 ≠ 0) :
    ∃ i : ℕ, z * w ^ i ∈ Subgroup.zpowers r := by
  have hb' : b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hzb : z ^ b = z ^ (b % 3) := (zpow_mod_three hzo b).symm
  have hz3 : z ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hzo, pow_orderOf_eq_one]
  rcases hb' with h1 | h2
  · refine ⟨(a % 3).toNat, Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩⟩
    have ha : ((a % 3).toNat : ℤ) = a % 3 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    rw [zpow_one, hr, hzb, h1, zpow_one, ← zpow_natCast, ha, zpow_mod_three hwo,
      (hwz.zpow_left a).eq]
  · refine ⟨(2 * a % 3).toNat, Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩⟩
    have ha : ((2 * a % 3).toNat : ℤ) = 2 * a % 3 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    rw [← zpow_natCast, ha, zpow_mod_three hwo, hr, hzb, h2, (hwz.zpow_zpow a 2).mul_zpow,
      ← zpow_mul, ← zpow_mul, mul_comm a 2, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add,
      hz3, one_mul, zpow_one, (hwz.zpow_left (2 * a)).eq]

theorem exists_pow_eq_mul [Finite X] {p : ℕ} {w z r : X} (hp : p.Prime) (hwo : orderOf w = p)
    (hzo : orderOf z = p) (hro : orderOf r = p) (hwz : Commute w z) (hrw : Commute r w)
    (hr : r ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z) (hrw' : r ∉ Subgroup.zpowers w) :
    ∃ k j : ℤ, r ^ k = z * w ^ j := by
  have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers r ≤
      Subgroup.zpowers w ⊔ Subgroup.zpowers z :=
    sup_le le_sup_left ((Subgroup.zpowers_le).mpr hr)
  have hcw : Subgroup.zpowers w ≤ Subgroup.centralizer (Subgroup.zpowers r : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hrw.zpow_left n).eq
  have hc1 : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers r : Subgroup X) = p * p := by
    have := card_sup_zpowers hp le_rfl hro hrw' hcw
    rw [Nat.card_zpowers, hwo] at this
    exact this
  have heq : Subgroup.zpowers w ⊔ Subgroup.zpowers r = Subgroup.zpowers w ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc1]; exact card_sup_zpowers_le hwo hzo hwz)
  have hz : z ∈ Subgroup.zpowers r ⊔ Subgroup.zpowers w := by
    rw [sup_comm, heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hrN : Subgroup.zpowers r ≤ Subgroup.normalizer (Subgroup.zpowers w : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hrw.zpow_right n).eq.symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hrN] at hz
  obtain ⟨a, ha, b, hb, hab⟩ := hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨k, -j, ?_⟩
  rw [← hab, zpow_neg, mul_inv_cancel_right]

theorem mem_zpowers_of_zpow_ne_one {p : ℕ} {w : X} (hp : p.Prime) (hwo : orderOf w = p) {m : ℤ}
    (hm : w ^ m ≠ 1) : w ∈ Subgroup.zpowers (w ^ m) := by
  have : Finite (Subgroup.zpowers w) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers, hwo]
    exact hp.ne_zero
  have hle : Subgroup.zpowers (w ^ m) ≤ Subgroup.zpowers w :=
    (Subgroup.zpowers_le).mpr (Subgroup.zpow_mem_zpowers w m)
  have hdvd : Nat.card (Subgroup.zpowers (w ^ m)) ∣ p := by
    rw [← hwo, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exfalso
    apply hm
    have := Subgroup.eq_bot_of_card_eq _ h1
    have hmem : w ^ m ∈ Subgroup.zpowers (w ^ m) := Subgroup.mem_zpowers _
    rw [this, Subgroup.mem_bot] at hmem
    exact hmem
  · have heq : Subgroup.zpowers (w ^ m) = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h1, Nat.card_zpowers, hwo])
    rw [heq]; exact Subgroup.mem_zpowers w

end CFSG.AGLEmbedding
