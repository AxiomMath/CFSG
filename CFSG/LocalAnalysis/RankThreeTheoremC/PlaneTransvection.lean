module

import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

section Coordinates

variable {p : ℕ}

omit [Finite G] in
theorem pow_eq_pow_of_natCast_eq_of_pow_eq_one {y : G} (hy : y ^ p = 1) {m m' : ℕ}
    (h : (m : ZMod p) = m') : y ^ m = y ^ m' := by
  rw [pow_eq_pow_mod m hy, pow_eq_pow_mod m' hy]
  exact congrArg _ ((ZMod.natCast_eq_natCast_iff' m m' p).1 h)

theorem exists_pow_mul_pow_of_mem_plane [Fact p.Prime] {D : Subgroup G} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {z d : G} (hzD : z ∈ D) (hz1 : z ≠ 1) (hd : d ∈ D)
    (hdz : d ∉ zpowers z) {x : G} (hx : x ∈ D) : ∃ s t : ℕ, x = d ^ s * z ^ t := by
  have hp : p.Prime := Fact.out
  have hzp : z ^ p = 1 := hD.2 z hzD
  have hdp : d ^ p = 1 := hD.2 d hd
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcd : d * z = z * d := hcomm d hd z hzD
  have hcardz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hle : zpowers z ⊔ zpowers d ≤ D := sup_le (zpowers_le.2 hzD) (zpowers_le.2 hd)
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers z) hdp hdz
    (fun e he => hcomm e (zpowers_le.2 hzD he) d hd)
  have hsup : zpowers z ⊔ zpowers d = D :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hDc, hcard, hcardz, sq]))
  have hnorm : zpowers d ≤ normalizer (zpowers z : Set G) := by
    rw [zpowers_le]
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro h hh
    exact hcomm h (zpowers_le.2 hzD hh) d hd
  have hx' : x ∈ (↑(zpowers z ⊔ zpowers d) : Set G) := by rw [hsup]; exact hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  obtain ⟨t, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ha)
  obtain ⟨s, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hb)
  exact ⟨s, t, (Commute.pow_pow hcd s t).eq.symm⟩

omit [Finite G] in
theorem exists_conj_pow_eq_pow_mul_pow {d z n : G} (hcd : d * z = z * d)
    (hnz : n * z = z * n) {a b : ℕ} (hab : n * d * n⁻¹ = d ^ a * z ^ b) (j : ℕ) :
    ∃ β : ℕ, n ^ j * d * (n ^ j)⁻¹ = d ^ (a ^ j) * z ^ β := by
  have hz : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨β, hβ⟩ := ih
    refine ⟨b * a ^ j + β, ?_⟩
    have hcomm : Commute (d ^ a) (z ^ b) := Commute.pow_pow hcd a b
    calc n ^ (j + 1) * d * (n ^ (j + 1))⁻¹
        = n * (n ^ j * d * (n ^ j)⁻¹) * n⁻¹ := by rw [pow_succ']; group
      _ = (n * d * n⁻¹) ^ (a ^ j) * (n * z * n⁻¹) ^ β := by
          rw [hβ, conj_pow, conj_pow]; group
      _ = (d ^ a * z ^ b) ^ (a ^ j) * z ^ β := by rw [hab, hz]
      _ = d ^ (a ^ (j + 1)) * z ^ (b * a ^ j + β) := by
          rw [hcomm.mul_pow, ← pow_mul, ← pow_mul, pow_add z (b * a ^ j) β, pow_succ' a j,
            mul_assoc]

omit [Finite G] in
theorem natCast_eq_one_of_eq_pow_mul_pow [Fact p.Prime] {d z : G} (hdp : d ^ p = 1)
    (hdz : d ∉ zpowers z) {e β : ℕ} (h : d = d ^ e * z ^ β) : (e : ZMod p) = 1 := by
  by_contra hne
  have hp : p.Prime := Fact.out
  have hc : (e : ZMod p) - 1 ≠ 0 := sub_ne_zero.2 hne
  have hmem : d ^ ((p - 1) + e) ∈ zpowers z := by
    have h1 : d ^ ((p - 1) + e) * z ^ β = 1 := by
      rw [pow_add, mul_assoc, ← h, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hdp]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem (mem_zpowers z) β)
  apply hdz
  have h2 : d = (d ^ ((p - 1) + e)) ^ (((e : ZMod p) - 1)⁻¹).val := by
    rw [← pow_mul]
    refine (pow_one d).symm.trans (pow_eq_pow_of_natCast_eq_of_pow_eq_one hdp ?_)
    rw [Nat.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self,
      ZMod.natCast_zmod_val, Nat.cast_one]
    rw [show ((0 : ZMod p) - 1 + e) = e - 1 by ring]
    exact (mul_inv_cancel₀ hc).symm
  rw [h2]
  exact pow_mem hmem _

omit [Finite G] in
theorem conj_eq_mul_pow_of_natCast_eq_one {d z n : G} (hdp : d ^ p = 1) {a b : ℕ}
    (hab : n * d * n⁻¹ = d ^ a * z ^ b) (ha : (a : ZMod p) = 1) : n * d * n⁻¹ = d * z ^ b := by
  rw [hab, pow_eq_pow_of_natCast_eq_of_pow_eq_one hdp (m' := 1) (by rw [ha, Nat.cast_one]), pow_one]

omit [Finite G] in
theorem transvection_conj_pow_eq {d z n : G} (hnz : n * z = z * n) {b : ℕ}
    (hb : n * d * n⁻¹ = d * z ^ b) (j : ℕ) : n ^ j * d * (n ^ j)⁻¹ = d * z ^ (j * b) := by
  have hz : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
  induction j with
  | zero => simp
  | succ j ih =>
    calc n ^ (j + 1) * d * (n ^ (j + 1))⁻¹
        = n * (n ^ j * d * (n ^ j)⁻¹) * n⁻¹ := by rw [pow_succ']; group
      _ = (n * d * n⁻¹) * (n * z * n⁻¹) ^ (j * b) := by rw [ih, conj_pow]; group
      _ = d * z ^ ((j + 1) * b) := by
          rw [hb, hz, show (j + 1) * b = b + j * b by ring, pow_add z b (j * b), mul_assoc]

end Coordinates

theorem exists_pow_conj_zpowers_eq {p : ℕ} [Fact p.Prime] {D : Subgroup G}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {z n : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hn : ∃ k : ℕ, n ^ (p ^ k) = 1) (hnD : n ∈ normalizer (D : Set G)) (hnz : n * z = z * n)
    (hnC : n ∉ centralizer (D : Set G)) {d d' : G} (hd : d ∈ D) (hdz : d ∉ zpowers z)
    (hd' : d' ∈ D) (hd'z : d' ∉ zpowers z) :
    ∃ k : ℕ, zpowers (n ^ k * d * (n ^ k)⁻¹) = zpowers d' := by
  have hzp : z ^ p = 1 := hD.2 z hzD
  have hdp : d ^ p = 1 := hD.2 d hd
  have hcd : d * z = z * d := congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩)
  have hz : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
  have hgen : ∀ {x : G}, x ∈ D → ∃ s t : ℕ, x = d ^ s * z ^ t := fun {x} hx =>
    exists_pow_mul_pow_of_mem_plane hD hDc hzD hz1 hd hdz hx
  obtain ⟨a, b, hab⟩ := hgen ((mem_normalizer_iff.1 hnD d).1 hd)
  obtain ⟨k, hk⟩ := hn
  have ha : (a : ZMod p) = 1 := by
    obtain ⟨β, hβ⟩ := exists_conj_pow_eq_pow_mul_pow hcd hnz hab (p ^ k)
    rw [hk, inv_one, mul_one, one_mul] at hβ
    have h1 := natCast_eq_one_of_eq_pow_mul_pow hdp hdz hβ
    rwa [Nat.cast_pow, ZMod.pow_card_pow] at h1
  have hb' := conj_eq_mul_pow_of_natCast_eq_one hdp hab ha
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro hb0
    apply hnC
    have hzb : z ^ b = z ^ 0 :=
      pow_eq_pow_of_natCast_eq_of_pow_eq_one hzp (by rw [hb0, Nat.cast_zero])
    have hnd : n * d * n⁻¹ = d := by rw [hb', hzb, pow_zero, mul_one]
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨s, t, rfl⟩ := hgen hx
    have h1 : n * (d ^ s * z ^ t) * n⁻¹ = d ^ s * z ^ t := by
      calc n * (d ^ s * z ^ t) * n⁻¹ = (n * d * n⁻¹) ^ s * (n * z * n⁻¹) ^ t := by
            rw [conj_pow, conj_pow]; group
        _ = d ^ s * z ^ t := by rw [hnd, hz]
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  obtain ⟨s, t, hd'e⟩ := hgen hd'
  have hs0 : (s : ZMod p) ≠ 0 := by
    intro hs
    apply hd'z
    have hds : d ^ s = d ^ 0 :=
      pow_eq_pow_of_natCast_eq_of_pow_eq_one hdp (by rw [hs, Nat.cast_zero])
    rw [hd'e, hds, pow_zero, one_mul]
    exact pow_mem (mem_zpowers z) t
  obtain ⟨s', hs'c⟩ : ∃ s' : ℕ, (s' : ZMod p) = (s : ZMod p)⁻¹ :=
    ⟨_, ZMod.natCast_zmod_val _⟩
  have hss' : ((s * s' : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hs'c, mul_inv_cancel₀ hs0, Nat.cast_one]
  have hts : ((t * s' * s : ℕ) : ZMod p) = (t : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_mul, hs'c, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  obtain ⟨j, hjc⟩ : ∃ j : ℕ,
      (j : ZMod p) = (t : ZMod p) * (s : ZMod p)⁻¹ * (b : ZMod p)⁻¹ :=
    ⟨_, ZMod.natCast_zmod_val _⟩
  have hjb : ((j * b : ℕ) : ZMod p) = ((t * s' : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_mul, hjc, hs'c, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  refine ⟨j, ?_⟩
  rw [transvection_conj_pow_eq hnz hb' j, pow_eq_pow_of_natCast_eq_of_pow_eq_one hzp hjb]
  apply le_antisymm
  · rw [zpowers_le]
    have h1 : d' ^ s' = d * z ^ (t * s') := by
      rw [hd'e, (Commute.pow_pow hcd s t).mul_pow s', ← pow_mul, ← pow_mul,
        pow_eq_pow_of_natCast_eq_of_pow_eq_one hdp hss', pow_one]
    rw [← h1]
    exact pow_mem (mem_zpowers d') s'
  · rw [zpowers_le]
    have h1 : (d * z ^ (t * s')) ^ s = d' := by
      rw [hd'e, (Commute.pow_right hcd (t * s')).mul_pow s, ← pow_mul,
        pow_eq_pow_of_natCast_eq_of_pow_eq_one hzp hts]
    rw [← h1]
    exact pow_mem (mem_zpowers _) s

end CFSG.LocalAnalysis.RankThreeTheoremC
