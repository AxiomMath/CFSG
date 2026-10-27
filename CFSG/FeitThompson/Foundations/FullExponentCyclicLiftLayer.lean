module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p m n : ℕ} {S : Type*} [CommGroup S]

theorem omega1_eq_ker_powMonoidHom (p : ℕ) (S : Type*) [CommGroup S] :
    omega1 p S = (powMonoidHom p : S →* S).ker :=
  le_antisymm (omega1_le fun x hx => by simpa [MonoidHom.mem_ker] using hx)
    fun x hx => mem_omega1_of_pow_eq_one (by simpa [MonoidHom.mem_ker] using hx)

theorem mem_omega1_iff_pow_eq_one {x : S} : x ∈ omega1 p S ↔ x ^ p = 1 := by
  rw [omega1_eq_ker_powMonoidHom]; simp [MonoidHom.mem_ker]

theorem coe_omega1_commGroup (p : ℕ) (S : Type*) [CommGroup S] :
    (omega1 p S : Set S) = {s : S | s ^ p = 1} :=
  Set.ext fun _ => mem_omega1_iff_pow_eq_one

theorem isPGroup_omega1 (p : ℕ) (S : Type*) [CommGroup S] : IsPGroup p ↥(omega1 p S) :=
  fun g => ⟨1, Subtype.ext (by simpa [pow_one] using mem_omega1_iff_pow_eq_one.1 g.2)⟩

theorem map_omega1_subtype (K : Subgroup S) :
    (omega1 p ↥K).map K.subtype = K ⊓ omega1 p S := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf, mem_omega1_iff_pow_eq_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg (Subgroup.subtype K) hy⟩
  · rintro ⟨hxK, hx⟩
    exact ⟨⟨x, hxK⟩, Subtype.ext (by simpa using hx), rfl⟩

theorem le_omega1_of_card_eq_prime {B : Subgroup S} (hB : Nat.card B = p) : B ≤ omega1 p S := by
  intro x hx
  refine mem_omega1_iff_pow_eq_one.2 ?_
  have h : (⟨x, hx⟩ : ↥B) ^ Nat.card ↥B = 1 := pow_card_eq_one'
  rw [hB] at h
  simpa using congrArg (Subgroup.subtype B) h

private theorem card_lt_card_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : H < K) : Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h.le))
    fun he => absurd (Subgroup.eq_of_le_of_card_ge h.le he.ge) h.ne

theorem card_omega1_le_sq [Finite S] (hp : p.Prime) (h3 : 3 ∉ elementaryAbelianRanks p S) :
    Nat.card ↥(omega1 p S) ≤ p ^ 2 := by
  have := Fact.mk hp
  obtain ⟨d, hd⟩ := (isPGroup_omega1 p S).exists_card_eq
  rw [hd]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(omega1 p S)) p
    (n := 3) (hd ▸ pow_dvd_pow p (by omega))
  refine h3 ((mem_elementaryAbelianRanks_iff_exists_subgroup hp).2
    ⟨K.map (omega1 p S).subtype, inferInstance, fun x hx => ?_, ?_⟩)
  · exact mem_omega1_iff_pow_eq_one.1 (Subgroup.map_subtype_le K hx)
  · rw [Subgroup.card_map_of_injective (omega1 p S).subtype_injective, hK]

theorem eq_zpowers_of_card_eq_prime [Finite S] (hp : p.Prime) {H : Subgroup S}
    (hH : Nat.card H = p) {w : S} (hw : w ∈ H) (hw1 : w ≠ 1) : H = zpowers w := by
  have hle : zpowers w ≤ H := zpowers_le.2 hw
  have hdvd : orderOf w ∣ p := by
    rw [← hH, ← Nat.card_zpowers w]; exact Subgroup.card_dvd_of_le hle
  have hord : orderOf w = p :=
    ((Nat.dvd_prime hp).1 hdvd).resolve_left fun h => hw1 (orderOf_eq_one_iff.1 h)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hH, Nat.card_zpowers, hord])).symm

theorem eq_of_card_eq_prime [Finite S] (hp : p.Prime) {H K : Subgroup S} (hH : Nat.card H = p)
    (hK : Nat.card K = p) {w : S} (hwH : w ∈ H) (hwK : w ∈ K) (hw1 : w ≠ 1) : H = K := by
  rw [eq_zpowers_of_card_eq_prime hp hH hwH hw1, eq_zpowers_of_card_eq_prime hp hK hwK hw1]

theorem exists_ne_one_mem_of_card_eq_prime [Finite S] (hp : p.Prime) {B : Subgroup S}
    (hB : Nat.card B = p) : ∃ b : S, b ∈ B ∧ b ≠ 1 :=
  (Subgroup.nontrivial_iff_exists_ne_one B).1
    (Finite.one_lt_card_iff_nontrivial.1 (by rw [hB]; exact hp.one_lt))

theorem card_inf_omega1_zpowers [Finite S] {z : S} (hz : orderOf z = p ^ (m + 1)) :
    Nat.card ↥(zpowers z ⊓ omega1 p S) = p := by
  rw [← map_omega1_subtype, Subgroup.card_map_of_injective (zpowers z).subtype_injective,
    omega1_eq_ker_powMonoidHom, IsCyclic.card_powMonoidHom_ker, Nat.card_zpowers, hz,
    Nat.gcd_eq_right (dvd_pow_self p (Nat.succ_ne_zero m))]

theorem pow_mem_inf_omega1_zpowers {z : S} (hz : orderOf z = p ^ (m + 1)) :
    z ^ p ^ m ∈ zpowers z ⊓ omega1 p S :=
  ⟨pow_mem (mem_zpowers z) _, mem_omega1_iff_pow_eq_one.2 (by
    rw [← pow_mul, ← pow_succ, ← hz, pow_orderOf_eq_one])⟩

theorem pow_ne_one_of_orderOf_eq (hp : p.Prime) {z : S} (hz : orderOf z = p ^ (m + 1)) :
    z ^ p ^ m ≠ 1 := fun h => by
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hz] at hdvd
  exact absurd ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd) (by omega)

theorem orderOf_eq_pow_succ_of_pow_eq (hp : p.Prime) {z b : S} (hb1 : b ≠ 1) (hbp : b ^ p = 1)
    (hzb : z ^ p ^ m = b) : orderOf z = p ^ (m + 1) := by
  obtain ⟨k, hk, hz⟩ := (Nat.dvd_prime_pow hp).1
    (orderOf_dvd_of_pow_eq_one (by rw [pow_succ, pow_mul, hzb, hbp] : z ^ p ^ (m + 1) = 1))
  refine hz.trans (congrArg _ (le_antisymm hk ?_))
  by_contra hlt
  exact hb1 (hzb ▸ orderOf_dvd_iff_pow_eq_one.1 (hz ▸ pow_dvd_pow p (by omega)))

theorem coe_range_powMonoidHom (k : ℕ) (S : Type*) [CommGroup S] :
    ((powMonoidHom k : S →* S).range : Set S) = {t : S | ∃ s : S, s ^ k = t} := (rfl)

theorem mem_range_powMonoidHom (k : ℕ) (s : S) : s ^ k ∈ (powMonoidHom k : S →* S).range :=
  ⟨s, rfl⟩

instance characteristic_range_powMonoidHom (k : ℕ) :
    ((powMonoidHom k : S →* S).range).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  rintro φ x ⟨g, rfl⟩
  exact ⟨φ g, by simp [powMonoidHom_apply, ← map_pow]⟩

theorem range_powMonoidHom_le_omega1 (hexp : Monoid.exponent S = p ^ (m + 1)) :
    (powMonoidHom (p ^ m) : S →* S).range ≤ omega1 p S := by
  rintro x ⟨g, rfl⟩
  rw [mem_omega1_iff_pow_eq_one, powMonoidHom_apply, ← pow_mul, ← pow_succ]
  exact hexp ▸ Monoid.pow_exponent_eq_one g

theorem nontrivial_range_powMonoidHom [Finite S] (hp : p.Prime) (hS : IsPGroup p S)
    (hexp : Monoid.exponent S = p ^ (m + 1)) :
    Nontrivial ↥((powMonoidHom (p ^ m) : S →* S).range) := by
  obtain ⟨g, hg⟩ := IsPGroup.exists_orderOf_eq_exponent hp hS
  exact (Subgroup.nontrivial_iff_exists_ne_one _).2
    ⟨g ^ p ^ m, ⟨g, rfl⟩, pow_ne_one_of_orderOf_eq hp (hg.trans hexp)⟩

theorem card_range_powMonoidHom_eq_of_lt [Finite S] (hp : p.Prime) (hS : IsPGroup p S)
    (h3 : 3 ∉ elementaryAbelianRanks p S) (hexp : Monoid.exponent S = p ^ (m + 1))
    (hlt : (powMonoidHom (p ^ m) : S →* S).range < omega1 p S) :
    Nat.card ↥((powMonoidHom (p ^ m) : S →* S).range) = p := by
  have := Fact.mk hp
  have hnt := nontrivial_range_powMonoidHom hp hS hexp
  obtain ⟨d, hd⟩ := ((isPGroup_omega1 p S).to_le hlt.le).exists_card_eq
  have h1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hd
      exact absurd hd.1 (not_subsingleton _)
    · exact h
  have h2 : d < 2 := by
    have hlt' : Nat.card ↥((powMonoidHom (p ^ m) : S →* S).range) < p ^ 2 :=
      lt_of_lt_of_le (card_lt_card_of_lt hlt) (card_omega1_le_sq hp h3)
    rw [hd] at hlt'
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt'
  rw [hd, show d = 1 by omega, pow_one]

theorem characteristic_nontrivial_range_powMonoidHom_le_omega1 [Finite S] (hp : p.Prime)
    (hS : IsPGroup p S) (hn : 1 ≤ n) (hexp : Monoid.exponent S = p ^ n) :
    ((powMonoidHom (p ^ (n - 1)) : S →* S).range).Characteristic ∧
      Nontrivial ↥((powMonoidHom (p ^ (n - 1)) : S →* S).range) ∧
      (powMonoidHom (p ^ (n - 1)) : S →* S).range ≤ omega1 p S := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨inferInstance, nontrivial_range_powMonoidHom hp hS hexp,
    range_powMonoidHom_le_omega1 hexp⟩

theorem card_eq_and_inf_omega1_zpowers_eq_of_lt [Finite S] (hp : p.Prime) (hS : IsPGroup p S)
    (h3 : 3 ∉ elementaryAbelianRanks p S) (hn : 1 ≤ n) (hexp : Monoid.exponent S = p ^ n)
    (hlt : (powMonoidHom (p ^ (n - 1)) : S →* S).range < omega1 p S) :
    Nat.card ↥((powMonoidHom (p ^ (n - 1)) : S →* S).range) = p ∧
      ∀ z : S, orderOf z = Monoid.exponent S →
        zpowers z ⊓ omega1 p S = (powMonoidHom (p ^ (n - 1)) : S →* S).range := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt ⊢
  have hcard := card_range_powMonoidHom_eq_of_lt hp hS h3 hexp hlt
  refine ⟨hcard, fun z hz => ?_⟩
  have hz' : orderOf z = p ^ (m + 1) := hz.trans hexp
  exact eq_of_card_eq_prime hp (card_inf_omega1_zpowers hz') hcard
    (pow_mem_inf_omega1_zpowers hz') ⟨z, rfl⟩ (pow_ne_one_of_orderOf_eq hp hz')

theorem exists_orderOf_eq_exponent_inf_omega1_zpowers_eq_of_eq [Finite S] (hp : p.Prime)
    (hn : 1 ≤ n) (hexp : Monoid.exponent S = p ^ n)
    (heq : (powMonoidHom (p ^ (n - 1)) : S →* S).range = omega1 p S)
    {B : Subgroup S} (hBle : B ≤ omega1 p S) (hB : Nat.card B = p) :
    ∃ z : S, orderOf z = Monoid.exponent S ∧ zpowers z ⊓ omega1 p S = B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at heq
  obtain ⟨b, hbB, hb1⟩ := exists_ne_one_mem_of_card_eq_prime hp hB
  have hbp : b ^ p = 1 := mem_omega1_iff_pow_eq_one.1 (hBle hbB)
  obtain ⟨z, hzb⟩ : ∃ z : S, z ^ p ^ m = b := heq.symm.le (mem_omega1_iff_pow_eq_one.2 hbp)
  have hz' : orderOf z = p ^ (m + 1) := orderOf_eq_pow_succ_of_pow_eq hp hb1 hbp hzb
  refine ⟨z, hz'.trans hexp.symm, eq_of_card_eq_prime hp (card_inf_omega1_zpowers hz') hB
    (pow_mem_inf_omega1_zpowers hz') (hzb ▸ hbB) (hzb ▸ hb1)⟩

end

end CFSG.FeitThompson
