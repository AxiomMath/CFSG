module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo smallRankS smallRankR)
open scoped commutatorElement

structure KxCfg {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T S L : Subgroup G) : Prop where
  conf : S622Conf p P M x z T S
  simple : S622IsSimpleSection L ⊥
  le_C : L ≤ centralizer ({x} : Set G)
  z_mem : z ∈ L
  rank : CFSG.Open.pRank p L ≤ 1
  not_le : ¬ L ≤ M
  norm : M ⊓ centralizer ({x} : Set G) ≤ normalizer (L : Set G)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

theorem isSimpleGroup_of_section_bot {L : Subgroup G} (hs : S622IsSimpleSection L ⊥) :
    IsSimpleGroup ↥L :=
  Subgroup.isSimpleGroup_iff.mpr ⟨hs.2.2.1.symm, fun H' hH' hn => hs.2.2.2.1 H' bot_le hH' hn⟩

theorem exists_not_comm_of_section_bot {L : Subgroup G} (hs : S622IsSimpleSection L ⊥) :
    ∃ a b : ↥L, a * b ≠ b * a := by
  have h := hs.2.2.2.2
  push Not at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab ?_⟩
  have h2 : a * b = b * a := congrArg Subtype.val h'
  rw [Subgroup.mem_bot]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, h2]

theorem commutator_zpowers_le_of_le_normalizer {z : G} {L S' : Subgroup G} (hz : z ∈ L)
    (hS : S' ≤ normalizer (L : Set G)) : ⁅zpowers z, S'⁆ ≤ L := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have haL : a ∈ L := (zpowers_le.mpr hz) ha
  have hbN : b ∈ normalizer (L : Set G) := hS hb
  rw [commutatorElement_def]
  have h1 : b * a⁻¹ * b⁻¹ ∈ L := (mem_normalizer_iff.mp hbN a⁻¹).mp (L.inv_mem haL)
  have h2 : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  rw [h2]
  exact L.mul_mem haL h1

theorem exists_not_commute_of_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G}
    (hzp : z ^ p = 1) {S' : Subgroup G} (hS2 : IsPGroup 2 S')
    (hzS : z ∈ normalizer (S' : Set G)) (hne : ⁅zpowers z, S'⁆ ≠ ⊥) :
    ∃ y ∈ (⁅zpowers z, S'⁆ : Subgroup G), z * y ≠ y * z := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, zpowers_le]
  rw [mem_centralizer_iff]
  intro s hs
  set c0 : G := ⁅z, s⁆ with hc0
  have hc0R : c0 ∈ (⁅zpowers z, S'⁆ : Subgroup G) := Subgroup.commutator_mem_commutator
    (mem_zpowers z) hs
  have hzc : z * c0 = c0 * z := hcon c0 hc0R
  have hzs : z * s * z⁻¹ = c0 * s := by
    rw [hc0, commutatorElement_def]; group
  have hconj : ∀ k : ℕ, z ^ k * s * (z ^ k)⁻¹ = c0 ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : z ^ (k + 1) * s * (z ^ (k + 1))⁻¹ = z * (z ^ k * s * (z ^ k)⁻¹) * z⁻¹ := by
        group
      rw [h1, ih]
      have h2 : z * (c0 ^ k * s) * z⁻¹ = (z * c0 ^ k * z⁻¹) * (z * s * z⁻¹) := by group
      have h3 : z * c0 ^ k * z⁻¹ = c0 ^ k := by
        have := (Commute.pow_right (show Commute z c0 from hzc) k).eq
        rw [mul_inv_eq_iff_eq_mul]
        exact this
      rw [h2, h3, hzs, pow_succ]
      group
  have hcp : c0 ^ p = 1 := by
    have := hconj p
    rw [hzp] at this
    simp only [inv_one, mul_one, one_mul] at this
    have h2 : c0 ^ p * s = 1 * s := by rw [one_mul]; exact this.symm
    exact mul_right_cancel h2
  have hc0S : c0 ∈ S' := by
    have h1 : z * s * z⁻¹ ∈ S' := (mem_normalizer_iff.mp hzS s).mp hs
    rw [hc0, commutatorElement_def]
    exact S'.mul_mem h1 (S'.inv_mem hs)
  obtain ⟨k, hk⟩ := hS2 ⟨c0, hc0S⟩
  have hk' : c0 ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hord : orderOf c0 = 1 := by
    have h1 : orderOf c0 ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c0 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hc01 : c0 = 1 := orderOf_eq_one_iff.mp hord
  have : z * s * z⁻¹ = s := by rw [hzs, hc01, one_mul]
  have h5 : z * s = s * z := by
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  exact h5.symm

namespace KxCfg

theorem isSimple (c : KxCfg p P M x z T S L) : IsSimpleGroup ↥L :=
  isSimpleGroup_of_section_bot c.simple

theorem S_le_normalizer (c : KxCfg p P M x z T S L) : S ≤ normalizer (L : Set G) :=
  (le_inf c.conf.S_le_M c.conf.S_le_centralizer).trans c.norm

theorem commutator_le (c : KxCfg p P M x z T S L) : ⁅zpowers z, S⁆ ≤ L :=
  commutator_zpowers_le_of_le_normalizer c.z_mem c.S_le_normalizer

theorem normalizer_le (c : KxCfg p P M x z T S L) {U : Subgroup G} (hUL : U ≤ L)
    (hU2 : IsPGroup 2 U) (hz : z ∈ normalizer (U : Set G)) (hUM : U ⊓ M ≠ ⊥) :
    normalizer (U : Set G) ≤ M := by
  have hU1 : U ≠ ⊥ := fun h => hUM (by rw [h]; exact bot_inf_eq _)
  have hxU : x ∈ normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer (U : Set G) (mem_centralizer_iff.mpr fun h hh =>
      mem_centralizer_singleton_iff.mp (c.le_C (hUL hh)))
  have hB : zpowers x ⊔ zpowers z ≤ normalizer (U : Set G) :=
    sup_le (zpowers_le.mpr hxU) (zpowers_le.mpr hz)
  have hUM' : U ≤ M :=
    le_of_inf_ne_bot c.conf.config.prop614 c.conf.config.B_le_M hU2 hB hUM
  exact S622Conf.normalizer_le_of_invariant c.conf.config hU2 hU1 hUM' hB

theorem normalizer_zpowers_le (c : KxCfg p P M x z T S L) :
    normalizer (zpowers z : Set G) ⊓ L ≤ M :=
  inf_le_left.trans c.conf.config.normalizer_zpowers_le'

theorem orderOf_z (c : KxCfg p P M x z T S L) : orderOf z = p := by
  haveI : Fact p.Prime := ⟨c.conf.config.prime⟩
  exact orderOf_eq_prime c.conf.config.central.pow_eq_one c.conf.config.central.ne_one

theorem exists_not_commute (c : KxCfg p P M x z T S L) :
    ∃ y ∈ (⁅zpowers z, S⁆ : Subgroup G), z * y ≠ y * z :=
  exists_not_commute_of_ne_bot c.conf.config.prime c.conf.config.ne_two
    c.conf.config.central.pow_eq_one c.conf.S_isPGroup
    (c.conf.z_le_normalizer (mem_zpowers z)) c.conf.R_ne_bot

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
