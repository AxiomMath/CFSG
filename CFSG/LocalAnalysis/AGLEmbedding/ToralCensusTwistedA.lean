module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedACore
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedASetup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

namespace ToralCensus

theorem three_dvd_two_pow_sub_one_or_add_one (f : ℕ) : 3 ∣ 2 ^ f - 1 ∨ 3 ∣ 2 ^ f + 1 := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
  · left
    have := Nat.sub_dvd_pow_sub_pow 4 1 k
    rwa [one_pow, show (4 : ℕ) ^ k = 2 ^ (k + k) by rw [← two_mul, pow_mul]; norm_num] at this
  · right
    have := Odd.nat_add_dvd_pow_add_pow 2 1 hf
    rwa [one_pow] at this

theorem prime_dvd_sub_or_add_of_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ 2 - 1) :
    p ∣ q - 1 ∨ p ∣ q + 1 := by
  rw [← one_pow 2, Nat.sq_sub_sq] at h
  exact (hp.dvd_mul.mp h).symm

theorem coprime_two_pow_add_one_of_dvd_sub_one {m f : ℕ} (hm : m.Prime) (hm2 : m ≠ 2)
    (hmq : m ∣ 2 ^ f - 1) : Nat.Coprime (2 ^ f + 1) m := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).mpr fun hd => hm2 ?_)
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : m ∣ 2 := by
    have := Nat.dvd_sub hd hmq
    rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at this
  exact (Nat.prime_dvd_prime_iff_eq hm Nat.prime_two).mp h2

theorem exists_eq_twistedA {d : TauCeti.LieTypeIndex} (hd : IdxTwistedA d) :
    ∃ r₀ q, d = .twistedA r₀ q := by
  cases d <;> first | exact ⟨_, _, rfl⟩ | exact hd.elim


theorem exists_hypData {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} (hP : CompParab L J)
    (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) {u : Y}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) {m : ℕ} (hum : u ^ m = 1)
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ) (h : UnitaryFieldData 2 f K) (r ε : ℕ)
      (J' : Subgroup (hypSU h r ε)) (T : Sylow 2 (hypSU h r ε)) (t : hypSU h r ε),
      1 ≤ r ∧ ε ≤ 1 ∧ (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f) ∧
      Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J' ∧ J' ≠ ⊤ ∧
      t ^ m ∈ hypScalars h r ε ∧ (∀ y : hypSU h r ε, Commute y t → y ∈ J') ∧
      Nat.card (Subgroup.center ↥L) ∣ 2 ^ f + 1 ∧
      (u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) →
        t ∈ perfectJoin J' ⊔ hypScalars h r ε) ∧
      (Nat.Coprime (2 ^ f + 1) m → CycPerfect m J →
        ∀ V : Subgroup (hypSU h r ε), V ≤ J' → ⁅V, V⁆ = V →
          ∀ Q : Subgroup (hypSU h r ε), Q ≤ V → IsPGroup m Q → IsCyclic Q) := by
  obtain ⟨K, hK, hKf, f, h, r, ε, ρ, hr, hε, hq, hρ, hZ⟩ :=
    exists_hypCover hP.comp hP.odd d hd e
  obtain ⟨T, hT⟩ := exists_sylow_normalizer_le_comap_of_surjective hρ hP.parab
  obtain ⟨t, c, hc, rfl, htm⟩ := exists_lift_of_mem_sup hρ hZ hu hum
  have hcardZ : Nat.card (hypScalars h r ε) ∣ 2 ^ f + 1 := by
    rw [card_hypScalars h (by omega)]
    exact Nat.gcd_dvd_right _ _
  exact ⟨K, hK, hKf, f, h, r, ε, (J.subgroupOf L).comap ρ, T, t, hr, hε, hq, hT,
    comap_ne_top_of_ne hρ hP.parab.1 hP.ne_top, htm, forall_commute_mem_comap hc rfl hfix,
    (card_center_dvd_card_of_surjective hρ hZ).trans hcardZ,
    fun hj => mem_perfectJoin_sup_of_mul_mem hρ hZ
      (normOneScalars_le_center h (hypSU h r ε) (2 * r + ε)) hP.parab.1 hc hj,
    fun hcop hcyc => cycPerfect_comap hZ (Nat.Coprime.coprime_dvd_left hcardZ hcop) hcyc⟩

end ToralCensus


theorem fixCensusCenterVoid_isLieOf_twistedA : FixCensusCenterVoid (IsLieOf IdxTwistedA) := by
  intro Y _ _ L J u hD hX
  obtain ⟨d, hd, ⟨e⟩⟩ := hX
  obtain ⟨K, _, _, f, h, r, ε, J', T, t, hr, hε, -, hT, hJ', ht, hfix, hZ, -, -⟩ :=
    ToralCensus.exists_hypData hD.parab d hd e hD.mem hD.pow hD.fix
  exact ToralCensus.false_of_dvd_add_one_hyp h hr hε Nat.prime_three (by norm_num)
    (hD.three_dvd.trans hZ) T hT hJ' ht hfix

theorem fixThreeVoid_isLieOf_twistedA : FixThreeVoid (IsLieOf IdxTwistedA) := by
  intro Y _ _ L J u hD hX
  obtain ⟨d, hd, ⟨e⟩⟩ := hX
  obtain ⟨K, _, _, f, h, r, ε, J', T, t, hr, hε, -, hT, hJ', ht, hfix, -, hjoin, hcyc⟩ :=
    ToralCensus.exists_hypData hD.parab d hd e (Subgroup.mem_sup_left hD.mem) hD.pow hD.fix
  rcases ToralCensus.three_dvd_two_pow_sub_one_or_add_one f with h3 | h3
  · exact ToralCensus.false_of_dvd_sub_one_hyp h hr hε Nat.prime_three (by norm_num) h3 T hT hJ'
      ht hfix (hjoin hD.join) (hcyc (ToralCensus.coprime_two_pow_add_one_of_dvd_sub_one
        Nat.prime_three (by norm_num) h3) hD.cyc)
  · exact ToralCensus.false_of_dvd_add_one_hyp h hr hε Nat.prime_three (by norm_num) h3 T hT hJ'
      ht hfix

theorem fixPrimeTwistedATorus_holds : FixPrimeTwistedATorus := by
  intro Y _ _ L J p u hD hX
  exfalso
  obtain ⟨d, hd, hnt, ⟨e⟩⟩ := hX
  obtain ⟨K, _, _, f, h, r, ε, J', T, t, hr, hε, hq, hT, hJ', ht, hfix, -, hjoin, hcyc⟩ :=
    ToralCensus.exists_hypData hD.parab d hd e hD.mem hD.pow hD.fix
  obtain ⟨r₀, q, hdq⟩ := ToralCensus.exists_eq_twistedA hd
  have hpq : p ∣ (2 ^ f) ^ 2 - 1 := by
    rw [hdq] at hnt
    simp only [IndexTorusFree, not_or, not_not] at hnt
    rw [← hq r₀ q hdq]
    exact hnt.2
  have hp2 : p ≠ 2 := by have := hD.five_le; omega
  rcases ToralCensus.prime_dvd_sub_or_add_of_dvd_sq_sub_one hD.prime hpq with h1 | h1
  · exact ToralCensus.false_of_dvd_sub_one_hyp h hr hε hD.prime hp2 h1 T hT hJ' ht hfix
      (hjoin hD.join)
      (hcyc (ToralCensus.coprime_two_pow_add_one_of_dvd_sub_one hD.prime hp2 h1) hD.cyc)
  · exact ToralCensus.false_of_dvd_add_one_hyp h hr hε hD.prime hp2 h1 T hT hJ' ht hfix

theorem fixPrimeTwistedA_of_griess (hGA : GriessAllModelsStatement) : FixPrimeTwistedA :=
  fixPrimeTwistedA_of_torus hGA fixPrimeTwistedATorus_holds

end CFSG.AGLEmbedding
