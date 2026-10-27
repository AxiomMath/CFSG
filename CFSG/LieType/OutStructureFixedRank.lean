module

public import CFSG.GroupTheory.FixedPointQuotientCard
public import CFSG.LieType.OutStructureAGeneral

public section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open

namespace CFSG.LieType.OutStructure

theorem prime_dvd_pow_prime_mul_sub_one_iff {p q d : ℕ} (hp : p.Prime) (hq : 1 ≤ q) :
    p ∣ q ^ (p * d) - 1 ↔ p ∣ q ^ d - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.dvd_pow_prime_sub_one_iff
    (p := p) (q := q ^ d) (Nat.one_le_pow d q hq)
  rwa [← pow_mul, mul_comm d p] at h

theorem natCard_eq_natCard_semilinearFixedSubfield_pow {K : Type*} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    Nat.card K =
      Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) ^ p := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hchar, hKcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (e : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hchar e.pos hK hσ
  rw [hK, hcard, ← pow_mul, Nat.div_mul_cancel hdvd]

theorem fixedSubgroup_fieldAut_eq_range_of_one_le {K : Type*} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n)
    (hdiv : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    (CFSG.autFixedSubgroup (fieldAut n K σ) : Set (projectiveSL n K)) =
      ((CFSG.RankThree.PartOne.linearSubfieldInclusion n
        (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).range :
        Set (projectiveSL n K)) := by
  have hk : ∀ x, x ∈ CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ ↔ σ x = x :=
    fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hdesc : ∀ a : Kˣ,
      (a : K) ∈ CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ →
      (∃ u : Kˣ, u ^ n = a) →
      ∃ w : Kˣ, (w : K) ∈ CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ ∧
        w ^ n = a := by
    by_cases hpn : p ∣ n
    · have hpK : ¬ p ∣ Nat.card Kˣ := by
        rw [Nat.card_units]
        intro h
        exact hdiv (Nat.dvd_gcd hpn h)
      exact CFSG.RankThree.PartOne.KCLinearSubfield.root_descent_of_not_dvd hp hk hσp hpK
    · exact CFSG.RankThree.PartOne.KCLinearSubfield.root_descent_of_coprime hk hσp
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm
  have h := CFSG.RankThree.PartOne.KCLinearSubfield.fixed_points_eq_range
    (k := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) (σ := σ) hk
    (by omega) hdesc
  ext x
  simpa [CFSG.mem_autFixedSubgroup] using
    congrArg (fun S : Set (projectiveSL n K) => x ∈ S) h

theorem pRank_projectiveSL_pow_prime {K K₀ : Type} [Field K] [Finite K]
    [Field K₀] [Finite K₀] {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hcard : Nat.card K = Nat.card K₀ ^ p)
    (hpK : ¬ p ∣ Nat.card K)
    (hdiv : ¬ p ∣ Nat.gcd m (Nat.card K - 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K₀)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK₀ : ¬ p ∣ Nat.card K₀ := by
    intro h
    apply hpK
    rw [hcard]
    exact h.trans (dvd_pow_self (Nat.card K₀) hp.ne_zero)
  have hiff : p ∣ Nat.card K - 1 ↔ p ∣ Nat.card K₀ - 1 := by
    rw [hcard]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.dvd_pow_prime_sub_one_iff
      (p := p) (q := Nat.card K₀) Nat.card_pos
  have hdiv₀ : ¬ p ∣ Nat.gcd m (Nat.card K₀ - 1) := by
    intro h
    apply hdiv
    have hK₀ : p ∣ Nat.card K₀ - 1 := h.trans (Nat.gcd_dvd_right m (Nat.card K₀ - 1))
    have hK : p ∣ Nat.card K - 1 := by
      rw [hcard]
      simpa using (prime_dvd_pow_prime_mul_sub_one_iff (p := p) (q := Nat.card K₀) (d := 1)
        hp Nat.card_pos).2 (by simpa using hK₀)
    exact Nat.dvd_gcd (h.trans (Nat.gcd_dvd_left m (Nat.card K₀ - 1))) hK
  rw [pRank_projectiveSL_formula (N := m) (K := K) hp hp2 hm hpK hdiv,
    pRank_projectiveSL_formula (N := m) (K := K₀) hp hp2 hm hpK₀ hdiv₀]
  by_cases h : p ∣ Nat.card K₀ - 1
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hK => h (hiff.mp hK)), if_neg h]
    congr 1
    rw [hcard]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.orderOf_natCast_pow_prime
      (p := p) (q := Nat.card K₀)

theorem pRank_autFixedSubgroup_eq_of_hdiv {K : Type} [Field K] [Finite K] {m p : ℕ}
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 1 ≤ m) (hpK : ¬ p ∣ Nat.card K)
    (hdiv : ¬ p ∣ Nat.gcd m (Nat.card K - 1)) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup (fieldAut m K σ)) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) := by
  let K₀ := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ
  have hfix := fixedSubgroup_fieldAut_eq_range_of_one_le (K := K) hp hm hdiv σ hσ
  have hsub : CFSG.autFixedSubgroup (fieldAut m K σ) =
      (CFSG.RankThree.PartOne.linearSubfieldInclusion m K₀).range :=
    SetLike.coe_injective hfix
  have hinj : Function.Injective (CFSG.RankThree.PartOne.linearSubfieldInclusion m K₀) :=
    CFSG.RankThree.PartOne.linearSubfieldInclusion_injective (by omega) K₀
  have h1 : CFSG.Open.pRank p (CFSG.autFixedSubgroup (fieldAut m K σ)) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K₀)) := by
    rw [hsub]
    exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (CFSG.RankThree.PartOne.linearSubfieldInclusion m K₀).range).trans
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (MonoidHom.ofInjective hinj)).symm
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K₀)) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) :=
    (pRank_projectiveSL_pow_prime (K := K) (K₀ := K₀) hp hp2 hm
      (natCard_eq_natCard_semilinearFixedSubfield_pow hp σ hσ) hpK hdiv).symm
  exact h1.trans h2

theorem pRank_autFixedSubgroup_eq {K : Type} [Field K] [Finite K] {m p : ℕ}
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (hpK : ¬ p ∣ Nat.card K)
    (hdiv : ¬ p ∣ Nat.gcd m (Nat.card K - 1)) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup (fieldAut m K σ)) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) :=
  pRank_autFixedSubgroup_eq_of_hdiv σ hσ hp hp2 (by omega) hpK hdiv

end CFSG.LieType.OutStructure
