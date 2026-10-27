module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
public import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Foundations.HallLiftThroughNormalPi
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.PLengthOneNormalSeries
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.SmallestPrimeNormalComplementRankTwo
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

variable {p q : ℕ} {G : Type*} [Group G] [Finite G]

private theorem exists_eq_pow_of_isPiNumber_singleton {n : ℕ} (hn : n ≠ 0)
    (h : IsPiNumber ({p} : Set ℕ) n) : ∃ a : ℕ, n = p ^ a :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn fun {d} hd hdvd =>
    isPiNumber_iff.1 h d (Nat.mem_primeFactors.2 ⟨hd, hdvd, hn⟩)⟩

omit [Finite G] in
theorem isHallSubgroup_compl_singleton_of_index_eq_pow {K : Subgroup G} (hp : p.Prime)
    (hcard : ¬ p ∣ Nat.card K) (hindex : ∃ a : ℕ, K.index = p ^ a) :
    IsHallSubgroup ({p}ᶜ : Set ℕ) K where
  natCard := isPiNumber_iff.2 fun r hr hr' =>
    hcard (Set.mem_singleton_iff.1 hr' ▸ Nat.dvd_of_mem_primeFactors hr)
  index := by
    obtain ⟨a, ha⟩ := hindex
    rw [compl_compl]
    refine isPiNumber_iff.2 fun r hr => ?_
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp [ha] at hr
    · rw [ha, Nat.primeFactors_prime_pow hpos.ne' hp] at hr
      simpa using hr

theorem pComplCore_eq_top_of_not_dvd {X : Type*} [Group X] [Finite X] (h : ¬ p ∣ Nat.card X) :
    pComplCore p X = ⊤ :=
  top_le_iff.1 (le_pComplCore (Subgroup.normal_of_characteristic ⊤)
    (by rw [Subgroup.card_top]; exact fun hmem => h (Nat.dvd_of_mem_primeFactors hmem)))

theorem exists_index_pComplCore_eq_pow_of_le_primeFactors {X : Type*} [Group X] [Finite X]
    [Group.IsSolvable X] (hp : p.Prime) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    ∃ a : ℕ, (pComplCore p X).index = p ^ a := by
  by_cases hpX : p ∣ Nat.card X
  · exact exists_index_pComplCore_eq_pow hp hpX hmin hodd hrank
  · exact ⟨0, by rw [pComplCore_eq_top_of_not_dvd hpX, Subgroup.index_top, pow_zero]⟩

theorem elementaryAbelianPRank_fittingRaw_le_of_normal (hq : 1 < q) {N : Subgroup G}
    (hN : N.Normal) :
    elementaryAbelianPRank q ↥(fittingRaw ↥N) ≤ elementaryAbelianPRank q ↥(fittingRaw G) := by
  have h1 : elementaryAbelianPRank q ↥(fittingRaw ↥N)
      = elementaryAbelianPRank q ↥((fittingRaw ↥N).map N.subtype) :=
    elementaryAbelianPRank_eq_of_mulEquiv hq
      ((fittingRaw ↥N).equivMapOfInjective _ N.subtype_injective)
  rw [h1]
  exact elementaryAbelianPRank_le_of_le hq (map_subtype_fittingRaw_le_fittingRaw hN)

theorem natCard_fittingPiPart_singleton (hp : p.Prime) (G : Type*) [Group G] [Finite G] :
    Nat.card ↥(fittingPiPart ({p} : Set ℕ) G)
      = p ^ (Nat.card ↥(fittingRaw G)).factorization p := by
  have := fittingRaw_isNilpotent G
  obtain ⟨a, ha⟩ := exists_eq_pow_of_isPiNumber_singleton (p := p)
    (n := Nat.card ↥(fittingPiPart ({p} : Set ℕ) G)) Nat.card_pos.ne'
    (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_fittingPiPart _ _))
  have hfac : (Nat.card ↥(fittingPiPart ({p} : Set ℕ) G)).factorization p
      = (Nat.card ↥(fittingRaw G)).factorization p := by
    rw [natCard_fittingPiPart]
    exact factorization_natCard_sylowPiPart hp rfl
  rw [ha] at hfac ⊢
  rw [hp.factorization_pow] at hfac
  simp only [Finsupp.single_eq_same] at hfac
  rw [hfac]

theorem isMulCommutative_quotient_fittingRaw [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    IsMulCommutative (G ⧸ fittingRaw G) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 (commutator_le_fittingRaw hodd hrank)

theorem isNilpotent_quotient_fittingRaw [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    Group.IsNilpotent (G ⧸ fittingRaw G) :=
  have := isMulCommutative_quotient_fittingRaw hodd hrank
  isNilpotent_of_isMulCommutative _

def fittingPComplPreimage (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)).comap (QuotientGroup.mk' (fittingRaw G))

theorem fittingPComplPreimage_eq_comap (p : ℕ) (G : Type*) [Group G] [Finite G] :
    fittingPComplPreimage p G =
      (sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)).comap (QuotientGroup.mk' (fittingRaw G)) :=
  (rfl)

instance fittingPComplPreimage_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (fittingPComplPreimage p G).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk (sylowPiPart_characteristic _ _)

theorem fittingRaw_le_fittingPComplPreimage (p : ℕ) (G : Type*) [Group G] [Finite G] :
    fittingRaw G ≤ fittingPComplPreimage p G := by
  rw [fittingPComplPreimage_eq_comap]
  exact le_comap_mk' _

theorem relIndex_fittingRaw_fittingPComplPreimage (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (fittingRaw G).relIndex (fittingPComplPreimage p G)
      = Nat.card ↥(sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)) := by
  rw [fittingPComplPreimage_eq_comap]
  exact relIndex_comap_mk' _ _

theorem exists_index_fittingPComplPreimage_eq_pow (p : ℕ) (G : Type*) [Group G] [Finite G] :
    ∃ a : ℕ, (fittingPComplPreimage p G).index = p ^ a := by
  have hidx : (fittingPComplPreimage p G).index
      = (sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)).index := by
    rw [fittingPComplPreimage_eq_comap]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  refine exists_eq_pow_of_isPiNumber_singleton Subgroup.index_ne_zero_of_finite ?_
  rw [hidx]
  have h := isPiNumber_compl_index_sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)
  rwa [compl_compl] at h

theorem natCard_mul_relIndex_fittingRaw (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Nat.card ↥(fittingRaw G) * (fittingRaw G).relIndex (fittingPComplPreimage p G)
      = Nat.card ↥(fittingPComplPreimage p G) := by
  rw [Subgroup.relIndex, ← natCard_subgroupOf_of_le (fittingRaw_le_fittingPComplPreimage p G)]
  exact Subgroup.card_mul_index _

theorem not_dvd_relIndex_fittingRaw [Group.IsSolvable G] (hp : p.Prime) (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    ¬ p ∣ (fittingRaw G).relIndex (fittingPComplPreimage p G) := by
  have := isNilpotent_quotient_fittingRaw hodd hrank
  rw [relIndex_fittingRaw_fittingPComplPreimage]
  intro hd
  exact isPiSubgroup_iff.1 (isPiSubgroup_sylowPiPart ({p}ᶜ : Set ℕ) (G ⧸ fittingRaw G)) p
    (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩) rfl

theorem factorization_natCard_fittingPComplPreimage [Group.IsSolvable G] (hp : p.Prime)
    (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    (Nat.card ↥(fittingPComplPreimage p G)).factorization p
      = (Nat.card ↥(fittingRaw G)).factorization p := by
  have hnd := not_dvd_relIndex_fittingRaw hp hodd hrank
  have hne : (fittingRaw G).relIndex (fittingPComplPreimage p G) ≠ 0 := by
    intro h; rw [h] at hnd; exact hnd (dvd_zero p)
  rw [← natCard_mul_relIndex_fittingRaw p G, Nat.factorization_mul Nat.card_pos.ne' hne]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

theorem elementaryAbelianPRank_fittingPComplPreimage_le [Group.IsSolvable G] (hp : p.Prime)
    (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    elementaryAbelianPRank p ↥(fittingPComplPreimage p G) ≤ 2 := by
  have hle : fittingPiPart ({p} : Set ℕ) G ≤ fittingPComplPreimage p G :=
    le_trans fittingPiPart_le_fittingRaw (fittingRaw_le_fittingPComplPreimage p G)
  have hcard : Nat.card ↥((fittingPiPart ({p} : Set ℕ) G).subgroupOf (fittingPComplPreimage p G))
      = p ^ (Nat.card ↥(fittingPComplPreimage p G)).factorization p := by
    rw [natCard_subgroupOf_of_le hle, natCard_fittingPiPart_singleton hp,
      factorization_natCard_fittingPComplPreimage hp hodd hrank]
  have h1 := elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hcard
  have h2 : elementaryAbelianPRank p
      ↥((fittingPiPart ({p} : Set ℕ) G).subgroupOf (fittingPComplPreimage p G))
      = elementaryAbelianPRank p ↥(fittingPiPart ({p} : Set ℕ) G) :=
    elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (Subgroup.subgroupOfEquivOfLe hle)
  rw [← h1, h2]
  exact le_trans (elementaryAbelianPRank_le_of_le hp.one_lt fittingPiPart_le_fittingRaw)
    (hrank p hp)

def charHallPCompl (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (pComplCore p ↥(fittingPComplPreimage p G)).map (fittingPComplPreimage p G).subtype

theorem charHallPCompl_eq_map (p : ℕ) (G : Type*) [Group G] [Finite G] :
    charHallPCompl p G
      = (pComplCore p ↥(fittingPComplPreimage p G)).map (fittingPComplPreimage p G).subtype :=
  (rfl)

instance charHallPCompl_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (charHallPCompl p G).Characteristic := by
  rw [charHallPCompl_eq_map]
  exact Subgroup.characteristic_of_characteristic_of_characteristic

theorem charHallPCompl_map_equiv (p : ℕ) (G : Type*) [Group G] [Finite G] (ϕ : G ≃* G) :
    (charHallPCompl p G).map ϕ.toMonoidHom = charHallPCompl p G :=
  Subgroup.characteristic_iff_map_eq.1 (charHallPCompl_characteristic p G) ϕ

instance charHallPCompl_normal (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (charHallPCompl p G).Normal := Subgroup.normal_of_characteristic _

theorem charHallPCompl_le (p : ℕ) (G : Type*) [Group G] [Finite G] :
    charHallPCompl p G ≤ fittingPComplPreimage p G := Subgroup.map_subtype_le _

theorem natCard_charHallPCompl (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Nat.card ↥(charHallPCompl p G) = Nat.card ↥(pComplCore p ↥(fittingPComplPreimage p G)) :=
  Subgroup.card_map_of_injective (fittingPComplPreimage p G).subtype_injective

theorem relIndex_charHallPCompl (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (charHallPCompl p G).relIndex (fittingPComplPreimage p G)
      = (pComplCore p ↥(fittingPComplPreimage p G)).index := by
  rw [charHallPCompl_eq_map, Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (fittingPComplPreimage p G).subtype_injective]

theorem not_dvd_natCard_charHallPCompl (hp : p.Prime) (G : Type*) [Group G] [Finite G] :
    ¬ p ∣ Nat.card ↥(charHallPCompl p G) := by
  rw [natCard_charHallPCompl]
  exact not_dvd_natCard_pComplCore hp _

theorem exists_index_charHallPCompl_eq_pow [Group.IsSolvable G] (hp : p.Prime)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → p ≤ q) (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    ∃ a : ℕ, (charHallPCompl p G).index = p ^ a := by
  obtain ⟨b, hb⟩ := exists_index_fittingPComplPreimage_eq_pow p G
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (pComplCore p ↥(fittingPComplPreimage p G)).index = p ^ c :=
    exists_index_pComplCore_eq_pow_of_le_primeFactors hp
      (fun r hr hrH => hmin r hr (hrH.trans (Subgroup.card_subgroup_dvd_card _)))
      (hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _))
      (elementaryAbelianPRank_fittingPComplPreimage_le hp hodd hrank)
  exact ⟨c + b, by
    rw [← Subgroup.relIndex_mul_index (charHallPCompl_le p G), relIndex_charHallPCompl, hc, hb,
      pow_add]⟩

theorem isHallSubgroup_charHallPCompl [Group.IsSolvable G] (hp : p.Prime)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → p ≤ q) (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    IsHallSubgroup ({p}ᶜ : Set ℕ) (charHallPCompl p G) :=
  isHallSubgroup_compl_singleton_of_index_eq_pow hp (not_dvd_natCard_charHallPCompl hp G)
    (exists_index_charHallPCompl_eq_pow hp hmin hodd hrank)

theorem elementaryAbelianPRank_fittingRaw_charHallPCompl_le (hq : q.Prime) (p : ℕ) (G : Type*)
    [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    elementaryAbelianPRank q ↥(fittingRaw ↥(charHallPCompl p G)) ≤ 2 :=
  le_trans (elementaryAbelianPRank_fittingRaw_le_of_normal hq.one_lt
    (Subgroup.normal_of_characteristic _)) (hrank q hq)

theorem charHallPCompl_isCharacteristicHall [Group.IsSolvable G] (hp : p.Prime)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → p ≤ q) (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    (charHallPCompl p G).Characteristic ∧ IsHallSubgroup ({p}ᶜ : Set ℕ) (charHallPCompl p G) ∧
      ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw ↥(charHallPCompl p G)) ≤ 2 :=
  ⟨charHallPCompl_characteristic p G, isHallSubgroup_charHallPCompl hp hmin hodd hrank,
    fun q hq => elementaryAbelianPRank_fittingRaw_charHallPCompl_le hq p G hrank⟩

private theorem minFac_prime_natCard_and_min (X : Type*) [Finite X] [Nontrivial X] :
    (Nat.card X).minFac.Prime ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card X → (Nat.card X).minFac ≤ r :=
  have h1 : Nat.card X ≠ 1 := by have := Finite.one_lt_card (α := X); omega
  ⟨Nat.minFac_prime h1, fun _ hr hd => Nat.minFac_le_of_dvd hr.two_le hd⟩

theorem exists_characteristic_isHallSubgroup_compl_of_minFac [Nontrivial G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw G) ≤ 2) :
    ∃ K : Subgroup G, K.Characteristic ∧
      IsHallSubgroup (({(Nat.card G).minFac} : Set ℕ)ᶜ) K ∧
      ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw ↥K) ≤ 2 :=
  ⟨charHallPCompl (Nat.card G).minFac G,
    charHallPCompl_isCharacteristicHall (minFac_prime_natCard_and_min G).1
      (minFac_prime_natCard_and_min G).2 hodd hrank⟩

end

end CFSG.FeitThompson
