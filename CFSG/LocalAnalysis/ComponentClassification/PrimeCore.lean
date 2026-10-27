module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Fitting

public section

namespace CFSG.ComponentClassification.PrimeCore

@[expose] noncomputable def subgroup (prime : ℕ) (G : Type*) [Group G] : Subgroup G :=
  CFSG.pCore prime G

theorem normal (prime : ℕ) (G : Type*) [Group G] : (subgroup prime G).Normal :=
  CFSG.pCore_normal

theorem isPGroup (prime : ℕ) (G : Type*) [Group G] : IsPGroup prime (subgroup prime G) :=
  CFSG.pCore_isPGroup

theorem maximal {G : Type*} [Group G] (prime : ℕ) (candidate : Subgroup G)
    [candidate.Normal] (hprime : IsPGroup prime candidate) : candidate ≤ subgroup prime G :=
  le_sSup ⟨inferInstance, hprime⟩

theorem characteristic (prime : ℕ) (G : Type*) [Group G] :
    (subgroup prime G).Characteristic :=
  CFSG.pCore_characteristic

theorem normal_monotone {G : Type*} [Group G] (prime : ℕ)
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (subgroup prime normalSubgroup).map normalSubgroup.subtype ≤ subgroup prime G := by
  let : (subgroup prime normalSubgroup).Characteristic := characteristic prime normalSubgroup
  let : ((subgroup prime normalSubgroup).map normalSubgroup.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  exact maximal prime _ ((isPGroup prime normalSubgroup).map normalSubgroup.subtype)

theorem le_fitting (prime : ℕ) (G : Type*) [Group G] [Finite G] [Fact prime.Prime] :
    subgroup prime G ≤ Fitting.subgroup G := by
  let : (subgroup prime G).Normal := normal prime G
  let : Group.IsNilpotent (subgroup prime G) := (isPGroup prime G).isNilpotent
  exact Fitting.maximal _

theorem eq_top_of_all_sylow {G : Type*} [Group G] [Finite G] (candidate : Subgroup G)
    (hcontains : ∀ prime : ℕ, prime.Prime → ∀ sylow : Sylow prime G,
      (sylow : Subgroup G) ≤ candidate) : candidate = ⊤ := by
  apply Subgroup.index_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro prime hprime hdivides
  let : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime G := Classical.choice inferInstance
  exact sylow.not_dvd_index (hdivides.trans (Subgroup.index_dvd_of_le
    (hcontains prime hprime sylow)))

theorem nilpotent_normal_le_join {G : Type*} [Group G] [Finite G]
    (candidate : Subgroup G) [candidate.Normal] [Group.IsNilpotent candidate] :
    candidate ≤ ⨆ prime : {prime : ℕ // prime.Prime}, subgroup prime.val G := by
  let joined : Subgroup G := ⨆ prime : {prime : ℕ // prime.Prime}, subgroup prime.val G
  have htop : joined.subgroupOf candidate = ⊤ := by
    apply eq_top_of_all_sylow
    intro prime hprime sylow
    let : Fact prime.Prime := ⟨hprime⟩
    let : (sylow : Subgroup candidate).Normal := inferInstance
    let : (sylow : Subgroup candidate).Characteristic :=
      sylow.characteristic_of_normal inferInstance
    let image := (sylow : Subgroup candidate).map candidate.subtype
    let : image.Normal := ConjAct.normal_of_characteristic_of_normal
    have hle : image ≤ subgroup prime G := maximal prime image (sylow.isPGroup'.map candidate.subtype)
    intro member hmember
    exact (le_iSup (fun prime : {prime : ℕ // prime.Prime} => subgroup prime.val G)
      ⟨prime, hprime⟩) (hle (Subgroup.mem_map_of_mem candidate.subtype hmember))
  intro member hmember
  have hjoined : (⟨member, hmember⟩ : candidate) ∈ joined.subgroupOf candidate := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hjoined

theorem fitting_eq_join (G : Type*) [Group G] [Finite G] :
    Fitting.subgroup G = ⨆ prime : {prime : ℕ // prime.Prime}, subgroup prime.val G := by
  apply le_antisymm
  · apply sSup_le
    intro candidate hcandidate
    let : candidate.Normal := hcandidate.1
    let : Group.IsNilpotent candidate := hcandidate.2
    exact nilpotent_normal_le_join candidate
  · apply iSup_le
    intro prime
    let : Fact prime.val.Prime := ⟨prime.property⟩
    exact le_fitting prime.val G

theorem fitting_normal_monotone {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (Fitting.subgroup normalSubgroup).map normalSubgroup.subtype ≤ Fitting.subgroup G := by
  rw [fitting_eq_join, Subgroup.map_iSup]
  apply iSup_le
  intro prime
  let : Fact prime.val.Prime := ⟨prime.property⟩
  exact (normal_monotone prime.val normalSubgroup).trans (le_fitting prime.val G)

theorem fitting_eq_two_of_odd_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : CFSG.Open.componentClassificationOddCore G = ⊥) :
    Fitting.subgroup G = subgroup 2 G := by
  rw [fitting_eq_join]
  apply le_antisymm
  · apply iSup_le
    intro prime
    by_cases heq : prime.val = 2
    · rw [heq]
    · let : (subgroup prime.val G).Normal := normal prime.val G
      let : Fact prime.val.Prime := ⟨prime.property⟩
      have hodd : Odd (Nat.card (subgroup prime.val G)) := by
        obtain ⟨exponent, hcard⟩ := (isPGroup prime.val G).exists_card_eq
        rw [hcard]
        exact (prime.property.odd_of_ne_two heq).pow
      have hle := OddCore.maximal G (subgroup prime.val G) inferInstance hodd
      rw [hcorefree] at hle
      exact hle.trans bot_le
  · exact le_iSup (fun prime : {prime : ℕ // prime.Prime} => subgroup prime.val G)
      ⟨2, Nat.prime_two⟩

end CFSG.ComponentClassification.PrimeCore
