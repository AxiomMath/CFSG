module

public import CFSG.LocalAnalysis.ComponentClassification.PrimeCore

public section

namespace CFSG.ComponentClassification.FittingNilpotence

theorem prime_cores_commute {G : Type*} [Group G] (first second : ℕ)
    [Fact first.Prime] [Fact second.Prime] (hne : first ≠ second) :
    ∀ left right : G, left ∈ PrimeCore.subgroup first G → right ∈ PrimeCore.subgroup second G →
      Commute left right :=
  Subgroup.commute_of_normal_of_disjoint _ _ (PrimeCore.normal first G) (PrimeCore.normal second G)
    (IsPGroup.disjoint_of_ne first second hne _ _ (PrimeCore.isPGroup first G) (PrimeCore.isPGroup second G))

theorem prime_core_eq_bot_of_not_dvd {G : Type*} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (hnotDivides : ¬ prime ∣ Nat.card G) :
    PrimeCore.subgroup prime G = ⊥ := by
  have hcard := (PrimeCore.isPGroup prime G).card_eq_or_dvd
  have hone : Nat.card (PrimeCore.subgroup prime G) = 1 := hcard.resolve_right
    (fun hdivides => hnotDivides (hdivides.trans (Subgroup.card_subgroup_dvd_card _)))
  exact (Subgroup.eq_bot_iff_card _).mpr hone

theorem fitting_eq_finite_join (G : Type*) [Group G] [Finite G] :
    Fitting.subgroup G = ⨆ prime : ↥(Nat.card G).primeFactors, PrimeCore.subgroup prime.val G := by
  rw [PrimeCore.fitting_eq_join]
  apply le_antisymm
  · apply iSup_le
    intro prime
    let : Fact prime.val.Prime := ⟨prime.property⟩
    by_cases hdivides : prime.val ∣ Nat.card G
    · exact le_iSup_of_le (⟨prime.val, Nat.mem_primeFactors.mpr
        ⟨prime.property, hdivides, Nat.card_pos.ne'⟩⟩ : ↥(Nat.card G).primeFactors) le_rfl
    · rw [prime_core_eq_bot_of_not_dvd prime.val hdivides]
      exact bot_le
  · apply iSup_le
    intro prime
    exact le_iSup_of_le (⟨prime.val, (Nat.mem_primeFactors.mp prime.property).1⟩ : {prime : ℕ // prime.Prime}) le_rfl

theorem nilpotent (G : Type*) [Group G] [Finite G] : Group.IsNilpotent (Fitting.subgroup G) := by
  classical
  let factors : ↥(Nat.card G).primeFactors → Subgroup G := fun prime => PrimeCore.subgroup prime.val G
  have hprime : ∀ prime : ↥(Nat.card G).primeFactors, prime.val.Prime :=
    fun prime => (Nat.mem_primeFactors.mp prime.property).1
  let : ∀ prime : ↥(Nat.card G).primeFactors, Fact prime.val.Prime := fun prime => ⟨hprime prime⟩
  let : ∀ prime : ↥(Nat.card G).primeFactors, Group.IsNilpotent (factors prime) :=
    fun prime => (PrimeCore.isPGroup prime.val G).isNilpotent
  have hcommutes : Pairwise (fun first second : ↥(Nat.card G).primeFactors =>
      ∀ left right : G, left ∈ factors first → right ∈ factors second → Commute left right) := by
    intro first second hne
    exact prime_cores_commute first.val second.val (fun heq => hne (Subtype.ext heq))
  let product := Subgroup.noncommPiCoprod hcommutes
  have hrange : product.range = Fitting.subgroup G :=
    Subgroup.noncommPiCoprod_range.trans (fitting_eq_finite_join G).symm
  let : Group.IsNilpotent product.range := Group.nilpotent_of_surjective product.rangeRestrict
    (MonoidHom.rangeRestrict_surjective product)
  exact (Group.isNilpotent_congr (MulEquiv.subgroupCongr hrange)).mp inferInstance

theorem nilpotent_of_le {G : Type*} [Group G] (candidate containing : Subgroup G)
    [Group.IsNilpotent containing] (hle : candidate ≤ containing) : Group.IsNilpotent candidate :=
  (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hle)).mp inferInstance

theorem subgroupOf_nilpotent {G : Type*} [Group G] (nilpotentSubgroup candidate : Subgroup G)
    [Group.IsNilpotent nilpotentSubgroup] : Group.IsNilpotent (nilpotentSubgroup.subgroupOf candidate) := by
  let intersection := nilpotentSubgroup ⊓ candidate
  let : Group.IsNilpotent intersection := nilpotent_of_le intersection nilpotentSubgroup inf_le_left
  let localSubgroup := nilpotentSubgroup.subgroupOf candidate
  have himage : localSubgroup.map candidate.subtype = intersection := Subgroup.subgroupOf_map_subtype _ _
  let : Group.IsNilpotent (localSubgroup.map candidate.subtype) :=
    (Group.isNilpotent_congr (MulEquiv.subgroupCongr himage)).mpr inferInstance
  exact (Group.isNilpotent_congr
    (localSubgroup.equivMapOfInjective candidate.subtype candidate.subtype_injective)).mpr inferInstance

theorem normal_intersection {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (Fitting.subgroup normalSubgroup).map normalSubgroup.subtype =
      Fitting.subgroup G ⊓ normalSubgroup := by
  apply le_antisymm
  · exact le_inf (PrimeCore.fitting_normal_monotone normalSubgroup) (Subgroup.map_subtype_le _)
  · let fitting := Fitting.subgroup G
    let : fitting.Normal := Fitting.normal G
    let : Group.IsNilpotent fitting := nilpotent G
    let : Group.IsNilpotent (fitting.subgroupOf normalSubgroup) := subgroupOf_nilpotent _ _
    have hle := Subgroup.map_mono (f := normalSubgroup.subtype)
      (Fitting.maximal (fitting.subgroupOf normalSubgroup))
    rwa [Subgroup.subgroupOf_map_subtype] at hle

theorem map_le_of_equiv {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (Fitting.subgroup G).map equivalence.toMonoidHom ≤ Fitting.subgroup H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro candidate hcandidate
  let : candidate.Normal := hcandidate.1
  let : Group.IsNilpotent candidate := hcandidate.2
  let image := candidate.map equivalence.toMonoidHom
  let : image.Normal := Subgroup.Normal.map inferInstance equivalence.toMonoidHom equivalence.surjective
  let : Group.IsNilpotent image := (Group.isNilpotent_congr
    (candidate.equivMapOfInjective equivalence.toMonoidHom equivalence.injective)).mp inferInstance
  exact Subgroup.map_le_iff_le_comap.mp (Fitting.maximal image)

theorem equiv_invariant {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (Fitting.subgroup G).map equivalence.toMonoidHom = Fitting.subgroup H := by
  apply le_antisymm (map_le_of_equiv equivalence)
  intro member hmember
  have hinverse := map_le_of_equiv equivalence.symm
    (Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hmember)
  exact ⟨equivalence.symm member, hinverse, equivalence.apply_symm_apply member⟩

theorem normal_step_monotone {G : Type*} [Group G] [Finite G]
    (lower upper : Subgroup G) (hle : lower ≤ upper) [(lower.subgroupOf upper).Normal] :
    (Fitting.subgroup lower).map lower.subtype ≤ (Fitting.subgroup upper).map upper.subtype := by
  let localLower := lower.subgroupOf upper
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  have htransport : (Fitting.subgroup localLower).map equivalence.toMonoidHom = Fitting.subgroup lower :=
    equiv_invariant equivalence
  have hcomposition : lower.subtype.comp equivalence.toMonoidHom = upper.subtype.comp localLower.subtype := by
    ext member
    rfl
  rw [← htransport, Subgroup.map_map, hcomposition, ← Subgroup.map_map]
  exact Subgroup.map_mono (PrimeCore.fitting_normal_monotone localLower)

theorem subnormal_monotone {G : Type*} [Group G] [Finite G]
    (candidate : Subgroup G) (hsubnormal : candidate.IsSubnormal) :
    (Fitting.subgroup candidate).map candidate.subtype ≤ Fitting.subgroup G := by
  induction hsubnormal with
  | top =>
      have heq : (⊤ : Subgroup G).subtype = Subgroup.topEquiv.toMonoidHom := by ext member; rfl
      rw [heq, equiv_invariant]
  | step lower upper hle _ hnormal hinduction =>
      let : (lower.subgroupOf upper).Normal := hnormal
      exact (normal_step_monotone lower upper hle).trans hinduction

theorem subnormal_intersection {G : Type*} [Group G] [Finite G]
    (candidate : Subgroup G) (hsubnormal : candidate.IsSubnormal) :
    (Fitting.subgroup candidate).map candidate.subtype = Fitting.subgroup G ⊓ candidate := by
  apply le_antisymm
  · exact le_inf (subnormal_monotone candidate hsubnormal) (Subgroup.map_subtype_le _)
  · let fitting := Fitting.subgroup G
    let : fitting.Normal := Fitting.normal G
    let : Group.IsNilpotent fitting := nilpotent G
    let : Group.IsNilpotent (fitting.subgroupOf candidate) := subgroupOf_nilpotent _ _
    have hle := Subgroup.map_mono (f := candidate.subtype) (Fitting.maximal (fitting.subgroupOf candidate))
    rwa [Subgroup.subgroupOf_map_subtype] at hle

end CFSG.ComponentClassification.FittingNilpotence
