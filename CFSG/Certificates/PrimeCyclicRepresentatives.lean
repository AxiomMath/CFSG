module

public import CFSG.Certificates.PrimeCyclicRepresentativesPowers

public section

namespace CFSG.Certificates.PrimeCyclicRepresentatives

variable {P : Type*} [Group P] [LinearOrder P]

@[expose] def representatives (p : ℕ) (hp : p.Prime) : Set P :=
  {r | ∃ x : P, x ≠ 1 ∧ x ^ p = 1 ∧ minimum p hp x = r}

theorem minimum_mem_representatives (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) : minimum p hp x ∈ representatives p hp :=
  ⟨x, hx, hpow, rfl⟩

theorem orderOf_of_mem_representatives (p : ℕ) (hp : p.Prime) {r : P}
    (hr : r ∈ representatives p hp) : orderOf r = p := by
  obtain ⟨x, hx, hpow, rfl⟩ := hr
  exact orderOf_minimum p hp hx hpow

theorem mem_representatives_iff_least (p : ℕ) (hp : p.Prime) (r : P) :
    r ∈ representatives p hp ↔ orderOf r = p ∧
      ∀ y ∈ Subgroup.zpowers r, y ≠ 1 → r ≤ y := by
  constructor
  · rintro ⟨x, hx, hpow, hmin⟩
    have hleast := (minimum_eq_iff_least p hp hx hpow r).mp hmin
    have hgroup : Subgroup.zpowers r = Subgroup.zpowers x := by
      simpa only [hmin] using zpowers_minimum p hp hx hpow
    refine ⟨?_, fun y hy hy1 => hleast.2.2 y ?_ hy1⟩
    · simpa only [hmin] using orderOf_minimum p hp hx hpow
    · rwa [← hgroup]
  · rintro ⟨horder, hleast⟩
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨hpow, hr1⟩ := orderOf_eq_prime_iff.mp horder
    refine ⟨r, hr1, hpow, ?_⟩
    exact (minimum_eq_iff_least p hp hr1 hpow r).mpr
      ⟨Subgroup.mem_zpowers r, hr1, hleast⟩

theorem minimum_self_of_mem_representatives (p : ℕ) (hp : p.Prime) {r : P}
    (hr : r ∈ representatives p hp) : minimum p hp r = r := by
  obtain ⟨horder, hleast⟩ := (mem_representatives_iff_least p hp r).mp hr
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpow, hr1⟩ := orderOf_eq_prime_iff.mp horder
  exact (minimum_eq_iff_least p hp hr1 hpow r).mpr
    ⟨Subgroup.mem_zpowers r, hr1, hleast⟩

theorem eq_of_mem_representatives_of_zpowers_eq (p : ℕ) (hp : p.Prime)
    {r s : P} (hr : r ∈ representatives p hp) (hs : s ∈ representatives p hp)
    (hgroup : Subgroup.zpowers r = Subgroup.zpowers s) : r = s := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hrp, hr1⟩ := orderOf_eq_prime_iff.mp (orderOf_of_mem_representatives p hp hr)
  obtain ⟨hsp, hs1⟩ := orderOf_eq_prime_iff.mp (orderOf_of_mem_representatives p hp hs)
  have h := minimum_eq_of_zpowers_eq p hp hr1 hrp hs1 hsp hgroup
  rwa [minimum_self_of_mem_representatives p hp hr,
    minimum_self_of_mem_representatives p hp hs] at h

omit [LinearOrder P] in
theorem orderOf_and_zpowers_eq_of_mem_prime_subgroup (p : ℕ) (hp : p.Prime)
    (Q : Subgroup P) (hQ : Nat.card Q = p) {x : P} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    orderOf x = p ∧ Subgroup.zpowers x = Q := by
  have hpow : x ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (by simpa only [hQ] using Q.orderOf_dvd_natCard hx)
  have horder := orderOf_eq_prime_of_power p hp hx1 hpow
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact hp.ne_zero)
  refine ⟨horder, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_⟩
  rw [Nat.card_zpowers, horder, hQ]

theorem exists_representative_of_prime_subgroup (p : ℕ) (hp : p.Prime)
    (Q : Subgroup P) (hQ : Nat.card Q = p) :
    ∃ r : P, r ∈ representatives p hp ∧ Subgroup.zpowers r = Q := by
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact hp.ne_zero)
  let : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; exact hp.one_lt)
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  have hx1 : (x : P) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨horder, hgroup⟩ := orderOf_and_zpowers_eq_of_mem_prime_subgroup p hp Q hQ
    x.property hx1
  have hpow : (x : P) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [horder])
  exact ⟨minimum p hp (x : P), minimum_mem_representatives p hp hx1 hpow,
    (zpowers_minimum p hp hx1 hpow).trans hgroup⟩

theorem existsUnique_representative_of_prime_subgroup (p : ℕ) (hp : p.Prime)
    (Q : Subgroup P) (hQ : Nat.card Q = p) :
    ∃! r : P, r ∈ representatives p hp ∧ Subgroup.zpowers r = Q := by
  obtain ⟨r, hr, hgroup⟩ := exists_representative_of_prime_subgroup p hp Q hQ
  refine ⟨r, ⟨hr, hgroup⟩, ?_⟩
  rintro s ⟨hs, hsQ⟩
  exact eq_of_mem_representatives_of_zpowers_eq p hp hs hr (hsQ.trans hgroup.symm)

theorem zpowers_bijOn_representatives (p : ℕ) (hp : p.Prime) :
    Set.BijOn (Subgroup.zpowers : P → Subgroup P) (representatives p hp)
      {Q | Nat.card Q = p} := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    change Nat.card (Subgroup.zpowers r) = p
    rw [Nat.card_zpowers, orderOf_of_mem_representatives p hp hr]
  · intro r hr s hs hgroup
    exact eq_of_mem_representatives_of_zpowers_eq p hp hr hs hgroup
  · intro Q hQ
    exact exists_representative_of_prime_subgroup p hp Q hQ

@[expose] def representativeSubgroup (p : ℕ) (hp : p.Prime) :
    {r : P // r ∈ representatives p hp} → {Q : Subgroup P // Nat.card Q = p} :=
  fun r => ⟨Subgroup.zpowers r.val,
    by rw [Nat.card_zpowers, orderOf_of_mem_representatives p hp r.property]⟩

theorem representativeSubgroup_bijective (p : ℕ) (hp : p.Prime) :
    Function.Bijective (representativeSubgroup (P := P) p hp) := by
  constructor
  · intro r s h
    apply Subtype.ext
    exact eq_of_mem_representatives_of_zpowers_eq p hp r.property s.property
      (congrArg Subtype.val h)
  · intro Q
    obtain ⟨r, hr, hgroup⟩ := exists_representative_of_prime_subgroup p hp Q.val Q.property
    exact ⟨⟨r, hr⟩, Subtype.ext hgroup⟩

@[expose] noncomputable def representativeEquiv (p : ℕ) (hp : p.Prime) :
    {r : P // r ∈ representatives p hp} ≃ {Q : Subgroup P // Nat.card Q = p} :=
  Equiv.ofBijective (representativeSubgroup (P := P) p hp)
    (representativeSubgroup_bijective p hp)

theorem representativeEquiv_apply (p : ℕ) (hp : p.Prime)
    (r : {r : P // r ∈ representatives p hp}) :
    (representativeEquiv p hp r).val = Subgroup.zpowers r.val := rfl

theorem card_representatives (p : ℕ) (hp : p.Prime) :
    Nat.card {r : P // r ∈ representatives p hp} =
      Nat.card {Q : Subgroup P // Nat.card Q = p} :=
  Nat.card_congr (representativeEquiv p hp)

theorem representatives_eq_empty_of_subsingleton [Subsingleton P] (p : ℕ) (hp : p.Prime) :
    representatives (P := P) p hp = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨x, hx, _, _⟩
  exact hx (Subsingleton.elim _ _)

theorem representatives_eq_empty_iff (p : ℕ) (hp : p.Prime) :
    representatives (P := P) p hp = ∅ ↔ ∀ Q : Subgroup P, Nat.card Q ≠ p := by
  constructor
  · intro hempty Q hQ
    obtain ⟨r, hr, _⟩ := exists_representative_of_prime_subgroup p hp Q hQ
    simp only [hempty, Set.mem_empty_iff_false] at hr
  · intro hnone
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    apply hnone (Subgroup.zpowers r)
    rw [Nat.card_zpowers, orderOf_of_mem_representatives p hp hr]

theorem nonzeroPowers_two (x : P) : nonzeroPowers 2 x = {x} := by
  ext y
  rw [mem_nonzeroPowers_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, hjp, he⟩
    have hj1 : j = 1 := by omega
    simpa only [hj1, pow_one] using he.symm
  · intro he
    exact ⟨1, le_rfl, by decide, by simpa only [pow_one] using he.symm⟩

theorem minimum_two (hp : Nat.Prime 2) (x : P) : minimum 2 hp x = x := by
  unfold minimum
  simp only [nonzeroPowers_two, Finset.min'_singleton]

theorem representatives_two (hp : Nat.Prime 2) :
    representatives (P := P) 2 hp = {x | x ≠ 1 ∧ x ^ 2 = 1} := by
  ext r
  simp only [representatives, Set.mem_ofPred_eq, minimum_two]
  aesop

section Finite

variable [Fintype P]

@[expose] def representativesFinset (p : ℕ) (hp : p.Prime) : Finset P :=
  (Finset.univ.filter fun x : P => x ≠ 1 ∧ x ^ p = 1).image (minimum p hp)

theorem mem_representativesFinset_iff (p : ℕ) (hp : p.Prime) (r : P) :
    r ∈ representativesFinset p hp ↔ r ∈ representatives p hp := by
  simp only [representativesFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, representatives, Set.mem_ofPred_eq]
  aesop

theorem coe_representativesFinset (p : ℕ) (hp : p.Prime) :
    (↑(representativesFinset (P := P) p hp) : Set P) = representatives p hp := by
  ext r
  exact mem_representativesFinset_iff p hp r

theorem representativesFinset_card_eq_subgroups (p : ℕ) (hp : p.Prime) :
    (representativesFinset (P := P) p hp).card =
      Nat.card {Q : Subgroup P // Nat.card Q = p} := by
  have h := card_representatives (P := P) p hp
  rw [← coe_representativesFinset p hp] at h
  change Nat.card (representativesFinset (P := P) p hp) = _ at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

end Finite

end PrimeCyclicRepresentatives

open PrimeCyclicRepresentatives

variable {P : Type*} [Group P] [LinearOrder P]

theorem prime_cyclic_canonical_representatives (p : ℕ) (hp : p.Prime) :
    (∀ r ∈ representatives (P := P) p hp, orderOf r = p) ∧
      Set.BijOn (Subgroup.zpowers : P → Subgroup P) (representatives p hp)
        {Q | Nat.card Q = p} ∧
      ∀ Q : Subgroup P, Nat.card Q = p →
        ∃! r : P, r ∈ representatives p hp ∧ Subgroup.zpowers r = Q :=
  ⟨fun _ hr => orderOf_of_mem_representatives p hp hr,
    zpowers_bijOn_representatives p hp, existsUnique_representative_of_prime_subgroup p hp⟩

end CFSG.Certificates
