module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionColumns

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace CyclicSymmetricFour

open Equiv

section SymmetricFour

@[expose] def cycleA : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def cycleB : alternatingGroup (Fin 4) :=
  ⟨swap 1 2 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem alternating_words : ∀ g : alternatingGroup (Fin 4), ∃ i j k : Fin 3,
    g = cycleA ^ (i : ℕ) * cycleB ^ (j : ℕ) * cycleA ^ (k : ℕ) := by
  decide

theorem cycle_relations : cycleA ^ 3 = 1 ∧ cycleB ^ 3 = 1 ∧ (cycleA * cycleB) ^ 2 = 1 ∧
    cycleA ≠ 1 ∧ cycleB ≠ 1 ∧ cycleA * cycleB ≠ 1 := by
  decide

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem exists_conj_of_relations : ∀ u v : alternatingGroup (Fin 4), u ^ 3 = 1 → v ^ 3 = 1 →
    (u * v) ^ 2 = 1 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → ∃ s : Perm (Fin 4),
      s * (cycleA : Perm (Fin 4)) * s⁻¹ = u ∧ s * (cycleB : Perm (Fin 4)) * s⁻¹ = v := by
  decide

theorem eq_one_of_forall_commute : ∀ s : Perm (Fin 4),
    (∀ g : alternatingGroup (Fin 4), s * g = g * s) → s = 1 := by
  decide

theorem alternating_eq_one_of_forall_commute : ∀ g : alternatingGroup (Fin 4),
    (∀ h : alternatingGroup (Fin 4), g * h = h * g) → g = 1 := by
  decide

theorem alternating_involution_card :
    (Finset.univ.filter (fun g : alternatingGroup (Fin 4) => g ^ 2 = 1 ∧ g ≠ 1)).card = 3 := by
  decide

theorem odd_involution_card :
    (Finset.univ.filter (fun s : Perm (Fin 4) => Perm.sign s = -1 ∧ s ^ 2 = 1)).card = 6 := by
  decide

theorem alternating_involution_conj : ∀ g g' : alternatingGroup (Fin 4), g ^ 2 = 1 → g ≠ 1 →
    g' ^ 2 = 1 → g' ≠ 1 → ∃ c : alternatingGroup (Fin 4), c * g * c⁻¹ = g' := by
  decide

theorem odd_involution_conj : ∀ s s' : Perm (Fin 4), Perm.sign s = -1 → s ^ 2 = 1 →
    Perm.sign s' = -1 → s' ^ 2 = 1 → ∃ c : Perm (Fin 4), c * s * c⁻¹ = s' := by
  decide

theorem isSwap_iff (s : Perm (Fin 4)) : s.IsSwap ↔ (Perm.sign s = -1 ∧ s ^ 2 = 1) := by
  unfold Perm.IsSwap
  revert s
  decide

theorem dihedral_not_commutative : ∃ x y : DihedralGroup 4, x * y ≠ y * x := by
  decide

theorem nat_card_alternating_involutions :
    Nat.card {g : alternatingGroup (Fin 4) // g ^ 2 = 1 ∧ g ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact alternating_involution_card

theorem nat_card_odd_involutions :
    Nat.card {s : Perm (Fin 4) // Perm.sign s = -1 ∧ s ^ 2 = 1} = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact odd_involution_card

theorem conjNormal_surjective : Function.Surjective
    (MulAut.conjNormal : Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4))) := by
  intro β
  obtain ⟨hA3, hB3, hAB2, hA1, hB1, hAB1⟩ := cycle_relations
  have hne : ∀ g : alternatingGroup (Fin 4), g ≠ 1 → β g ≠ 1 := fun g hg h =>
    hg (β.injective (h.trans (map_one β).symm))
  obtain ⟨s, hsA, hsB⟩ := exists_conj_of_relations (β cycleA) (β cycleB)
    (by rw [← map_pow, hA3, map_one]) (by rw [← map_pow, hB3, map_one])
    (by rw [← map_mul, ← map_pow, hAB2, map_one]) (hne _ hA1) (hne _ hB1)
    (by rw [← map_mul]; exact hne _ hAB1)
  refine ⟨s, MulEquiv.ext fun g => ?_⟩
  have hA : MulAut.conjNormal s cycleA = β cycleA :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hsA)
  have hB : MulAut.conjNormal s cycleB = β cycleB :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hsB)
  obtain ⟨i, j, k, rfl⟩ := alternating_words g
  simp only [map_mul, map_pow, hA, hB]

theorem conjNormal_injective : Function.Injective
    (MulAut.conjNormal : Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4))) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  apply eq_one_of_forall_commute s
  intro g
  have h := congrArg (fun f : MulAut (alternatingGroup (Fin 4)) =>
    ((f g : alternatingGroup (Fin 4)) : Perm (Fin 4))) hs
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc s * (g : Perm (Fin 4)) = s * g * s⁻¹ * s := by group
    _ = g * s := by rw [h]

@[expose] noncomputable def autEquiv : Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
  MulEquiv.ofBijective MulAut.conjNormal ⟨conjNormal_injective, conjNormal_surjective⟩

theorem autEquiv_apply (s : Perm (Fin 4)) : autEquiv s = MulAut.conjNormal s := rfl

end SymmetricFour

section Orders

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {p : ℕ} [Fact p.Prime]

omit [Fintype H] in
theorem prime_not_dvd_twenty_four (hp5 : 5 ≤ p) : ¬ p ∣ 24 := by
  have hp : p.Prime := Fact.out
  intro h
  have h' : p ∣ 2 ^ 3 * 3 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

omit [Fintype H] [Fact p.Prime] in
theorem card_centralizer_eq (W : Subgroup H) [W.Normal] [IsCyclic W] {a : ℕ}
    (hWcard : Nat.card W = p ^ a)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin 4)) :
    Nat.card (Subgroup.centralizer (W : Set H)) = 12 * p ^ a := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (W.subgroupOf (Subgroup.centralizer (W : Set H))),
    Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CyclicInversion.le_centralizer_of_isCyclic W)).toEquiv, hWcard]
  norm_num [Nat.factorial]

omit [Fintype H] [Fact p.Prime] in
theorem card_eq (W : Subgroup H) [W.Normal] [IsCyclic W] {a : ℕ} (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin 4)) :
    Nat.card H = 24 * p ^ a := by
  rw [← (Subgroup.centralizer (W : Set H)).card_mul_index, card_centralizer_eq W hWcard ψ,
    hindex]
  ring

omit [Fintype H] in
theorem card_eq_sylow (W : Subgroup H) (hp5 : 5 ≤ p) {a : ℕ} (hWcard : Nat.card W = p ^ a)
    (hHcard : Nat.card H = 24 * p ^ a) :
    Nat.card W = p ^ (Nat.card H).factorization p := by
  have hp : p.Prime := Fact.out
  rw [hHcard, Nat.factorization_mul (by norm_num) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_twenty_four hp5), zero_add, hWcard]

end Orders

section Structure

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {p : ℕ} [Fact p.Prime]
  (W : Sylow p H) [IsCyclic (W : Subgroup H)] [(W : Subgroup H).Normal]
  (N : Subgroup (Subgroup.centralizer (W : Set H))) [N.Normal]

omit [Fintype H] [Fact p.Prime] [IsCyclic (W : Subgroup H)] in
theorem normalizer_eq_top : Subgroup.normalizer (W : Set H) = ⊤ :=
  Subgroup.normalizer_eq_top (H := (W : Subgroup H))

omit [Fintype H] [Fact p.Prime] [IsCyclic (W : Subgroup H)] in
theorem mem_normalizer (h : H) : h ∈ Subgroup.normalizer ((W : Subgroup H) : Set H) := by
  rw [Subgroup.normalizer_eq_top (H := (W : Subgroup H))]
  trivial

omit [Fintype H] [Fact p.Prime] [IsCyclic (W : Subgroup H)] in
theorem relIndex_eq_two (hindex : (Subgroup.centralizer (W : Set H)).index = 2) :
    (Subgroup.centralizer (W : Set H)).relIndex (Subgroup.normalizer (W : Set H)) = 2 := by
  rw [normalizer_eq_top W, Subgroup.relIndex_top_right, hindex]

omit [Fintype H] in
theorem inverts_of_not_mem (hp2 : p ≠ 2) (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2) (h : H)
    (hh : h ∉ Subgroup.centralizer (W : Set H)) (w : H) (hw : w ∈ (W : Subgroup H)) :
    h * w * h⁻¹ = w⁻¹ :=
  CyclicInversion.inverts_of_mem_normalizer (W : Subgroup H) hp2 a hWcard
    (relIndex_eq_two W hindex) h (mem_normalizer W h) hh w hw

omit [Fintype H] [Fact p.Prime] [IsCyclic (W : Subgroup H)] in
theorem complement_normal (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set H) ⧸ N)) :
    (N.map (Subgroup.centralizer (W : Set H)).subtype).Normal :=
  ⟨fun j hj h => CyclicInversion.map_complement_normalized W N hcop hpq h
    (mem_normalizer W h) j hj⟩

omit [Fintype H] [Fact p.Prime] [(W : Subgroup H).Normal] in
theorem mem_of_mem_centralizer_complement
    (hcomp : ((W : Subgroup H).subgroupOf (Subgroup.centralizer (W : Set H))).IsComplement' N)
    (φ : N.map (Subgroup.centralizer (W : Set H)).subtype ≃* alternatingGroup (Fin 4))
    (k : H) (hkK : k ∈ Subgroup.centralizer (W : Set H))
    (hkC : k ∈ Subgroup.centralizer
      ((N.map (Subgroup.centralizer (W : Set H)).subtype : Subgroup H) : Set H)) :
    k ∈ (W : Subgroup H) := by
  set kk : Subgroup.centralizer (W : Set H) := ⟨k, hkK⟩ with hkk
  set w := CyclicInversion.complementProjection W N hcomp kk with hw
  set n := (CyclicInversion.sylowInclusion W w)⁻¹ * kk with hn
  have hnN : n ∈ N := CyclicInversion.inv_inclusion_projection_mul_mem W N hcomp kk
  have hnJ : (n : H) ∈ N.map (Subgroup.centralizer (W : Set H)).subtype := ⟨n, hnN, rfl⟩
  have hnval : (n : H) = (w : H)⁻¹ * k := by
    rw [hn, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hcomm : ∀ j ∈ N.map (Subgroup.centralizer (W : Set H)).subtype, (n : H) * j = j * n := by
    intro j hj
    have hjK : j ∈ Subgroup.centralizer (W : Set H) := Subgroup.map_subtype_le N hj
    have h1 : (w : H) * j = j * w := Subgroup.mem_centralizer_iff.mp hjK w w.2
    have h2 : j * k = k * j := Subgroup.mem_centralizer_iff.mp hkC j hj
    have h1' : (w : H)⁻¹ * j = j * (w : H)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    rw [hnval, mul_assoc, ← h2, ← mul_assoc, h1', mul_assoc]
  have hφ : φ ⟨n, hnJ⟩ = 1 := by
    apply alternating_eq_one_of_forall_commute
    intro g
    obtain ⟨j, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm j j.2)
  have hn1 : (n : H) = 1 :=
    congrArg Subtype.val (φ.injective (hφ.trans (map_one φ).symm))
  rw [hnval] at hn1
  rw [← inv_mul_eq_one.mp hn1]
  exact w.2

omit [(W : Subgroup H).Normal] in
theorem centralizer_complement_le (hp2 : p ≠ 2) (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set H) ⧸ N))
    (hcomp : ((W : Subgroup H).subgroupOf (Subgroup.centralizer (W : Set H))).IsComplement' N)
    (φ : N.map (Subgroup.centralizer (W : Set H)).subtype ≃* alternatingGroup (Fin 4))
    (P : Sylow 2 H) (eP : (P : Subgroup H) ≃* DihedralGroup 4) :
    Subgroup.centralizer
        ((N.map (Subgroup.centralizer (W : Set H)).subtype : Subgroup H) : Set H) ≤
      Subgroup.centralizer (W : Set H) := by
  have hp : p.Prime := Fact.out
  intro h hhC
  by_contra hhK
  have hh2 : h ^ 2 ∈ (W : Subgroup H) :=
    mem_of_mem_centralizer_complement W N hcomp φ (h ^ 2)
      (Subgroup.sq_mem_of_index_two hindex h) (Subgroup.pow_mem _ hhC 2)
  have hm : (h ^ 2) ^ (p ^ a) = 1 := by
    have h1 := pow_card_eq_one' (G := (W : Subgroup H)) (x := ⟨h ^ 2, hh2⟩)
    rw [hWcard] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨s, hs⟩ := (hp.odd_of_ne_two hp2).pow (n := a)
  obtain ⟨z, hz⟩ : ∃ z, z = h ^ (p ^ a) := ⟨_, rfl⟩
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, mul_comm, pow_mul, hm]
  have hzK : z ∉ Subgroup.centralizer (W : Set H) := by
    intro hzK
    apply hhK
    have hsK : (h ^ 2) ^ s ∈ Subgroup.centralizer (W : Set H) :=
      Subgroup.pow_mem _ (Subgroup.sq_mem_of_index_two hindex h) s
    have heq : h = ((h ^ 2) ^ s)⁻¹ * z := by
      rw [hz, hs, pow_succ h (2 * s), pow_mul h 2 s, inv_mul_cancel_left]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsK) hzK
  have hz1 : z ≠ 1 := fun h1 => hzK (h1 ▸ Subgroup.one_mem _)
  have hzC : z ∈ Subgroup.centralizer
      ((N.map (Subgroup.centralizer (W : Set H)).subtype : Subgroup H) : Set H) := by
    rw [hz]
    exact Subgroup.pow_mem _ hhC _
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨P', hP'⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, hzord, pow_one] :
      Nat.card (Subgroup.zpowers z) = 2 ^ 1)).exists_le_sylow
  have hzP' : z ∈ (P' : Subgroup H) := hP' (Subgroup.mem_zpowers z)
  let e' : (P' : Subgroup H) ≃* DihedralGroup 4 := (Sylow.equiv P P').symm.trans eP
  have hP'card : Nat.card (P' : Subgroup H) = 8 := by
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
  have hKn : (Subgroup.centralizer (W : Set H)).Normal := Subgroup.normal_of_index_eq_two hindex
  have hrel : (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (H := Subgroup.centralizer (W : Set H))
      (K := (P' : Subgroup H))
    rw [hindex] at hdvd
    have hne : (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) ≠ 1 := fun h1 =>
      hzK (Subgroup.relIndex_eq_one.mp h1 hzP')
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hcardKP : Nat.card ((Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H)) =
      2 ^ 2 := by
    have h1 := Subgroup.card_mul_index
      ((Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H))
    change _ * (Subgroup.centralizer (W : Set H)).relIndex (P' : Subgroup H) = _ at h1
    rw [hrel, hP'card] at h1
    omega
  have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardKP
  have hJmem : ∀ x ∈ (P' : Subgroup H), x ∈ Subgroup.centralizer (W : Set H) →
      x ∈ N.map (Subgroup.centralizer (W : Set H)).subtype := by
    intro x hxP hxK
    rw [CyclicInversion.mem_map_complement_iff W N hcop hpq]
    refine ⟨hxK, ?_⟩
    have hdvd : orderOf x ∣ 2 ^ 3 := by
      have h1 := Subgroup.orderOf_dvd_natCard _ hxP
      rw [hP'card] at h1
      norm_num
      exact h1
    refine Nat.Coprime.coprime_dvd_right hdvd ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_)
    intro h8
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8))
  have hzcomm : ∀ x ∈ (P' : Subgroup H), x ∈ Subgroup.centralizer (W : Set H) → Commute x z :=
    fun x hxP hxK => Subgroup.mem_centralizer_iff.mp hzC x (hJmem x hxP hxK)
  have hKcomm : ∀ x ∈ (P' : Subgroup H), x ∈ Subgroup.centralizer (W : Set H) →
      ∀ y ∈ (P' : Subgroup H), y ∈ Subgroup.centralizer (W : Set H) → Commute x y := by
    intro x hxP hxK y hyP hyK
    have h1 := hab.is_comm.comm
      (⟨⟨x, hxP⟩, hxK⟩ : (Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H))
      ⟨⟨y, hyP⟩, hyK⟩
    exact congrArg (fun t : (Subgroup.centralizer (W : Set H)).subgroupOf (P' : Subgroup H) =>
      ((t : (P' : Subgroup H)) : H)) h1
  have hdecomp : ∀ x ∈ (P' : Subgroup H), ∃ y ∈ (P' : Subgroup H),
      y ∈ Subgroup.centralizer (W : Set H) ∧ (x = y ∨ x = y * z) := by
    intro x hxP
    by_cases hxK : x ∈ Subgroup.centralizer (W : Set H)
    · exact ⟨x, hxP, hxK, Or.inl rfl⟩
    · refine ⟨x * z, Subgroup.mul_mem _ hxP hzP',
        (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hxK hzK), Or.inr ?_⟩
      rw [mul_assoc, ← pow_two, hz2, mul_one]
  have hcommP : ∀ x ∈ (P' : Subgroup H), ∀ y ∈ (P' : Subgroup H), Commute x y := by
    intro x hxP y hyP
    obtain ⟨x', hx'P, hx'K, hx⟩ := hdecomp x hxP
    obtain ⟨y', hy'P, hy'K, hy⟩ := hdecomp y hyP
    have hxy := hKcomm x' hx'P hx'K y' hy'P hy'K
    have hxz := hzcomm x' hx'P hx'K
    have hyz := hzcomm y' hy'P hy'K
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy
    · exact hxy.mul_right hxz
    · exact hxy.mul_left hyz.symm
    · exact (hxy.mul_right hxz).mul_left (hyz.symm.mul_right (Commute.refl z))
  obtain ⟨x, y, hxy⟩ := dihedral_not_commutative
  apply hxy
  have h1 : e'.symm x * e'.symm y = e'.symm y * e'.symm x :=
    Subtype.ext (hcommP _ (e'.symm x).2 _ (e'.symm y).2).eq
  simpa using congrArg e' h1

end Structure

section Conjugation

variable {H : Type u} [Group H]

@[expose] noncomputable def conjugationPerm (J : Subgroup H) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin 4)) : H →* Perm (Fin 4) :=
  autEquiv.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal)

theorem conjugationPerm_apply_of_mem (J : Subgroup H) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin 4)) (j : J) :
    conjugationPerm J φ j = (φ j : Perm (Fin 4)) := by
  have h1 : MulAut.congr φ (MulAut.conjNormal (j : H)) = autEquiv (φ j : Perm (Fin 4)) := by
    rw [MulAut.conjNormal_val, autEquiv_apply, MulAut.conjNormal_val]
    refine MulEquiv.ext fun g => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  unfold conjugationPerm
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, h1, MulEquiv.symm_apply_apply]

theorem conjugationPerm_eq_one_iff (J : Subgroup H) [J.Normal]
    (φ : J ≃* alternatingGroup (Fin 4)) (h : H) :
    conjugationPerm J φ h = 1 ↔ h ∈ Subgroup.centralizer (J : Set H) := by
  unfold conjugationPerm
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 j hj
    have h2 := congrArg (fun f : MulAut J => ((f ⟨j, hj⟩ : J) : H)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc j * h = h * j * h⁻¹ * h := by rw [h2]
      _ = h * j := by group
  · intro h1
    refine MulEquiv.ext fun j => Subtype.ext ?_
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h1 j j.2, mul_inv_cancel_right]

end Conjugation

section Complement

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] {p : ℕ} [Fact p.Prime]
  (W : Sylow p H) [IsCyclic (W : Subgroup H)] [(W : Subgroup H).Normal]
  (N : Subgroup (Subgroup.centralizer (W : Set H))) [N.Normal]

omit [Fintype H] [Fact p.Prime] [IsCyclic (W : Subgroup H)] [(W : Subgroup H).Normal] in
theorem mem_complement_of_mem (E : Subgroup H) (hEcop : Nat.Coprime p (Nat.card E))
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set H) ⧸ N)) (e : H) (heE : e ∈ E)
    (heK : e ∈ Subgroup.centralizer (W : Set H)) :
    e ∈ N.map (Subgroup.centralizer (W : Set H)).subtype :=
  (CyclicInversion.mem_map_complement_iff W N hcop hpq e).mpr
    ⟨heK, Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard E heE) hEcop⟩

omit [Fintype H] [Fact p.Prime] [(W : Subgroup H).Normal] in
theorem complement_le (E : Subgroup H) (hE : (W : Subgroup H).IsComplement' E)
    (hEcop : Nat.Coprime p (Nat.card E)) (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set H) ⧸ N)) :
    N.map (Subgroup.centralizer (W : Set H)).subtype ≤ E := by
  intro j hj
  obtain ⟨⟨w, e⟩, hwe, -⟩ := Subgroup.IsComplement.existsUnique hE j
  have hwe' : (w : H) * e = j := hwe
  have hjK := Subgroup.map_subtype_le N hj
  have heK : (e : H) ∈ Subgroup.centralizer (W : Set H) := by
    have h1 : (e : H) = (w : H)⁻¹ * j := by rw [← hwe']; group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (CyclicInversion.sylow_le_centralizer W w.2)) hjK
  have heJ := mem_complement_of_mem W N E hEcop hcop hpq e e.2 heK
  have hwJ : (w : H) ∈ N.map (Subgroup.centralizer (W : Set H)).subtype := by
    have h1 : (w : H) = j * (e : H)⁻¹ := by rw [← hwe']; group
    rw [h1]
    exact Subgroup.mul_mem _ hj (Subgroup.inv_mem _ heJ)
  have hw1 : (w : H) = 1 := by
    have hmem : (w : H) ∈ (W : Subgroup H) ⊓ N.map (Subgroup.centralizer (W : Set H)).subtype :=
      ⟨w.2, hwJ⟩
    rw [CyclicInversion.inf_map_complement W N a hWcard hcop hpq] at hmem
    exact hmem
  rw [← hwe', hw1, one_mul]
  exact e.2

omit [(W : Subgroup H).Normal] in
theorem conjugationPerm_complement_injective (hp2 : p ≠ 2) (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set H) ⧸ N))
    (hcomp : ((W : Subgroup H).subgroupOf (Subgroup.centralizer (W : Set H))).IsComplement' N)
    [(N.map (Subgroup.centralizer (W : Set H)).subtype).Normal]
    (φ : N.map (Subgroup.centralizer (W : Set H)).subtype ≃* alternatingGroup (Fin 4))
    (P : Sylow 2 H) (eP : (P : Subgroup H) ≃* DihedralGroup 4)
    (E : Subgroup H) (hE : (W : Subgroup H).IsComplement' E) :
    Function.Injective
      ((conjugationPerm (N.map (Subgroup.centralizer (W : Set H)).subtype) φ).comp E.subtype) := by
  rw [injective_iff_map_eq_one]
  intro e he
  rw [MonoidHom.comp_apply, conjugationPerm_eq_one_iff] at he
  have heK := centralizer_complement_le W N hp2 a hWcard hindex hcop hpq hcomp φ P eP he
  have heW := mem_of_mem_centralizer_complement W N hcomp φ e heK he
  exact Subtype.ext (Subgroup.disjoint_def.mp hE.disjoint heW e.2)

end Complement

section Involutions

variable {H : Type u} [Group H] (W J E : Subgroup H)

omit W J E in
theorem sq_mul_of_inverts {w e : H} (hinv : e * w * e⁻¹ = w⁻¹) : (w * e) ^ 2 = e ^ 2 := by
  rw [pow_two, pow_two]
  calc w * e * (w * e) = w * (e * w * e⁻¹) * (e * e) := by group
    _ = e * e := by rw [hinv]; group

theorem eq_one_of_sq_eq_one (hodd : Odd (Nat.card W)) {w : H} (hw : w ∈ W) (hw2 : w ^ 2 = 1) :
    w = 1 := by
  have hcop : Nat.Coprime (orderOf w) (Nat.card W) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hw2) (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard W hw))

theorem outer_involution_iff (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJW : W ⊓ J = ⊥) (hEK : ∀ e ∈ E, e ∈ Subgroup.centralizer (W : Set H) → e ∈ J)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    {w e : H} (hw : w ∈ W) (he : e ∈ E) :
    (w * e ∉ J ∧ orderOf (w * e) = 2) ↔ (e ∉ J ∧ e ^ 2 = 1) := by
  by_cases heJ : e ∈ J
  · refine iff_of_false (fun ⟨hweJ, hord⟩ => hweJ ?_) (fun h => h.1 heJ)
    have hcomm : Commute w e := Subgroup.mem_centralizer_iff.mp (hJK heJ) w hw
    have hsq : (w * e) ^ 2 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hw2 : w ^ 2 = (e ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hcomm.mul_pow, hsq]
    have hw2J : w ^ 2 ∈ W ⊓ J := ⟨Subgroup.pow_mem _ hw 2, by
      rw [hw2]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ heJ 2)⟩
    rw [hJW, Subgroup.mem_bot] at hw2J
    rw [eq_one_of_sq_eq_one W hodd hw hw2J, one_mul]
    exact heJ
  · have heK : e ∉ Subgroup.centralizer (W : Set H) := fun h => heJ (hEK e he h)
    have hweK : w * e ∉ Subgroup.centralizer (W : Set H) := fun h => heK (by
      have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWK hw)) h
      rwa [inv_mul_cancel_left] at h1)
    have hweJ : w * e ∉ J := fun h => hweK (hJK h)
    rw [orderOf_eq_prime_iff, sq_mul_of_inverts (hinv e heK w hw)]
    exact ⟨fun h => ⟨heJ, h.2.1⟩, fun h => ⟨hweJ, h.2, fun h1 => hweK (h1 ▸ Subgroup.one_mem _)⟩⟩

theorem card_outer_involutions (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJW : W ⊓ J = ⊥) (hEK : ∀ e ∈ E, e ∈ Subgroup.centralizer (W : Set H) → e ∈ J)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hcompl : W.IsComplement' E) (σ : E ≃* Perm (Fin 4))
    (hσ : ∀ e : E, (e : H) ∈ J ↔ σ e ∈ alternatingGroup (Fin 4)) :
    Nat.card {u : H // u ∉ J ∧ orderOf u = 2} = Nat.card W * 6 := by
  let e0 : W × E ≃ H := Equiv.ofBijective (fun x : W × E => (x.1 : H) * x.2) hcompl
  have h1 : {x : W × E // (x.2 : H) ∉ J ∧ (x.2 : H) ^ 2 = 1} ≃
      {u : H // u ∉ J ∧ orderOf u = 2} :=
    e0.subtypeEquiv fun x =>
      (outer_involution_iff W J E hodd hWK hJK hJW hEK hinv x.1.2 x.2.2).symm
  have h2 : {x : W × E // (x.2 : H) ∉ J ∧ (x.2 : H) ^ 2 = 1} ≃
      W × {e : E // (e : H) ∉ J ∧ (e : H) ^ 2 = 1} :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h3 : {e : E // (e : H) ∉ J ∧ (e : H) ^ 2 = 1} ≃
      {s : Perm (Fin 4) // Perm.sign s = -1 ∧ s ^ 2 = 1} :=
    σ.toEquiv.subtypeEquiv fun e => by
      have hsign : (σ e ∉ alternatingGroup (Fin 4)) ↔ Perm.sign (σ e) = -1 := by
        rw [Perm.mem_alternatingGroup]
        rcases Int.units_eq_one_or (Perm.sign (σ e)) with h | h <;> rw [h] <;> decide
      have hsq : (e : H) ^ 2 = 1 ↔ σ e ^ 2 = 1 := by
        rw [← map_pow, MulEquiv.map_eq_one_iff, ← Subgroup.coe_pow, OneMemClass.coe_eq_one]
      rw [hσ e, hsign, hsq]
      rfl
  rw [← Nat.card_congr h1, Nat.card_congr h2, Nat.card_prod, Nat.card_congr h3,
    nat_card_odd_involutions]

omit W E in
theorem card_inner_involutions (φ : J ≃* alternatingGroup (Fin 4)) :
    Nat.card {u : H // u ∈ J ∧ orderOf u = 2} = 3 := by
  rw [← nat_card_alternating_involutions]
  refine Nat.card_congr
    { toFun := fun u => ⟨φ ⟨u.1, u.2.1⟩, ?_⟩
      invFun := fun g => ⟨(φ.symm g : H), (φ.symm g).2, ?_⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · rw [← orderOf_eq_prime_iff, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact u.2.2
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime_iff.mpr g.2

omit J E in
theorem exists_sq_eq (hodd : Odd (Nat.card W)) (w : H) (hw : w ∈ W) :
    ∃ y ∈ W, y ^ 2 = w := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨w ^ (k + 1), Subgroup.pow_mem _ hw _, ?_⟩
  have hpow : w ^ Nat.card W = 1 := by
    have h1 : (⟨w, hw⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  rw [← pow_mul, show (k + 1) * 2 = Nat.card W + 1 by omega, pow_succ, hpow, one_mul]

theorem isConj_involutions_iff (hodd : Odd (Nat.card W))
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJW : W ⊓ J = ⊥) (hEK : ∀ e ∈ E, e ∈ Subgroup.centralizer (W : Set H) → e ∈ J)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hWn : W.Normal) (hJn : J.Normal) (hcompl : W.IsComplement' E) (σ : E ≃* Perm (Fin 4))
    (hσ : ∀ e : E, (e : H) ∈ J ↔ σ e ∈ alternatingGroup (Fin 4))
    (φ : J ≃* alternatingGroup (Fin 4)) (u v : H) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v ↔ (u ∈ J ↔ v ∈ J) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    constructor
    · intro huJ
      rw [← hc]
      exact hJn.conj_mem u huJ c
    · intro hvJ
      have h1 : u = c⁻¹ * v * c⁻¹⁻¹ := by rw [← hc]; group
      rw [h1]
      exact hJn.conj_mem v hvJ c⁻¹
  intro huv
  by_cases huJ : u ∈ J
  · have hvJ := huv.mp huJ
    have hg1 : φ ⟨u, huJ⟩ ^ 2 = 1 ∧ φ ⟨u, huJ⟩ ≠ 1 := by
      rw [← orderOf_eq_prime_iff, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hu
    have hg2 : φ ⟨v, hvJ⟩ ^ 2 = 1 ∧ φ ⟨v, hvJ⟩ ≠ 1 := by
      rw [← orderOf_eq_prime_iff, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hv
    obtain ⟨c, hc⟩ := alternating_involution_conj _ _ hg1.1 hg1.2 hg2.1 hg2.2
    refine isConj_iff.mpr ⟨(φ.symm c : H), ?_⟩
    have h1 : φ.symm c * ⟨u, huJ⟩ * (φ.symm c)⁻¹ = ⟨v, hvJ⟩ :=
      φ.injective (by simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc])
    exact congrArg Subtype.val h1
  · have hvJ : v ∉ J := fun h => huJ (huv.mpr h)
    obtain ⟨⟨w₁, e₁⟩, hu1, -⟩ := Subgroup.IsComplement.existsUnique hcompl u
    obtain ⟨⟨w₂, e₂⟩, hv1, -⟩ := Subgroup.IsComplement.existsUnique hcompl v
    have hu1' : (w₁ : H) * e₁ = u := hu1
    have hv1' : (w₂ : H) * e₂ = v := hv1
    have hu' := (outer_involution_iff W J E hodd hWK hJK hJW hEK hinv w₁.2 e₁.2).mp
      (by rw [hu1']; exact ⟨huJ, hu⟩)
    have hv' := (outer_involution_iff W J E hodd hWK hJK hJW hEK hinv w₂.2 e₂.2).mp
      (by rw [hv1']; exact ⟨hvJ, hv⟩)
    have hodd' : ∀ e : E, (e : H) ∉ J → (e : H) ^ 2 = 1 →
        Perm.sign (σ e) = -1 ∧ σ e ^ 2 = 1 := by
      intro e heJ he2
      refine ⟨?_, ?_⟩
      · rw [hσ e, Perm.mem_alternatingGroup] at heJ
        rcases Int.units_eq_one_or (Perm.sign (σ e)) with h | h
        · exact absurd h heJ
        · exact h
      · rw [← map_pow, MulEquiv.map_eq_one_iff, ← OneMemClass.coe_eq_one, Subgroup.coe_pow]
        exact he2
    obtain ⟨c, hc⟩ := odd_involution_conj (σ ⟨e₁, e₁.2⟩) (σ ⟨e₂, e₂.2⟩)
      (hodd' _ hu'.1 hu'.2).1 (hodd' _ hu'.1 hu'.2).2 (hodd' _ hv'.1 hv'.2).1
      (hodd' _ hv'.1 hv'.2).2
    have hce : σ.symm c * ⟨e₁, e₁.2⟩ * (σ.symm c)⁻¹ = ⟨e₂, e₂.2⟩ :=
      σ.injective (by simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc])
    have hce' : ((σ.symm c : E) : H) * e₁ * ((σ.symm c : E) : H)⁻¹ = e₂ := congrArg Subtype.val hce
    set c' : H := ((σ.symm c : E) : H) with hc'
    have hw₃ : c' * w₁ * c'⁻¹ ∈ W := hWn.conj_mem w₁ w₁.2 c'
    have hconj1 : c' * u * c'⁻¹ = (c' * w₁ * c'⁻¹) * e₂ := by
      rw [← hu1', ← hce']
      group
    obtain ⟨y, hyW, hy⟩ := exists_sq_eq W hodd ((w₂ : H) * (c' * w₁ * c'⁻¹)⁻¹)
      (Subgroup.mul_mem _ w₂.2 (Subgroup.inv_mem _ hw₃))
    have he₂K : (e₂ : H) ∉ Subgroup.centralizer (W : Set H) := fun h => hv'.1 (hEK e₂ e₂.2 h)
    have hinv₂ : (e₂ : H) * y⁻¹ * (e₂ : H)⁻¹ = y := by
      rw [hinv e₂ he₂K y⁻¹ (Subgroup.inv_mem _ hyW), inv_inv]
    have hcomm : y * (c' * w₁ * c'⁻¹) = (c' * w₁ * c'⁻¹) * y :=
      Subgroup.mem_centralizer_iff.mp (hWK hw₃) y hyW
    refine isConj_iff.mpr ⟨y * c', ?_⟩
    calc y * c' * u * (y * c')⁻¹ = y * (c' * u * c'⁻¹) * y⁻¹ := by group
      _ = y * (c' * w₁ * c'⁻¹) * ((e₂ : H) * y⁻¹ * (e₂ : H)⁻¹) * e₂ := by
        rw [hconj1]
        group
      _ = y * (c' * w₁ * c'⁻¹) * y * e₂ := by rw [hinv₂]
      _ = y ^ 2 * (c' * w₁ * c'⁻¹) * e₂ := by
        rw [mul_assoc y, ← hcomm, pow_two, mul_assoc y y]
      _ = v := by rw [hy, inv_mul_cancel_right, hv1']

omit W J E in
theorem card_centralizer_mul_card_conj [Finite H] (u : H) :
    Nat.card (Subgroup.centralizer {u}) * Nat.card {v : H // IsConj v u} = Nat.card H := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct H) u)
  rw [MulAction.index_stabilizer] at h1
  have h2 : (MulAction.orbit (ConjAct H) u).ncard = Nat.card {v : H // IsConj v u} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => ConjAct.mem_orbit_conjAct)
  rw [h2] at h1
  rw [h1]
  exact Nat.card_congr ConjAct.toConjAct.toEquiv.symm

end Involutions

section Induction

open scoped Classical

variable {H : Type u} [Group H] [Fintype H]

@[expose] noncomputable def indexTwoSign (K : Subgroup H) (hK : K.index = 2) : H →* ℂˣ where
  toFun h := if h ∈ K then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a ∈ K <;> by_cases hb : b ∈ K <;>
      simp [ha, hb, Subgroup.mul_mem_iff_of_index_two hK]

omit [Fintype H] in
theorem indexTwoSign_apply (K : Subgroup H) (hK : K.index = 2) (h : H) :
    (indexTwoSign K hK h : ℂ) = if h ∈ K then 1 else -1 := by
  unfold indexTwoSign
  split_ifs <;> simp [*]

theorem card_filter_not_mem (K : Subgroup H) (hK : K.index = 2) :
    (Finset.univ.filter (fun c : H => c ∉ K)).card = Nat.card K := by
  have hK' : (Finset.univ.filter (fun c : H => c ∈ K)).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset H))
    (fun c => c ∈ K)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK'] at hsplit
  have hH := K.card_mul_index
  rw [hK] at hH
  omega

theorem inducedFunction_index_two (K : Subgroup H) (hK : K.index = 2) (f g : K → ℂ)
    (hf : ∀ (k : K) (c : H) (hmem : c⁻¹ * (k : H) * c ∈ K),
      f ⟨c⁻¹ * k * c, hmem⟩ = if c ∈ K then f k else g k) (h : H) :
    inducedFunction K f h = if hh : h ∈ K then f ⟨h, hh⟩ + g ⟨h, hh⟩ else 0 := by
  have hKn := Subgroup.normal_of_index_eq_two hK
  unfold inducedFunction
  by_cases hh : h ∈ K
  · rw [dite_eq_left hh]
    have hterm : ∀ c : H, (if hmem : c⁻¹ * h * c ∈ K then f ⟨c⁻¹ * h * c, hmem⟩ else 0) =
        if c ∈ K then f ⟨h, hh⟩ else g ⟨h, hh⟩ := by
      intro c
      have hmem : c⁻¹ * h * c ∈ K := by
        have h1 := hKn.conj_mem h hh c⁻¹
        rwa [inv_inv] at h1
      rw [dite_eq_left hmem]
      exact hf ⟨h, hh⟩ c hmem
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, card_filter_not_mem K hK]
    have hc1 : ((Finset.univ.filter fun c : H => c ∈ K).card : ℂ) = Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rw [hc1, ← mul_add, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'),
      one_mul]
  · rw [dite_eq_right hh, Finset.sum_eq_zero, mul_zero]
    intro c _
    rw [dite_eq_right]
    intro hmem
    apply hh
    have h1 := hKn.conj_mem _ hmem c
    simpa [mul_assoc] using h1

end Induction

section Characters

open scoped Classical

variable {H : Type u} [Group H] [Fintype H] (W J : Subgroup H)
  (π : Subgroup.centralizer (W : Set H) →* W)

omit [Fintype H] in
theorem projection_conj (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hJK : J ≤ Subgroup.centralizer (W : Set H)) (hJn : J.Normal)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hπW : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k)
    (hπJ : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1)
    (hdecomp : ∀ k : Subgroup.centralizer (W : Set H), ((π k : W) : H)⁻¹ * k ∈ J)
    (k : Subgroup.centralizer (W : Set H)) (c : H)
    (hmem : c⁻¹ * (k : H) * c ∈ Subgroup.centralizer (W : Set H)) :
    π ⟨c⁻¹ * k * c, hmem⟩ = if c ∈ Subgroup.centralizer (W : Set H) then π k else (π k)⁻¹ := by
  have hn := hdecomp k
  have hnc : c⁻¹ * (((π k : W) : H)⁻¹ * k) * c ∈ J := by
    have h1 := hJn.conj_mem _ hn c⁻¹
    rwa [inv_inv] at h1
  by_cases hc : c ∈ Subgroup.centralizer (W : Set H)
  · rw [ite_eq_left hc]
    have hcw : c⁻¹ * ((π k : W) : H) * c = (π k : W) := by
      have h1 : ((π k : W) : H) * c = c * (π k : W) :=
        Subgroup.mem_centralizer_iff.mp hc _ (π k).2
      rw [mul_assoc, h1, inv_mul_cancel_left]
    have heq : (⟨c⁻¹ * k * c, hmem⟩ : Subgroup.centralizer (W : Set H)) =
        ⟨(π k : W), hWK (π k).2⟩ * ⟨c⁻¹ * (((π k : W) : H)⁻¹ * k) * c, hJK hnc⟩ := by
      apply Subtype.ext
      change c⁻¹ * (k : H) * c = (π k : W) * (c⁻¹ * (((π k : W) : H)⁻¹ * k) * c)
      calc c⁻¹ * (k : H) * c =
          (c⁻¹ * ((π k : W) : H) * c) * (c⁻¹ * (((π k : W) : H)⁻¹ * k) * c) := by group
        _ = _ := by rw [hcw]
    rw [heq, map_mul, hπJ ⟨_, hJK hnc⟩ hnc, mul_one]
    exact Subtype.ext (hπW _ (π k).2)
  · rw [ite_eq_right hc]
    have hcinv : c⁻¹ ∉ Subgroup.centralizer (W : Set H) := fun h => hc (by
      simpa using Subgroup.inv_mem _ h)
    have hcw : c⁻¹ * ((π k : W) : H) * c = ((π k : W) : H)⁻¹ := by
      have h1 := hinv c⁻¹ hcinv _ (π k).2
      rwa [inv_inv] at h1
    have hwinv : ((π k : W) : H)⁻¹ ∈ W := Subgroup.inv_mem _ (π k).2
    have heq : (⟨c⁻¹ * k * c, hmem⟩ : Subgroup.centralizer (W : Set H)) =
        ⟨((π k : W) : H)⁻¹, hWK hwinv⟩ *
          ⟨c⁻¹ * (((π k : W) : H)⁻¹ * k) * c, hJK hnc⟩ := by
      apply Subtype.ext
      change c⁻¹ * (k : H) * c = ((π k : W) : H)⁻¹ * (c⁻¹ * (((π k : W) : H)⁻¹ * k) * c)
      calc c⁻¹ * (k : H) * c =
          (c⁻¹ * ((π k : W) : H) * c) * (c⁻¹ * (((π k : W) : H)⁻¹ * k) * c) := by group
        _ = _ := by rw [hcw]
    rw [heq, map_mul, hπJ ⟨_, hJK hnc⟩ hnc, mul_one]
    exact Subtype.ext (hπW _ hwinv)

theorem induced_linear_apply (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJn : J.Normal)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hπW : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k)
    (hπJ : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1)
    (hdecomp : ∀ k : Subgroup.centralizer (W : Set H), ((π k : W) : H)⁻¹ * k ∈ J)
    (lam : W →* ℂˣ) (h : H) :
    inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ)) h =
      if hh : h ∈ Subgroup.centralizer (W : Set H) then
        (lam (π ⟨h, hh⟩) : ℂ) + (lam (π ⟨h, hh⟩)⁻¹ : ℂ) else 0 :=
  inducedFunction_index_two _ hindex _ (fun k => (lam (π k)⁻¹ : ℂ)) (fun k c hmem => by
    rw [projection_conj W J π hWK hJK hJn hinv hπW hπJ hdecomp k c hmem]
    split_ifs <;> rfl) h

theorem column_apply (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJn : J.Normal)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hπW : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k)
    (hπJ : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1)
    (hdecomp : ∀ k : Subgroup.centralizer (W : Set H), ((π k : W) : H)⁻¹ * k ∈ J)
    (lam : W →* ℂˣ) (h : H) :
    inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => 1 - (lam (π k) : ℂ)) h =
      1 + (indexTwoSign _ hindex h : ℂ) -
        inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ)) h := by
  rw [inducedFunction_index_two _ hindex _ (fun k => 1 - (lam (π k)⁻¹ : ℂ)) (fun k c hmem => by
      rw [projection_conj W J π hWK hJK hJn hinv hπW hπJ hdecomp k c hmem]
      split_ifs <;> rfl) h,
    induced_linear_apply W J π hindex hWK hJK hJn hinv hπW hπJ hdecomp lam h,
    indexTwoSign_apply]
  by_cases hh : h ∈ Subgroup.centralizer (W : Set H)
  · rw [dite_eq_left hh, dite_eq_left hh, ite_eq_left hh]
    ring
  · rw [dite_eq_right hh, dite_eq_right hh, ite_eq_right hh]
    ring

theorem induced_linear_norm (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJn : J.Normal)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hπW : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k)
    (hπJ : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1)
    (hdecomp : ∀ k : Subgroup.centralizer (W : Set H), ((π k : W) : H)⁻¹ * k ∈ J)
    (lam : W →* ℂˣ) (hlam2 : lam ^ 2 ≠ 1) :
    characterPairing
        (inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ)))
        (inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ))) = 1 := by
  rw [characterPairing_inducedFunction_left _ _ _ (fun x c => inducedFunction_conjugate _ _ x c)]
  unfold characterPairing
  let square : Subgroup.centralizer (W : Set H) →* ℂ := (Units.coeHom ℂ).comp ((lam ^ 2).comp π)
  have hterm : ∀ k : Subgroup.centralizer (W : Set H), (lam (π k) : ℂ) *
      inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ))
        ((k⁻¹ : Subgroup.centralizer (W : Set H)) : H) = 1 + square k := by
    intro k
    rw [induced_linear_apply W J π hindex hWK hJK hJn hinv hπW hπJ hdecomp lam,
      dite_eq_left (k⁻¹).2]
    simp only [Subtype.coe_eta, map_inv, inv_inv, square, MonoidHom.comp_apply,
      Units.coeHom_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    rw [mul_add, mul_inv_cancel₀ (Units.ne_zero _), pow_two]
  have hne : square ≠ 1 := by
    intro h1
    apply hlam2
    ext w
    have h2 := congrArg (fun f : Subgroup.centralizer (W : Set H) →* ℂ => f ⟨w, hWK w.2⟩) h1
    have hπw : π ⟨w, hWK w.2⟩ = w := Subtype.ext (hπW _ w.2)
    simpa [square, hπw] using h2
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_hom_units_eq_zero _ hne,
    add_zero, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
    mul_one, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

theorem exists_label_induced_linear (basis : FiniteIrreducibleCharacterBasis H)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hWK : W ≤ Subgroup.centralizer (W : Set H)) (hJK : J ≤ Subgroup.centralizer (W : Set H))
    (hJn : J.Normal)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hπW : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k)
    (hπJ : ∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1)
    (hdecomp : ∀ k : Subgroup.centralizer (W : Set H), ((π k : W) : H)⁻¹ * k ∈ J)
    (lam : W →* ℂˣ) (hlam2 : lam ^ 2 ≠ 1) :
    ∃ θ, (basis.representation θ).character =
      inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ)) := by
  let linear : Subgroup.centralizer (W : Set H) →* ℂ := (Units.coeHom ℂ).comp (lam.comp π)
  let data := coinducedFiniteComplexRepresentation (Subgroup.centralizer (W : Set H))
    ({ vector := ℂ, representation := scalarHomRepresentation linear } :
      FiniteComplexRepresentation (Subgroup.centralizer (W : Set H)))
  have hchar : data.character =
      inducedFunction (Subgroup.centralizer (W : Set H)) (fun k => (lam (π k) : ℂ)) := by
    funext g
    rw [coinducedFiniteComplexRepresentation_character]
    have hlin : ({ vector := ℂ, representation := scalarHomRepresentation linear } :
        FiniteComplexRepresentation (Subgroup.centralizer (W : Set H))).character = linear :=
      scalarHomRepresentation_character linear
    rw [hlin]
    rfl
  obtain ⟨θ, hθ⟩ := character_norm_one_basis_character basis data (by
    rw [hchar]
    exact induced_linear_norm W J π hindex hWK hJK hJn hinv hπW hπJ hdecomp lam hlam2)
  exact ⟨θ, hθ.trans hchar⟩

end Characters

section Sums

open scoped Classical

variable {H : Type u} [Group H] [Fintype H]

omit [Group H] in
theorem card_filter_eq_nat_card (P : H → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.card {u // P u} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem involution_average (J : Subgroup H) (χ : H → ℂ)
    (hχ : ∀ x c : H, χ (c * x * c⁻¹) = χ x) (t x : H)
    (hconjt : ∀ u, u ∈ J → orderOf u = 2 → IsConj u t)
    (hconjx : ∀ u, u ∉ J → orderOf u = 2 → IsConj u x) (m : ℕ) (hm : 0 < m)
    (hinner : Nat.card {u : H // u ∈ J ∧ orderOf u = 2} = 3)
    (houter : Nat.card {u : H // u ∉ J ∧ orderOf u = 2} = 6 * m)
    (hHcard : Nat.card H = 24 * m) :
    (Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), χ u =
      χ t / (8 * m) + χ x / 4 := by
  have hconst : ∀ u c, IsConj u c → χ u = χ c := by
    intro u c huc
    obtain ⟨g, hg⟩ := isConj_iff.mp huc
    rw [← hg, hχ]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u => u ∈ J)]
  have hcard1 : ((Finset.univ.filter (fun u : H => orderOf u = 2)).filter
      (fun u => u ∈ J)).card = 3 := by
    rw [Finset.filter_filter, card_filter_eq_nat_card, ← hinner]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
  have hcard2 : ((Finset.univ.filter (fun u : H => orderOf u = 2)).filter
      (fun u => u ∉ J)).card = 6 * m := by
    rw [Finset.filter_filter, card_filter_eq_nat_card, ← houter]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
  rw [Finset.sum_congr rfl fun u hu => hconst u t (by
      rw [Finset.mem_filter, Finset.mem_filter] at hu
      exact hconjt u hu.2 hu.1.2),
    Finset.sum_congr rfl fun u hu => hconst u x (by
      rw [Finset.mem_filter, Finset.mem_filter] at hu
      exact hconjx u hu.2 hu.1.2),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard1, hcard2, hHcard]
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp
  ring

theorem sum_pairing_three (basis : FiniteIrreducibleCharacterBasis H) (a b c : basis.index)
    (T : H → ℂ)
    (hT : ∀ h, T h = (basis.representation a).character h + (basis.representation b).character h -
      (basis.representation c).character h)
    (F : basis.index → ℂ) :
    ∑ α, characterPairing T (basis.representation α).character * F α = F a + F b - F c := by
  have hpair : ∀ β α : basis.index, characterPairing (basis.representation β).character
      (basis.representation α).character = if β = α then 1 else 0 := by
    intro β α
    rw [characterPairing_irreducible _ _ (basis.irreducible β) (basis.irreducible α)]
    by_cases h : β = α
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right (fun h' => h (basis.distinct h')), ite_eq_right h]
  have hTα : ∀ α, characterPairing T (basis.representation α).character =
      (if a = α then 1 else 0) + (if b = α then 1 else 0) - (if c = α then 1 else 0) := by
    intro α
    rw [← hpair a α, ← hpair b α, ← hpair c α]
    unfold characterPairing
    rw [← mul_add, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hT]
    ring
  simp only [hTα, add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Sums

end CyclicSymmetricFour

open CyclicSymmetricFour

open scoped Classical in
theorem cyclic_prime_power_A4_centralizer_inversion_normalizer_sign_S4_column_sum
    {H : Type u} [Group H] [Fintype H] (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ℕ)
    (W : Subgroup H) [W.Normal] [IsCyclic W] (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hquot : Nonempty (Subgroup.centralizer (W : Set H) ⧸
      W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃* alternatingGroup (Fin 4)))
    (hdihedral : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4))
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ (J : Subgroup H) (π : Subgroup.centralizer (W : Set H) →* W) (E : Subgroup H)
      (σ : E ≃* Equiv.Perm (Fin 4)),
      J ≤ Subgroup.centralizer (W : Set H) ∧
      (J.subgroupOf (Subgroup.centralizer (W : Set H))).Characteristic ∧
      Nat.Coprime p (Nat.card J) ∧
      W ⊔ J = Subgroup.centralizer (W : Set H) ∧ W ⊓ J = ⊥ ∧
      (∀ w ∈ W, ∀ j ∈ J, w * j = j * w) ∧
      Nonempty (J ≃* alternatingGroup (Fin 4)) ∧ J.Normal ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ W → (π k : H) = k) ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1) ∧
      J ≤ E ∧ W ⊔ E = ⊤ ∧ W ⊓ E = ⊥ ∧
      (∀ e : E, (e : H) ∈ J ↔ σ e ∈ alternatingGroup (Fin 4)) ∧
      (∀ e : E, ∀ w ∈ W,
        (e : H) * w * (e : H)⁻¹ = w ^ ((Equiv.Perm.sign (σ e) : ℤˣ) : ℤ)) ∧
      Nat.card (Subgroup.centralizer (W : Set H)) = 12 * p ^ a ∧ Nat.card H = 24 * p ^ a ∧
      Nat.card {u : H // u ∈ J ∧ orderOf u = 2} = 3 ∧
      Nat.card {u : H // u ∉ J ∧ orderOf u = 2} = 6 * p ^ a ∧
      (∀ u v : H, orderOf u = 2 → orderOf v = 2 → (IsConj u v ↔ (u ∈ J ↔ v ∈ J))) ∧
      (∀ u ∈ J, orderOf u = 2 → Nat.card (Subgroup.centralizer {u}) = 8 * p ^ a) ∧
      (∀ u : H, u ∉ J → orderOf u = 2 → Nat.card (Subgroup.centralizer {u}) = 4) ∧
      ∀ lam : W →* ℂˣ, orderOf lam = p →
        ∃ θε θμ : basis.index,
          (∀ w ∈ W, ∀ e : E, (basis.representation θε).character (w * e) =
            (((Equiv.Perm.sign (σ e) : ℤˣ) : ℤ) : ℂ)) ∧
          Module.finrank ℂ (basis.representation θμ).vector = 2 ∧
          (∀ h : H, inducedFunction (Subgroup.centralizer (W : Set H))
              (fun k => 1 - (lam (π k) : ℂ)) h =
            1 + (basis.representation θε).character h - (basis.representation θμ).character h) ∧
          (∀ t ∈ J, orderOf t = 2 → (basis.representation θμ).character t = 2) ∧
          (∀ x : E, (σ x).IsSwap → (basis.representation θμ).character x = 0) ∧
          ∀ t ∈ J, orderOf t = 2 → ∀ x : E, (σ x).IsSwap →
            (∀ α : basis.index, (Nat.card H : ℂ)⁻¹ *
                ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u =
              (basis.representation α).character t / (8 * (p : ℂ) ^ a) +
                (basis.representation α).character x / 4) ∧
            ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 = 1 / 8 ∧
            (Nat.card H : ℂ) * ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 = 3 * (p : ℂ) ^ a := by
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ⟩ := hquot
  obtain ⟨P, ⟨eP⟩⟩ := hdihedral
  have hKcard := card_centralizer_eq W hWcard ψ
  have hHcard := card_eq W hWcard hindex ψ
  have hsyl := card_eq_sylow W hp hWcard hHcard
  obtain ⟨S, rfl⟩ : ∃ S : Sylow p H, (S : Subgroup H) = W := ⟨Sylow.ofCard W hsyl, rfl⟩
  have hcop24 : Nat.Coprime p 24 :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr (prime_not_dvd_twenty_four hp)
  obtain ⟨N, hNn, hcop, hpq⟩ := CyclicInversion.exists_centralizer_normal_complement S
  have hcomp := CyclicInversion.isComplement'_complement S N a hWcard hcop hpq
  have hJn : (N.map (Subgroup.centralizer (S : Set H)).subtype).Normal :=
    complement_normal S N hcop hpq
  have hWK : (S : Subgroup H) ≤ Subgroup.centralizer ((S : Subgroup H) : Set H) :=
    CyclicInversion.le_centralizer_of_isCyclic _
  have hJK : N.map (Subgroup.centralizer (S : Set H)).subtype ≤
      Subgroup.centralizer ((S : Subgroup H) : Set H) := Subgroup.map_subtype_le N
  have hJW := CyclicInversion.inf_map_complement S N a hWcard hcop hpq
  have hinv : ∀ h, h ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) →
      ∀ w ∈ (S : Subgroup H), h * w * h⁻¹ = w⁻¹ := inverts_of_not_mem S hp2 a hWcard hindex
  have hJmem : ∀ k : Subgroup.centralizer (S : Set H),
      (k : H) ∈ N.map (Subgroup.centralizer (S : Set H)).subtype → k ∈ N := by
    rintro k ⟨n, hn, hnk⟩
    rwa [← (Subtype.ext hnk : n = k)]
  let φ : N.map (Subgroup.centralizer (S : Set H)).subtype ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective N _ (Subgroup.subtype_injective _)).symm.trans
      (hcomp.symm.QuotientMulEquiv.symm.trans ψ)
  have hWindex : (S : Subgroup H).index = 24 := by
    have h1 := (S : Subgroup H).card_mul_index
    rw [hWcard, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hpp.pos a) (by rw [h1]; ring)
  obtain ⟨E, hE⟩ := Subgroup.exists_right_complement'_of_coprime (N := (S : Subgroup H))
    (by rw [hWcard, hWindex]; exact Nat.Coprime.pow_left a hcop24)
  have hEcard : Nat.card E = 24 := by
    have h1 := hE.card_mul_card
    rw [hWcard, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hpp.pos a) (by rw [h1]; ring)
  have hEcop : Nat.Coprime p (Nat.card E) := by
    rw [hEcard]
    exact hcop24
  have hJE := complement_le S N E hE hEcop a hWcard hcop hpq
  have hEK : ∀ e ∈ E, e ∈ Subgroup.centralizer ((S : Subgroup H) : Set H) →
      e ∈ N.map (Subgroup.centralizer (S : Set H)).subtype :=
    fun e he heK => mem_complement_of_mem S N E hEcop hcop hpq e he heK
  have hinj := conjugationPerm_complement_injective S N hp2 a hWcard hindex hcop hpq hcomp φ P eP
    E hE
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [hEcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide)
  let σ : E ≃* Equiv.Perm (Fin 4) := MulEquiv.ofBijective _ hbij
  have hσapply : ∀ e : E,
      σ e = conjugationPerm (N.map (Subgroup.centralizer (S : Set H)).subtype) φ e :=
    fun e => rfl
  have hσJ : ∀ e : E, (e : H) ∈ N.map (Subgroup.centralizer (S : Set H)).subtype ↔
      σ e ∈ alternatingGroup (Fin 4) := by
    intro e
    constructor
    · intro he
      have h1 : σ e = (φ ⟨e, he⟩ : Equiv.Perm (Fin 4)) :=
        conjugationPerm_apply_of_mem _ φ ⟨e, he⟩
      rw [h1]
      exact (φ ⟨e, he⟩).2
    · intro hs
      obtain ⟨j, hj⟩ := φ.surjective ⟨σ e, hs⟩
      have h1 : σ ⟨j, hJE j.2⟩ = (φ j : Equiv.Perm (Fin 4)) := conjugationPerm_apply_of_mem _ φ j
      have h2 : σ ⟨j, hJE j.2⟩ = σ e := by
        rw [h1, hj]
      rw [← σ.injective h2]
      exact j.2
  have hsign : ∀ e : E, ∀ w ∈ (S : Subgroup H),
      (e : H) * w * (e : H)⁻¹ = w ^ ((Equiv.Perm.sign (σ e) : ℤˣ) : ℤ) := by
    intro e w hw
    by_cases heJ : (e : H) ∈ N.map (Subgroup.centralizer (S : Set H)).subtype
    · have hs : Equiv.Perm.sign (σ e) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp ((hσJ e).mp heJ)
      rw [hs, Units.val_one, zpow_one]
      have hc : w * e = e * w := Subgroup.mem_centralizer_iff.mp (hJK heJ) w hw
      rw [← hc, mul_inv_cancel_right]
    · have hs : Equiv.Perm.sign (σ e) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (σ e)) with h | h
        · exact absurd ((hσJ e).mpr (Equiv.Perm.mem_alternatingGroup.mpr h)) heJ
        · exact h
      rw [hs, Units.val_neg, Units.val_one, zpow_neg, zpow_one]
      exact hinv e (fun h => heJ (hEK e e.2 h)) w hw
  have hodd : Odd (Nat.card (S : Subgroup H)) := by
    rw [hWcard]
    exact (hpp.odd_of_ne_two hp2).pow
  have hinner := card_inner_involutions (N.map (Subgroup.centralizer (S : Set H)).subtype) φ
  have houter : Nat.card {u : H // u ∉ N.map (Subgroup.centralizer (S : Set H)).subtype ∧
      orderOf u = 2} = 6 * p ^ a := by
    rw [card_outer_involutions (S : Subgroup H) _ E hodd hWK hJK hJW hEK hinv hE σ hσJ, hWcard,
      mul_comm]
  have hclass := isConj_involutions_iff (S : Subgroup H) _ E hodd hWK hJK hJW hEK hinv
    inferInstance hJn hE σ hσJ φ
  have hconj_order : ∀ u v : H, IsConj v u → orderOf v = orderOf u := by
    intro u v hvu
    obtain ⟨c, hc⟩ := isConj_iff.mp hvu
    rw [← hc]
    exact ((MulAut.conj c).orderOf_eq v).symm
  have hcentJ : ∀ u ∈ N.map (Subgroup.centralizer (S : Set H)).subtype, orderOf u = 2 →
      Nat.card (Subgroup.centralizer {u}) = 8 * p ^ a := by
    intro u huJ hu
    have h1 := card_centralizer_mul_card_conj u
    have h2 : Nat.card {v : H // IsConj v u} = 3 := by
      rw [← hinner]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun hvu => ?_, fun hv => ?_⟩)
      · have hv : orderOf v = 2 := (hconj_order u v hvu).trans hu
        exact ⟨((hclass v u hv hu).mp hvu).mpr huJ, hv⟩
      · exact (hclass v u hv.2 hu).mpr (iff_of_true hv.1 huJ)
    rw [h2, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) (by rw [h1]; ring)
  have hcentout : ∀ u : H, u ∉ N.map (Subgroup.centralizer (S : Set H)).subtype →
      orderOf u = 2 → Nat.card (Subgroup.centralizer {u}) = 4 := by
    intro u huJ hu
    have h1 := card_centralizer_mul_card_conj u
    have h2 : Nat.card {v : H // IsConj v u} = 6 * p ^ a := by
      rw [← houter]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun hvu => ?_, fun hv => ?_⟩)
      · have hv : orderOf v = 2 := (hconj_order u v hvu).trans hu
        exact ⟨fun hvJ => huJ (((hclass v u hv hu).mp hvu).mp hvJ), hv⟩
      · exact (hclass v u hv.2 hu).mpr (iff_of_false hv.1 huJ)
    rw [h2, hHcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 6 * p ^ a) (by rw [h1]; ring)
  refine ⟨N.map (Subgroup.centralizer (S : Set H)).subtype,
    CyclicInversion.complementProjection S N hcomp, E, σ, hJK,
    CyclicInversion.map_complement_characteristic S N hcop hpq,
    by rw [CyclicInversion.card_map_complement]; exact hcop,
    CyclicInversion.sup_map_complement S N hcomp, hJW,
    fun w hw j hj => Subgroup.mem_centralizer_iff.mp (hJK hj) w hw, ⟨φ⟩, hJn,
    fun k hk => CyclicInversion.complementProjection_of_mem S N hcomp k hk,
    fun k hk => CyclicInversion.complementProjection_of_mem_complement S N hcomp k (hJmem k hk),
    hJE, hE.sup_eq_top, disjoint_iff.mp hE.disjoint, hσJ, hsign, hKcard, hHcard, hinner, houter,
    hclass, hcentJ, hcentout, ?_⟩
  intro lam hlam
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hlam] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h1)
  have hπW : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H), (k : H) ∈ (S : Subgroup H) →
      (CyclicInversion.complementProjection S N hcomp k : H) = k :=
    fun k hk => CyclicInversion.complementProjection_of_mem S N hcomp k hk
  have hπJ : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H),
      (k : H) ∈ N.map (Subgroup.centralizer (S : Set H)).subtype →
        CyclicInversion.complementProjection S N hcomp k = 1 :=
    fun k hk => CyclicInversion.complementProjection_of_mem_complement S N hcomp k (hJmem k hk)
  have hdecomp : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H),
      ((CyclicInversion.complementProjection S N hcomp k : (S : Subgroup H)) : H)⁻¹ * k ∈
        N.map (Subgroup.centralizer (S : Set H)).subtype :=
    fun k => ⟨_, CyclicInversion.inv_inclusion_projection_mul_mem S N hcomp k, rfl⟩
  obtain ⟨θμ, hθμ⟩ := exists_label_induced_linear (S : Subgroup H) _
    (CyclicInversion.complementProjection S N hcomp) basis hindex hWK hJK hJn hinv hπW hπJ hdecomp
    lam hlam2
  obtain ⟨θε, hθε⟩ := CyclicInversion.exists_label_of_linear basis (indexTwoSign _ hindex)
  have hT := column_apply (S : Subgroup H) _ (CyclicInversion.complementProjection S N hcomp)
    hindex hWK hJK hJn hinv hπW hπJ hdecomp lam
  have hμ := induced_linear_apply (S : Subgroup H) _
    (CyclicInversion.complementProjection S N hcomp) hindex hWK hJK hJn hinv hπW hπJ hdecomp lam
  have hμt : ∀ t ∈ N.map (Subgroup.centralizer (S : Set H)).subtype,
      (basis.representation θμ).character t = 2 := by
    intro t ht
    rw [hθμ, hμ t, dite_eq_left (hJK ht), hπJ ⟨t, hJK ht⟩ ht, inv_one, map_one, Units.val_one]
    norm_num
  have hμx : ∀ x : H, x ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) →
      (basis.representation θμ).character x = 0 := by
    intro x hx
    rw [hθμ, hμ x, dite_eq_right hx]
  have hε : ∀ h : H, (basis.representation θε).character h =
      if h ∈ Subgroup.centralizer ((S : Subgroup H) : Set H) then 1 else -1 := by
    intro h
    rw [hθε h, indexTwoSign_apply]
  have hdeg : ∀ θ : basis.index, (basis.representation θ).character 1 =
      Module.finrank ℂ (basis.representation θ).vector := by
    intro θ
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have hμ1 : (basis.representation θμ).character 1 = 2 := hμt 1 (Subgroup.one_mem _)
  have hε1 : (basis.representation θε).character 1 = 1 := by
    rw [hε, ite_eq_left (Subgroup.one_mem _)]
  have hp1 : (basis.representation principal).character 1 = 1 := by
    rw [hprincipal, Pi.one_apply]
  have hTfun : ∀ h : H, inducedFunction (Subgroup.centralizer ((S : Subgroup H) : Set H))
      (fun k => 1 - (lam (CyclicInversion.complementProjection S N hcomp k) : ℂ)) h =
        (basis.representation principal).character h + (basis.representation θε).character h -
          (basis.representation θμ).character h := by
    intro h
    rw [hT h, hθε h, hθμ, hprincipal, Pi.one_apply]
  refine ⟨θε, θμ, ?_, ?_, fun h => by rw [hTfun h, hprincipal, Pi.one_apply],
    fun t ht _ => hμt t ht, fun x hx => hμx x ?_, ?_⟩
  · intro w hw e
    rw [hε]
    have hwK := hWK hw
    by_cases heJ : (e : H) ∈ N.map (Subgroup.centralizer (S : Set H)).subtype
    · have hs : Equiv.Perm.sign (σ e) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp ((hσJ e).mp heJ)
      rw [hs, ite_eq_left (Subgroup.mul_mem _ hwK (hJK heJ))]
      simp
    · have hs : Equiv.Perm.sign (σ e) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (σ e)) with h | h
        · exact absurd ((hσJ e).mpr (Equiv.Perm.mem_alternatingGroup.mpr h)) heJ
        · exact h
      have hweK : w * e ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) := fun h => heJ (hEK e
        e.2 (by
          have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hwK) h
          rwa [inv_mul_cancel_left] at h1))
      rw [hs, ite_eq_right hweK]
      simp
  · have h1 := hdeg θμ
    rw [hμ1] at h1
    exact_mod_cast h1.symm
  · have hsx := (isSwap_iff (σ x)).mp hx
    intro hxK
    have hs := (hσJ x).mp (hEK x x.2 hxK)
    rw [Equiv.Perm.mem_alternatingGroup, hsx.1] at hs
    exact absurd hs (by decide)
  intro t ht htord x hx
  have hsx := (isSwap_iff (σ x)).mp hx
  have hxJ : (x : H) ∉ N.map (Subgroup.centralizer (S : Set H)).subtype := by
    intro h
    have hs := (hσJ x).mp h
    rw [Equiv.Perm.mem_alternatingGroup, hsx.1] at hs
    exact absurd hs (by decide)
  have hxK : (x : H) ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) :=
    fun h => hxJ (hEK x x.2 h)
  have hx2 : orderOf (x : H) = 2 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, fun h1 => hxJ (h1 ▸ Subgroup.one_mem _)⟩
    have h1 : x ^ 2 = 1 := σ.injective (by rw [map_pow, hsx.2, map_one])
    exact congrArg Subtype.val h1
  have hconjt : ∀ u, u ∈ N.map (Subgroup.centralizer (S : Set H)).subtype → orderOf u = 2 →
      IsConj u t := fun u hu huo => (hclass u t huo htord).mpr (iff_of_true hu ht)
  have hconjx : ∀ u, u ∉ N.map (Subgroup.centralizer (S : Set H)).subtype → orderOf u = 2 →
      IsConj u x := fun u hu huo => (hclass u x huo hx2).mpr (iff_of_false hu hxJ)
  have havg : ∀ α : basis.index, (Nat.card H : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), (basis.representation α).character u =
        (basis.representation α).character t / (8 * (p : ℂ) ^ a) +
          (basis.representation α).character x / 4 := by
    intro α
    rw [involution_average _ (basis.representation α).character
      (fun g c => Representation.char_conj _ g c) t x hconjt hconjx (p ^ a) (pow_pos hpp.pos a)
      hinner houter hHcard]
    push_cast
    ring
  have hsum : ∑ α : basis.index, characterPairing
      (inducedFunction (Subgroup.centralizer ((S : Subgroup H) : Set H))
        (fun k => 1 - (lam (CyclicInversion.complementProjection S N hcomp k) : ℂ)))
        (basis.representation α).character *
      ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
        (basis.representation α).character u) ^ 2 /
      (basis.representation α).character 1 = 1 / 8 := by
    simp_rw [mul_div_assoc]
    rw [sum_pairing_three basis principal θε θμ _ hTfun, havg, havg, havg, hprincipal]
    simp only [Pi.one_apply]
    rw [hε t, ite_eq_left (hJK ht), hε x, ite_eq_right hxK, hμt t ht, hμx x hxK, hε1, hμ1]
    have hpa : (p : ℂ) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hpp.ne_zero)
    field_simp
    ring
  refine ⟨havg, hsum, ?_⟩
  rw [hsum, hHcard]
  push_cast
  ring

end CFSG.Semidihedral.Principal
