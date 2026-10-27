module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic
public import CFSG.ClassicalInvolution.Asc77.AscSixInv

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem uniqueInvolution_comm {R : Subgroup G} {z : G} (hz : IsUniqueInvolution R z) {r : G}
    (hr : r ∈ R) : r * z = z * r := by
  have h1 : r * z * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hz.mem) (R.inv_mem hr)
  have h2 : (r * z * r⁻¹) * (r * z * r⁻¹) = 1 := by
    calc (r * z * r⁻¹) * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    have : r⁻¹ * (r * z * r⁻¹) * r = r⁻¹ * 1 * r := by rw [h]
    simpa [mul_assoc] using this
  · calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]

theorem natCard_conjSub (g : G) (A : Subgroup G) : Nat.card ↥(conjSub g A) = Nat.card ↥A :=
  (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

theorem isCyclic_conjSub (g : G) {A : Subgroup G} (h : IsCyclic ↥A) :
    IsCyclic ↥(conjSub g A) := by
  let e := Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact (MulEquiv.isCyclic e).mp h

theorem cyclic_comm {A : Subgroup G} (h : IsCyclic ↥A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hx' : x = (g : G) ^ m := by simpa using (congrArg Subtype.val hm).symm
  have hy' : y = (g : G) ^ n := by simpa using (congrArg Subtype.val hn).symm
  rw [hx', hy']
  exact (Commute.zpow_zpow_self (g : G) m n).eq

theorem isPGroup_of_isQuatSub {R : Subgroup G} (hR : IsQuatSub R) : IsPGroup 2 ↥R := by
  obtain ⟨k, -, hk⟩ := hR.natCard_eq
  exact IsPGroup.of_card (n := k + 2) hk

theorem orderOf_eq_two_pow_of_isQuatSub {R : Subgroup G} (hR : IsQuatSub R) {g : G} (hg : g ∈ R) :
    ∃ j : ℕ, orderOf g = 2 ^ j := by
  have := (IsPGroup.iff_orderOf (p := 2) (G := ↥R)).mp (isPGroup_of_isQuatSub hR) ⟨g, hg⟩
  simpa [Subgroup.orderOf_mk] using this

theorem natCard_eq_eight_of_not_sixteen_le {R : Subgroup G} (hR : IsQuatSub R)
    (h : ¬ 16 ≤ Nat.card R) : Nat.card R = 8 := by
  obtain ⟨k, hk, hkc⟩ := hR.natCard_eq
  have hk1 : k = 1 := by
    by_contra hk1
    have h3 : 2 ^ 4 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hk1
  simpa using hkc

theorem four_le_natCard_of_index_two {R C : Subgroup G} (hR : IsQuatSub R)
    (hcard : Nat.card R = 2 * Nat.card C) : 4 ≤ Nat.card C := by
  have := hR.eight_le
  omega

variable [Finite G]

theorem inv_mul_mem_of_index_two {R C : Subgroup G} (hCR : C ≤ R)
    (hcard : Nat.card R = 2 * Nat.card C) {g h : G} (hg : g ∈ R) (hh : h ∈ R) (hgC : g ∉ C)
    (hhC : h ∉ C) : g⁻¹ * h ∈ C := by
  have hrel : C.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card C R
    rw [inf_eq_left.mpr hCR, hcard] at h1
    have hU0 : 0 < Nat.card C := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  have hidx : (C.subgroupOf R).index = 2 := hrel
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have key : ∀ x : G, ∀ hx : x ∈ R, x ∉ C → (⟨x, hx⟩ : ↥R) * a ∈ C.subgroupOf R := by
    intro x hx hxC
    have := ha ⟨x, hx⟩
    have hn : (⟨x, hx⟩ : ↥R) ∉ C.subgroupOf R := hxC
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 hn
  have hg' : g⁻¹ ∈ R := R.inv_mem hg
  have hh' : h⁻¹ ∈ R := R.inv_mem hh
  have h1 := key g⁻¹ hg' (fun hc => hgC (by simpa using C.inv_mem hc))
  have h2 := key h⁻¹ hh' (fun hc => hhC (by simpa using C.inv_mem hc))
  have h3 := (C.subgroupOf R).mul_mem h1 ((C.subgroupOf R).inv_mem h2)
  have h4 : g⁻¹ * h = (((⟨g⁻¹, hg'⟩ : ↥R) * a) * ((⟨h⁻¹, hh'⟩ : ↥R) * a)⁻¹ : ↥R) := by
    simp [mul_assoc]
  rw [h4]
  exact h3

theorem mem_of_index_two {R C : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hCR : C ≤ R) (hcard : Nat.card R = 2 * Nat.card C) :
    z ∈ C := by
  obtain ⟨k, hk, hkc⟩ := hR.natCard_eq
  have h2 : 2 ∣ Nat.card C := by
    have h4 := four_le_natCard_of_index_two hR hcard
    have hdvd : Nat.card C ∣ 2 ^ (k + 2) := hkc ▸ Subgroup.card_dvd_of_le hCR
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj']
    rcases j with _ | j
    · rw [hj'] at h4; simp at h4
    · exact ⟨2 ^ j, by ring⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 h2
  have hcG : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
  have hsq : (c : G) * (c : G) = 1 := by
    have := pow_orderOf_eq_one (c : G)
    rwa [hcG, pow_two] at this
  have hne : (c : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hcG
    omega
  rcases hz.unique c (hCR c.2) hsq with h | h
  · exact absurd h hne
  · rw [← h]
    exact c.2

theorem sq_eq_of_not_mem {R C : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hCR : C ≤ R) (hC : IsCyclic ↥C)
    (hcard : Nat.card R = 2 * Nat.card C) {g : G} (hg : g ∈ R) (hgC : g ∉ C) : g * g = z := by
  obtain ⟨C₁, hC₁R, hC₁c, hC₁card, hC₁mem⟩ := hR.exists_cyclic_max
  have hle4 : orderOf g ≤ 4 := by
    by_contra hgt
    push Not at hgt
    by_cases h16 : 16 ≤ Nat.card R
    · have hCeq : C = C₁ := hR.eq_of_cyclic hCR hC₁R hC hC₁c hcard hC₁card h16
      exact hgC (hCeq ▸ hC₁mem g hg hgt)
    · have hR8 := natCard_eq_eight_of_not_sixteen_le hR h16
      have hC₁4 : Nat.card C₁ = 4 := by omega
      have hmem := hC₁mem g hg hgt
      have hdvd : orderOf g ∣ Nat.card C₁ := by
        rw [← Subgroup.orderOf_mk g hmem]
        exact orderOf_dvd_natCard (⟨g, hmem⟩ : ↥C₁)
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  obtain ⟨j, hj⟩ := orderOf_eq_two_pow_of_isQuatSub hR hg
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hz1 : z ∈ C := mem_of_index_two hR hz hCR hcard
  have hg1 : g ≠ 1 := fun h => hgC (h ▸ C.one_mem)
  have hgz : g ≠ z := fun h => hgC (h ▸ hz1)
  have hord : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 := by
    interval_cases j <;> simp [hj]
  rcases hord with hj | hj | hj
  · exfalso
    exact hg1 (orderOf_eq_one_iff.mp hj)
  · exfalso
    have hsq : g * g = 1 := by
      have := pow_orderOf_eq_one g
      rwa [hj, pow_two] at this
    rcases hz.unique g hg hsq with h | h
    · exact hg1 h
    · exact hgz h
  · have hg4 : g ^ 4 = 1 := by
      have := pow_orderOf_eq_one g
      rwa [hj] at this
    have hsq : (g * g) * (g * g) = 1 := by
      rw [← hg4]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have hne : g * g ≠ 1 := by
      intro h
      have h2 : g ^ 2 = 1 := by rw [pow_two]; exact h
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hj] at this
      omega
    rcases hz.unique (g * g) (R.mul_mem hg hg) hsq with h | h
    · exact absurd h hne
    · exact h

theorem conj_eq_inv_of_not_mem {R C : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hCR : C ≤ R) (hC : IsCyclic ↥C)
    (hcard : Nat.card R = 2 * Nat.card C) {g : G} (hg : g ∈ R) (hgC : g ∉ C) {c : G} (hc : c ∈ C) :
    g * c * g⁻¹ = c⁻¹ := by
  have hgc : g * c ∈ R := R.mul_mem hg (hCR hc)
  have hgcC : g * c ∉ C := fun h => hgC (by simpa using C.mul_mem h (C.inv_mem hc))
  have h1 : (g * c) * (g * c) = z := sq_eq_of_not_mem hR hz hCR hC hcard hgc hgcC
  have h2 : g * g = z := sq_eq_of_not_mem hR hz hCR hC hcard hg hgC
  have hzc : c⁻¹ * z = z * c⁻¹ := (uniqueInvolution_comm hz (hCR (C.inv_mem hc))).symm.symm
  have h3 : c * g * c = g := by
    have : g * (c * g * c) = g * g := by
      calc g * (c * g * c) = (g * c) * (g * c) := by group
        _ = z := h1
        _ = g * g := h2.symm
    exact mul_left_cancel this
  have h4 : c * g = g * c⁻¹ := by
    have := congrArg (fun x => x * c⁻¹) h3
    simpa [mul_assoc] using this
  have hgi : g⁻¹ = g * z := by
    have hzz : z * z = 1 := hz.sq
    calc g⁻¹ = g⁻¹ * (g * g) * (g * g)⁻¹ * 1 := by group
      _ = g⁻¹ * (g * g) * z⁻¹ * 1 := by rw [h2]
      _ = g * z⁻¹ := by group
      _ = g * z := by rw [inv_eq_of_mul_eq_one_right hzz]
  calc g * c * g⁻¹ = g * c * g * z := by rw [hgi]; group
    _ = g * (c * g) * z := by group
    _ = g * (g * c⁻¹) * z := by rw [h4]
    _ = (g * g) * c⁻¹ * z := by group
    _ = z * (c⁻¹ * z) := by rw [h2]; group
    _ = z * (z * c⁻¹) := by rw [hzc]
    _ = (z * z) * c⁻¹ := by group
    _ = c⁻¹ := by rw [hz.sq, one_mul]

theorem exists_invariant_cyclic {R V : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hV2 : IsPGroup 2 V) (hVR : ∀ y ∈ V, conjSub y R = R) :
    ∃ C : Subgroup G, C ≤ R ∧ IsCyclic ↥C ∧ Nat.card R = 2 * Nat.card C ∧
      ∀ y ∈ V, conjSub y C = C := by
  obtain ⟨C₁, hC₁R, hC₁c, hC₁card, hC₁mem⟩ := hR.exists_cyclic_max
  by_cases h16 : 16 ≤ Nat.card R
  · refine ⟨C₁, hC₁R, hC₁c, hC₁card, fun y hy => ?_⟩
    have hle : conjSub y C₁ ≤ R := by
      have := conjSub_mono (n := y) hC₁R
      rwa [hVR y hy] at this
    exact hR.eq_of_cyclic hle hC₁R (isCyclic_conjSub y hC₁c) hC₁c
      (by rw [natCard_conjSub]; exact hC₁card) hC₁card h16
  · have hR8 := natCard_eq_eight_of_not_sixteen_le hR h16
    have hVn : V ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mpr (hVR y hy)
    have hP : IsPGroup 2 ↥(V ⊔ R) := hV2.to_sup_of_normal_right' (isPGroup_of_isQuatSub hR) hVn
    have hPn : V ⊔ R ≤ Subgroup.normalizer (R : Set G) :=
      sup_le hVn Subgroup.le_normalizer
    obtain ⟨A, hAR, hAc, hA4, hAinv⟩ := exists_invariant_cyclic_order_four hP le_sup_right
      (fun p hp => mem_normalizer_iff_conjSub_eq.mp (hPn hp)) hz (by omega)
    exact ⟨A, hAR, hAc, by omega, fun y hy => hAinv y ((le_sup_left : V ≤ V ⊔ R) hy)⟩

end CFSG.ClassicalInvolution.Asc77.AscL62
