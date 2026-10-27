module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

section Config

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_eight_config_perm (p : Fin 8 → α) (hp : Function.Injective p) :
    ∃ a c t₁ t₂ : Perm α, Perm.sign a = 1 ∧ Perm.sign c = 1 ∧ a.cycleType = {2, 2} ∧
      c.cycleType = {2, 2} ∧ (a * c).cycleType = {2, 2, 2, 2} ∧ t₁.IsThreeCycle ∧
      t₂.IsThreeCycle ∧ t₁ * t₂ = c ∧ Commute a t₁ ∧ Commute a t₂ := by
  have hne : ∀ i j : Fin 8, i ≠ j → p i ≠ p j := fun i j h => hp.ne h
  have hd : ∀ i j k l : Fin 8, [i, j, k, l].Nodup →
      Disjoint (swap (p i) (p j)) (swap (p k) (p l)) := fun i j k l h =>
    disjoint_swap_swap (h.map hp)
  have hct : ∀ i j k l : Fin 8, [i, j, k, l].Nodup →
      (swap (p i) (p j) * swap (p k) (p l)).cycleType = {2, 2} := fun i j k l h =>
    cycleType_swap_mul_swap_of_nodup (h.map hp)
  refine ⟨swap (p 0) (p 1) * swap (p 2) (p 3), swap (p 4) (p 5) * swap (p 6) (p 7),
    swap (p 4) (p 5) * swap (p 4) (p 6), swap (p 4) (p 6) * swap (p 6) (p 7), ?_, ?_,
    hct 0 1 2 3 (by decide), hct 4 5 6 7 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, sign_swap (hne 0 1 (by decide)), sign_swap (hne 2 3 (by decide))]
    decide
  · rw [map_mul, sign_swap (hne 4 5 (by decide)), sign_swap (hne 6 7 (by decide))]
    decide
  · have hdisj : Disjoint (swap (p 0) (p 1) * swap (p 2) (p 3))
        (swap (p 4) (p 5) * swap (p 6) (p 7)) :=
      ((hd 0 1 4 5 (by decide)).mul_right (hd 0 1 6 7 (by decide))).mul_left
        ((hd 2 3 4 5 (by decide)).mul_right (hd 2 3 6 7 (by decide)))
    rw [hdisj.cycleType_mul, hct 0 1 2 3 (by decide), hct 4 5 6 7 (by decide)]
    rfl
  · exact isThreeCycle_swap_mul_swap_same (hne 4 5 (by decide)) (hne 4 6 (by decide))
      (hne 5 6 (by decide))
  · rw [show swap (p 4) (p 6) * swap (p 6) (p 7) = swap (p 6) (p 4) * swap (p 6) (p 7) by
      rw [swap_comm (p 4) (p 6)]]
    exact isThreeCycle_swap_mul_swap_same (hne 6 4 (by decide)) (hne 6 7 (by decide))
      (hne 4 7 (by decide))
  · simp [mul_assoc]
  · exact (((hd 0 1 4 5 (by decide)).mul_right (hd 0 1 4 6 (by decide))).mul_left
        ((hd 2 3 4 5 (by decide)).mul_right (hd 2 3 4 6 (by decide)))).commute
  · exact (((hd 0 1 4 6 (by decide)).mul_right (hd 0 1 6 7 (by decide))).mul_left
        ((hd 2 3 4 6 (by decide)).mul_right (hd 2 3 6 7 (by decide)))).commute

end Config

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem exists_eight_config (hn : 8 ≤ n) :
    ∃ a c t₁ t₂ : alternatingGroup (Fin n),
      (a : Perm (Fin n)).cycleType = {2, 2} ∧ (c : Perm (Fin n)).cycleType = {2, 2} ∧
      ((a * c : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} ∧
      t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧ t₁ * t₂ = c ∧ Commute a t₁ ∧ Commute a t₂ := by
  obtain ⟨a, c, t₁, t₂, ha, hc, hac, hc', hacc, ht₁, ht₂, ht, hat₁, hat₂⟩ :=
    exists_eight_config_perm (Fin.castLE hn) (Fin.castLE_injective hn)
  have h3 : ∀ {g : Perm (Fin n)}, g.IsThreeCycle → ∀ hg : g ∈ alternatingGroup (Fin n),
      (⟨g, hg⟩ : alternatingGroup (Fin n)) ^ 3 = 1 := fun {g} hg _ =>
    Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hg.orderOf, pow_orderOf_eq_one])
  exact ⟨⟨a, Perm.mem_alternatingGroup.mpr ha⟩, ⟨c, Perm.mem_alternatingGroup.mpr hc⟩,
    ⟨t₁, Perm.mem_alternatingGroup.mpr ht₁.sign⟩, ⟨t₂, Perm.mem_alternatingGroup.mpr ht₂.sign⟩,
    hac, hc', hacc, h3 ht₁ _, h3 ht₂ _, Subtype.ext ht, Subtype.ext hat₁.eq, Subtype.ext hat₂.eq⟩

namespace TwoCover

theorem exists_lift_two_two_sq_ne_one (hπ : TwoCover π) (hn : 5 ≤ n) :
    ∃ y : H, ((π y : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2} ∧ y ^ 2 ≠ 1 := by
  have := hπ.finite'
  have : Group.IsPerfect H := hπ.perfect
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hne : π.ker ≠ ⊥ := by
    intro h
    have := hπ.card_ker
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨x, z, hx, -, -, hz1, -, hxz⟩ := CFSG.QuasithinUnique.Ch1.alt_cover_structure (m := m)
    (by omega) π hπ.surj hπ.ker_le_center hπ.isPGroup_ker' hne
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  refine ⟨x i₀ * x i₁, ?_, by rw [hxz i₀ i₁ h01]; exact hz1⟩
  rw [map_mul, hx, hx, coe_altThreeCycle_mul h01]
  refine cycleType_swap_mul_swap_of_nodup ?_
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true]
  exact ⟨⟨(addNat_two_ne_zero i₀).symm, zero_ne_one_fin, (addNat_two_ne_zero i₁).symm⟩,
    ⟨addNat_two_ne_one i₀, addNat_two_ne h01⟩, (addNat_two_ne_one i₁).symm⟩

theorem sq_eq_one_of_cycleType_eq {g : alternatingGroup (Fin n)} {c : Multiset ℕ}
    (hc : ∀ i ∈ c, i = 2) (hg : (g : Perm (Fin n)).cycleType = c) : g ^ 2 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact Perm.pow_prime_eq_one_iff.mpr (fun i hi => hc i (hg ▸ hi)))

theorem sq_mem_ker_ne_one_of_cycleType_two_two (hπ : TwoCover π) (hn : 5 ≤ n) {x : H}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2}) :
    x ^ 2 ∈ π.ker ∧ x ^ 2 ≠ 1 := by
  obtain ⟨y, hy, hy1⟩ := hπ.exists_lift_two_two_sq_ne_one hn
  have hyk : y ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact sq_eq_one_of_cycleType_eq (c := {2, 2}) (by simp) hy
  have hxy : x ^ 2 = y ^ 2 :=
    hπ.sq_eq_of_isConj (isConj_alternatingGroup_of_cycleType_eq_two_two hx hy) hyk
  rw [hxy]
  exact ⟨hyk, hy1⟩

theorem orderOf_eq_four_of_cycleType_two_two (hπ : TwoCover π) (hn : 5 ≤ n) {x : H}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2}) :
    orderOf x = 4 := by
  obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn hx
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by rw [pow_one]; exact h1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul]; exact hπ.sq_eq_one_of_mem_ker' hk)
  rw [h]
  norm_num

theorem sq_eq_one_of_cycleType_two_two_two_two (hπ : TwoCover π) (hn : 8 ≤ n) {x : H}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2}) :
    x ^ 2 = 1 := by
  obtain ⟨a, c, t₁, t₂, ha, hc, hac, ht₁, ht₂, ht, hat₁, hat₂⟩ := exists_eight_config hn
  have hn5 : 5 ≤ n := by omega
  obtain ⟨â, hâ⟩ := hπ.surj a
  obtain ⟨ĉ, hĉ⟩ := hπ.surj c
  obtain ⟨x₁, ⟨hx₁, hx₁3⟩, -⟩ := hπ.existsUnique_lift_pow_three t₁ ht₁
  obtain ⟨x₂, ⟨hx₂, hx₂3⟩, -⟩ := hπ.existsUnique_lift_pow_three t₂ ht₂
  have h1 : Commute â x₁ := hπ.commute_of_pow_three hx₁3 (by rw [hâ, hx₁]; exact hat₁)
  have h2 : Commute â x₂ := hπ.commute_of_pow_three hx₂3 (by rw [hâ, hx₂]; exact hat₂)
  have hk : (x₁ * x₂)⁻¹ * ĉ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hx₁, hx₂, ht, hĉ, inv_mul_cancel]
  have hâk : Commute â ((x₁ * x₂)⁻¹ * ĉ) :=
    Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) â
  have hcomm : Commute â ĉ := by
    have hĉk : ĉ = x₁ * x₂ * ((x₁ * x₂)⁻¹ * ĉ) := by group
    rw [hĉk]
    exact (h1.mul_right h2).mul_right hâk
  have hâ2 : â ^ 2 ∈ π.ker ∧ â ^ 2 ≠ 1 :=
    hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn5 (by rw [hâ]; exact ha)
  have hsq : ĉ ^ 2 = â ^ 2 := hπ.sq_eq_of_isConj
    (isConj_alternatingGroup_of_cycleType_eq_two_two (by rw [hĉ]; exact hc)
      (by rw [hâ]; exact ha)) hâ2.1
  have hâĉ : (â * ĉ) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hsq, ← sq, hπ.sq_eq_one_of_mem_ker' hâ2.1]
  have hconj : IsConj (π x) (π (â * ĉ)) :=
    isConj_alternatingGroup_of_cycleType_eq_two_two_two_two hx
      (by rw [map_mul, hâ, hĉ]; exact hac)
  rw [hπ.sq_eq_of_isConj hconj (by rw [hâĉ]; exact (π.ker).one_mem), hâĉ]

theorem orderOf_eq_two_of_cycleType_two_two_two_two (hπ : TwoCover π) (hn : 8 ≤ n) {x : H}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2}) :
    orderOf x = 2 ∧ x ∉ π.ker := by
  have hne : π x ≠ 1 := by
    intro h
    rw [h, OneMemClass.coe_one, Perm.cycleType_one] at hx
    simp at hx
  refine ⟨orderOf_eq_prime (hπ.sq_eq_one_of_cycleType_two_two_two_two hn hx) ?_,
    fun hk => hne hk⟩
  rintro rfl
  exact hne (map_one π)

theorem cycleType_of_orderOf_eq_two (hπ : TwoCover π) (hn : 8 ≤ n) (hn' : n ≤ 11) {x : H}
    (hx : orderOf x = 2) (hxk : x ∉ π.ker) :
    ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} := by
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hσ2 : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hx2, map_one, OneMemClass.coe_one]
  have hσ1 : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)) ≠ 1 := fun h =>
    hxk (by rw [MonoidHom.mem_ker]; exact Subtype.ext h)
  have hsign : Perm.sign ((π x : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 :=
    Perm.mem_alternatingGroup.mp (π x).2
  obtain ⟨k, hk⟩ : ∃ k, ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType =
      Multiset.replicate k 2 := ⟨_, Perm.cycleType_of_pow_prime_eq_one hσ2⟩
  have hsum := Perm.sum_cycleType_le ((π x : alternatingGroup (Fin n)) : Perm (Fin n))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ1 (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk5 : k ≤ 5 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  rw [hk]
  interval_cases k
  · exact absurd hsign (by decide)
  · exfalso
    exact (hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by omega) (x := x) hk).2 hx2
  · exact absurd hsign (by decide)
  · rfl
  · exact absurd hsign (by decide)

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
