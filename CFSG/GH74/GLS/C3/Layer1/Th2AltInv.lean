module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Th2.AltInv

open Equiv Equiv.Perm Subgroup

variable {m : ℕ}

theorem cycleType_replicate_two {σ : Perm (Fin m)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  rw [Multiset.eq_replicate]
  refine ⟨rfl, fun b hb => ?_⟩
  have hdvd : b ∣ 2 := hord ▸ dvd_of_mem_cycleType hb
  have hle : 2 ≤ b := two_le_of_mem_cycleType hb
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem cycleType_involution (hm : m ≤ 11) {s : alternatingGroup (Fin m)} (h2 : s * s = 1)
    (h1 : s ≠ 1) :
    (s : Perm (Fin m)).cycleType = {2, 2} ∨ (s : Perm (Fin m)).cycleType = {2, 2, 2, 2} := by
  set σ : Perm (Fin m) := (s : Perm (Fin m)) with hσ
  have hσ2 : σ * σ = 1 := congrArg Subtype.val h2
  have hσ1 : σ ≠ 1 := fun h => h1 (Subtype.ext h)
  have hrep := cycleType_replicate_two hσ2 hσ1
  set j := Multiset.card σ.cycleType with hj
  have hsum : σ.cycleType.sum = 2 * j := by
    rw [hrep, Multiset.sum_replicate]
    simp [hj, mul_comm]
  have hle : σ.cycleType.sum ≤ m := by
    have := sum_cycleType_le σ
    simpa using this
  have hj0 : j ≠ 0 := by
    intro h0
    apply hσ1
    rw [← cycleType_eq_zero]
    exact Multiset.card_eq_zero.1 h0
  have hsign : sign σ = 1 := mem_alternatingGroup.1 s.2
  rw [sign_of_cycleType, hsum] at hsign
  have heven : Even j := by
    have h3 : (-1 : ℤˣ) ^ (2 * j + j) = 1 := by
      rw [hj]; exact hsign
    have : (-1 : ℤˣ) ^ (2 * j + j) = (-1 : ℤˣ) ^ j := by
      rw [pow_add, pow_mul]; simp
    rw [this] at h3
    rcases Nat.even_or_odd j with he | ho
    · exact he
    · exfalso
      rw [ho.neg_one_pow] at h3
      exact absurd (congrArg Units.val h3) (by decide)
  have hj2 : 2 * j ≤ 11 := hsum ▸ hle.trans hm
  obtain ⟨k, hk⟩ := heven
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · left; rw [hrep]; have : j = 2 := by omega
    rw [this]; rfl
  · right; rw [hrep]; have : j = 4 := by omega
    rw [this]; rfl

theorem exists_odd_commuting {σ : Perm (Fin m)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ g : Perm (Fin m), g * σ = σ * g ∧ sign g = -1 := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  have hσσ : σ (σ a) = a := by
    have := congrArg (fun f : Perm (Fin m) => f a) h2
    simpa [Perm.mul_apply] using this
  refine ⟨swap a (σ a), ?_, sign_swap (Ne.symm ha)⟩
  have : σ * swap a (σ a) = swap a (σ a) * σ := by
    rw [mul_swap_eq_swap_mul, hσσ, swap_comm (σ a) a]
  exact this.symm

theorem isConj_of_cycleType_eq {s t : alternatingGroup (Fin m)} (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hcyc : (s : Perm (Fin m)).cycleType = (t : Perm (Fin m)).cycleType) : IsConj s t := by
  have hσ2 : (s : Perm (Fin m)) * (s : Perm (Fin m)) = 1 := congrArg Subtype.val hs2
  have hσ1 : (s : Perm (Fin m)) ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 hcyc)
  obtain ⟨g, hg, hgs⟩ := exists_odd_commuting hσ2 hσ1
  have hmem : ∀ d : Perm (Fin m), d * (s : Perm (Fin m)) * d⁻¹ = (t : Perm (Fin m)) → sign d = 1 →
      IsConj s t := by
    intro d hd hsd
    refine isConj_iff.2 ⟨⟨d, mem_alternatingGroup.2 hsd⟩, Subtype.ext ?_⟩
    simpa using hd
  rcases Int.units_eq_one_or (sign c) with h | h
  · exact hmem c hc h
  · refine hmem (c * g) ?_ ?_
    · have : g * (s : Perm (Fin m)) * g⁻¹ = (s : Perm (Fin m)) := by rw [hg]; group
      calc c * g * (s : Perm (Fin m)) * (c * g)⁻¹ = c * (g * (s : Perm (Fin m)) * g⁻¹) * c⁻¹ := by group
        _ = (t : Perm (Fin m)) := by rw [this]; exact hc
    · rw [map_mul, h, hgs]; rfl

theorem card_centralizer_alt {s : alternatingGroup (Fin m)} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    Nat.card ↥(centralizer ({s} : Set (alternatingGroup (Fin m)))) * 2 =
      Nat.card ↥(centralizer ({(s : Perm (Fin m))} : Set (Perm (Fin m)))) := by
  set σ : Perm (Fin m) := (s : Perm (Fin m)) with hσ
  have hσ2 : σ * σ = 1 := congrArg Subtype.val hs2
  have hσ1 : σ ≠ 1 := fun h => hs1 (Subtype.ext h)
  set Cσ : Subgroup (Perm (Fin m)) := centralizer ({σ} : Set (Perm (Fin m))) with hCσ
  let ψ : ↥Cσ →* ℤˣ := sign.comp Cσ.subtype
  obtain ⟨g, hg, hgs⟩ := exists_odd_commuting hσ2 hσ1
  have hgC : g ∈ Cσ := by
    rw [hCσ, mem_centralizer_singleton_iff]
    exact hg
  have hsurj : Function.Surjective ψ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp [ψ]⟩
    · exact ⟨⟨g, hgC⟩, by simpa [ψ] using hgs⟩
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top] at h1
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
  rw [hunits] at h1
  have hbij : Nat.card ↥(centralizer ({s} : Set (alternatingGroup (Fin m)))) = Nat.card ↥ψ.ker := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c => (⟨⟨(c : alternatingGroup (Fin m)).1, ?_⟩, ?_⟩ : ↥ψ.ker)) ⟨?_, ?_⟩)
    · have h := c.2
      rw [mem_centralizer_singleton_iff] at h ⊢
      exact (congrArg Subtype.val h)
    · have := (c : alternatingGroup (Fin m)).2
      rw [MonoidHom.mem_ker]
      simpa [ψ] using mem_alternatingGroup.1 this
    · intro c c' h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥ψ.ker => (z : ↥Cσ).1) h
    · rintro ⟨⟨d, hd⟩, hψ⟩
      have hdA : d ∈ alternatingGroup (Fin m) := by
        rw [mem_alternatingGroup]
        simpa [ψ] using (MonoidHom.mem_ker.1 hψ)
      refine ⟨⟨⟨d, hdA⟩, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := mem_centralizer_singleton_iff.1 hd
      exact this
  rw [hbij]
  exact h1

theorem nat_card_centralizer_two_two {σ : Perm (Fin m)} (h : σ.cycleType = {2, 2}) :
    Nat.card ↥(centralizer ({σ} : Set (Perm (Fin m)))) = (m - 4).factorial * 8 := by
  rw [nat_card_centralizer, h]
  simp [Multiset.toFinset_cons, Multiset.count_cons]
  ring

theorem nat_card_centralizer_two_four {σ : Perm (Fin m)} (h : σ.cycleType = {2, 2, 2, 2}) :
    Nat.card ↥(centralizer ({σ} : Set (Perm (Fin m)))) = (m - 8).factorial * 384 := by
  rw [nat_card_centralizer, h]
  simp [Multiset.toFinset_cons, Multiset.count_cons, Nat.factorial]
  ring

theorem isConj_equiv_iff' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b : X} :
    IsConj (e a) (e b) ↔ IsConj a b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨e.symm c, ?_⟩
    apply e.injective
    simpa using hc
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact isConj_iff.2 ⟨e c, by simpa using congrArg e hc⟩

theorem card_centralizer_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    Nat.card ↥(centralizer ({x} : Set X)) = Nat.card ↥(centralizer ({e x} : Set Y)) := by
  have h : (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := mem_centralizer_singleton_iff.1 hz
      rw [mem_centralizer_singleton_iff]
      simpa using congrArg e hz'
    · intro hy
      have hy' : y * e x = e x * y := mem_centralizer_singleton_iff.1 hy
      refine ⟨e.symm y, ?_, by simp⟩
      show e.symm y ∈ centralizer ({x} : Set X)
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      simpa using hy'
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem factorization_two_eq {n k : ℕ} (hn : n ≠ 0) (h1 : 2 ^ k ∣ n) (h2 : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  have a := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 h1
  have b : ¬ k + 1 ≤ n.factorization 2 := fun h =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).2 h)
  omega

theorem numerics (hm : m = 9 ∨ m = 10 ∨ m = 11) :
    ¬ 5 ∣ (m - 8).factorial * 384 ∧
      ¬ 2 ^ ((m.factorial / 2).factorization 2) ∣ (m - 4).factorial * 4 := by
  rcases hm with rfl | rfl | rfl
  · refine ⟨by decide, ?_⟩
    have : (Nat.factorial 9 / 2).factorization 2 = 6 :=
      factorization_two_eq (by decide) (by decide) (by decide)
    rw [this]; decide
  · refine ⟨by decide, ?_⟩
    have : (Nat.factorial 10 / 2).factorization 2 = 7 :=
      factorization_two_eq (by decide) (by decide) (by decide)
    rw [this]; decide
  · refine ⟨by decide, ?_⟩
    have : (Nat.factorial 11 / 2).factorization 2 = 7 :=
      factorization_two_eq (by decide) (by decide) (by decide)
    rw [this]; decide

theorem orderOf_two_sq {X : Type*} [Group X] {x : X} (hx : orderOf x = 2) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx, sq] at this

theorem alt_facts (hm : m = 9 ∨ m = 10 ∨ m = 11) {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin m)) {x : X} (hx : orderOf x = 2)
    (h5 : 5 ∣ Nat.card ↥(centralizer ({x} : Set X)))
    {W : Subgroup X} (hW : Nat.card ↥W = 2 ^ (Nat.card X).factorization 2) {v : X}
    (hv2 : orderOf v = 2) (hvc : ∀ w ∈ W, w * v = v * w) :
    ¬ IsConj x v ∧ (∀ t : X, orderOf t = 2 → IsConj t x ∨ IsConj t v) ∧
      ∃ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({v} : Set X)) ∧
        ¬ 2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set X)) := by
  have hm11 : m ≤ 11 := by omega
  have : NeZero m := ⟨by omega⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hXcard : Nat.card X = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  obtain ⟨hn5, hn2⟩ := numerics hm
  rw [← hXcard] at hn2
  set k := (Nat.card X).factorization 2 with hk
  have hone : ∀ {y : X}, orderOf y = 2 → e y * e y = 1 ∧ e y ≠ 1 := by
    intro y hy
    refine ⟨by rw [← map_mul, orderOf_two_sq hy, map_one], fun h => ?_⟩
    have : y = 1 := e.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hy
    omega
  obtain ⟨hx'2, hx'1⟩ := hone hx
  obtain ⟨hv'2, hv'1⟩ := hone hv2
  have hCx : Nat.card ↥(centralizer ({x} : Set X)) = Nat.card ↥(centralizer ({e x} : Set _)) :=
    card_centralizer_equiv e x
  have hCv : Nat.card ↥(centralizer ({v} : Set X)) = Nat.card ↥(centralizer ({e v} : Set _)) :=
    card_centralizer_equiv e v
  have hAx := card_centralizer_alt hx'2 hx'1
  have hAv := card_centralizer_alt hv'2 hv'1
  have htype_x : ((e x : alternatingGroup (Fin m)) : Perm (Fin m)).cycleType = {2, 2} := by
    rcases cycleType_involution hm11 hx'2 hx'1 with h | h
    · exact h
    · exfalso
      have hS := nat_card_centralizer_two_four h
      have : 5 ∣ (m - 8).factorial * 384 := by
        rw [← hS, ← hAx]
        exact (hCx ▸ h5).mul_right 2
      exact hn5 this
  have hCxval : Nat.card ↥(centralizer ({x} : Set X)) = (m - 4).factorial * 4 := by
    have hS := nat_card_centralizer_two_two htype_x
    rw [hCx]
    omega
  have h2k : 2 ^ k ∣ Nat.card ↥(centralizer ({v} : Set X)) := by
    have hle : W ≤ centralizer ({v} : Set X) := fun w hw =>
      mem_centralizer_singleton_iff.2 (hvc w hw)
    rw [← hW]
    exact Subgroup.card_dvd_of_le hle
  have htype_v : ((e v : alternatingGroup (Fin m)) : Perm (Fin m)).cycleType = {2, 2, 2, 2} := by
    rcases cycleType_involution hm11 hv'2 hv'1 with h | h
    · exfalso
      have hS := nat_card_centralizer_two_two h
      have : Nat.card ↥(centralizer ({v} : Set X)) = (m - 4).factorial * 4 := by
        rw [hCv]
        omega
      rw [this] at h2k
      exact hn2 h2k
    · exact h
  refine ⟨?_, ?_, k, h2k, by rw [hCxval]; exact hn2⟩
  · intro h
    have h1 := (isConj_equiv_iff' e).2 h
    obtain ⟨c, hc⟩ := isConj_iff.1 h1
    have h2 : IsConj ((e x : alternatingGroup (Fin m)) : Perm (Fin m))
        ((e v : alternatingGroup (Fin m)) : Perm (Fin m)) :=
      isConj_iff.2 ⟨(c : Perm (Fin m)), congrArg Subtype.val hc⟩
    have := isConj_iff_cycleType_eq.1 h2
    rw [htype_x, htype_v] at this
    exact absurd this (by decide)
  · intro t ht
    obtain ⟨ht2, ht1⟩ := hone ht
    rcases cycleType_involution hm11 ht2 ht1 with h | h
    · left
      exact (isConj_equiv_iff' e).1 (isConj_of_cycleType_eq ht2 ht1 (h.trans htype_x.symm))
    · right
      exact (isConj_equiv_iff' e).1 (isConj_of_cycleType_eq ht2 ht1 (h.trans htype_v.symm))

end CFSG.GH74.GLS.Th2.AltInv
