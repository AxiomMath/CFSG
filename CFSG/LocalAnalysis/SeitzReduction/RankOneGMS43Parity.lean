module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

variable {P : Type*} [Group P] [Finite P]

theorem exists_conj_partner (hP : IsPGroup 2 P) {j z : P} (hj : j * j = 1) (hj1 : j ≠ 1)
    (hjZ : ∃ s : P, s * j ≠ j * s)
    (hinv : ∀ y : P, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z) :
    ∃ x : P, IsConj j x ∧ x * j = j * x ∧ x ≠ j ∧ (x = z ∨ x = j * z) ∧
      ∀ y : P, IsConj j y → y * j = j * y → y = j ∨ y = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype P := Fintype.ofFinite P
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  let f : Function.End {y : P // IsConj j y} := fun y =>
    ⟨j * y * j⁻¹, y.2.trans (isConj_iff.mpr ⟨j, rfl⟩)⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext y
    apply Subtype.ext
    show j * (j * (y : P) * j⁻¹) * j⁻¹ = y
    rw [hjinv, show j * (j * (y : P) * j) * j = (j * j) * y * (j * j) by group, hj, one_mul,
      mul_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hcard : 2 ∣ Fintype.card {y : P // IsConj j y} := by
    have hP' : IsPGroup 2 (ConjAct P) := hP.of_equiv ConjAct.toConjAct
    have e : {y : P // IsConj j y} ≃ MulAction.orbit (ConjAct P) j :=
      { toFun := fun y => ⟨y, ConjAct.mem_orbit_conjAct.mpr y.2.symm⟩
        invFun := fun y => ⟨y, (ConjAct.mem_orbit_conjAct.mp y.2).symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    obtain ⟨n, hn⟩ := hP'.card_orbit j
    rw [Fintype.card_eq_nat_card, Nat.card_congr e, hn]
    rcases n with _ | n
    · exfalso
      obtain ⟨s, hs⟩ := hjZ
      have h1 : Nat.card {y : P // IsConj j y} = 1 := by rw [Nat.card_congr e, hn, pow_zero]
      have hsub : Subsingleton {y : P // IsConj j y} :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      have h2 : j = s * j * s⁻¹ := congrArg Subtype.val (hsub.elim ⟨j, IsConj.refl j⟩
        ⟨s * j * s⁻¹, isConj_iff.mpr ⟨s, rfl⟩⟩)
      apply hs
      calc s * j = s * j * s⁻¹ * s := by group
        _ = j * s := by rw [← h2]
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  set A : Finset P := Finset.univ.filter (fun y => IsConj j y ∧ y * j = j * y) with hA
  have hfix : Fintype.card (Function.fixedPoints f) = A.card := by
    rw [hA, ← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h1 : j * (y.1 : P) * j⁻¹ = y.1 := congrArg Subtype.val y.2
      calc (y.1 : P) * j = j * y.1 * j⁻¹ * j := by rw [h1]
        _ = j * y.1 := by group
    · apply Subtype.ext
      show j * y.1 * j⁻¹ = y.1
      rw [← y.2.2]
      group
  have heven : 2 ∣ A.card := by
    rw [← hfix]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcard))
  have hAinv : ∀ y ∈ A, y = j ∨ y = z ∨ y = j * z := by
    intro y hy
    obtain ⟨hyc, hyj⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ := isConj_iff.mp hyc
    have hyy : g * j * g⁻¹ * (g * j * g⁻¹) = 1 := by
      rw [show g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ by group, hj]
      group
    have hy1 : g * j * g⁻¹ ≠ 1 := fun h1 => hj1 (by
      calc j = g⁻¹ * (g * j * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
    rcases hinv _ hyj hyy with h | h | h | h
    · exact absurd h hy1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl j, rfl⟩
  have hAle : A.card ≤ 3 := by
    have hsub : A ⊆ ({j, z, j * z} : Finset P) := fun y hy => by
      rcases hAinv y hy with h | h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_three
  obtain ⟨x, hxA, hxj⟩ : ∃ x ∈ A, x ≠ j := by
    by_contra hall
    push Not at hall
    have : A.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      rw [hall a ha, hall b hb]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨j, hjA⟩
    omega
  obtain ⟨hxc, hxj'⟩ := (Finset.mem_filter.mp hxA).2
  have hxz : x = z ∨ x = j * z := by
    rcases hAinv x hxA with h | h | h
    · exact absurd h hxj
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨x, hxc, hxj', hxj, hxz, fun y hyc hyj => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hyj1, hyx⟩ := hne
  have hyA : y ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyc, hyj⟩
  have h3 : ({j, x, y} : Finset P).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxj.symm, hyj1.symm]),
      Finset.card_pair hyx.symm]
  have h4 : ({j, x, y} : Finset P) ⊆ A := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hjA
    · exact hxA
    · exact hyA
  have h5 := Finset.card_le_card h4
  have hA3 : A.card = 3 := by omega
  rw [hA3] at heven
  omega

omit [Finite P] in
theorem mul_partner_mem_center (hP : IsPGroup 2 P) {j x : P} (hj : j * j = 1)
    (hxc : IsConj j x) (hxj : x * j = j * x) (hxne : x ≠ j)
    (huniq : ∀ y : P, IsConj j y → y * j = j * y → y = j ∨ y = x) :
    ∀ s : P, s * (j * x) = (j * x) * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  obtain ⟨j', hj'⟩ : ∃ j', j' = s * j * s⁻¹ := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x', x' = s * x * s⁻¹ := ⟨_, rfl⟩
  have hj'j' : j' * j' = 1 := by
    rw [hj', show s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ by group, hj]
    group
  have hj'inv : j'⁻¹ = j' := inv_eq_of_mul_eq_one_right hj'j'
  have hj'c : IsConj j j' := isConj_iff.mpr ⟨s, hj'.symm⟩
  have hx'c : IsConj j x' := hxc.trans (isConj_iff.mpr ⟨s, hx'.symm⟩)
  have hx'j' : x' * j' = j' * x' := by
    rw [hx', hj']
    calc s * x * s⁻¹ * (s * j * s⁻¹) = s * (x * j) * s⁻¹ := by group
      _ = s * (j * x) * s⁻¹ := by rw [hxj]
      _ = s * j * s⁻¹ * (s * x * s⁻¹) := by group
  have huniq' : ∀ y : P, IsConj j y → y * j' = j' * y → y = j' ∨ y = x' := by
    intro y hyc hyj'
    have h1 : IsConj j (s⁻¹ * y * s) := hyc.trans (isConj_iff.mpr ⟨s⁻¹, by group⟩)
    have h2 : (s⁻¹ * y * s) * j = j * (s⁻¹ * y * s) := by
      calc (s⁻¹ * y * s) * j = s⁻¹ * (y * j') * s := by rw [hj']; group
        _ = s⁻¹ * (j' * y) * s := by rw [hyj']
        _ = j * (s⁻¹ * y * s) := by rw [hj']; group
    rcases huniq _ h1 h2 with h | h
    · left
      calc y = s * (s⁻¹ * y * s) * s⁻¹ := by group
        _ = j' := by rw [h, hj']
    · right
      calc y = s * (s⁻¹ * y * s) * s⁻¹ := by group
        _ = x' := by rw [h, hx']
  have key : j' * x' = j * x := by
    by_cases hcomm : j' * j = j * j'
    · rcases huniq j' hj'c hcomm with h | h
      · rcases huniq x' hx'c (by rw [← h]; exact hx'j') with h' | h'
        · exfalso
          apply hxne
          have h2 : s * x * s⁻¹ = s * j * s⁻¹ := by rw [← hx', ← hj', h', h]
          calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
            _ = s⁻¹ * (s * j * s⁻¹) * s := by rw [h2]
            _ = j := by group
        · rw [h, h']
      · rcases huniq' j (IsConj.refl j) hcomm.symm with h' | h'
        · exact absurd (h'.trans h).symm hxne
        · rw [h, ← h']
          exact hxj
    ·
      obtain ⟨c, hc⟩ : ∃ c, c = j * j' := ⟨_, rfl⟩
      have hc2 : c * c ≠ 1 := by
        intro h1
        apply hcomm
        have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right h1
        rw [hc, mul_inv_rev, hjinv, hj'inv] at h2
        exact h2
      obtain ⟨k₀, hk₀⟩ := hP c
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk₀)
      have hm2 : 2 ≤ m := by
        by_contra hlt
        push Not at hlt
        apply hc2
        have h1 : orderOf c ∣ 2 := by
          rw [hm]
          exact (pow_dvd_pow 2 (by omega : m ≤ 1)).trans (by norm_num)
        rw [← sq]
        exact orderOf_dvd_iff_pow_eq_one.mp h1
      obtain ⟨n, k, hnk, hnlt, hnn⟩ : ∃ n k : ℕ, n = k + k ∧ n < 2 ^ m ∧ n + n = 2 ^ m := by
        refine ⟨2 ^ (m - 1), 2 ^ (m - 2), ?_, ?_, ?_⟩
        · rw [← two_mul, ← pow_succ']
          congr 1
          omega
        · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        · rw [← two_mul, ← pow_succ']
          congr 1
          omega
      have hz2 : c ^ n * c ^ n = 1 := by rw [← pow_add, hnn, ← hm, pow_orderOf_eq_one]
      have hz1 : c ^ n ≠ 1 :=
        pow_ne_one_of_lt_orderOf (by omega) (by rw [hm]; exact hnlt)
      have hzinv : (c ^ n)⁻¹ = c ^ n := inv_eq_of_mul_eq_one_right hz2
      have conjk : ∀ u : P, u * c * u⁻¹ = c⁻¹ →
          c ^ k * u * (c ^ k)⁻¹ = u * c ^ n ∧ u * c ^ n = c ^ n * u := by
        intro u hu
        have h1 : u * c ^ k * u⁻¹ = (c ^ k)⁻¹ := by rw [← conj_pow, hu, inv_pow]
        have h2 : u * (c ^ k)⁻¹ * u⁻¹ = c ^ k := by
          rw [show u * (c ^ k)⁻¹ * u⁻¹ = (u * c ^ k * u⁻¹)⁻¹ by group, h1, inv_inv]
        have h3 : u * (c ^ k)⁻¹ = c ^ k * u := by
          calc u * (c ^ k)⁻¹ = u * (c ^ k)⁻¹ * u⁻¹ * u := by group
            _ = c ^ k * u := by rw [h2]
        have h4 : u * c ^ n * u⁻¹ = c ^ n := by rw [← conj_pow, hu, inv_pow, hzinv]
        have h5 : u * c ^ n = c ^ n * u := by
          calc u * c ^ n = u * c ^ n * u⁻¹ * u := by group
            _ = c ^ n * u := by rw [h4]
        refine ⟨?_, h5⟩
        calc c ^ k * u * (c ^ k)⁻¹ = c ^ k * (u * (c ^ k)⁻¹) := by group
          _ = c ^ k * (c ^ k * u) := by rw [h3]
          _ = c ^ n * u := by rw [← mul_assoc, ← pow_add, ← hnk]
          _ = u * c ^ n := h5.symm
      have hjc : j * c * j⁻¹ = c⁻¹ := by
        rw [hc, mul_inv_rev, hjinv, hj'inv]
        calc j * (j * j') * j = (j * j) * j' * j := by group
          _ = j' * j := by rw [hj, one_mul]
      have hj'c' : j' * c * j'⁻¹ = c⁻¹ := by
        rw [hc, mul_inv_rev, hjinv, hj'inv]
        calc j' * (j * j') * j' = j' * j * (j' * j') := by group
          _ = j' * j := by rw [hj'j', mul_one]
      obtain ⟨hk1, hk2⟩ := conjk j hjc
      obtain ⟨hk1', hk2'⟩ := conjk j' hj'c'
      have hxz : j * c ^ n = x := by
        have hc1 : IsConj j (j * c ^ n) := isConj_iff.mpr ⟨c ^ k, hk1⟩
        have hc2' : (j * c ^ n) * j = j * (j * c ^ n) := by rw [mul_assoc, ← hk2]
        rcases huniq _ hc1 hc2' with h | h
        · exfalso
          apply hz1
          calc c ^ n = j⁻¹ * (j * c ^ n) := by group
            _ = 1 := by rw [h, inv_mul_cancel]
        · exact h
      have hx'z : j' * c ^ n = x' := by
        have hc1 : IsConj j (j' * c ^ n) := hj'c.trans (isConj_iff.mpr ⟨c ^ k, hk1'⟩)
        have hc2' : (j' * c ^ n) * j' = j' * (j' * c ^ n) := by rw [mul_assoc, ← hk2']
        rcases huniq' _ hc1 hc2' with h | h
        · exfalso
          apply hz1
          calc c ^ n = j'⁻¹ * (j' * c ^ n) := by group
            _ = 1 := by rw [h, inv_mul_cancel]
        · exact h
      rw [← hxz, ← hx'z, ← mul_assoc, ← mul_assoc, hj, hj'j']
  calc s * (j * x) = (s * (j * x) * s⁻¹) * s := by group
    _ = (j' * x') * s := by rw [hj', hx']; group
    _ = (j * x) * s := by rw [key]

theorem exists_conj_partner_mem_center (hP : IsPGroup 2 P) {j z : P} (hj : j * j = 1)
    (hj1 : j ≠ 1) (hjZ : j ∉ center P)
    (hinv : ∀ y : P, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z) :
    ∃ x : P, IsConj j x ∧ x * j = j * x ∧ x ≠ j ∧ (x = z ∨ x = j * z) ∧
      (∀ y : P, IsConj j y → y * j = j * y → y = j ∨ y = x) ∧ j * x ∈ center P := by
  have hjZ' : ∃ s : P, s * j ≠ j * s := by
    by_contra hall
    push Not at hall
    exact hjZ (mem_center_iff.mpr hall)
  obtain ⟨x, hxc, hxj, hxne, hxz, huniq⟩ := exists_conj_partner hP hj hj1 hjZ' hinv
  exact ⟨x, hxc, hxj, hxne, hxz, huniq,
    mem_center_iff.mpr (mul_partner_mem_center hP hj hxc hxj hxne huniq)⟩

end GMS43

end CFSG.SeitzReduction.RankOne
