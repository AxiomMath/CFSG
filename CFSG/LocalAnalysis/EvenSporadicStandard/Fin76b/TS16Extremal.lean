module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G]

@[expose] def extremalClasses (M Q : Subgroup G) (z : G) (c : ℕ) : Set (Set G) :=
  {O | ∃ y ∈ Q, (∃ m ∈ M, y = m * z * m⁻¹) ∧ Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = c ∧
    O = {w | ∃ q ∈ Q, w = q * y * q⁻¹}}

theorem exists_two_mod [Finite G] {Q Q' : Subgroup G} (hQ' : IsPGroup 2 Q') (hlt : Q < Q') :
    ∃ n ∈ Q', n ∉ Q ∧ n * n ∈ Q ∧ ∀ q ∈ Q, n * q * n⁻¹ ∈ Q ∧ n⁻¹ * q * n ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Q' := Q.subgroupOf Q' with hH
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨hle, x, hxQ', hxQ⟩ := IsConcreteLE.lt_iff_le_and_exists.1 hlt
    have : (⟨x, hxQ'⟩ : Q') ∈ H := htop ▸ mem_top _
    exact hxQ (mem_subgroupOf.1 this)
  have : Group.IsNilpotent Q' := hQ'.isNilpotent
  have hnc : H < normalizer (H : Set Q') := Group.normalizerCondition_of_isNilpotent H hHlt
  obtain ⟨-, a, haN, haH⟩ := IsConcreteLE.lt_iff_le_and_exists.1 hnc
  obtain ⟨k, hk⟩ := hQ' a
  have hex : ∃ j : ℕ, a ^ (2 ^ j) ∈ H := ⟨k, by rw [hk]; exact H.one_mem⟩
  classical
  obtain ⟨j, hj, hmin⟩ : ∃ j, a ^ (2 ^ j) ∈ H ∧ ∀ i < j, a ^ (2 ^ i) ∉ H :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact haH (by simpa using hj)
  have hjj : j - 1 < j := Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos
  set n' : Q' := a ^ (2 ^ (j - 1)) with hn'
  have hn'H : n' ∉ H := hmin _ hjj
  have hn'sq : n' * n' ∈ H := by
    have : n' * n' = a ^ (2 ^ j) := by
      rw [hn', ← pow_add, ← two_mul, ← pow_succ']
      congr 2
      omega
    rw [this]; exact hj
  have hn'N : n' ∈ normalizer (H : Set Q') := (normalizer (H : Set Q')).pow_mem haN _
  refine ⟨(n' : G), n'.2, fun h => hn'H (mem_subgroupOf.2 h), mem_subgroupOf.1 hn'sq, ?_⟩
  intro q hq
  have hqQ' : q ∈ Q' := hlt.le hq
  have hqH : (⟨q, hqQ'⟩ : Q') ∈ H := mem_subgroupOf.2 hq
  constructor
  · have := (Subgroup.mem_normalizer_iff.1 hn'N ⟨q, hqQ'⟩).1 hqH
    exact mem_subgroupOf.1 this
  · have := (Subgroup.mem_normalizer_iff.1 ((normalizer (H : Set Q')).inv_mem hn'N) ⟨q, hqQ'⟩).1 hqH
    have h2 := mem_subgroupOf.1 this
    simpa using h2


theorem conj_mem_extremalClasses {M Q : Subgroup G} {z : G} {c : ℕ} {n : G}
    (hn1 : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) (hn2 : ∀ q ∈ Q, n⁻¹ * q * n ∈ Q)
    (hext : ∀ y ∈ Q, (∃ g : G, y = g * z * g⁻¹) →
      Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = c → ∃ m ∈ M, y = m * z * m⁻¹)
    {O : Set G} (hO : O ∈ extremalClasses M Q z c) :
    (fun w => n * w * n⁻¹) '' O ∈ extremalClasses M Q z c := by
  obtain ⟨y, hyQ, ⟨m, hmM, hym⟩, hcard, rfl⟩ := hO
  have hy'Q : n * y * n⁻¹ ∈ Q := hn1 y hyQ
  have hy'z : ∃ g : G, n * y * n⁻¹ = g * z * g⁻¹ :=
    ⟨n * m, by rw [hym]; group⟩
  have hcard' : Nat.card ↥(Q ⊓ centralizer ({n * y * n⁻¹} : Set G)) = c := by
    rw [← hcard]
    symm
    refine Nat.card_congr ((MulAut.conj n).toEquiv.subtypeEquiv (fun w => ?_))
    simp only [mem_inf, mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv, MulAut.conj_apply]
    constructor
    · rintro ⟨hwQ, hw⟩
      refine ⟨hn1 w hwQ, ?_⟩
      calc n * w * n⁻¹ * (n * y * n⁻¹) = n * (w * y) * n⁻¹ := by group
        _ = n * (y * w) * n⁻¹ := by rw [hw]
        _ = n * y * n⁻¹ * (n * w * n⁻¹) := by group
    · rintro ⟨hwQ, hw⟩
      have hwQ' : w ∈ Q := by
        have := hn2 _ hwQ
        simpa [mul_assoc] using this
      refine ⟨hwQ', ?_⟩
      have h1 : n * (w * y) * n⁻¹ = n * (y * w) * n⁻¹ := by
        calc n * (w * y) * n⁻¹ = n * w * n⁻¹ * (n * y * n⁻¹) := by group
          _ = n * y * n⁻¹ * (n * w * n⁻¹) := hw
          _ = n * (y * w) * n⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h1)
  obtain ⟨m', hm'M, hm'⟩ := hext _ hy'Q hy'z hcard'
  refine ⟨n * y * n⁻¹, hy'Q, ⟨m', hm'M, hm'⟩, hcard', ?_⟩
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨n * q * n⁻¹, hn1 q hq, by group⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨n⁻¹ * q * n * y * (n⁻¹ * q * n)⁻¹, ⟨n⁻¹ * q * n, hn2 q hq, rfl⟩, by group⟩


theorem not_dvd_index_of_odd_extremalClasses [Finite G] {M Q : Subgroup G} {z : G} {c : ℕ}
    (hQ : IsPGroup 2 Q)
    (hc : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R → R ≤ centralizer ({g * z * g⁻¹} : Set G) →
      Nat.card R ≤ c)
    (hext : ∀ y ∈ Q, (∃ g : G, y = g * z * g⁻¹) →
      Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = c → ∃ m ∈ M, y = m * z * m⁻¹)
    (hodd : Odd (Nat.card (extremalClasses M Q z c))) : ¬ 2 ∣ Q.index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hdvd
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  have hlt : Q < (Q' : Subgroup G) :=
    lt_of_le_of_ne hQQ' (fun h => Q'.not_dvd_index (h ▸ hdvd))
  obtain ⟨n, hnQ', hnQ, hn2, hnorm⟩ := exists_two_mod Q'.isPGroup' hlt
  have hn1 : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := fun q hq => (hnorm q hq).1
  have hn1' : ∀ q ∈ Q, n⁻¹ * q * n ∈ Q := fun q hq => (hnorm q hq).2
  let f : Function.End (extremalClasses M Q z c) := fun O =>
    ⟨(fun w => n * w * n⁻¹) '' O.1, conj_mem_extremalClasses hn1 hn1' hext O.2⟩
  have hff : f * f = 1 := by
    funext O
    apply Subtype.ext
    obtain ⟨y, hyQ, -, -, hO⟩ := O.2
    show (fun w => n * w * n⁻¹) '' ((fun w => n * w * n⁻¹) '' O.1) = O.1
    rw [hO]
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
      exact ⟨n * n * q, Q.mul_mem hn2 hq, by group⟩
    · rintro ⟨q, hq, rfl⟩
      have hq' : (n * n)⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem hn2) hq
      exact ⟨n * ((n * n)⁻¹ * q * y * ((n * n)⁻¹ * q)⁻¹) * n⁻¹,
        ⟨(n * n)⁻¹ * q * y * ((n * n)⁻¹ * q)⁻¹, ⟨(n * n)⁻¹ * q, hq', rfl⟩, rfl⟩, by group⟩
  have : Finite (extremalClasses M Q z c) := Set.finite_coe_iff.2 (Set.toFinite _)
  have : Fintype (extremalClasses M Q z c) := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1)
    (by simpa [pow_two] using hff)
  have hodd' : Odd (Fintype.card (extremalClasses M Q z c)) := by
    rwa [← Nat.card_eq_fintype_card]
  have hfixodd : Odd (Fintype.card (Function.fixedPoints f)) := by
    rw [Nat.odd_iff] at hodd' ⊢
    have h1 := hmod
    unfold Nat.ModEq at h1
    omega
  obtain ⟨⟨O, hO⟩, hfO⟩ : ∃ O : extremalClasses M Q z c, f O = O := by
    have : 0 < Fintype.card (Function.fixedPoints f) := by
      obtain ⟨k, hk⟩ := hfixodd
      omega
    obtain ⟨⟨O, hO⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨O, hO⟩
  obtain ⟨y, hyQ, ⟨m, hmM, hym⟩, hcard, rfl⟩ := hO
  have hfix : (fun w => n * w * n⁻¹) '' {w | ∃ q ∈ Q, w = q * y * q⁻¹} =
      {w | ∃ q ∈ Q, w = q * y * q⁻¹} := congrArg Subtype.val hfO
  have hmem : n * y * n⁻¹ ∈ {w | ∃ q ∈ Q, w = q * y * q⁻¹} := by
    rw [← hfix]
    exact ⟨y, ⟨1, Q.one_mem, by simp⟩, rfl⟩
  obtain ⟨q, hqQ, hq⟩ := hmem
  have hwc : q⁻¹ * n ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : n * y = q * y * q⁻¹ * n := by
      calc n * y = (n * y * n⁻¹) * n := by group
        _ = q * y * q⁻¹ * n := by rw [hq]
    calc q⁻¹ * n * y = q⁻¹ * (n * y) := by group
      _ = q⁻¹ * (q * y * q⁻¹ * n) := by rw [h1]
      _ = y * (q⁻¹ * n) := by group
  have hR2 : IsPGroup 2 ((Q' : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G) :=
    Q'.isPGroup'.to_le inf_le_left
  have hRc : Nat.card ((Q' : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ c :=
    hc m _ hR2 (by rw [← hym]; exact inf_le_right)
  have hle : Q ⊓ centralizer ({y} : Set G) ≤ (Q' : Subgroup G) ⊓ centralizer ({y} : Set G) :=
    inf_le_inf_right _ hQQ'
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hRc)
  have hmemR : q⁻¹ * n ∈ (Q' : Subgroup G) ⊓ centralizer ({y} : Set G) :=
    ⟨(Q' : Subgroup G).mul_mem ((Q' : Subgroup G).inv_mem (hQQ' hqQ)) hnQ', hwc⟩
  rw [← heq] at hmemR
  exact hnQ (by simpa using Q.mul_mem hqQ hmemR.1)

end CFSG.EvenSporadicStandard.Fin76b
