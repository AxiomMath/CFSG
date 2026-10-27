module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.CommuteOfCommutator
public import CFSG.Milestones.ASVolI.A3L3.StepsBase

public section

namespace CFSG.GroupTheory

open scoped Pointwise
open scoped commutatorElement

variable {X : Type} [Group X]

theorem eq_one_of_conj_eq_inv_mul_of_odd
    {t k w : X} (htk : t * k * t⁻¹ = w * k⁻¹) (hwk : Commute w k)
    (hw2 : w * w = 1) (hkodd : Odd (orderOf k)) :
    w = 1 := by
  by_contra hw1
  have hw_order_dvd : orderOf w ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hw_order : orderOf w = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hw_order_dvd with h | h
    · exact (hw1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hcop : Nat.Coprime (orderOf w) (orderOf k⁻¹) := by
    rw [hw_order, orderOf_inv]
    exact (Nat.coprime_two_right.mpr hkodd).symm
  have horder_wk : orderOf (w * k⁻¹) = 2 * orderOf k := by
    rw [hwk.inv_right.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hw_order, orderOf_inv]
  have hconj_order : orderOf (t * k * t⁻¹) = orderOf k := by
    refine (SemiconjBy.orderOf_eq t ?_).symm
    show t * k = (t * k * t⁻¹) * t
    group
  have horder_eq : orderOf (w * k⁻¹) = orderOf k := by
    rw [← htk, hconj_order]
  have hbad : 2 * orderOf k = orderOf k := by
    rw [← horder_wk, horder_eq]
  have hkpos : 0 < orderOf k := by
    rcases hkodd with ⟨m, hm⟩
    omega
  have h21 : 2 = 1 :=
    Nat.eq_of_mul_eq_mul_right hkpos (by simpa [one_mul] using hbad)
  norm_num at h21

theorem exists_mul_centralizer_pow_card_eq_one [Finite X]
    {K B : Subgroup X} (hBodd : Odd (Nat.card B))
    (hBKC : B ≤ K ⊔ Subgroup.centralizer (K : Set X))
    (hZ2 : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set X) → z ^ 2 = 1)
    {b : X} (hb : b ∈ B) :
    ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set X),
      b = k * c ∧ k ^ Nat.card B = 1 ∧ c ^ Nat.card B = 1 := by
  classical
  let C := Subgroup.centralizer (K : Set X)
  have hcommKC : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.mp hc k hk
  obtain ⟨k, hk, c, hc, hkc⟩ :=
    exists_mul_of_mem_sup_of_commute hcommKC (hBKC hb)
  have hbc : b = k * c := hkc.symm
  have hcomm : Commute k c := hcommKC k hk c hc
  have hbn : b ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb)
  have hprod : k ^ Nat.card B * c ^ Nat.card B = 1 := by
    rw [← hcomm.mul_pow, ← hbc]
    exact hbn
  set z := k ^ Nat.card B with hzdef
  have hcn : c ^ Nat.card B = z⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hzK : z ∈ K := K.pow_mem hk _
  have hzC : z ∈ C := by
    have hz_eq : z = (c ^ Nat.card B)⁻¹ := by rw [hcn, inv_inv]
    rw [hz_eq]
    exact C.inv_mem (C.pow_mem hc _)
  have hz2 : z ^ 2 = 1 := hZ2 z hzK hzC
  have hz2mul : z * z = 1 := by simpa [pow_two] using hz2
  have hcommkz : Commute k z := hcommKC k hk z hzC
  have hcommzc : Commute z c := hcommKC z hzK c hc
  obtain ⟨m, hm⟩ := hBodd
  have hzpow : z ^ Nat.card B = z := by
    rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have hkn : (k * z) ^ Nat.card B = 1 := by
    rw [hcommkz.mul_pow, ← hzdef, hzpow, hz2mul]
  have hcn' : (z * c) ^ Nat.card B = 1 := by
    rw [hcommzc.mul_pow, hzpow, hcn, mul_inv_cancel]
  refine ⟨k * z, K.mul_mem hk hzK, z * c, C.mul_mem hzC hc, ?_, hkn, hcn'⟩
  calc
    b = k * c := hbc
    _ = k * (z * z) * c := by rw [hz2mul, mul_one]
    _ = (k * z) * (z * c) := by group

theorem eq_sup_inf_centralizer_of_permuting_inner [Finite X]
    {B K T : Subgroup X} {t : X}
    (hBc : IsMulCommutative ↥B) (hBo : Odd (Nat.card B))
    (hTp : IsPGroup 2 T)
    (hperm : (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X))
    (hBKC : B ≤ K ⊔ Subgroup.centralizer (K : Set X))
    (hZ2 : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set X) → z ^ 2 = 1)
    (htT : t ∈ T) (htK : t ∈ K)
    (hinv : ∀ b ∈ B, t * b * t⁻¹ * b ∈ Subgroup.centralizer (K : Set X)) :
    B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) := by
  classical
  let C := Subgroup.centralizer (K : Set X)
  have hcommKC : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.mp hc k hk
  apply le_antisymm
  · intro b hb
    obtain ⟨k, hk, c, hc, hbc, hkn, hcn⟩ :=
      exists_mul_centralizer_pow_card_eq_one hBo hBKC hZ2 hb
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hBo (orderOf_dvd_of_pow_eq_one hkn)
    have hck : Commute c k := (hcommKC k hk c hc).symm
    have hct : Commute c t := (hcommKC t htK c hc).symm
    have hcalc : t * (k * c) * t⁻¹ * (k * c) =
        (t * k * t⁻¹ * k) * (c * c) := by
      calc
        t * (k * c) * t⁻¹ * (k * c)
            = t * k * (c * t⁻¹) * k * c := by group
        _ = t * k * (t⁻¹ * c) * k * c := by rw [hct.inv_right.eq]
        _ = t * k * t⁻¹ * (c * k) * c := by group
        _ = t * k * t⁻¹ * (k * c) * c := by rw [hck.eq]
        _ = (t * k * t⁻¹ * k) * (c * c) := by group
    have hwC : t * k * t⁻¹ * k ∈ C := by
      have hmem := hinv b hb
      rw [hbc, hcalc] at hmem
      have hc2C : c * c ∈ C := C.mul_mem hc hc
      have h := C.mul_mem hmem (C.inv_mem hc2C)
      simpa [mul_assoc] using h
    have hwK : t * k * t⁻¹ * k ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem htK hk) (K.inv_mem htK)) hk
    have hw2 : (t * k * t⁻¹ * k) * (t * k * t⁻¹ * k) = 1 := by
      simpa [pow_two] using hZ2 _ hwK hwC
    have hwk : Commute (t * k * t⁻¹ * k) k :=
      (Subgroup.mem_centralizer_iff.mp hwC k hk).symm
    have htk_eq : t * k * t⁻¹ = (t * k * t⁻¹ * k) * k⁻¹ := by group
    have hw1 : t * k * t⁻¹ * k = 1 :=
      eq_one_of_conj_eq_inv_mul_of_odd htk_eq hwk hw2 hkodd
    have hkt : t * k * t⁻¹ = k⁻¹ := by
      simpa [hw1] using htk_eq
    have htct : t * c * t⁻¹ = c := by
      have htc : t * c = c * t := hcommKC t htK c hc
      rw [htc]
      group
    have htbt : t * b * t⁻¹ = k⁻¹ * c := by
      rw [hbc]
      calc
        t * (k * c) * t⁻¹ = (t * k * t⁻¹) * (t * c * t⁻¹) := by group
        _ = k⁻¹ * c := by rw [hkt, htct]
    have htbt_b : t * b * t⁻¹ * b = c * c := by
      rw [htbt, hbc]
      calc
        (k⁻¹ * c) * (k * c) = k⁻¹ * (c * k) * c := by group
        _ = k⁻¹ * (k * c) * c := by rw [hck.eq]
        _ = c * c := by group
    have hc2_mem : c * c ∈ B ⊔ T := by
      have htX : t ∈ B ⊔ T := Subgroup.mem_sup_right htT
      have hbX : b ∈ B ⊔ T := Subgroup.mem_sup_left hb
      have hmem_sup : t * b * t⁻¹ * b ∈ B ⊔ T :=
        (B ⊔ T).mul_mem
          ((B ⊔ T).mul_mem ((B ⊔ T).mul_mem htX hbX) ((B ⊔ T).inv_mem htX)) hbX
      rwa [htbt_b] at hmem_sup
    have hcBT : c ∈ B ⊔ T := by
      obtain ⟨m, hm⟩ := hBo
      have hc_eq : c = (c * c) ^ (m + 1) := by
        calc
          c = c ^ Nat.card B * c := by rw [hcn, one_mul]
          _ = c ^ (Nat.card B + 1) := (pow_succ c (Nat.card B)).symm
          _ = c ^ (2 * (m + 1)) := by
            congr 1
            omega
          _ = (c * c) ^ (m + 1) := by rw [pow_mul, pow_two]
      rw [hc_eq]
      exact Subgroup.pow_mem _ hc2_mem _
    have hBnorm : B ≤ Subgroup.normalizer (Subgroup.zpowers c : Set X) := by
      intro b' hb'
      obtain ⟨k', hk', c', hc', hb'c', hk'n, hc'n⟩ :=
        exists_mul_centralizer_pow_card_eq_one hBo hBKC hZ2 hb'
      have hb'b : b' * b = b * b' := by
        simpa using congrArg Subtype.val
          (hBc.is_comm.comm (⟨b', hb'⟩ : ↥B) (⟨b, hb⟩ : ↥B))
      have hb'conj : b' * b * b'⁻¹ = b := by
        calc
          b' * b * b'⁻¹ = (b * b') * b'⁻¹ := by rw [hb'b]
          _ = b := by group
      have hc'k : Commute c' k := (hcommKC k hk c' hc').symm
      have hb'k_eq : b' * k * b'⁻¹ = k' * k * k'⁻¹ := by
        rw [hb'c']
        calc
          (k' * c') * k * (k' * c')⁻¹ = k' * (c' * k * c'⁻¹) * k'⁻¹ := by group
          _ = k' * k * k'⁻¹ := by rw [hc'k.eq]; group
      let d := c' * c * c'⁻¹
      have hdC : d ∈ C := by
        have hc'N : c' ∈ Subgroup.normalizer (C : Set X) :=
          (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set X)) hc'
        exact (Subgroup.mem_normalizer_iff.mp hc'N c).mp hc
      have hk'_fix_C : ∀ x ∈ C, k' * x * k'⁻¹ = x := by
        intro x hx
        have hxk : k' * x = x * k' := Subgroup.mem_centralizer_iff.mp hx k' hk'
        rw [hxk]
        group
      have hb'c_eq : b' * c * b'⁻¹ = d := by
        rw [hb'c']
        calc
          (k' * c') * c * (k' * c')⁻¹ = k' * (c' * c * c'⁻¹) * k'⁻¹ := by group
          _ = k' * d * k'⁻¹ := by rw [show d = c' * c * c'⁻¹ from rfl]
          _ = d := hk'_fix_C d hdC
      have hprod_eq : (k' * k * k'⁻¹) * d = k * c := by
        calc
          (k' * k * k'⁻¹) * d = (b' * k * b'⁻¹) * (b' * c * b'⁻¹) := by
            rw [hb'k_eq, hb'c_eq]
          _ = b' * (k * c) * b'⁻¹ := by group
          _ = b' * b * b'⁻¹ := by rw [← hbc]
          _ = b := hb'conj
          _ = k * c := hbc
      let z := c * d⁻¹
      have hkzk_eq : k' * k * k'⁻¹ = k * z := by
        have h := congrArg (fun x => x * d⁻¹) hprod_eq
        simpa [z, mul_assoc] using h
      have hzK : z ∈ K := by
        have hz_eq : z = k⁻¹ * (k' * k * k'⁻¹) := by
          rw [hkzk_eq]
          group
        rw [hz_eq]
        exact K.mul_mem (K.inv_mem hk)
          (K.mul_mem (K.mul_mem hk' hk) (K.inv_mem hk'))
      have hzC : z ∈ C := C.mul_mem hc (C.inv_mem hdC)
      have hz2 : z * z = 1 := by
        simpa [pow_two] using hZ2 z hzK hzC
      have hk'z : Commute k' z := hcommKC k' hk' z hzC
      have hcomm_eq : ⁅k', k⁆ = z := by
        rw [commutatorElement_def]
        calc
          k' * k * k'⁻¹ * k⁻¹ = (k * z) * k⁻¹ := by rw [hkzk_eq]
          _ = z := by
            have hzk : k * z = z * k := Subgroup.mem_centralizer_iff.mp hzC k hk
            rw [hzk]
            group
      have hcomm_k'comm : Commute k' ⁅k', k⁆ := by
        rw [hcomm_eq]
        exact hk'z
      have hcomm2 : ⁅k', k⁆ * ⁅k', k⁆ = 1 := by
        rw [hcomm_eq]
        simpa [pow_two] using hZ2 z hzK hzC
      have hk'odd : Odd (orderOf k') :=
        Odd.of_dvd_nat hBo (orderOf_dvd_of_pow_eq_one hk'n)
      have hcomm_k'k : Commute k' k :=
        commute_of_commute_commutatorElement_of_odd hcomm_k'comm hcomm2 hk'odd
      have hb'k_comm : Commute b' k := by
        rw [hb'c']
        exact hcomm_k'k.mul_left hc'k
      have hb'b_comm : Commute b' b := hb'b
      have hc_eq_k : c = k⁻¹ * b := by
        rw [hbc]
        group
      have hb'c_comm : b' * c = c * b' := by
        rw [hc_eq_k]
        exact (hb'k_comm.inv_right.mul_right hb'b_comm).eq
      apply Subgroup.mem_normalizer_iff.mpr
      intro x
      have hcomm : Commute b' c := hb'c_comm
      constructor
      · intro hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [(hcomm.zpow_right j).eq]
        simpa [mul_assoc] using Subgroup.zpow_mem_zpowers c j
      · intro hx
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hconj := congrArg (fun y => b'⁻¹ * y * b') hj
        have hxpow : c ^ j = x := by
          simpa [← (hcomm.zpow_right j).eq, mul_assoc] using hconj
        rw [← hxpow]
        exact Subgroup.zpow_mem_zpowers c j
    have hzpc_le : Subgroup.zpowers c ≤ B ⊔ T := (Subgroup.zpowers_le).mpr hcBT
    have hzpc_odd : Odd (Nat.card (Subgroup.zpowers c)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hBo (orderOf_dvd_of_pow_eq_one hcn)
    have hcB : c ∈ B :=
      (CFSG.ASVolI.burnsideA315y_le_of_odd (X := X) (B := B) (S := T)
        (N := Subgroup.zpowers c) hBo hTp hperm hzpc_le hBnorm hzpc_odd)
        (Subgroup.mem_zpowers c)
    have hkB : k ∈ B := by
      have hk_eq : k = b * c⁻¹ := by
        rw [hbc]
        group
      rw [hk_eq]
      exact B.mul_mem hb (B.inv_mem hcB)
    rw [hbc]
    exact Subgroup.mul_mem_sup ⟨hkB, hk⟩ ⟨hcB, hc⟩
  · exact sup_le inf_le_left inf_le_left

end CFSG.GroupTheory

end
