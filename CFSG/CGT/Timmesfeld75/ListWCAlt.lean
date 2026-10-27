module

public import CFSG.CGT.Timmesfeld75.ListWCBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open Equiv.Perm

theorem card_eq_four_of_two_part_eight {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 8 * m) (σ : G) (hσ4 : σ ^ 4 = 1) (hσ2 : σ ^ 2 ≠ 1) {T : Subgroup G}
    (hT : IsElemAbelian 2 T) (h4 : 4 ≤ Nat.card T) : Nat.card T = 4 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_two_of_isElemAbelian hT)
  have hdvd : 2 ^ n ∣ 8 * m := hn ▸ hG ▸ Subgroup.card_subgroup_dvd_card T
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hm)
  have h8 : 2 ^ n ∣ 2 ^ 3 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  have hn3 : n ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h8
  have hn2 : 2 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
  · simpa using hn
  exfalso
  have hidx : T.index = m := by
    have h := T.card_mul_index
    rw [hn, hG] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  let P : Sylow 2 G := (isPGroup_two_of_isElemAbelian hT).toSylow (by
    rw [hidx]
    exact hm.not_two_dvd_nat)
  have hσ : IsPGroup 2 (Subgroup.zpowers σ) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hσ4)
  obtain ⟨Q, hQ⟩ := hσ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hσQ : σ ∈ conjSubgroup g T := by
    have h1 : σ ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers σ)
    rw [← hg, Sylow.coe_subgroup_smul] at h1
    exact h1
  apply hσ2
  rw [pow_two]
  exact elemAbelian_mul_self (isElemAbelian_conjSubgroup hT g) hσQ

theorem cycleType_eq_two_two_of_involution {k : ℕ} (hk : k ≤ 7) {x : Equiv.Perm (Fin k)}
    (hxA : x ∈ alternatingGroup (Fin k)) (hx : x * x = 1) (hx1 : x ≠ 1) :
    x.cycleType = {2, 2} := by
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  obtain ⟨n, hn⟩ := cycleType_prime_order (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : (n + 1) * 2 ≤ 7 := by
    have h1 := sum_cycleType_le x
    rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h1
    omega
  have hsign := (mem_alternatingGroup.1 hxA)
  rw [sign_of_cycleType, hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hn2 : n ≤ 2 := by omega
  interval_cases n
  · norm_num at hsign
  · rw [hn]
    rfl
  · norm_num at hsign

theorem isConj_of_involution_alt {k : ℕ} (hk6 : 6 ≤ k) (hk7 : k ≤ 7)
    {x y : alternatingGroup (Fin k)} (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1)
    (hy1 : y ≠ 1) : IsConj x y := by
  have hcx := cycleType_eq_two_two_of_involution hk7 x.2 (congrArg Subtype.val hx)
    (fun h => hx1 (Subtype.ext h))
  have hcy := cycleType_eq_two_two_of_involution hk7 y.2 (congrArg Subtype.val hy)
    (fun h => hy1 (Subtype.ext h))
  apply alternatingGroup.isConj_of (isConj_iff_cycleType_eq.2 (hcx.trans hcy.symm))
  rw [← sum_cycleType, hcx, Fintype.card_fin]
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  omega

@[expose] def altFourCycle (k : ℕ) (hk : 6 ≤ k) : alternatingGroup (Fin k) :=
  ⟨(List.formPerm [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]) *
    List.formPerm [⟨4, by omega⟩, ⟨5, by omega⟩], by
    rw [mem_alternatingGroup, map_mul]
    rw [List.formPerm_cons_cons, List.formPerm_cons_cons, List.formPerm_cons_cons,
      List.formPerm_singleton, List.formPerm_cons_cons, List.formPerm_singleton]
    simp only [mul_one, map_mul]
    rw [sign_swap (by simp), sign_swap (by simp), sign_swap (by simp), sign_swap (by simp)]
    decide⟩


theorem altFourCycle_pow {k : ℕ} (hk6 : 6 ≤ k) (hk7 : k ≤ 7) :
    altFourCycle k hk6 ^ 4 = 1 ∧ altFourCycle k hk6 ^ 2 ≠ 1 := by
  interval_cases k <;> decide +revert

theorem exists_card_alt_eq_eight_mul {k : ℕ} (hk6 : 6 ≤ k) (hk7 : k ≤ 7) :
    ∃ m : ℕ, Odd m ∧ Nat.card (alternatingGroup (Fin k)) = 8 * m := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  interval_cases k
  · exact ⟨45, by decide, by decide⟩
  · exact ⟨315, by decide, by decide⟩

theorem alt67_wc {G : Type} [Group G] [Finite G] {k : ℕ} (hk6 : 6 ≤ k) (hk7 : k ≤ 7)
    (e : G ≃* alternatingGroup (Fin k)) {T : Subgroup G} (hT : IsWC T) (h4 : 4 ≤ Nat.card T) :
    Nat.card T = 4 ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  obtain ⟨m, hm, hcard⟩ := exists_card_alt_eq_eight_mul hk6 hk7
  obtain ⟨hσ4, hσ2⟩ := altFourCycle_pow hk6 hk7
  refine ⟨card_eq_four_of_two_part_eight hm (by rw [Nat.card_congr e.toEquiv, hcard])
    (e.symm (altFourCycle k hk6)) (by rw [← map_pow, hσ4, map_one]) (fun h => hσ2 ?_) hT.1 h4,
    hT.transitive_of_isConj fun x hx hx1 y hy hy1 => ?_⟩
  · rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  · have hx2 := elemAbelian_mul_self hT.1 hx
    have hy2 := elemAbelian_mul_self hT.1 hy
    have hc := isConj_of_involution_alt hk6 hk7 (x := e x) (y := e y)
      (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (e.injective (h.trans (map_one e).symm)))
      (by rw [← map_mul, hy2, map_one]) (fun h => hy1 (e.injective (h.trans (map_one e).symm)))
    simpa using MonoidHom.map_isConj e.symm.toMonoidHom hc

end CFSG.CGT.Timmesfeld75
