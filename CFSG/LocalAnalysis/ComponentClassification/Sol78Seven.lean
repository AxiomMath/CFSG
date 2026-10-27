module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.Sol78

open Equiv Subgroup
open scoped Pointwise

@[expose] def dtA : alternatingGroup (Fin 7) :=
  ⟨swap 0 2 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def dtB : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem cycleType_eq_of_orderOf_eq_two {w : alternatingGroup (Fin 7)} (hw : orderOf w = 2) :
    (w : Perm (Fin 7)).cycleType = Multiset.replicate 2 2 := by
  have hw' : orderOf (w : Perm (Fin 7)) = 2 := by rw [Subgroup.orderOf_coe, hw]
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := (w : Perm (Fin 7)))
    (by rw [hw']; exact Nat.prime_two)
  rw [hw'] at hn
  have hsum := Perm.sum_cycleType (w : Perm (Fin 7))
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : (w : Perm (Fin 7)).support.card ≤ 7 := by
    simpa using Finset.card_le_univ (w : Perm (Fin 7)).support
  have hsign := Perm.sign_of_cycleType (w : Perm (Fin 7))
  rw [hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    (Perm.mem_alternatingGroup.mp w.2)] at hsign
  have hev : Even ((n + 1) * 2 + (n + 1)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hn1 : n + 1 = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rw [hn, hn1]

theorem orderOf_dtA : orderOf dtA = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem orderOf_dtB : orderOf dtB = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem isConj_dtA {w : alternatingGroup (Fin 7)} (hw : orderOf w = 2) : IsConj dtA w := by
  apply alternatingGroup.isConj_of
  · rw [Perm.isConj_iff_cycleType_eq, cycleType_eq_of_orderOf_eq_two orderOf_dtA,
      cycleType_eq_of_orderOf_eq_two hw]
  · decide

theorem orderOf_dtA_mul_dtB_sq : orderOf ((dtA * dtB) ^ 2) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem le_card_closure_dtA_dtB : 8 ≤ Nat.card (closure ({dtA, dtB} : Set _)) := by
  set D := closure ({dtA, dtB} : Set (alternatingGroup (Fin 7))) with hD
  have haD : dtA ∈ D := subset_closure (by simp)
  have hbD : dtB ∈ D := subset_closure (by simp)
  have habD : dtA * dtB ∈ D := mul_mem haD hbD
  have hord : orderOf (dtA * dtB) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := dtA * dtB) (by decide) (by decide)
    simpa using h
  set H := zpowers (dtA * dtB) with hH
  have hHD : H ≤ D := zpowers_le.mpr habD
  have hHcard : Nat.card H = 4 := by rw [hH, Nat.card_zpowers, hord]
  have hnot : dtA ∉ H := by
    rw [hH, mem_zpowers_iff]
    rintro ⟨k, hk⟩
    have hk' : (dtA * dtB) ^ (k % 4) = dtA := by
      have h1 : (dtA * dtB) ^ (k % 4) = (dtA * dtB) ^ k := by
        have h4 : (4 : ℤ) = (orderOf (dtA * dtB) : ℤ) := by rw [hord]; rfl
        rw [h4]
        exact zpow_mod_orderOf _ _
      rw [h1, hk]
    have hk4 : 0 ≤ k % 4 ∧ k % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _
      (by norm_num)⟩
    obtain ⟨j, hj, hjk⟩ : ∃ j : ℕ, j < 4 ∧ (k % 4 : ℤ) = j :=
      ⟨(k % 4).toNat, by omega, by omega⟩
    rw [hjk, zpow_natCast] at hk'
    interval_cases j <;> revert hk' <;> decide
  have hlt : H < D := lt_of_le_of_ne hHD fun h => hnot (h ▸ haD)
  have hdvd : Nat.card H ∣ Nat.card D := Subgroup.card_dvd_of_le hHD
  have hne : Nat.card H ≠ Nat.card D := fun h =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge hHD h.symm.le)
  obtain ⟨c, hc⟩ := hdvd
  rw [hHcard] at hc hne
  have hpos : 0 < Nat.card D := Nat.card_pos
  rcases c with _ | _ | c
  · omega
  · omega
  · omega

theorem card_closure_pair_le_eight {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 4 = 1) :
    Nat.card (closure ({a, b} : Set G)) ≤ 8 := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ha])
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hb])
  set H := zpowers (a * b) with hH
  set K := zpowers a with hK
  have hHcard : Nat.card H ≤ 4 := by
    rw [hH, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hab
  have hKcard : Nat.card K ≤ 2 := by
    rw [hK, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ha
  have hKN : K ≤ normalizer (H : Set G) := by
    rw [hK, zpowers_le, mem_normalizer_iff_map_conj_eq, hH, MonoidHom.map_zpowers]
    have h1 : (MulAut.conj a : G →* G) (a * b) = (a * b)⁻¹ := by
      change a * (a * b) * a⁻¹ = (a * b)⁻¹
      rw [hainv, mul_inv_rev, hainv, hbinv, ← mul_assoc, ← pow_two, ha, one_mul]
    rw [h1, zpowers_inv]
  have hle : closure ({a, b} : Set G) ≤ K ⊔ H := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_sup_left (mem_zpowers _)
    · have : x = a⁻¹ * (a * x) := by group
      rw [this]
      exact mul_mem (mem_sup_left (inv_mem (mem_zpowers _))) (mem_sup_right (mem_zpowers _))
  have hcoe : ((K ⊔ H : Subgroup G) : Set G) = (K : Set G) * (H : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K H hKN
  have hsurj : Function.Surjective (fun p : K × H => (⟨(p.1 : G) * p.2, by
      rw [← SetLike.mem_coe, hcoe]
      exact Set.mul_mem_mul p.1.2 p.2.2⟩ : (K ⊔ H : Subgroup G))) := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, hcoe] at hx
    obtain ⟨k, hk, h, hh, rfl⟩ := hx
    exact ⟨(⟨k, hk⟩, ⟨h, hh⟩), rfl⟩
  calc Nat.card (closure ({a, b} : Set G)) ≤ Nat.card (K ⊔ H : Subgroup G) :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card (K × H) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card K * Nat.card H := Nat.card_prod _ _
    _ ≤ 2 * 4 := Nat.mul_le_mul hKcard hHcard
    _ = 8 := by norm_num

theorem card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

section DoubleCover

variable {E : Type*} [Group E] [Finite E]

theorem mem_center_of_orderOf_eq_two_of_alternating_seven [Group.IsPerfect E]
    (hZ : Nat.card (center E) = 2) (e : E ⧸ center E ≃* alternatingGroup (Fin 7)) {u : E}
    (hu : orderOf u = 2) : u ∈ center E := by
  classical
  by_contra huZ
  set Z := center E with hZdef
  set π : E →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : ∀ x, π x = 1 ↔ x ∈ Z := by
    intro x
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZsq : ∀ c ∈ Z, c ^ 2 = 1 := by
    intro c hc
    have h := orderOf_dvd_natCard (⟨c, hc⟩ : Z)
    rw [hZ, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hwu : orderOf (π u) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hu2, map_one]
    · intro h
      exact huZ ((hker u).mp h)
  have hlift : ∀ d : alternatingGroup (Fin 7), orderOf d = 2 → ∀ d' : E, π d' = d →
      d' ^ 2 = 1 := by
    intro d hd d' hd'
    obtain ⟨c, hc⟩ := isConj_iff.mp ((isConj_dtA hwu).symm.trans (isConj_dtA hd))
    obtain ⟨g, rfl⟩ := hπs c
    set v := g * u * g⁻¹ with hv
    have hv2 : v ^ 2 = 1 := by
      rw [hv, pow_two, show g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group,
        ← pow_two, hu2, mul_one, mul_inv_cancel]
    have hvd : π v = d := by rw [hv, map_mul, map_mul, map_inv, hc]
    have hk : d' * v⁻¹ ∈ Z := by
      rw [← hker, map_mul, map_inv, hvd, hd', mul_inv_cancel]
    have hcomm : Commute (d' * v⁻¹) v := ((mem_center_iff.mp hk) v).symm
    have hd'eq : d' = (d' * v⁻¹) * v := by group
    rw [hd'eq, hcomm.mul_pow, hZsq _ hk, hv2, mul_one]
  obtain ⟨a', ha'⟩ := hπs dtA
  obtain ⟨b', hb'⟩ := hπs dtB
  have ha2 : a' ^ 2 = 1 := hlift dtA orderOf_dtA a' ha'
  have hb2 : b' ^ 2 = 1 := hlift dtB orderOf_dtB b' hb'
  have hab4 : (a' * b') ^ 4 = 1 := by
    have h := hlift _ orderOf_dtA_mul_dtB_sq ((a' * b') ^ 2) (by rw [map_pow, map_mul, ha', hb'])
    rw [← pow_mul] at h
    exact h
  set P₀ := closure ({a', b'} : Set E) with hP₀
  have hP₀le : Nat.card P₀ ≤ 8 := card_closure_pair_le_eight ha2 hb2 hab4
  have hmap : P₀.map π = closure ({dtA, dtB} : Set _) := by
    rw [hP₀, MonoidHom.map_closure, Set.image_pair, ha', hb']
  have hP₀ge : 8 ≤ Nat.card (P₀.map π) := hmap ▸ le_card_closure_dtA_dtB
  have hbij : Function.Bijective (π.subgroupMap P₀) :=
    (MonoidHom.subgroupMap_surjective π P₀).bijective_of_nat_card_le (hP₀le.trans hP₀ge)
  have hP₀card : Nat.card P₀ = 8 := le_antisymm hP₀le
    (hP₀ge.trans (Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective π P₀)))
  have hP₀Z : ∀ x ∈ P₀, x ∈ Z → x = 1 := by
    intro x hxP hxZ
    have h1 : π.subgroupMap P₀ ⟨x, hxP⟩ = π.subgroupMap P₀ 1 := by
      apply Subtype.ext
      change π x = π 1
      rw [(hker x).mpr hxZ, map_one]
    exact congrArg Subtype.val (hbij.1 h1)
  have : Nontrivial Z := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZ]
    norm_num
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := exists_ne (1 : Z)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := hZsq z hzZ
  have hzP₀ : z ∉ P₀ := fun h => hz1' (hP₀Z z h hzZ)
  set P := P₀ ⊔ Z with hPdef
  have hP₀P : P₀ ≤ P := le_sup_left
  have hZP : Z ≤ P := le_sup_right
  have hcoe : (P : Set E) = (P₀ : Set E) * (Z : Set E) := Subgroup.mul_normal P₀ Z
  have hPcard : Nat.card P = 16 := by
    have hbij' : Function.Bijective (fun p : P₀ × Z => (⟨(p.1 : E) * p.2, by
        rw [← SetLike.mem_coe, hcoe]
        exact Set.mul_mem_mul p.1.2 p.2.2⟩ : P)) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨p, hp⟩, ⟨c, hc⟩⟩ ⟨⟨p', hp'⟩, ⟨c', hc'⟩⟩ h
        have h1 : p * c = p' * c' := congrArg Subtype.val h
        have h2 : p'⁻¹ * p = c' * c⁻¹ := by
          calc p'⁻¹ * p = p'⁻¹ * (p * c) * c⁻¹ := by group
            _ = p'⁻¹ * (p' * c') * c⁻¹ := by rw [h1]
            _ = c' * c⁻¹ := by group
        have h3 : p'⁻¹ * p = 1 :=
          hP₀Z _ (mul_mem (inv_mem hp') hp) (h2 ▸ mul_mem hc' (inv_mem hc))
        have hpp : p = p' := by
          calc p = p' * (p'⁻¹ * p) := by group
            _ = p' := by rw [h3, mul_one]
        subst hpp
        have hcc : c = c' := mul_left_cancel h1
        subst hcc
        rfl
      · rintro ⟨x, hx⟩
        rw [← SetLike.mem_coe, hcoe] at hx
        obtain ⟨p, hp, c, hc, rfl⟩ := hx
        exact ⟨(⟨p, hp⟩, ⟨c, hc⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij'), Nat.card_prod, hP₀card, hZ]
  have hEcard : Nat.card E = 5040 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZ,
      Nat.card_congr e.toEquiv, card_alternating_seven]
  have hPidx : P.index = 315 := by
    have h := Subgroup.card_mul_index P
    rw [hPcard, hEcard] at h
    omega
  have hP₀idx : (P₀.subgroupOf P).index = 2 := by
    have h := Subgroup.card_mul_index (P₀.subgroupOf P)
    rw [Nat.card_congr (subgroupOfEquivOfLe hP₀P).toEquiv, hP₀card, hPcard] at h
    omega
  have : (P₀.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hP₀idx
  have hQcard : Nat.card (P ⧸ P₀.subgroupOf P) = 2 := by
    rw [← Subgroup.index, hP₀idx]
  have : IsCyclic (P ⧸ P₀.subgroupOf P) := isCyclic_of_prime_card (p := 2) hQcard
  let : CommGroup (P ⧸ P₀.subgroupOf P) := IsCyclic.commGroup
  set ϕ : P →* P ⧸ P₀.subgroupOf P := QuotientGroup.mk' (P₀.subgroupOf P) with hϕ
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc := (mem_center_iff.mp (pow_mem hzZ k)) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have htr := MonoidHom.transfer_eq_pow ϕ z hkey
  have hz315 : z ^ P.index = z := by
    rw [hPidx, show 315 = 2 * 157 + 1 by norm_num, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have htriv : ϕ.transfer z = 1 := by
    have hcomm := Abelianization.commutator_subset_ker (ϕ.transfer)
    have hzc : z ∈ commutator E := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact mem_top z
    exact hcomm hzc
  rw [htr, hϕ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at htriv
  change z ^ P.index ∈ P₀ at htriv
  rw [hz315] at htriv
  exact hzP₀ htriv

theorem pRank_two_le_one_of_alternating_seven [Group.IsPerfect E]
    (hZ : Nat.card (center E) = 2) (e : E ⧸ center E ≃* alternatingGroup (Fin 7)) :
    CFSG.pRank 2 E ≤ 1 := by
  classical
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hsub : A ≤ center E := by
    intro a ha
    have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    · exact mem_center_of_orderOf_eq_two_of_alternating_seven hZ e
        (orderOf_eq_prime h2 ha1)
  have hle : Nat.card A ≤ 2 := hZ ▸ Subgroup.card_le_of_le hsub
  rw [hcard] at hle
  by_contra hr
  have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end DoubleCover

end CFSG.ComponentClassification.Sol78
