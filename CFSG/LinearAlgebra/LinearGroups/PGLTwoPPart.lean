module

public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.Dihedral.Glauberman.DicksonMaxList
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LinearGroups

open Subgroup
open scoped MatrixGroups Pointwise

private theorem exists_injective_pgl2_psl2 (p : ℕ) [Fact p.Prime] (k : Type*) [Field k]
    [Finite k] [CharP k p] :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (f : ℕ)
      (φ : PGL(Fin 2, k) →* BenderSuzuki.MatrixGroups.PSL2MatrixGroup E),
      Nat.card E = p ^ f ∧ Function.Injective φ := by
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  let e := MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := E))
  refine ⟨E, inferInstance, inferInstance, 2 * f,
    e.symm.toMonoidHom.comp ((pglExtend k E).codRestrict _ (pglExtend_mem_range_toPGL hsq)),
    hEp, ?_⟩
  intro a b hab
  exact pglExtend_injective (congrArg Subtype.val (e.symm.injective hab))

private theorem six_dvd_sq_sub_one {q : ℕ} (h2 : ¬ 2 ∣ q) (h3 : ¬ 3 ∣ q) : 6 ∣ q ^ 2 - 1 := by
  obtain ⟨t, ht | ht⟩ : ∃ t, q = 6 * t + 1 ∨ q = 6 * t + 5 := ⟨q / 6, by omega⟩
  · subst ht
    exact ⟨6 * t ^ 2 + 2 * t, by
      rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]; ring⟩
  · subst ht
    exact ⟨6 * t ^ 2 + 10 * t + 4, by
      rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]; ring⟩


theorem not_dvd_card_of_comm_permutes_noncyclic_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {k : Type*} [Field k] [Finite k] [CharP k p] {Y S : Subgroup PGL(Fin 2, k)}
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (_hYo : Odd (Nat.card Y)) (hS : IsPGroup 2 S)
    (hSc : ¬ IsCyclic S)
    (hYS : (Y : Set PGL(Fin 2, k)) * (S : Set PGL(Fin 2, k)) =
      (S : Set PGL(Fin 2, k)) * (Y : Set PGL(Fin 2, k))) :
    ¬ p ∣ Nat.card Y := by
  classical
  intro hpY
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  obtain ⟨E, _, _, f, φ, hE, hφ⟩ := exists_injective_pgl2_psl2 p k
  have : Finite PGL(Fin 2, k) := Finite.of_injective φ hφ
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpY
  have hu1 : (u : PGL(Fin 2, k)) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
  have hφu : φ u ≠ 1 := fun h => by
    have : (u : PGL(Fin 2, k)) = 1 := hφ (h.trans (map_one φ).symm)
    rw [← Subgroup.orderOf_coe, this, orderOf_one] at hu
    exact hp.one_lt.ne hu
  have hYp : IsPGroup p Y := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro q hq hqY
    by_contra hqp
    have := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqY
    have h1 : φ x = 1 :=
      Glauberman.Dickson.psl2_eq_one_of_commute hE
        (Commute.map (show Commute (x : PGL(Fin 2, k)) u from hYc _ x.2 _ u.2) φ)
        (by
          rw [orderOf_injective φ hφ, Subgroup.orderOf_coe, hx]
          exact (Nat.coprime_primes hq hp).2 hqp)
        (by rw [← map_pow, hu1, map_one]) hφu
    have : (x : PGL(Fin 2, k)) = 1 := hφ (h1.trans (map_one φ).symm)
    rw [← Subgroup.orderOf_coe, this, orderOf_one] at hx
    exact hq.one_lt.ne hx
  obtain ⟨a, ha⟩ := hYp.exists_card_eq
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card S) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ hcop2
  have hcardH : Nat.card (Y ⊔ S : Subgroup PGL(Fin 2, k)) = p ^ a * 2 ^ b := by
    rw [Quasithin.H23P4.card_eq_mul_of_coe_eq_mul
      (Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hYS) (inf_eq_bot_of_coprime hcop), ha, hb]
  set H' := (Y ⊔ S).map φ
  have hH' : Nat.card H' = p ^ a * 2 ^ b := by
    rw [Subgroup.card_map_of_injective hφ, hcardH]
  have hSH : S.map φ ≤ H' := Subgroup.map_mono le_sup_right
  have hSS : IsPGroup 2 (S.map φ) := hS.map φ
  have hpH : p ∣ Nat.card H' := by
    rw [hH']
    exact (ha ▸ hpY).mul_right _
  have hp3' : ¬ 3 ∣ p ^ a * 2 ^ b := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have h3 : ¬ 3 ∣ Nat.card H' := hH' ▸ hp3'
  have h6 : ∀ m : ℕ, 6 ∣ (p ^ m) ^ 2 - 1 := fun m =>
    six_dvd_sq_sub_one
      (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        (Nat.prime_two.dvd_of_dvd_pow h)).symm)
      (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm)
  have hq1 : 1 ≤ Nat.card E := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hE
  have hpE : p ∣ Nat.card E := hE ▸ dvd_pow_self p hf0
  have hnot : ∀ n : ℕ, Nat.Coprime (Nat.card E) n → ¬ p ∣ n := fun n hn hpn =>
    hp.not_dvd_one (hn.gcd_eq_one ▸ Nat.dvd_gcd hpE hpn)
  suffices hcyc : IsCyclic (S.map φ) from
    hSc (isCyclic_of_injective (S.equivMapOfInjective φ hφ).toMonoidHom (MulEquiv.injective _))
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hE H' with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩
  ·
    have hSp : IsPGroup p (S.map φ) := (@IsElementaryAbelian.isPGroup p H' _ hel).to_le hSH
    rw [disjoint_self.1 (hSp.disjoint_of_coprime hSS hcop2)]
    infer_instance
  ·
    exact Subgroup.isCyclic_of_le hSH
  ·
    rw [hcard] at hpH
    have hpz : p ∣ z := ((Nat.Prime.dvd_mul hp).1 hpH).resolve_left fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rcases hz with hz | hz
    · exact (hnot _ (CFSG.Glauberman.Dickson.hq_coprime_split_order _ hq1) (hpz.trans hz)).elim
    · exact (hnot _ (CFSG.Glauberman.Dickson.hq_coprime_nonsplit_order _ hq1)
        (hpz.trans hz)).elim
  ·
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  ·
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  ·
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  ·
    have := hN
    have hNp : IsPGroup p N := @IsElementaryAbelian.isPGroup p N _ hNel
    let π := QuotientGroup.mk' N
    have hπ : Function.Surjective (π.comp C.subtype) := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
      have hh : h ∈ ((N ⊔ C : Subgroup H') : Set H') := by
        rw [hsup]
        exact Subgroup.mem_top h
      rw [Subgroup.normal_mul] at hh
      obtain ⟨n, hn, c, hc, rfl⟩ := Set.mem_mul.1 hh
      refine ⟨⟨c, hc⟩, ?_⟩
      show QuotientGroup.mk' N c = QuotientGroup.mk' N (n * c)
      rw [map_mul, QuotientGroup.mk'_apply N n, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
    have : IsCyclic (H' ⧸ N) := isCyclic_of_surjective _ hπ
    let ψ : S.map φ →* H' := Subgroup.inclusion hSH
    refine isCyclic_of_injective (π.comp ψ) ?_
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsN : ψ s ∈ N := (QuotientGroup.eq_one_iff _).1 hs
    have hos : orderOf s = orderOf (⟨ψ s, hsN⟩ : N) := by
      rw [Subgroup.orderOf_mk (ψ s) hsN, orderOf_injective ψ (Subgroup.inclusion_injective hSH)]
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 hNp ⟨ψ s, hsN⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hSS s
    rw [← hos] at hi
    rw [hi] at hj
    have hi0 : i = 0 := by
      by_contra hi0
      have : p ∣ 2 ^ j := hj ▸ dvd_pow_self p hi0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  ·
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula (GaloisField p m)
      ⟨p, m, hp, hp.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hm, GaloisField.card p m hm⟩,
      GaloisField.card p m hm]
    obtain ⟨j, hj⟩ := h6 m
    rw [hj, show p ^ m * (6 * j) = 2 * (3 * (p ^ m * j)) by ring,
      Nat.mul_div_cancel_left _ two_pos]
    exact dvd_mul_right 3 _
  ·
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.pgl2_card_formula (GaloisField p m),
      GaloisField.card p m hm]
    exact dvd_mul_of_dvd_right ((by norm_num : 3 ∣ 6).trans (h6 m)) _

theorem eq_one_of_pow_eq_one_of_normalizes_noncyclic_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {k : Type*} [Field k] [Finite k] [CharP k p] {S : Subgroup PGL(Fin 2, k)}
    (hS : IsPGroup 2 S) (hSc : ¬ IsCyclic S) {y : PGL(Fin 2, k)} (hy : y ^ p = 1)
    (hyS : y ∈ normalizer (S : Set PGL(Fin 2, k))) : y = 1 := by
  by_contra hy1
  have hp := (Fact.out : p.Prime)
  have hoy : orderOf y = p := orderOf_eq_prime hy hy1
  have hle : zpowers y ≤ normalizer (S : Set PGL(Fin 2, k)) := (zpowers_le).2 hyS
  refine not_dvd_card_of_comm_permutes_noncyclic_two hp5 (Y := zpowers y) (S := S)
    (fun a ha b hb => ?_) ?_ hS hSc ?_ (by rw [Nat.card_zpowers, hoy])
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self y i j).eq
  · rw [Nat.card_zpowers, hoy]
    exact hp.odd_of_ne_two (by omega)
  · rw [← coe_mul_of_left_le_normalizer_right _ _ hle,
      ← coe_mul_of_right_le_normalizer_left _ _ hle, sup_comm]

end CFSG.LinearGroups

end
