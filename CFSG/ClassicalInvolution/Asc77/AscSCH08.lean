module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank

theorem card_sl2 (K : Type*) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem exists_zpowers_sylow_sl2 {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hK : Nat.card K = ℓ ^ f) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrℓ : r ≠ ℓ) :
    ∃ t : SpecialLinearGroup (Fin 2) K,
      (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization r ≤
        (Nat.card (Subgroup.zpowers t)).factorization r := by
  classical
  obtain ⟨hmem, hDcard, hPcard, -, -, -, hcyc⟩ := CFSG.SectionRank.OddCover.odd_psl_two_sylow_data
    (K := K) hℓ2 hK
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r (SpecialLinearGroup (Fin 2) K)))
  let e := specialLinearGroupEquivStatedSL 2 K
  let qm : SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSL 2 K) :=
    (QuotientGroup.mk' _).comp e.toMonoidHom
  have hr2' : Odd r := (Fact.out : r.Prime).odd_of_ne_two hr2
  have hinj : Function.Injective
      (qm.comp (P : Subgroup (SpecialLinearGroup (Fin 2) K)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : qm x = 1 := hx
    have hxD : e (x : SpecialLinearGroup (Fin 2) K) ∈
        (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) :=
      (QuotientGroup.eq_one_iff _).1 hx1
    have hsq : (e (x : SpecialLinearGroup (Fin 2) K)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K))
        (x := ⟨e (x : SpecialLinearGroup (Fin 2) K), hxD⟩)
      rw [hDcard] at this
      exact congrArg Subtype.val this
    have hx2 : (x : SpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, hsq, map_one]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') x
    have h1 : orderOf (x : SpecialLinearGroup (Fin 2) K) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have h2 : orderOf (x : SpecialLinearGroup (Fin 2) K) ∣ r ^ k := by
      rw [Subgroup.orderOf_coe, hk]
    have hcop : Nat.Coprime (r ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes (Fact.out : r.Prime) Nat.prime_two).2 hr2)
    have h3 : orderOf (x : SpecialLinearGroup (Fin 2) K) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
    exact Subtype.ext (orderOf_eq_one_iff.1 h3)
  set Q : Subgroup (StatedProj (StatedSL 2 K)) :=
    (P : Subgroup (SpecialLinearGroup (Fin 2) K)).map qm
    with hQ
  have hcardQ : Nat.card Q = Nat.card P := by
    have : Q = (qm.comp (P : Subgroup (SpecialLinearGroup (Fin 2) K)).subtype).range := by
      rw [hQ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hq1 : 0 < Nat.card K := Nat.card_pos
  have hqsq : 2 ∣ Nat.card K ^ 2 - 1 := by
    have hodd : Odd (Nat.card K) := by
      rw [hK]; exact Odd.pow ((Fact.out : ℓ.Prime).odd_of_ne_two hℓ2)
    have : Odd (Nat.card K ^ 2) := hodd.pow
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by omega⟩
  obtain ⟨m, hm⟩ := hqsq
  have hmne : m ≠ 0 := by
    rintro rfl
    have h0 := card_sl2 K
    rw [hm] at h0
    have := Nat.card_pos (α := SpecialLinearGroup (Fin 2) K)
    omega
  have hPSL : Nat.card (StatedProj (StatedSL 2 K)) = Nat.card K * m := by
    rw [hPcard, ← hK, hm, Nat.mul_div_cancel_left _ two_pos]
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (2 * m) := by
    rw [card_sl2, hm]
  have hr2f : (2 : ℕ).factorization r = 0 := by
    rw [(Nat.prime_two).factorization]
    exact Finsupp.single_eq_of_ne hr2
  have hvals : (Nat.card (StatedProj (StatedSL 2 K))).factorization r =
      (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization r := by
    rw [hPSL, hSL, Nat.factorization_mul hq1.ne' hmne, Finsupp.add_apply,
      Nat.factorization_mul hq1.ne' (by omega), Finsupp.add_apply,
      Nat.factorization_mul (by norm_num) hmne, Finsupp.add_apply, hr2f, zero_add]
  have hcardP : Nat.card P = r ^ (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization r :=
    Sylow.card_eq_multiplicity P
  have hQcard : Nat.card Q = r ^ (Nat.card (StatedProj (StatedSL 2 K))).factorization r := by
    rw [hcardQ, hcardP, hvals]
  set R : Sylow r (StatedProj (StatedSL 2 K)) := Sylow.ofCard Q hQcard with hR
  have hRQ : (R : Subgroup (StatedProj (StatedSL 2 K))) = Q := Sylow.coe_ofCard Q hQcard
  have hQcyc : IsCyclic Q := by
    have := hcyc r (Fact.out : r.Prime) hr2 hrℓ R
    rwa [hRQ] at this
  have hPcyc : IsCyclic (P : Subgroup (SpecialLinearGroup (Fin 2) K)) := by
    let g : (P : Subgroup (SpecialLinearGroup (Fin 2) K)) →* Q :=
      (qm.comp (P : Subgroup (SpecialLinearGroup (Fin 2) K)).subtype).codRestrict Q
        (fun x => ⟨x, x.2, rfl⟩)
    exact isCyclic_of_injective g (fun x y hxy => hinj (congrArg Subtype.val hxy))
  obtain ⟨g, hg⟩ := hPcyc.exists_generator
  refine ⟨(g : SpecialLinearGroup (Fin 2) K), ?_⟩
  have hzp : Subgroup.zpowers (g : SpecialLinearGroup (Fin 2) K) =
      (P : Subgroup (SpecialLinearGroup (Fin 2) K)) := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]; exact g.2
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by
        have := congrArg Subtype.val hk
        simpa using this⟩
  rw [hzp]
  rw [hcardP, Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Fact.out,
    smul_eq_mul, mul_one]

end CFSG.ClassicalInvolution.Asc77.SCH
