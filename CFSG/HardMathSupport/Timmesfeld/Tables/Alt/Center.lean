module

public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Alt

open Equiv

theorem isPGroup_two_center_of_eight_le {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    {n : ℕ} (hn : 8 ≤ n) (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) :
    IsPGroup 2 (Subgroup.center L) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup L := Subgroup.center L with hMdef
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 M))
  set T : Subgroup L := (P : Subgroup M).map M.subtype with hTdef
  have hTM : T ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTn : T.Normal := Subgroup.normal_of_le_center hTM
  set q : L →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' M) with hqdef
  have hqsurj : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective M)
  have hqker : q.ker = M := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hTq : T ≤ q.ker := hqker ▸ hTM
  set η : L ⧸ T →* alternatingGroup (Fin (m + 2)) := QuotientGroup.lift T q hTq with hηdef
  have hη : Function.Surjective η := by
    intro s
    obtain ⟨x, hx⟩ := hqsurj s
    exact ⟨QuotientGroup.mk x, hx⟩
  have hηK : η.ker = M.map (QuotientGroup.mk' T) := by
    rw [hηdef, QuotientGroup.ker_lift, hqker]
  have hcentral : η.ker ≤ Subgroup.center (L ⧸ T) := by
    rw [hηK]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective T y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx u]
  have : Group.IsPerfect (L ⧸ T) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective T)
  have h1 : Nat.card L = Nat.card (L ⧸ T) * Nat.card T :=
    T.card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (L ⧸ T) = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [η.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have h3 : Nat.card L = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card M := by
    rw [M.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv]
  have h4 : Nat.card T = Nat.card P := Subgroup.card_map_of_injective M.subtype_injective
  set a := (Nat.card M).factorization 2 with ha
  have h5 : Nat.card P = 2 ^ a := Sylow.card_eq_multiplicity P
  have hM : Nat.card M = Nat.card η.ker * 2 ^ a := by
    have e1 := h3.symm.trans h1
    rw [h2, h4, h5, mul_assoc] at e1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e1
  have hodd : Odd (Nat.card η.ker) := by
    have hc := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := M)).ne'
    have e1 : Nat.card M / 2 ^ a = Nat.card η.ker := by
      rw [hM, Nat.mul_div_cancel _ (pow_pos two_pos _)]
    rw [e1] at hc
    exact Nat.coprime_two_left.mp hc
  have hK1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hη hcentral hodd
  rw [hK1, one_mul] at hM
  exact IsPGroup.of_card hM

theorem pow_prime_eq_one_of_card_eq_sq {Q : Type*} [Group Q] {p : ℕ} [hp : Fact p.Prime]
    (hQ : Nat.card Q = p ^ 2) (hcyc : ¬ IsCyclic Q) (x : Q) : x ^ p = 1 := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact pow_ne_zero 2 hp.out.ne_zero)
  obtain ⟨m, hm, hx⟩ := (Nat.dvd_prime_pow hp.out).1 (hQ ▸ orderOf_dvd_natCard x)
  interval_cases m
  · rw [pow_zero, orderOf_eq_one_iff] at hx
    rw [hx, one_pow]
  · rw [pow_one] at hx
    rw [← hx, pow_orderOf_eq_one]
  · exact absurd (isCyclic_of_orderOf_eq_card x (hx.trans hQ.symm)) hcyc

theorem factorization_center_le {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] (p : ℕ)
    [hp : Fact p.Prime] (hfac : (Nat.card (L ⧸ Subgroup.center L)).factorization p ≤ 2) :
    (Nat.card (Subgroup.center L)).factorization p ≤ 1 ∧
      ((Nat.card (L ⧸ Subgroup.center L)).factorization p ≤ 1 →
        (Nat.card (Subgroup.center L)).factorization p = 0) := by
  let f : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' _
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hker : f.ker = Subgroup.center L := QuotientGroup.ker_mk' _
  obtain ⟨C⟩ : Nonempty (Sylow p f.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow p (L ⧸ Subgroup.center L)) := inferInstance
  set vZ := (Nat.card (Subgroup.center L)).factorization p with hvZ
  set v := (Nat.card (L ⧸ Subgroup.center L)).factorization p with hv
  have hC : Nat.card (C : Subgroup f.ker) = p ^ vZ := by
    rw [C.card_eq_multiplicity, hvZ,
      Nat.card_congr (MulEquiv.subgroupCongr hker).toEquiv]
  have hQ : Nat.card (Q : Subgroup (L ⧸ Subgroup.center L)) = p ^ v := Q.card_eq_multiplicity
  have hcyc_of_le : v ≤ 1 → IsCyclic (Q : Subgroup (L ⧸ Subgroup.center L)) := by
    intro h
    interval_cases hv0 : v
    · rw [pow_zero, Nat.card_eq_one_iff_unique] at hQ
      obtain ⟨hs, -⟩ := hQ
      infer_instance
    · rw [pow_one] at hQ
      exact isCyclic_of_prime_card hQ
  have hbot_zero : (C : Subgroup f.ker) = ⊥ → vZ = 0 := by
    intro h
    rw [h, Subgroup.card_bot] at hC
    exact (Nat.pow_right_injective hp.out.two_le (hC.symm.trans (pow_zero p).symm))
  refine ⟨?_, fun h1 => ?_⟩
  · by_cases hcyc : IsCyclic (Q : Subgroup (L ⧸ Subgroup.center L))
    · have := hbot_zero
        ((CFSG.ShultStronglyClosedTI.small_sylow_central_cover_bound f hsurj hker.le C Q).1 hcyc)
      omega
    · have hv2 : v = 2 := by
        by_contra hne
        exact hcyc (hcyc_of_le (by omega))
      have hQ2 : Nat.card (Q : Subgroup (L ⧸ Subgroup.center L)) = p ^ 2 := by rw [hQ, hv2]
      have helem : CFSG.Open.IsElemAbelian p (Q : Subgroup (L ⧸ Subgroup.center L)) :=
        ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ2, fun x hx =>
          congrArg Subtype.val (pow_prime_eq_one_of_card_eq_sq hQ2 hcyc ⟨x, hx⟩)⟩
      have hle := ((CFSG.ShultStronglyClosedTI.small_sylow_central_cover_bound f hsurj
        hker.le C Q).2 helem hQ2).2
      rw [hC] at hle
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (by simpa using hle)
  · exact hbot_zero
      ((CFSG.ShultStronglyClosedTI.small_sylow_central_cover_bound f hsurj hker.le C Q).1
        (hcyc_of_le h1))

theorem card_alternating_dvd {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) :
    Nat.card (alternatingGroup (Fin n)) ∣ 2520 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  interval_cases n <;> decide

theorem card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem factorization_alternating_le_two {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (Nat.card (alternatingGroup (Fin n))).factorization p ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hne : Nat.card (alternatingGroup (Fin n)) ≠ 0 := Nat.card_pos.ne'
  have h3 : p ^ 3 ∣ Nat.card (alternatingGroup (Fin n)) :=
    (hp.pow_dvd_iff_le_factorization hne).2 hcon
  have h4 : p ^ 3 ∣ 2520 := h3.trans (card_alternating_dvd h5 h7)
  have h6 : p ^ 3 ≤ 2520 := Nat.le_of_dvd (by norm_num) h4
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp13 : p ≤ 13 := by
    by_contra hc
    push Not at hc
    have : 14 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases p <;> omega

theorem factorization_alternating_le_one {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : p ≠ 3 ∨ n = 5) :
    (Nat.card (alternatingGroup (Fin n))).factorization p ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hne : Nat.card (alternatingGroup (Fin n)) ≠ 0 := Nat.card_pos.ne'
  have h4 : p ^ 2 ∣ Nat.card (alternatingGroup (Fin n)) :=
    (hp.pow_dvd_iff_le_factorization hne).2 hcon
  rcases h3 with h3 | rfl
  · have h4' : p ^ 2 ∣ 2520 := h4.trans (card_alternating_dvd h5 h7)
    have h6 : p ^ 2 ≤ 2520 := Nat.le_of_dvd (by norm_num) h4'
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hp50 : p ≤ 50 := by
      by_contra hc
      push Not at hc
      have : 51 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  · rw [card_alternating_five] at h4
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h6 : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h4
    have hp8 : p ≤ 7 := by
      by_contra hc
      push Not at hc
      have : 8 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    interval_cases p <;> omega

theorem center_facts {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {n : ℕ} (hn : 5 ≤ n)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (Nat.card (Subgroup.center L)).factorization p ≤ 1 ∧
      (p ∣ Nat.card (Subgroup.center L) → p = 3 ∧ (n = 6 ∨ n = 7)) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hn8 : 8 ≤ n
  · obtain ⟨k, hk⟩ := (isPGroup_two_center_of_eight_le hn8 e).exists_card_eq
    have hnd : ¬ p ∣ Nat.card (Subgroup.center L) := by
      intro hd
      rw [hk] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have h0 := Nat.factorization_eq_zero_of_not_dvd hnd
    exact ⟨by omega, fun h => absurd h hnd⟩
  · have h7 : n ≤ 7 := by omega
    have hcard : Nat.card (L ⧸ Subgroup.center L) = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr e.toEquiv
    have key := factorization_center_le (L := L) p (by
      rw [hcard]
      exact factorization_alternating_le_two hn h7 hp hp2)
    refine ⟨key.1, fun hdvd => ?_⟩
    by_contra hcon
    have hne : Nat.card (Subgroup.center L) ≠ 0 := Nat.card_pos.ne'
    have h3 : p ≠ 3 ∨ n = 5 := by
      by_cases hp3 : p = 3
      · right
        by_contra h5
        exact hcon ⟨hp3, by omega⟩
      · exact Or.inl hp3
    have h0 := key.2 (by
      rw [hcard]
      exact factorization_alternating_le_one hn h7 hp hp2 h3)
    have := (hp.dvd_iff_one_le_factorization hne).1 hdvd
    omega

end CFSG.HardMathSupport.Timmesfeld.Tables.Alt
