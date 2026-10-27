module

public import CFSG.CGT.T75N.OddCycBender
public import CFSG.CGT.Timmesfeld75.Inputs214
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.Timmesfeld.Bridge.Asc72Width

public section

namespace CFSG.CGT.T75N

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

theorem benderCenterInput : BenderCenterInput := by
  classical
  intro K _ _ T hT hTbot hTnn hK hmodel
  have hB : IsBenderGroup (K ⧸ Subgroup.center K) := by
    rcases hmodel with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact .isPSL2 f hf e
    · exact .isSuzuki a ha e
  have hS : Setup K (classD T) := by
    refine ⟨?_, ⟨fun d hd => classD_orderOf hT hd, fun d hd e he => orderOf_mul_classD hT hd he⟩,
      ?_⟩
    · exact (single_class_or_normal hT hTbot).resolve_right hTnn
    · rw [closure_classD_eq_normalClosure, hK]
  have hodd : ∀ z ∈ Subgroup.center K, ∀ p : ℕ, p.Prime → orderOf z = p → p = 2 := by
    intro z hz p hpp hzp
    by_contra hp2
    have : Fact p.Prime := ⟨hpp⟩
    set E : Subgroup K := Subgroup.zpowers z with hE
    have hEc : E ≤ Subgroup.center K := (Subgroup.zpowers_le).2 hz
    have hEp : IsPGroup p E := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    obtain ⟨P⟩ : Nonempty (Sylow p K) := inferInstance
    let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' _
    have hPcyc : IsCyclic (P.map π) :=
      isCyclic_of_isPGroup_benderModel hmodel hp2 (P.map π) (P.isPGroup'.map π)
    let g : (P : Subgroup K) →* (P.map π : Subgroup (K ⧸ Subgroup.center K)) :=
      (π.comp (P : Subgroup K).subtype).codRestrict (P.map π)
        (fun x => Subgroup.mem_map_of_mem π x.2)
    have hker : g.ker ≤ Subgroup.center (P : Subgroup K) := by
      intro x hx
      have h1 : π x = 1 := congrArg Subtype.val hx
      have h2 : (x : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
    have hcomm : IsMulCommutative (P : Subgroup K) :=
      g.isMulCommutative_of_isCyclic_of_ker_le_center hker
    have hinf := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup P hcomm hEc hEp
    have hcard : Nat.card (K ⧸ commutator K) ≤ 2 := hS.index_commutator_le_two
    have hsq : ∀ x : K ⧸ commutator K, x ^ 2 = 1 := by
      intro x
      have hpos : 0 < Nat.card (K ⧸ commutator K) := Nat.card_pos
      have : x ^ Nat.card (K ⧸ commutator K) = 1 := pow_card_eq_one'
      interval_cases h : Nat.card (K ⧸ commutator K)
      · have h1 : x = 1 := by simpa using this
        rw [h1, one_pow]
      · exact this
    have hzp1 : ((z : K) : K ⧸ commutator K) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, ← hzp, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have hz1 : ((z : K) : K ⧸ commutator K) = 1 := by
      have := pow_gcd_eq_one.2 ⟨hzp1, hsq _⟩
      have hcop : Nat.gcd p 2 = 1 :=
        (Nat.Coprime.symm ((Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm hp2)))
      rwa [hcop, pow_one] at this
    have hzK : z ∈ commutator K := (QuotientGroup.eq_one_iff _).1 hz1
    have : z ∈ E ⊓ commutator K := Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers z, hzK⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hzp
    exact hpp.one_lt.ne hzp
  have hZ2 : IsPGroup 2 (Subgroup.center K) := by
    intro z
    have hn : orderOf (z : K) ≠ 0 := (orderOf_pos _).ne'
    have hpow : orderOf (z : K) = 2 ^ (orderOf (z : K)).primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hn
      intro d hd hdvd
      have := orderOf_pow_orderOf_div hn hdvd
      exact hodd _ (Subgroup.pow_mem _ z.2 _) d hd this
    refine ⟨(orderOf (z : K)).primeFactorsList.length, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hpow]
    exact pow_orderOf_eq_one _
  have hinf := inf_commutator_eq_bot_of_isBenderGroup hS (E := Subgroup.center K) le_rfl hZ2 hB
  have hnsolv : ¬ Group.IsSolvable K := by
    intro hsolv
    have : Group.IsSolvable (K ⧸ Subgroup.center K) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center K))
    obtain ⟨x, y, hxy⟩ := IsBenderGroup.exists_not_commute hB
    have : Nontrivial (K ⧸ Subgroup.center K) :=
      ⟨⟨x, y, fun h => hxy (h ▸ Commute.refl _)⟩⟩
    exact absurd (IsBenderGroup.commutator_eq_top hB)
      (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial _))
  obtain ⟨u, hu, v, hv, huv, hc⟩ := hS.exists_commute_of_not_isSolvable hnsolv
  have huvD := mul_mem_classD_of_commute hT hu hv hc.eq huv
  have h1 : Abelianization.of (u * v) = Abelianization.of u := hS.abelianization_eq huvD hu
  have h2 : Abelianization.of v = Abelianization.of u := hS.abelianization_eq hv hu
  rw [map_mul, h2] at h1
  have h3 : Abelianization.of u = 1 := by
    have := mul_eq_left.1 h1
    exact this
  have hsub : classD T ⊆ (commutator K : Set K) := by
    intro x hx
    have h4 := hS.abelianization_eq hx hu
    rw [h3] at h4
    have h5 : x ∈ (Abelianization.of : K →* Abelianization K).ker := h4
    rwa [Abelianization.ker_of] at h5
  have htop := hS.eq_top_of_subset (commutator K) hsub
  rw [htop, inf_top_eq] at hinf
  exact hinf


end CFSG.CGT.T75N
