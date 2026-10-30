module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Vocab
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

private lemma card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private lemma prime_dvd_20160 {p : ℕ} (hp : p.Prime) (h : p ∣ 20160) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 6 * (3 ^ 2 * (5 * 7)) := by
    rwa [show (20160 : ℕ) = 2 ^ 6 * (3 ^ 2 * (5 * 7)) by norm_num] at h
  rcases hp.dvd_mul.mp h' with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
    · rcases hp.dvd_mul.mp h with h5 | h7
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5)))
      · exact Or.inr (Or.inr (Or.inr
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7)))

theorem gh23_exists_order_five_or_seven {H : Subgroup (Equiv.Perm (Fin 8))}
    (hH : H ≤ alternatingGroup (Fin 8)) (hns : ¬ IsSolvable ↥H) :
    ∃ x ∈ H, orderOf x = 5 ∨ orderOf x = 7 := by
  classical
  by_contra hc
  push Not at hc
  have hn5 : ¬ 5 ∣ Nat.card ↥H := by
    rintro hdvd
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 (G := ↥H) hdvd
    exact (hc (x : Equiv.Perm (Fin 8)) x.2).1 (by rw [Subgroup.orderOf_coe, hx])
  have hn7 : ¬ 7 ∣ Nat.card ↥H := by
    rintro hdvd
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 (G := ↥H) hdvd
    exact (hc (x : Equiv.Perm (Fin 8)) x.2).2 (by rw [Subgroup.orderOf_coe, hx])
  have hcard20160 : Nat.card ↥H ∣ 20160 := by
    have h := Subgroup.card_dvd_of_le hH
    rwa [card_alt8] at h
  have hsupp : (Nat.card ↥H).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ Nat.card ↥H := Nat.dvd_of_mem_primeFactors hp
    rcases prime_dvd_20160 hpp (hpdvd.trans hcard20160) with h | h | h | h
    · subst h; simp
    · subst h; simp
    · exfalso
      rw [h] at hpdvd
      exact hn5 hpdvd
    · exfalso
      rw [h] at hpdvd
      exact hn7 hpdvd
  have hcard : Nat.card ↥H =
      2 ^ (Nat.card ↥H).factorization 2 * 3 ^ (Nat.card ↥H).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self Nat.card_pos.ne']
    rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _]
    simp
  exact hns (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard))

private lemma cycleType_eq_singleton_of_orderOf {x : Equiv.Perm (Fin 8)} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : orderOf x = p) : x.cycleType = {p} := by
  have hmem : ∀ n ∈ x.cycleType, n = p := by
    intro n hn
    have hdvd : n ∣ p := by
      rw [← hx]
      exact Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · exact h
  have hne : x.cycleType ≠ 0 := by
    intro h0
    have hlcm : x.cycleType.lcm = 1 := by rw [h0, Multiset.lcm_zero]
    rw [Equiv.Perm.lcm_cycleType, hx] at hlcm
    exact hp.ne_one hlcm
  have hcardpos : Multiset.card x.cycleType ≠ 0 := by
    intro hc0
    exact hne (Multiset.card_eq_zero.mp hc0)
  have hrepr : x.cycleType = Multiset.replicate (Multiset.card x.cycleType) p :=
    Multiset.eq_replicate_card.mpr hmem
  have hsum : x.cycleType.sum = Multiset.card x.cycleType * p := by
    rw [hrepr, Multiset.sum_replicate, Multiset.card_replicate]
    simp
  have hle : Multiset.card x.cycleType * p ≤ 8 := by
    have h := Equiv.Perm.sum_cycleType_le x
    rw [hsum, Fintype.card_fin] at h
    exact h
  have hcardle : Multiset.card x.cycleType ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ Multiset.card x.cycleType := by omega
    have hmul : 2 * p ≤ Multiset.card x.cycleType * p := Nat.mul_le_mul h2 le_rfl
    omega
  have hcard1 : Multiset.card x.cycleType = 1 := by omega
  rw [hrepr, hcard1]
  simp

theorem gh23_isConj_g5 {x : Equiv.Perm (Fin 8)} (hx : orderOf x = 5) : IsConj x gh23g5 := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, gh23g5_cycleType]
  exact cycleType_eq_singleton_of_orderOf (p := 5) (by norm_num) (by norm_num) hx

theorem gh23_isConj_g7 {x : Equiv.Perm (Fin 8)} (hx : orderOf x = 7) : IsConj x gh23g7 := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, gh23g7_cycleType]
  exact cycleType_eq_singleton_of_orderOf (p := 7) (by norm_num) (by norm_num) hx

private theorem NoNormalTwo.map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {H : Subgroup G} (h : NoNormalTwo H) : NoNormalTwo (H.map e.toMonoidHom) := by
  intro N' hN' hnorm' hp'
  have hN : N'.comap e.toMonoidHom ≤ H := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hN' hx
    rwa [← e.injective hax]
  have hp : IsPGroup 2 (N'.comap e.toMonoidHom) :=
    hp'.comap_of_injective e.toMonoidHom e.injective
  have hnorm : H ≤ Subgroup.normalizer (N'.comap e.toMonoidHom : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.mp (hnorm' ⟨a, ha, rfl⟩) (e x)
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] at h ⊢
    exact h
  have hbot := h _ hN hnorm hp
  rw [eq_bot_iff]
  intro y hy
  have hy' : e.symm y ∈ N'.comap e.toMonoidHom := by
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  rw [hbot, Subgroup.mem_bot] at hy'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply y, hy', map_one]

theorem NoNormalTwo.conj {G : Type*} [Group G] {H : Subgroup G} (h : NoNormalTwo H) (c : G) :
    NoNormalTwo (H.map (MulAut.conj c).toMonoidHom) :=
  NoNormalTwo.map_mulEquiv (MulAut.conj c) h

theorem alt8Classification_of_rooted (h : Alt8Rooted) : Alt8Classification := by
  intro H hH hns hNN
  have key : ∀ (c x : Equiv.Perm (Fin 8)), x ∈ H →
      (c * x * c⁻¹ = gh23g5 ∨ c * x * c⁻¹ = gh23g7) → GH23Concl ↥H := by
    intro c x hxH hcase
    let H' : Subgroup (Equiv.Perm (Fin 8)) := H.map (MulAut.conj c).toMonoidHom
    have hH' : H' ≤ alternatingGroup (Fin 8) := by
      intro y hy
      obtain ⟨z, hzH, hyz⟩ := hy
      rw [← hyz]
      have hmem : c * z * c⁻¹ ∈ alternatingGroup (Fin 8) :=
        (show (alternatingGroup (Fin 8)).Normal from inferInstance).conj_mem z (hH hzH) c
      exact hmem
    have hgH' : gh23g5 ∈ H' ∨ gh23g7 ∈ H' := by
      rcases hcase with hc | hc
      · left
        rw [← hc]
        exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hxH
      · right
        rw [← hc]
        exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hxH
    let e : ↥H ≃* ↥H' :=
      Subgroup.equivMapOfInjective H (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    have hns' : ¬ IsSolvable ↥H' := by
      intro hsol
      haveI : Group.IsSolvable ↥H' := hsol
      exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    have hNN' : NoNormalTwo H' := NoNormalTwo.conj hNN c
    have hres : GH23Concl ↥H' := h H' hH' hgH' hns' hNN'
    exact GH23Concl.of_mulEquiv e hres
  obtain ⟨x, hxH, hx | hx⟩ := gh23_exists_order_five_or_seven hH hns
  · obtain ⟨c, hc⟩ := isConj_iff.mp (gh23_isConj_g5 hx)
    exact key c x hxH (Or.inl hc)
  · obtain ⟨c, hc⟩ := isConj_iff.mp (gh23_isConj_g7 hx)
    exact key c x hxH (Or.inr hc)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
