module

public import CFSG.CGT.PushingUpLit.SolK.SevenFour

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

variable {d : ℕ}

theorem coreAct_pairVec_eq_iff {a b : Fin d} (hab : a ≠ b) (σ : Perm (Fin d)) :
    coreAct d σ (pairVec a b) = pairVec a b ↔
      ∀ x, σ x ∈ ({a, b} : Finset (Fin d)) ↔ x ∈ ({a, b} : Finset (Fin d)) := by
  rw [coreAct_eq_iff, vsupp_pairVec hab]
  exact mem_setStab

theorem exists_fixed_ne_of_order_four {s : Perm (Fin d)} (hs4 : s * s * (s * s) = 1)
    (hs2 : s * s ≠ 1) :
    ∃ v : ↥(coreMod d), coreAct d (s * s) v = v ∧ coreAct d s v ≠ v := by
  obtain ⟨a, ha⟩ : ∃ a, (s * s) a ≠ a := by
    by_contra h
    push Not at h
    exact hs2 (Equiv.ext h)
  have hu : ∀ y, (s * s) ((s * s) y) = y := fun y => by
    rw [← mul_apply, hs4]
    rfl
  have h1 : s a ≠ a := fun h => ha (by rw [mul_apply, h, h])
  have h2 : s a ≠ (s * s) a := fun h => h1 (by
    rw [mul_apply] at h
    exact (s.injective h).symm)
  refine ⟨pairVec a ((s * s) a), ?_, ?_⟩
  · rw [coreAct_pairVec_eq_iff (Ne.symm ha)]
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · right
        have := congrArg (fun y => (s * s) y) h
        simp only [hu] at this
        exact this
      · left
        exact (s * s).injective h
    · rintro (h | h)
      · right
        rw [h]
      · left
        rw [h, hu]
  · intro hv
    rw [coreAct_pairVec_eq_iff (Ne.symm ha)] at hv
    have := (hv a).2 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact h1 h
    · exact h2 h

theorem exists_third_fixed (hd : Odd d) {s : Perm (Fin d)} (hs : s * s = 1) {a b : Fin d}
    (hab : a ≠ b) (ha : s a = a) (hb : s b = b) : ∃ p : Fin d, s p = p ∧ p ≠ a ∧ p ≠ b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) (σ := s) (by
    rw [pow_one, pow_two]
    exact hs)
  by_contra hcon
  push Not at hcon
  have hsub : s.supportᶜ ⊆ {a, b} := by
    intro p hp
    have hp' : s p = p := by
      have := Finset.mem_compl.1 hp
      rwa [Equiv.Perm.mem_support, not_not] at this
    by_cases hpa : p = a
    · simp [hpa]
    · have := hcon p hp' hpa
      simp [this]
  have hge : ({a, b} : Finset (Fin d)) ⊆ s.supportᶜ := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    rcases hp with rfl | rfl
    · exact ha
    · exact hb
  have h2 : s.supportᶜ = {a, b} := Finset.Subset.antisymm hsub hge
  rw [h2, Finset.card_pair hab] at hmod
  have hodd : Odd (Fintype.card (Fin d)) := by simpa using hd
  have : Even (Fintype.card (Fin d)) := by
    rw [Nat.even_iff]
    exact hmod.symm
  exact (Nat.not_even_iff_odd.2 hodd) this

theorem exists_fixed_ne (hd : Odd d) (P : Subgroup (Perm (Fin d))) (hP : IsPGroup 2 P)
    (hcard : 3 ≤ Nat.card P) :
    ∃ σ ∈ P, ∃ τ ∈ P, σ ≠ 1 ∧ τ ≠ 1 ∧
      ∃ v : ↥(coreMod d), coreAct d σ v = v ∧ coreAct d τ v ≠ v := by
  classical
  by_cases hexp : ∃ σ ∈ P, σ * σ ≠ 1
  ·
    obtain ⟨σ, hσP, hσ⟩ := hexp
    obtain ⟨k, hk⟩ := hP ⟨σ, hσP⟩
    have hk' : σ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    have hj2 : 2 ≤ j := by
      by_contra hlt
      push Not at hlt
      apply hσ
      have : orderOf σ ∣ 2 := by
        rw [hj]
        exact (Nat.pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by simp)
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.1 this
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    set s := σ ^ (2 ^ i) with hs
    have hos : orderOf s = 4 := by
      rw [hs, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega)),
        hj, pow_add]
      exact Nat.mul_div_cancel_left 4 (by positivity)
    have hs4 : s * s * (s * s) = 1 := by
      have := pow_orderOf_eq_one s
      rw [hos] at this
      have h4 : s ^ 4 = s * s * (s * s) := by simp [pow_succ, mul_assoc]
      rw [← h4]
      exact this
    have hss : s * s ≠ 1 := by
      intro h
      have h2 : s ^ 2 = 1 := by rw [pow_two]; exact h
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hos] at this
      omega
    have hsP : s ∈ P := P.pow_mem hσP _
    obtain ⟨v, hv1, hv2⟩ := exists_fixed_ne_of_order_four hs4 hss
    refine ⟨s * s, P.mul_mem hsP hsP, s, hsP, hss, fun h => hss (by rw [h, mul_one]), v, hv1, hv2⟩
  ·
    push Not at hexp
    obtain ⟨t₁, ht₁P, ht₁⟩ : ∃ t ∈ P, t ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : P = ⊥ := by
        ext x
        simp only [Subgroup.mem_bot]
        exact ⟨fun hx => h x hx, fun hx => hx ▸ P.one_mem⟩
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    obtain ⟨a, ha⟩ : ∃ a, t₁ a ≠ a := by
      by_contra h
      push Not at h
      exact ht₁ (Equiv.ext h)
    set b := t₁ a with hb
    have hab : a ≠ b := fun h => ha h.symm
    have ht₁sq : ∀ x, t₁ (t₁ x) = x := fun x => by
      rw [← mul_apply, hexp t₁ ht₁P]
      rfl
    by_cases hall : ∀ t ∈ P, t ∈ setStab ({a, b} : Finset (Fin d))
    ·
      let g : ↥P → ↥({a, b} : Finset (Fin d)) := fun u =>
        ⟨(u : Perm (Fin d)) a, ((mem_setStab.1 (hall u u.2)) a).2 (by simp)⟩
      have hcard' : Fintype.card ↥({a, b} : Finset (Fin d)) < Fintype.card ↥P := by
        rw [Fintype.card_coe, Finset.card_pair hab, ← Nat.card_eq_fintype_card]
        omega
      obtain ⟨u, u', hne, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard'
      have hua : (u : Perm (Fin d)) a = (u' : Perm (Fin d)) a := congrArg Subtype.val hg
      set s : Perm (Fin d) := (u : Perm (Fin d))⁻¹ * (u' : Perm (Fin d)) with hs
      have hsP : s ∈ P := P.mul_mem (P.inv_mem u.2) u'.2
      have hs1 : s ≠ 1 := by
        intro h
        apply hne
        apply Subtype.ext
        have : (u' : Perm (Fin d)) = u := by
          have h1 : (u : Perm (Fin d)) * s = u' := by rw [hs]; group
          rw [← h1, h, mul_one]
        exact this.symm
      have hsa : s a = a := by
        rw [hs, mul_apply, ← hua]
        simp
      have hsb : s b = b := by
        have hsb' := (mem_setStab.1 (hall s hsP)) b
        have : s b ∈ ({a, b} : Finset (Fin d)) := hsb'.2 (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact absurd (s.injective (h.trans hsa.symm)) (Ne.symm hab)
        · exact h
      obtain ⟨p, hsp, hpa, hpb⟩ := exists_third_fixed hd (hexp s hsP) hab hsa hsb
      refine ⟨s, hsP, t₁, ht₁P, hs1, ht₁, pairVec a p, ?_, ?_⟩
      · rw [coreAct_pairVec_eq_iff (Ne.symm hpa)]
        intro x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · left
            exact s.injective (h.trans hsa.symm)
          · right
            exact s.injective (h.trans hsp.symm)
        · rintro (h | h)
          · left
            rw [h, hsa]
          · right
            rw [h, hsp]
      · intro hv
        rw [coreAct_pairVec_eq_iff (Ne.symm hpa)] at hv
        have := (hv a).2 (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact ha h
        · exact hpb h.symm
    · push Not at hall
      obtain ⟨t, htP, ht⟩ := hall
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact ht (Subgroup.one_mem _)
      refine ⟨t₁, ht₁P, t, htP, ht₁, ht1, pairVec a b, ?_, ?_⟩
      · rw [coreAct_pairVec_eq_iff hab]
        intro x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · right
            have := congrArg t₁ h
            rw [ht₁sq] at this
            rw [this]
          · left
            have := congrArg t₁ h
            rw [ht₁sq] at this
            rw [this, hb, ht₁sq]
        · rintro (h | h)
          · right
            rw [h]
          · left
            rw [h, hb, ht₁sq]
      · intro hv
        apply ht
        rw [coreAct_pairVec_eq_iff hab] at hv
        exact mem_setStab.2 hv

end CFSG.CGT.PushingUpLit.SolK
