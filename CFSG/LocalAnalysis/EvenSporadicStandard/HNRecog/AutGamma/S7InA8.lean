module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog

private lemma dvd_six_of_dvd_twelve_of_not_four {b : ℕ} (h : b ∣ 12) (h4 : ¬ 4 ∣ b) :
    b ∣ 6 := by
  have hb : b ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases b <;> first
    | (exfalso; norm_num at h4; done)
    | (exfalso; norm_num at h; done)
    | norm_num

private lemma dvd_four_of_dvd_twelve_of_not_three {b : ℕ} (h : b ∣ 12) (h3 : ¬ 3 ∣ b) :
    b ∣ 4 := by
  have hb : b ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases b <;> first
    | (exfalso; norm_num at h3; done)
    | (exfalso; norm_num at h; done)
    | norm_num

private lemma twelve_dvd_of_lcm_eq_twelve_of_dvd_two {m k : ℕ} (hlcm : lcm m k = 12)
    (hm : m ∣ 2) : 12 ∣ k := by
  have hk12 : k ∣ 12 := hlcm ▸ dvd_lcm_right m k
  have hm6 : m ∣ 6 := hm.trans (by norm_num)
  have hm4 : m ∣ 4 := hm.trans (by norm_num)
  have h4k : 4 ∣ k := by
    by_contra h4
    have hk6 : k ∣ 6 := dvd_six_of_dvd_twelve_of_not_four hk12 h4
    have hle : lcm m k ∣ 6 := lcm_dvd hm6 hk6
    rw [hlcm] at hle
    have : (12 : ℕ) ≤ 6 := Nat.le_of_dvd (by norm_num) hle
    omega
  have h3k : 3 ∣ k := by
    by_contra h3
    have hk4 : k ∣ 4 := dvd_four_of_dvd_twelve_of_not_three hk12 h3
    have hle : lcm m k ∣ 4 := lcm_dvd hm4 hk4
    rw [hlcm] at hle
    have : (12 : ℕ) ≤ 4 := Nat.le_of_dvd (by norm_num) hle
    omega
  have h : lcm 4 3 ∣ k := lcm_dvd h4k h3k
  rwa [show lcm 4 3 = 12 from by decide] at h

private lemma orderOf_ne_twelve_of_sign_one (σ : Equiv.Perm (Fin 8)) (hσ : orderOf σ = 12)
    (hsign : σ.sign = 1) : False := by
  have hlcm : σ.cycleType.lcm = 12 := by rw [Equiv.Perm.lcm_cycleType, hσ]
  have hdvd : ∀ b ∈ σ.cycleType, b ∣ 12 := fun b hb => by
    have := Equiv.Perm.dvd_of_mem_cycleType hb
    rwa [hσ] at this
  have hsum_le : σ.cycleType.sum ≤ 8 := by simpa using σ.sum_cycleType_le
  have h2le : ∀ b ∈ σ.cycleType, 2 ≤ b := fun b hb => Equiv.Perm.two_le_of_mem_cycleType hb
  have h4exists : ∃ b ∈ σ.cycleType, 4 ∣ b := by
    by_contra h
    push Not at h
    have h6 : ∀ b ∈ σ.cycleType, b ∣ 6 :=
      fun b hb => dvd_six_of_dvd_twelve_of_not_four (hdvd b hb) (h b hb)
    have hle : σ.cycleType.lcm ∣ 6 := Multiset.lcm_dvd.2 h6
    rw [hlcm] at hle
    have : (12 : ℕ) ≤ 6 := Nat.le_of_dvd (by norm_num) hle
    omega
  have h3exists : ∃ b ∈ σ.cycleType, 3 ∣ b := by
    by_contra h
    push Not at h
    have h4 : ∀ b ∈ σ.cycleType, b ∣ 4 :=
      fun b hb => dvd_four_of_dvd_twelve_of_not_three (hdvd b hb) (h b hb)
    have hle : σ.cycleType.lcm ∣ 4 := Multiset.lcm_dvd.2 h4
    rw [hlcm] at hle
    have : (12 : ℕ) ≤ 4 := Nat.le_of_dvd (by norm_num) hle
    omega
  obtain ⟨b4, hb4mem, hb4⟩ := h4exists
  obtain ⟨b3, hb3mem, hb3⟩ := h3exists
  have hb4le : b4 ≤ 8 := (Multiset.le_sum_of_mem hb4mem).trans hsum_le
  have hb4eq : b4 = 4 := by
    have hb4dvd : b4 ∣ 12 := hdvd b4 hb4mem
    interval_cases b4 <;> first
      | (exfalso; norm_num at hb4dvd; done)
      | (exfalso; norm_num at hb4; done)
      | norm_num
  have hb3le : b3 ≤ 8 := (Multiset.le_sum_of_mem hb3mem).trans hsum_le
  have hb3eq : b3 = 3 := by
    have hb3dvd : b3 ∣ 12 := hdvd b3 hb3mem
    have hb3ne6 : b3 ≠ 6 := by
      intro h
      have h4mem : 4 ∈ σ.cycleType := by rwa [hb4eq] at hb4mem
      have h6mem : 6 ∈ σ.cycleType := by rwa [h] at hb3mem
      have hsum_eq : σ.cycleType.sum = 4 + (σ.cycleType.erase 4).sum := by
        conv_lhs => rw [← Multiset.cons_erase h4mem]
        rw [Multiset.sum_cons]
      have h6mem' : 6 ∈ σ.cycleType.erase 4 :=
        (Multiset.mem_erase_of_ne (by norm_num)).2 h6mem
      have hle : 6 ≤ (σ.cycleType.erase 4).sum := Multiset.le_sum_of_mem h6mem'
      omega
    interval_cases b3 <;> first
      | (exfalso; norm_num at hb3dvd; done)
      | (exfalso; norm_num at hb3; done)
      | (exfalso; norm_num at hb3ne6; done)
      | norm_num
  have h4mem : 4 ∈ σ.cycleType := by rwa [hb4eq] at hb4mem
  have h3mem : 3 ∈ σ.cycleType := by rwa [hb3eq] at hb3mem
  have h3mem' : 3 ∈ σ.cycleType.erase 4 :=
    (Multiset.mem_erase_of_ne (by norm_num)).2 h3mem
  set u := (σ.cycleType.erase 4).erase 3 with hu_def
  have hs_decomp : σ.cycleType = 4 ::ₘ 3 ::ₘ u := by
    rw [← Multiset.cons_erase h4mem]
    congr 1
    rw [hu_def]
    exact (Multiset.cons_erase h3mem').symm
  have hempty : u = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have ha' : a ∈ (σ.cycleType.erase 4).erase 3 := by rwa [hu_def] at ha
    have has : a ∈ σ.cycleType := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ha')
    have h2a : 2 ≤ a := h2le a has
    have hle : 2 ≤ u.sum := h2a.trans (Multiset.le_sum_of_mem ha)
    have hsum_decomp : σ.cycleType.sum = 7 + u.sum := by
      rw [hs_decomp]
      simp only [Multiset.sum_cons]
      omega
    omega
  have hsum7 : σ.cycleType.sum = 7 := by
    rw [hs_decomp, hempty]
    simp
  have hcard2 : σ.cycleType.card = 2 := by
    rw [hs_decomp, hempty]
    simp
  have hsign' := Equiv.Perm.sign_of_cycleType σ
  rw [hsum7, hcard2] at hsign'
  rw [hsign] at hsign'
  have hpow : (-1 : ℤˣ) ^ (7 + 2) = -1 := by decide
  rw [hpow] at hsign'
  exact absurd hsign' (by decide)

private lemma orderOf_ne_twelve_alternatingGroup (α : alternatingGroup (Fin 8)) :
    orderOf α ≠ 12 := by
  intro hα
  have hσ : orderOf (α : Equiv.Perm (Fin 8)) = 12 := by
    rw [orderOf_submonoid]; exact hα
  exact orderOf_ne_twelve_of_sign_one (α : Equiv.Perm (Fin 8)) hσ
    (Equiv.Perm.mem_alternatingGroup.mp α.2)

theorem sym7_not_injective_of_isShapeTwoTwoTimesA8 {X : Type*} [Group X]
    (hX : IsShapeTwoTwoTimesA8 X) (f : Equiv.Perm (Fin 7) →* X) : ¬ Function.Injective f := by
  intro hf
  obtain ⟨e⟩ := hX
  let ψ : Equiv.Perm (Fin 7) →* Elem2 2 × alternatingGroup (Fin 8) := e.toMonoidHom.comp f
  have hψ : Function.Injective ψ := fun a b hab => hf (e.injective hab)
  let g : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5, 6]
  have hg12 : g ^ 12 = 1 := by decide +kernel
  have hg6 : g ^ 6 ≠ 1 := by decide +kernel
  have hg4 : g ^ 4 ≠ 1 := by decide +kernel
  have horder_g : orderOf g = 12 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hg12 ?_
    intro p hp hpd
    have hpd' : p ∣ 2 * 6 := by simpa using hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd' with h2 | h6
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      simpa using hg6
    · have h6' : p ∣ 2 * 3 := by simpa using h6
      rcases (Nat.Prime.dvd_mul hp).1 h6' with h2 | h3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
        simpa using hg6
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
        simpa using hg4
  have horderψ : orderOf (ψ g) = 12 := by
    rw [orderOf_injective ψ hψ g, horder_g]
  have hprod : (orderOf (ψ g).1).lcm (orderOf (ψ g).2) = 12 := by
    rw [← Prod.orderOf, horderψ]
  have hv2 : (ψ g).1 ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.ext
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero ((ψ g).1.toAdd i)
  have hm : orderOf (ψ g).1 ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv2
  have hk : 12 ∣ orderOf (ψ g).2 := twelve_dvd_of_lcm_eq_twelve_of_dvd_two hprod hm
  have hk12 : orderOf (ψ g).2 ∣ 12 :=
    hprod ▸ dvd_lcm_right (orderOf (ψ g).1) (orderOf (ψ g).2)
  have hkeq : orderOf (ψ g).2 = 12 := (Nat.dvd_antisymm hk hk12).symm
  exact orderOf_ne_twelve_alternatingGroup (ψ g).2 hkeq

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
