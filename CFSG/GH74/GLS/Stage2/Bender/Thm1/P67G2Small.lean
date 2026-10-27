module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Inner

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem g2_three_odd_aut_inner (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3)
    (α : MulAut (adjointGroup Tag.G2 K)) (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range := by
  obtain ⟨g, σ, hασ⟩ := g2_odd_nf Nat.prime_three (by norm_num) (le_refl 1) K
    (by rw [hK]; norm_num) α hα
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := K) Nat.prime_three (le_refl 1) (by rw [hK]; norm_num)
  have hσ : σ = 1 := by
    have : Subsingleton (K ≃+* K) := Finite.card_le_one_iff_subsingleton.1 (by rw [hcard])
    exact Subsingleton.elim _ _
  rw [hασ, hσ, map_one, mul_one]
  exact ⟨g, rfl⟩

theorem g2_three_false_of_n2 {r : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3)
    (hr : r.Prime) {V Z : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h2 : N2Cfg (adjointGroup Tag.G2 K) r V Z) : False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)) :=
    mulAut_conj_injective_of_center_bot hcen
  obtain ⟨-, hrodd, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have := hVe
  have hKodd : Odd (Nat.card K) := by rw [hK]; decide
  have hVinn : ∀ v ∈ V, v ∈
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range := by
    intro v hv
    apply g2_three_odd_aut_inner K hK
    have h1 : v ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    exact Odd.of_dvd_nat hrodd (orderOf_dvd_of_pow_eq_one h1)
  obtain ⟨E, hEe, hEc, hEV⟩ := exists_plane_of_inner hcen hVe hVc hVinn
  have := hEe
  have hq : Nat.card K = 3 := hK
  by_cases hr3 : r = 3
  · subst hr3
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
    have hzdvd : orderOf (z : MulAut (adjointGroup Tag.G2 K)) ∣ Nat.card Z := by
      have := orderOf_dvd_natCard z
      rwa [← Subgroup.orderOf_coe] at this
    have hz1' : orderOf (z : MulAut (adjointGroup Tag.G2 K)) ≠ 1 := by
      intro h
      apply hz1
      exact Subtype.ext (orderOf_eq_one_iff.1 h)
    obtain ⟨s, hs, hsz⟩ := Nat.exists_prime_and_dvd hz1'
    have hsZ : s ∣ Nat.card Z := hsz.trans hzdvd
    have hsodd : Odd s := Odd.of_dvd_nat hZodd hsZ
    have hs3 : s ≠ 3 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hZcop.symm hsZ
    have hs5 : 3 < s := by
      have h2' := hs.two_le
      have : s ≠ 2 := by rintro rfl; exact absurd hsodd (by decide)
      have h4 : s ≠ 4 := by rintro rfl; exact absurd hs (by decide)
      omega
    set z' : MulAut (adjointGroup Tag.G2 K) := (z : MulAut (adjointGroup Tag.G2 K)) ^
      (orderOf (z : MulAut (adjointGroup Tag.G2 K)) / s) with hz'
    have hz'ord : orderOf z' = s := orderOf_pow_orderOf_div (orderOf_pos _).ne' hsz
    have hz'Z : z' ∈ Z := Subgroup.pow_mem Z z.2 _
    obtain ⟨x, hx⟩ := g2_three_odd_aut_inner K hK z' (by rw [hz'ord]; exact hsodd)
    have hxord : orderOf x = s := by
      rw [← hz'ord, ← hx]
      exact (orderOf_injective _ hinj x).symm
    have hsY : s ∣ Nat.card (adjointGroup Tag.G2 K) := by
      rw [← hxord]
      exact orderOf_dvd_natCard x
    obtain ⟨hY1, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
    rw [hY1] at hsY
    have hsq : ¬ s ∣ Nat.card K := by
      rw [hq]
      intro h
      exact hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).1 h)
    have hcyc : IsCyclic (Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K))) := by
      rcases prime_dvd_g2_order hs hsq hsY with h | h | h | h
      · exfalso; rw [hq] at h
        exact absurd (hs5.trans_le (Nat.le_of_dvd (by norm_num) h)) (by norm_num)
      · exfalso; rw [hq] at h
        have h4 : s = 4 := le_antisymm (Nat.le_of_dvd (by norm_num) h) (Nat.succ_le_of_lt hs5)
        rw [h4] at hs
        exact absurd hs (by decide)
      · obtain ⟨T, -, -, -, -, hx'⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K
          hKodd 1 (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hs hs5 h
        exact (hx' x hxord).2.2.1
      · have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
        obtain ⟨T, -, -, -, -, hx'⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K
          hKodd (-1) (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1)
          (by push_cast [Nat.cast_sub hle]; ring) hs hs5 h
        exact (hx' x hxord).2.2.1
    have hEle : E ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hv : MulAut.conj e ∈ V := hEV ▸ ⟨e, he, rfl⟩
      have hc := hcomm _ hv z' hz'Z
      rw [← hx] at hc
      apply hinj
      rw [map_mul, map_mul]
      exact hc
    have hEcyc : IsCyclic E :=
      isCyclic_of_injective (Subgroup.inclusion hEle) (Subgroup.inclusion_injective hEle)
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc hEcyc
  ·
    have hr5 : 3 < r := by
      have := hr.two_le
      have : r ≠ 2 := by rintro rfl; exact absurd hrodd (by decide)
      have : r ≠ 4 := by rintro rfl; exact absurd hr (by decide)
      omega
    have hrY : r ∣ Nat.card (adjointGroup Tag.G2 K) := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
      rw [hEc]
      exact dvd_pow_self r two_ne_zero
    obtain ⟨hY1, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
    rw [hY1] at hrY
    have hrq : ¬ r ∣ Nat.card K := by
      rw [hq]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    rcases prime_dvd_g2_order hr hrq hrY with h | h | h | h
    · exfalso; rw [hq] at h
      exact absurd (hr5.trans_le (Nat.le_of_dvd (by norm_num) h)) (by norm_num)
    · exfalso; rw [hq] at h
      have h4 : r = 4 := le_antisymm (Nat.le_of_dvd (by norm_num) h) (Nat.succ_le_of_lt hr5)
      rw [h4] at hr
      exact absurd hr (by decide)
    · exact g2_no_plane_of_cyclotomic K hKodd hr hr5 (Or.inl h) E hEe hEc
    · exact g2_no_plane_of_cyclotomic K hKodd hr hr5 (Or.inr h) E hEe hEc

end CFSG.GH74.GLS.Stage2.Bender.Thm1
