module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5S2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5PermA

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Equiv Equiv.Perm

theorem lemma_T (Φ Ψ : Subgroup (Perm (Fin 4 ⊕ Fin 4))) (hΨΦ : Ψ ≤ Φ) (hΦ2 : IsPGroup 2 Φ)
    (hne : Ψ ≠ Φ) (hcard : 128 ≤ Nat.card Φ)
    (hblock : ∀ w ∈ Φ, ∀ p q : Fin 4 ⊕ Fin 4, p.isLeft = q.isLeft →
      (w p).isLeft = (w q).isLeft)
    (hV1 : ∀ v ∈ klein, Perm.sumCongr v 1 ∈ Ψ)
    (hσ : ∃ σ ∈ Ψ, (σ (Sum.inl 0)).isLeft = false) :
    ∃ τ : Perm (Fin 4), Perm.sign τ = -1 ∧ τ * τ = 1 ∧ Perm.sumCongr τ 1 ∈ Φ ∧
      Perm.sumCongr τ 1 ∉ Ψ := by
  classical
  rcases hσ with ⟨σ, hσΨ, hσ0⟩
  have hσΦ : σ ∈ Φ := hΨΦ hσΨ
  have hσinvΦ : σ⁻¹ ∈ Φ := Φ.inv_mem hσΦ
  have hσ_inl_right : ∀ i, (σ (Sum.inl i)).isLeft = false :=
    fun i => (hblock σ hσΦ (Sum.inl i) (Sum.inl 0) (by simp)).trans hσ0
  have hσinv_inl_right : ∀ i, (σ⁻¹ (Sum.inl i)).isLeft = false := by
    intro i
    cases hv : (σ⁻¹ (Sum.inl i)).isLeft with
    | false => rfl
    | true =>
        have h := hblock σ hσΦ (σ⁻¹ (Sum.inl i)) (Sum.inl 0) (by rw [hv]; rfl)
        simpa [hσ0] using h
  have hσinv_inr_left : ∀ j, (σ⁻¹ (Sum.inr j)).isLeft = true :=
    isLeft_of_isLeft_inl_false hσinv_inl_right
  have hcover : ∀ w ∈ Φ, w ∈ blockPart Φ ∨ σ⁻¹ * w ∈ blockPart Φ := by
    intro w hwΦ
    by_cases h0 : (w (Sum.inl 0)).isLeft = false
    · right
      have hwright : ∀ i, (w (Sum.inl i)).isLeft = false :=
        fun i => (hblock w hwΦ (Sum.inl i) (Sum.inl 0) (by simp)).trans h0
      exact ⟨mul_mem hσinvΦ hwΦ, mul_mem_range hwright hσinv_inr_left⟩
    · left
      have h0' : (w (Sum.inl 0)).isLeft = true := by
        cases hv : (w (Sum.inl 0)).isLeft with
        | false => exact absurd hv h0
        | true => rfl
      refine ⟨hwΦ, ?_⟩
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨i, rfl⟩
      obtain ⟨k, hk⟩ :=
        eq_inl_of_isLeft_true ((hblock w hwΦ (Sum.inl i) (Sum.inl 0) (by simp)).trans h0')
      exact ⟨k, hk.symm⟩
  have hrel : (blockPart Φ).relIndex Φ ∣ 2 :=
    Subgroup.relIndex_dvd_two_iff'.mpr ⟨σ⁻¹, hσinvΦ, fun b hbΦ => by
      rcases hcover b hbΦ with hbH | hbH
      · exact Or.inr hbH
      · exact Or.inl hbH⟩
  have hrelmul : (blockPart Φ).relIndex Φ * Nat.card (blockPart Φ) = Nat.card Φ := by
    have := Subgroup.relIndex_mul_card (H := blockPart Φ) (K := Φ)
    rwa [inf_eq_left.mpr inf_le_left] at this
  have hcardH : 64 ≤ Nat.card (blockPart Φ) := by
    have hrel_le : (blockPart Φ).relIndex Φ ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
    have h1 : Nat.card Φ ≤ 2 * Nat.card (blockPart Φ) := by
      rw [← hrelmul]
      exact Nat.mul_le_mul_right _ hrel_le
    omega
  have hH'eq_map : (blockPre Φ).map scHom = blockPart Φ := by
    show (Subgroup.comap scHom Φ).map scHom = Φ ⊓ scHom.range
    rw [Subgroup.map_comap_eq, inf_comm]
  have hH'card : Nat.card (blockPre Φ) = Nat.card (blockPart Φ) :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective (blockPre Φ) scHom Perm.sumCongrHom_injective).toEquiv).trans
      (by rw [hH'eq_map])
  have hcardH' : 64 ≤ Nat.card (blockPre Φ) := by rw [hH'card]; exact hcardH
  have hH'2 : IsPGroup 2 (blockPre Φ) :=
    hΦ2.comap_of_injective scHom Perm.sumCongrHom_injective
  have hP1_2 : IsPGroup 2 (proj1 Φ) := hH'2.map (MonoidHom.fst _ _)
  have hP2_2 : IsPGroup 2 (proj2 Φ) := hH'2.map (MonoidHom.snd _ _)
  have hcardperm : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide +kernel
  have hP1_le : Nat.card (proj1 Φ) ≤ 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP1_2
    rw [hn]
    have hdvd : 2 ^ n ∣ 24 := by
      rw [← hcardperm, ← hn]
      exact Subgroup.card_subgroup_dvd_card (proj1 Φ)
    have hnle : n ≤ 3 := by
      have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h24] at hdvd
      have hdvd' : 2 ^ n ∣ 2 ^ 3 :=
        ((by norm_num : Nat.Coprime 2 3).pow_left n).dvd_mul_right.mp hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd'
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (n := 2) (by norm_num) hnle
      _ = 8 := by norm_num
  have hP2_le : Nat.card (proj2 Φ) ≤ 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2_2
    rw [hn]
    have hdvd : 2 ^ n ∣ 24 := by
      rw [← hcardperm, ← hn]
      exact Subgroup.card_subgroup_dvd_card (proj2 Φ)
    have hnle : n ≤ 3 := by
      have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h24] at hdvd
      have hdvd' : 2 ^ n ∣ 2 ^ 3 :=
        ((by norm_num : Nat.Coprime 2 3).pow_left n).dvd_mul_right.mp hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd'
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (n := 2) (by norm_num) hnle
      _ = 8 := by norm_num
  have hprod_card : Nat.card ((proj1 Φ).prod (proj2 Φ)) =
      Nat.card (proj1 Φ) * Nat.card (proj2 Φ) :=
    (Nat.card_congr (Subgroup.prodEquiv (proj1 Φ) (proj2 Φ)).toEquiv).trans
      (Nat.card_prod (proj1 Φ) (proj2 Φ))
  have hH'_le_prod : blockPre Φ ≤ (proj1 Φ).prod (proj2 Φ) := by
    intro x hx
    exact Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hH'_eq_prod : blockPre Φ = (proj1 Φ).prod (proj2 Φ) := by
    refine Subgroup.eq_of_le_of_card_ge hH'_le_prod ?_
    rw [hprod_card]
    calc Nat.card (proj1 Φ) * Nat.card (proj2 Φ) ≤ 8 * 8 :=
          Nat.mul_le_mul hP1_le hP2_le
      _ = 64 := by norm_num
      _ ≤ Nat.card (blockPre Φ) := hcardH'
  have hproj : ∀ x ∈ blockPre Φ, (x.1, 1) ∈ blockPre Φ ∧ (1, x.2) ∈ blockPre Φ := by
    intro x hx
    rw [hH'_eq_prod, Subgroup.mem_prod] at hx
    refine ⟨?_, ?_⟩
    · rw [hH'_eq_prod, Subgroup.mem_prod]
      exact ⟨hx.1, Subgroup.one_mem _⟩
    · rw [hH'_eq_prod, Subgroup.mem_prod]
      exact ⟨Subgroup.one_mem _, hx.2⟩
  have hprojΦ : ∀ p q, scHom (p, q) ∈ Φ → scHom (p, 1) ∈ Φ ∧ scHom (1, q) ∈ Φ := by
    intro p q hpq
    have hmem : (p, q) ∈ blockPre Φ := Subgroup.mem_comap.mpr hpq
    obtain ⟨h1, h2⟩ := hproj (p, q) hmem
    exact ⟨Subgroup.mem_comap.mp h1, Subgroup.mem_comap.mp h2⟩
  have hex : ∃ x ∈ blockPre Φ, scHom x ∉ Ψ := by
    by_contra hcon
    push Not at hcon
    have hPhi_le : Φ ≤ Ψ := by
      intro w hwΦ
      rcases hcover w hwΦ with hwH | hwH
      · rw [← hH'eq_map] at hwH
        rcases Subgroup.mem_map.mp hwH with ⟨x, hx, rfl⟩
        exact hcon x hx
      · rw [← hH'eq_map] at hwH
        rcases Subgroup.mem_map.mp hwH with ⟨x, hx, hxeq⟩
        have hxΨ : σ⁻¹ * w ∈ Ψ := hxeq ▸ hcon x hx
        have hw_eq : w = σ * (σ⁻¹ * w) := by group
        rw [hw_eq]
        exact mul_mem hσΨ hxΨ
    exact hne (le_antisymm hΨΦ hPhi_le)
  obtain ⟨x, hxH', hxnotΨ⟩ := hex
  obtain ⟨p, q⟩ := x
  have hxΦ : scHom (p, q) ∈ Φ := Subgroup.mem_comap.mp hxH'
  obtain ⟨hp1, h1q⟩ := hprojΦ p q hxΦ
  have hprod_eq : scHom (p, q) = scHom (p, 1) * scHom (1, q) := by
    rw [show (p, q) = (p, 1) * (1, q) from by simp]
    exact map_mul scHom (p, 1) (1, q)
  have hp_or_hq : scHom (p, 1) ∉ Ψ ∨ scHom (1, q) ∉ Ψ := by
    by_contra h
    push Not at h
    exact hxnotΨ (by rw [hprod_eq]; exact mul_mem h.1 h.2)
  have hpstar : ∃ p' : Perm (Fin 4), scHom (p', 1) ∈ Φ ∧ scHom (p', 1) ∉ Ψ := by
    rcases hp_or_hq with h1 | h2
    · exact ⟨p, hp1, h1⟩
    · let w : Perm (Fin 4 ⊕ Fin 4) := σ * scHom (1, q) * σ⁻¹
      have hwΦ : w ∈ Φ := Φ.mul_mem (Φ.mul_mem hσΦ h1q) hσinvΦ
      have hwnotΨ : w ∉ Ψ := by
        intro hwΨ
        apply h2
        have hconj : σ⁻¹ * w * σ = scHom (1, q) := by
          simp only [w]
          group
        rw [← hconj]
        exact Ψ.mul_mem (Ψ.mul_mem (Ψ.inv_mem hσΨ) hwΨ) hσΨ
      have hwfix : ∀ j, w (Sum.inr j) = Sum.inr j := by
        intro j
        obtain ⟨i, hi⟩ := eq_inl_of_isLeft_true (hσinv_inr_left j)
        have hfix_left : scHom (1, q) (Sum.inl i) = Sum.inl i := by
          simp [scHom, Perm.sumCongrHom_apply]
        calc w (Sum.inr j) = (σ * scHom (1, q) * σ⁻¹) (Sum.inr j) := rfl
          _ = σ (scHom (1, q) (σ⁻¹ (Sum.inr j))) := by simp [Equiv.Perm.mul_apply]
          _ = σ (scHom (1, q) (Sum.inl i)) := by rw [hi]
          _ = σ (Sum.inl i) := by rw [hfix_left]
          _ = σ (σ⁻¹ (Sum.inr j)) := by rw [hi]
          _ = Sum.inr j := by simp
      have hw_range : w ∈ scHom.range := by
        apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
        rintro _ ⟨i, rfl⟩
        by_contra hnot
        obtain ⟨j, hj⟩ := eq_inr_of_not_mem hnot
        exact Sum.inl_ne_inr (w.injective (by rw [hj, hwfix j]))
      rcases MonoidHom.mem_range.mp hw_range with ⟨⟨q', r'⟩, hqr⟩
      have hr' : r' = 1 := by
        apply Equiv.ext
        intro j
        have h := hwfix j
        rw [← hqr] at h
        have h2' : (Sum.inr (r' j) : Fin 4 ⊕ Fin 4) = Sum.inr j := by
          simpa [scHom, Perm.sumCongrHom_apply] using h
        simpa using (Sum.inr.inj_iff).mp h2'
      have hq' : scHom (q', 1) = w := by
        rw [← hqr, hr']
      exact ⟨q', by rw [hq']; exact hwΦ, by rw [hq']; exact hwnotΨ⟩
  obtain ⟨p', hp'Φ, hp'notΨ⟩ := hpstar
  have hp'P1 : p' ∈ proj1 Φ := by
    have hmem : (p', 1) ∈ blockPre Φ := Subgroup.mem_comap.mpr hp'Φ
    exact Subgroup.mem_map.mpr ⟨(p', 1), hmem, rfl⟩
  have hsignp : Perm.sign p' = -1 := by
    by_contra hsign
    rcases Int.units_eq_one_or (Perm.sign p') with h1 | h1
    · by_cases hklein : p' ∈ klein
      · exact hp'notΨ (hV1 p' hklein)
      · obtain ⟨hp3, hp3ne⟩ := three_of_even_not_klein h1 hklein
        obtain ⟨k, hk⟩ := hP1_2 ⟨p', hp'P1⟩
        have hk' : p' ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hord : orderOf p' = 3 := orderOf_eq_prime hp3 hp3ne
        have hdvd : orderOf p' ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk'
        rw [hord] at hdvd
        have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
        norm_num at h32
    · exact absurd h1 hsign
  obtain ⟨v, hvklein, hvv⟩ := odd_mul_klein_involution hsignp
  have hprod_tau : Perm.sumCongr (p' * v) (1 : Perm (Fin 4)) =
      Perm.sumCongr p' (1 : Perm (Fin 4)) * Perm.sumCongr v (1 : Perm (Fin 4)) := by
    have h := (Perm.sumCongr_mul p' (1 : Perm (Fin 4)) v (1 : Perm (Fin 4))).symm
    simpa using h
  have hvΨ : Perm.sumCongr v (1 : Perm (Fin 4)) ∈ Ψ := hV1 v hvklein
  refine ⟨p' * v, ?_, hvv, ?_, ?_⟩
  · rw [Perm.sign_mul, hsignp, sign_of_mem_klein hvklein]
    simp
  · rw [hprod_tau]
    exact Φ.mul_mem hp'Φ (hΨΦ hvΨ)
  · intro hmem
    apply hp'notΨ
    change Perm.sumCongr p' (1 : Perm (Fin 4)) ∈ Ψ
    have hconj : Perm.sumCongr p' (1 : Perm (Fin 4)) =
        Perm.sumCongr (p' * v) (1 : Perm (Fin 4)) *
          (Perm.sumCongr v (1 : Perm (Fin 4)))⁻¹ := by
      rw [hprod_tau]
      group
    rw [hconj]
    exact Ψ.mul_mem hmem (Ψ.inv_mem hvΨ)

end CFSG.OddStandard.SmallF3.Omega.K5
