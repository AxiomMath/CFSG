module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionSetting

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G}

omit [Finite G] in
theorem Ps_zero_eq (σ : Setting G) (r : ℕ) : σ.Ps r 0 = pCoreIn r σ.N := rfl

omit [Finite G] in
theorem N_le_normalizer_Ps_zero (σ : Setting G) (r : ℕ) :
    σ.N ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
  le_normalizer_pCoreIn r σ.N

omit [Finite G] in
theorem isPGroup_F₀ : IsPGroup 2 σ.F₀ := isPGroup_D.to_le inf_le_left

theorem le_normalizer_of_mul_comm {B X : Subgroup G} (hB : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u)
    (hXB : X ≤ B) : B ≤ Subgroup.normalizer (X : Set G) := fun b hb =>
  mem_normalizer_of_conj_mem fun x hx => by
    rw [hB b hb x (hXB hx), mul_inv_cancel_right]
    exact hx

theorem Ps_zero_facts (hσ : σ.IsValid) (hV : σ.CorollaryV61) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card σ.ON) (hti : σ.TotallyInverted r) :
    IsSylowOf r (σ.Ps r 0) σ.ON ∧ (∀ u ∈ σ.Ps r 0, σ.x₂ * u * σ.x₂⁻¹ = u⁻¹) ∧
      ∀ u ∈ σ.Ps r 0, ∀ v ∈ σ.Ps r 0, u * v = v * u := by
  rw [Ps_zero_eq]
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdvd
  obtain ⟨R₀, hR₀, hTR₀⟩ := exists_isSylowOf_normalized_of_odd hr (isPGroup_T hσ)
    ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  rcases hV.sylow_centralized_or_inverted r hr R₀ hR₀ hTR₀ with hcen | hinv
  · exfalso
    have hR₀C : R₀ ≤ σ.C := fun g hg => mem_C_iff.mpr
      ⟨(Subgroup.mem_centralizer_singleton_iff.mp (σ.ON_le_N (hR₀.le hg))),
        Subgroup.mem_centralizer_singleton_iff.mp (hcen hg)⟩
    have hdvdR : r ∣ Nat.card R₀ := by
      rw [hR₀.card_eq]
      exact dvd_pow_self r (hr.factorization_pos_of_dvd Nat.card_pos.ne' hdvd).ne'
    exact hti (hdvdR.trans (Subgroup.card_dvd_of_le (le_inf hR₀C (hR₀.le.trans (ON_le_L hσ)))))
  · obtain ⟨B, hBON, hNB, hBinv, hBmax⟩ := hV.invertedHall
    have hBab : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
      mul_comm_of_conj_eq_inv hBinv hu hv
    have hR₀B := hBmax r hr R₀ hR₀ hTR₀ hinv
    have hR₀B' : IsSylowOf r R₀ B := hR₀.of_le hR₀B hBON
    have hNR₀ : σ.N ≤ Subgroup.normalizer (R₀ : Set G) := by
      intro n hn
      apply mem_normalizer_of_conjSub_le
      have h1 : conjSub n R₀ ≤ B := by
        rw [← conjSub_eq_self_of_mem (hNB hn)]
        exact conjSub_mono hR₀B
      have heq := hR₀B'.eq_of_le le_sup_left (sup_le hR₀B h1)
        (hR₀B'.isPGroup.to_sup_of_normal_right' (isPGroup_conjSub hR₀B'.isPGroup n)
          (hR₀B.trans (le_normalizer_of_mul_comm hBab h1)))
      exact le_sup_right.trans heq.le
    have hle1 : R₀ ≤ pCoreIn r σ.N := le_pCoreIn (hR₀.le.trans σ.ON_le_N) hNR₀ hR₀B'.isPGroup
    have hle2 : pCoreIn r σ.N ≤ σ.ON := le_oddCoreIn (pCoreIn_le r _)
      (le_normalizer_pCoreIn r _) (odd_card_of_isPGroup hr hr2 (isPGroup_pCoreIn r _))
    have heq : pCoreIn r σ.N = R₀ := hR₀.eq_of_le hle1 hle2 (isPGroup_pCoreIn r _)
    rw [heq]
    exact ⟨hR₀, fun u hu => hBinv u (hR₀B hu), fun u hu v hv => hBab u (hR₀B hu) v (hR₀B hv)⟩

theorem exists_P (hT : σ.TIFacts) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hti : σ.TotallyInverted r) :
    ∃ P : Subgroup G, IsSylowOf r P σ.C ∧ σ.D ≤ Subgroup.normalizer (P : Set G) ∧
      P ⊓ σ.L = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDC : σ.D ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
    (D_le_normalizer_T.trans normalizer_T_le_M).trans (normalizer_le_normalizer_oddCoreIn σ.C)
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_normalized_of_odd hr isPGroup_D hDC
    (odd_card_oddCoreIn σ.C)
  have hPC : P ≤ σ.C := hP.le.trans (oddCoreIn_le _)
  have hsyl : IsSylowOf r P σ.C := by
    refine isSylowOf_iff.mpr ⟨hPC, hP.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P (oddCoreIn σ.C) σ.C hP.le (oddCoreIn_le _)]
    intro hdvd
    rcases hr.dvd_mul.mp hdvd with h | h
    · exact (isSylowOf_iff.mp hP).2.2 h
    · have h1 := relIndex_sup_right_of_le_normalizer
        (F₀_le_C.trans (le_normalizer_oddCoreIn σ.C) : σ.F₀ ≤ _)
      rw [sup_comm, hT.C_eq] at h1
      rw [h1] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_F₀ (σ := σ))
      have h2 := h.trans (Subgroup.relIndex_dvd_card _ _)
      rw [hk] at h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  exact ⟨P, hsyl, hDP, inf_L_eq_bot hr hti hP.isPGroup hPC⟩

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
