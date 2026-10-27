module

public import CFSG.LargeExtraspecial.DWSm77Nine
public import CFSG.LargeExtraspecial.DWSm77Count

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

namespace Decomp

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} (D : Decomp S)

theorem eq_one_or_z_of_sq_eq_one_of_card_le (h2 : 2 ≤ S.width) (hB8 : Nat.card D.B ≤ 8)
    {b : G} (hb : b ∈ D.B) (hb2 : b ^ 2 = 1) : b = 1 ∨ b = S.z := by
  by_contra hne
  push Not at hne
  obtain ⟨hb1, hbz⟩ := hne
  have hbQ := D.B_le hb
  have hqb : S.q (S.cl b) = 0 := (S.q_cl_eq_zero_iff hbQ).mpr hb2
  have hb0 : S.cl b ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hbQ).mp h with h | h
    exacts [hb1 h, hbz h]
  obtain ⟨c, hc, hbc⟩ := D.exists_not_commute_B hb hb1 hbz
  have hcQ := D.B_le hc
  have hp := (S.polar_cl_eq_one_iff hbQ hcQ).mpr hbc
  obtain ⟨c', hc'B, hq', hp'⟩ : ∃ c' ∈ D.B, S.q (S.cl c') = 1 ∧
      polar S.q (S.cl b) (S.cl c') = 1 := by
    rcases zmod2_cases (S.q (S.cl c)) with hq | hq
    · refine ⟨b * c, D.B.mul_mem hb hc, ?_, ?_⟩
      · rw [S.cl_mul hbQ hcQ, q_add, hqb, hq, hp]
        decide
      · rw [S.cl_mul hbQ hcQ, polar_add_right,
          CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero, hp, zero_add]
    · exact ⟨c, hc, hq, hp⟩
  have hc'Q := D.B_le hc'B
  have hli : LinearIndependent (ZMod 2) ![S.cl b, S.cl c'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have e := congrArg (polar S.q (S.cl b)) hst
      rw [polar_add_right, polar_smul_right, polar_smul_right,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero, hp', polar_zero_right,
        smul_zero, zero_add, smul_eq_mul, mul_one] at e
      exact e
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    rcases zmod2_cases s with hs | hs
    · exact hs
    · rw [hs, one_smul] at hst
      exact absurd hst hb0
  have hspan : Submodule.span (ZMod 2) {S.cl b, S.cl c'} = S.clSub D.B := by
    have hrange : Set.range ![S.cl b, S.cl c'] = {S.cl b, S.cl c'} := by
      simp [Matrix.range_cons, Set.pair_comm]
    have hfin := finrank_span_eq_card hli
    rw [hrange, Fintype.card_fin] at hfin
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact S.cl_mem_clSub hb hbQ
      · exact S.cl_mem_clSub hc'B hc'Q
    · rw [hfin]
      have hcard := D.card_B
      have h4 : 2 ^ finrank (ZMod 2) (S.clSub D.B) ≤ 2 ^ 2 := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  have huniq : ∀ w ∈ S.clSub D.B, S.q w = 1 → w = S.cl c' := by
    intro w hw hqw
    rw [← hspan, Submodule.mem_span_pair] at hw
    obtain ⟨α, γ, rfl⟩ := hw
    rcases zmod2_cases α with rfl | rfl <;> rcases zmod2_cases γ with rfl | rfl
    · simp at hqw
    · simp
    · simp only [one_smul, zero_smul, add_zero] at hqw
      rw [hqb] at hqw
      exact absurd hqw (by decide)
    · simp only [one_smul] at hqw
      rw [q_add, hqb, hq', hp'] at hqw
      exact absurd hqw (by decide)
  have hfix : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c') = S.cl c' := by
    intro m
    refine huniq _ ?_ ?_
    · rw [S.ρ_cl m hc'Q]
      exact S.cl_mem_clSub (D.conj_B m m.2 c' hc'B) (S.conj_mem_QG m.2 hc'Q)
    · rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ m).2, hq']
  have h0 := eq_zero_of_forall_ρ_apply_eq S h2 hfix
  rw [h0, map_zero] at hq'
  exact absurd hq' (by decide)

omit [IsSimpleGroup G] in
theorem two_le_finrank_clSub_B : 2 ≤ finrank (ZMod 2) (S.clSub D.B) := by
  obtain ⟨b, hb, hb1, hbz⟩ := D.ne_B
  obtain ⟨b', hb', hbb'⟩ := D.exists_not_commute_B hb hb1 hbz
  have hbQ := D.B_le hb
  have hb'Q := D.B_le hb'
  have hp := (S.polar_cl_eq_one_iff hbQ hb'Q).mpr hbb'
  by_contra h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp (Nat.lt_succ_iff.mp (not_le.mp h))
  obtain ⟨c₁, hc₁⟩ := hv ⟨S.cl b, S.cl_mem_clSub hb hbQ⟩
  obtain ⟨c₂, hc₂⟩ := hv ⟨S.cl b', S.cl_mem_clSub hb' hb'Q⟩
  have e₁ : c₁ • (v : S.Qt) = S.cl b := congrArg Subtype.val hc₁
  have e₂ : c₂ • (v : S.Qt) = S.cl b' := congrArg Subtype.val hc₂
  rw [← e₁, ← e₂, polar_smul_left, polar_smul_right,
    CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero] at hp
  simp at hp

theorem false_of_mem_A (hn : 4 ≤ S.width) {g : G} (hxA : g * S.z * g⁻¹ ∈ D.A)
    (hxz : g * S.z * g⁻¹ ≠ S.z) : False := by
  have h2 : 2 ≤ S.width := by omega
  have hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z := fun h hh => by
    by_contra hne
    exact D.not_mem_B_of_mem_A hxA hxz hh hne
  have hAB := D.two_mul_card_B_le hxA hxz
  have hdim := D.finrank_add
  rw [D.card_A, D.card_B] at hAB
  have hd : finrank (ZMod 2) (S.clSub D.B) + 1 ≤ finrank (ZMod 2) (S.clSub D.A) := by
    have h : 2 ^ (finrank (ZMod 2) (S.clSub D.B) + 1) ≤ 2 ^ finrank (ZMod 2) (S.clSub D.A) := by
      rw [pow_succ]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have h8 : 8 < Nat.card D.A := by
    rw [D.card_A]
    have h3 : 3 ≤ finrank (ZMod 2) (S.clSub D.A) := by omega
    calc 8 < 2 * 2 ^ 3 := by norm_num
      _ ≤ 2 * 2 ^ finrank (ZMod 2) (S.clSub D.A) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) h3)
  have hB8 : 8 < Nat.card D.B ∨ ∀ b ∈ D.B, b ^ 2 = 1 → b = 1 ∨ b = S.z := by
    by_cases h : 8 < Nat.card D.B
    · exact Or.inl h
    · exact Or.inr fun b hb hb2 =>
        D.eq_one_or_z_of_sq_eq_one_of_card_le h2 (not_lt.mp h) hb hb2
  obtain ⟨h₁, h₂, hu, hv, huv⟩ := D.exists_not_commute_conj hB h8 hB8 hxA hxz
  have huz : h₁ * S.z * h₁⁻¹ ≠ S.z := fun h => huv (by
    rw [h]
    exact (S.z_comm_QG (D.A_le hv)).symm)
  have hvz : h₂ * S.z * h₂⁻¹ ≠ S.z := fun h => huv (by
    rw [h]
    exact S.z_comm_QG (D.A_le hu))
  have hw : ∀ d ∈ S.M, d * (h₂ * S.z * h₂⁻¹) * d⁻¹ ∈ D.A ∧
      (∃ k : G, k * S.z * k⁻¹ = d * (h₂ * S.z * h₂⁻¹) * d⁻¹) ∧
      d * (h₂ * S.z * h₂⁻¹) * d⁻¹ ≠ S.z := by
    intro d hd
    refine ⟨D.conj_A d hd _ hv, ⟨d * h₂, by group⟩, fun h => hvz ?_⟩
    calc h₂ * S.z * h₂⁻¹ = d⁻¹ * (d * (h₂ * S.z * h₂⁻¹) * d⁻¹) * d := by group
      _ = d⁻¹ * S.z * d := by rw [h]
      _ = S.z := by rw [S.z_comm (S.M.inv_mem hd)]; group
  have hX : finrank (ZMod 2) (S.clSub D.A) + 2 ≤ 2 * S.width := by
    have := D.two_le_finrank_clSub_B
    omega
  have hvX : ∀ d ∈ S.L0 h₁, S.cl (d * (h₂ * S.z * h₂⁻¹) * d⁻¹) ∈ S.clSub D.A := fun d hd =>
    S.cl_mem_clSub (hw d (S.L0_le_M h₁ hd)).1 (D.A_le (hw d (S.L0_le_M h₁ hd)).1)
  refine false_of_polar_eq_one_of_four_le S hn (D.A_le hu) huz (D.A_le hv) huv (S.clSub D.A) hX
    hvX ?_
  intro d₁ hd₁ d₂ hd₂ hne
  obtain ⟨hw₁A, hw₁', hw₁z⟩ := hw d₁ (S.L0_le_M h₁ hd₁)
  obtain ⟨hw₂A, hw₂', hw₂z⟩ := hw d₂ (S.L0_le_M h₁ hd₂)
  have hw₁Q := D.A_le hw₁A
  have hw₂Q := D.A_le hw₂A
  rcases zmod2_cases (polar S.q (S.cl (d₁ * (h₂ * S.z * h₂⁻¹) * d₁⁻¹))
      (S.cl (d₂ * (h₂ * S.z * h₂⁻¹) * d₂⁻¹))) with hp | hp
  · exfalso
    have hcomm := (S.polar_cl_eq_zero_iff hw₁Q hw₂Q).mp hp
    rcases D.eq_or_eq_mul_z_of_commute hB h8 hB8 hu ⟨h₁, rfl⟩ hv ⟨h₂, rfl⟩ huv hw₁A hw₁' hw₁z
      hw₂A hw₂' hw₂z hcomm with e | e
    · exact hne (by rw [e])
    · exact hne (by rw [e, S.cl_mul_z hw₁Q])
  · exact hp

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
