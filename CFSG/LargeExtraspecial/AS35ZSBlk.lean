module

public import CFSG.Fischer.Classification.Unitary.Local

public section

namespace CFSG.LargeExtraspecial.AS35ZS

open CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

noncomputable abbrev perpT (m : ℕ) : Subgroup (SUid frob (m + 2)) :=
  Subgroup.closure (tvU '' (ι m '' {w | herm frob w w = 0}))

theorem exists_lift {t : SUid frob m} (ht : t ∈ T frob m) :
    ∃ t' ∈ perpT m, t' • v₀ m = v₀ m ∧ t' • u₀ m = u₀ m ∧ ∀ z, t' • ι m z = ι m (t • z) := by
  rw [T_eq_closure_tvU] at ht
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨w, -, hw, rfl⟩ := hg
    have hιw : herm frob (ι m w) (ι m w) = 0 := by rw [herm_ι_ι, hw]
    refine ⟨tvU (ι m w), Subgroup.subset_closure ⟨ι m w, ⟨w, hw, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
    · rw [tvU_smul hιw, herm_ι_v₀, zero_smul, add_zero]
    · rw [tvU_smul hιw, herm_ι_u₀, zero_smul, add_zero]
    · intro z
      rw [tvU_smul hιw, herm_ι_ι, tvU_smul hw, map_add, map_smul]
  | one => exact ⟨1, Subgroup.one_mem _, one_smul _ _, one_smul _ _, fun z => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨g', hg', h1, h2, h3⟩ := ihg
    obtain ⟨h', hh', h4, h5, h6⟩ := ihh
    refine ⟨g' * h', Subgroup.mul_mem _ hg' hh', by rw [mul_smul, h4, h1],
      by rw [mul_smul, h5, h2], fun z => by rw [mul_smul, h6, h3, mul_smul]⟩
  | inv g _ ihg =>
    obtain ⟨g', hg', h1, h2, h3⟩ := ihg
    refine ⟨g'⁻¹, Subgroup.inv_mem _ hg', by rw [inv_smul_eq_iff, h1],
      by rw [inv_smul_eq_iff, h2], fun z => by rw [inv_smul_eq_iff, h3, smul_inv_smul]⟩

theorem eq_of_fix {g g' : SUid frob (m + 2)} (hv : g • v₀ m = v₀ m) (hu : g • u₀ m = u₀ m)
    (hv' : g' • v₀ m = v₀ m) (hu' : g' • u₀ m = u₀ m) (hι : ∀ z, g • ι m z = g' • ι m z) :
    g = g' := by
  refine ext_smul _ fun x => ?_
  rw [decomp x, smul_add, smul_add, smul_add, smul_add, smul_comm g, smul_comm g,
    smul_comm g', smul_comm g', hv, hu, hv', hu', hι]

theorem consL_e0 (m : ℕ) : consL (m + 1) (e0 K m) = (Pi.single 1 1 : Fin (m + 2) → K) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    rw [consL_apply, Fin.cons_succ, ← Fin.succ_zero_eq_one, e0]
    simp only [Pi.single_apply, Fin.succ_inj]

theorem ι_eq_consL (z : Fin m → K) : ι m z = consL (m + 1) (consL m z) := rfl

theorem exists_block {g : SUid frob (m + 2)} (hv : g • v₀ m = v₀ m) (hu : g • u₀ m = u₀ m) :
    ∃ g₀ : SUid frob m, ∀ z, g • ι m z = ι m (g₀ • z) := by
  obtain ⟨h1, h0⟩ := wd.fix_singles_of_fix (n := m) hv hu
  have hM : g • e0 K (m + 1) = e0 K (m + 1) := h0
  have hA : blk g hM • e0 K m = e0 K m := by
    have := smul_consL_eq_consL_blk hM (e0 K m)
    rw [consL_e0, h1, ← consL_e0, consL_apply, consL_apply] at this
    exact (Fin.cons_right_injective _ this).symm
  refine ⟨blk (blk g hM) hA, fun z => ?_⟩
  rw [ι_eq_consL, ι_eq_consL, smul_consL_eq_consL_blk hM, smul_consL_eq_consL_blk hA]

theorem tvU_mem_L_of_perp (hm : 2 ≤ m) {w : Fin (m + 2) → K} (hw : herm frob w w = 0)
    (hvw : herm frob (v₀ m) w = 0) : tvU w ∈ L m := by
  by_cases hs : ∀ c : K, w ≠ c • v₀ m
  · by_cases hw0 : w = 0
    · rw [hw0, tvU_zero]
      exact Subgroup.one_mem _
    · exact tvU_mem_L ⟨hw0, hw, hvw, hs⟩
  · push Not at hs
    obtain ⟨c, rfl⟩ := hs
    by_cases hc : c = 0
    · rw [hc, zero_smul, tvU_zero]
      exact Subgroup.one_mem _
    · rw [tvU_smul_vec herm_v₀_v₀ hc]
      exact tvU_v₀_mem_L hm

theorem perpT_le_L (hm : 2 ≤ m) : perpT m ≤ L m := by
  rw [Subgroup.closure_le]
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact tvU_mem_L_of_perp hm (by rw [herm_ι_ι, hw]) (herm_v₀_ι w)

theorem exists_iso_add (hm : 2 ≤ m) (y : Fin m → K) :
    ∃ w₁ w₂ : Fin m → K, herm frob w₁ w₁ = 0 ∧ herm frob w₂ w₂ = 0 ∧ y = w₁ + w₂ := by
  rcases herm_self_eq_zero_or_one y with hy | hy
  · exact ⟨0, y, herm_zero_left frob 0, hy, (zero_add y).symm⟩
  obtain ⟨w, hw, hwy⟩ : ∃ w : Fin m → K, herm frob w w = 0 ∧ herm frob w y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := eq_zero_of_forall_isotropic hm hcon
    rw [this, herm_zero_left] at hy
    exact zero_ne_one hy
  set d := herm frob w y with hd
  set w₁ := frob (ω * d⁻¹) • w with hw₁
  have h1 : herm frob w₁ y = ω := by
    rw [hw₁, herm_smul_left, frob_frob, ← hd, mul_assoc, inv_mul_cancel₀ hwy, mul_one]
  have h1' : herm frob y w₁ = frob ω := by rw [herm_conj frob frob_frob, h1]
  have hw₁w₁ : herm frob w₁ w₁ = 0 := herm_smul_smul_self hw _
  refine ⟨w₁, y - w₁, hw₁w₁, ?_, by abel⟩
  rw [herm_sub_left, herm_sub_right, herm_sub_right, hy, h1, h1', hw₁w₁]
  have := omega_add_frob
  linear_combination this + (1 - frob ω - ω) * two_eq_zero

theorem partner_eq {u' : Fin (m + 2) → K} (hvu : herm frob (v₀ m) u' = 1) :
    u' = herm frob (u₀ m) u' • v₀ m + u₀ m + ι m (π m u') := by
  conv_lhs => rw [decomp u']
  rw [hvu, one_smul]

theorem trace_partner {u' : Fin (m + 2) → K} (hu' : herm frob u' u' = 0)
    (hvu : herm frob (v₀ m) u' = 1) :
    herm frob (u₀ m) u' + frob (herm frob (u₀ m) u') = herm frob (π m u') (π m u') := by
  have := herm_eq_coords u' u'
  rw [hu', hvu, map_one, one_mul, mul_one] at this
  linear_combination -this - herm frob (π m u') (π m u') * two_eq_zero

theorem exists_mem_L_smul_u₀ (hm : 2 ≤ m) {u' : Fin (m + 2) → K} (hu' : herm frob u' u' = 0)
    (hvu : herm frob (v₀ m) u' = 1) : ∃ E ∈ L m, E • u₀ m = u' := by
  set c := herm frob (u₀ m) u' with hc
  set y := π m u' with hy
  obtain ⟨w₁, w₂, hw₁, hw₂, hyw⟩ := exists_iso_add hm y
  set a₁ : Fin (m + 2) → K := v₀ m + ι m w₁ with ha₁def
  set b : K := frob (1 + herm frob w₂ w₁) with hb
  set a₂ : Fin (m + 2) → K := b • v₀ m + ι m w₂ with ha₂def
  have ha₁ : herm frob a₁ a₁ = 0 := by
    simp only [ha₁def, herm_add_left, herm_add_right, herm_v₀_v₀, herm_v₀_ι, herm_ι_v₀,
      herm_ι_ι, hw₁, add_zero]
  have ha₂ : herm frob a₂ a₂ = 0 := by
    simp only [ha₂def, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      herm_v₀_v₀, herm_v₀_ι, herm_ι_v₀, herm_ι_ι, hw₂, mul_zero, add_zero]
  have hva₁ : herm frob (v₀ m) a₁ = 0 := by
    simp only [ha₁def, herm_add_right, herm_v₀_v₀, herm_v₀_ι, add_zero]
  have hva₂ : herm frob (v₀ m) a₂ = 0 := by
    simp only [ha₂def, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero,
      add_zero]
  have hp₁ : tvU a₁ • u₀ m = u₀ m + a₁ := by
    rw [tvU_smul ha₁]
    simp only [ha₁def, herm_add_left, herm_v₀_u₀, herm_ι_u₀, add_zero, one_smul]
  have hfb : frob b = 1 + herm frob w₂ w₁ := by rw [hb, frob_frob]
  have hp₂ : tvU a₂ • (u₀ m + a₁) = u₀ m + a₁ + a₂ := by
    rw [tvU_smul ha₂]
    have e : herm frob a₂ (u₀ m + a₁) = 1 := by
      simp only [ha₂def, ha₁def, herm_add_left, herm_add_right, herm_smul_left, herm_v₀_u₀,
        herm_v₀_v₀, herm_v₀_ι, herm_ι_u₀, herm_ι_v₀, herm_ι_ι, hfb]
      linear_combination herm frob w₂ w₁ * two_eq_zero
    rw [e, one_smul]
  have hL₁ : tvU a₁ ∈ L m := tvU_mem_L_of_perp hm ha₁ hva₁
  have hL₂ : tvU a₂ ∈ L m := tvU_mem_L_of_perp hm ha₂ hva₂
  have hsum : u₀ m + a₁ + a₂ = (1 + b) • v₀ m + u₀ m + ι m y := by
    rw [hyw, map_add, ha₁def, ha₂def, add_smul, one_smul]
    abel
  have htr := trace_partner hu' hvu
  have htr2 : (1 + b) + frob (1 + b) = herm frob y y := by
    rw [hyw, map_add, map_one, hfb, hb, herm_add_left, herm_add_right, herm_add_right, hw₁, hw₂,
      map_add, map_one, herm_conj frob frob_frob w₂ w₁]
    linear_combination (2 : K) * two_eq_zero
  have hdiff : (c - (1 + b)) + frob (c - (1 + b)) = 0 := by
    rw [map_sub]
    linear_combination htr - htr2
  rw [sub_K] at hdiff
  rcases (add_frob_eq_zero_iff _).1 hdiff with h0 | h1
  · refine ⟨tvU a₂ * tvU a₁, Subgroup.mul_mem _ hL₂ hL₁, ?_⟩
    rw [mul_smul, hp₁, hp₂, hsum, partner_eq hvu, ← hc, ← hy,
      show c = 1 + b by linear_combination h0 - (1 + b) * two_eq_zero]
  · refine ⟨tvU (v₀ m) * (tvU a₂ * tvU a₁),
      Subgroup.mul_mem _ (tvU_v₀_mem_L hm) (Subgroup.mul_mem _ hL₂ hL₁), ?_⟩
    rw [mul_smul, mul_smul, hp₁, hp₂, hsum, tvU_smul herm_v₀_v₀, partner_eq hvu, ← hc, ← hy]
    have e : herm frob (v₀ m) ((1 + b) • v₀ m + u₀ m + ι m y) = 1 := by
      simp only [herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_u₀, herm_v₀_ι, mul_zero,
        zero_add, add_zero]
    rw [e, one_smul, show c = (1 + b) + 1 by linear_combination h1 - (1 + b) * two_eq_zero,
      add_smul (1 + b) 1, one_smul]
    abel

theorem conj_mem_L {k : SUid frob (m + 2)} (hk : k • v₀ m = v₀ m) {l : SUid frob (m + 2)}
    (hl : l ∈ L m) : k * l * k⁻¹ ∈ L m := by
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [conj_tvU k hw.2.1]
    refine tvU_mem_L ⟨(smul_ne_zero_iff_ne k).2 hw.1, by rw [herm_smul_smul, hw.2.1], ?_,
      fun c hc => hw.2.2.2 c ?_⟩
    · rw [← hk, herm_smul_smul, hw.2.2.1]
    · rw [← smul_left_cancel_iff k, hc, smul_comm, hk]
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem exists_L_mul_fix (hm : 2 ≤ m) {g : SUid frob (m + 2)} (hg : g • v₀ m = v₀ m) :
    ∃ E ∈ L m, (E⁻¹ * g) • v₀ m = v₀ m ∧ (E⁻¹ * g) • u₀ m = u₀ m := by
  have hpar : herm frob (v₀ m) (g • u₀ m) = 1 := by
    have := herm_smul_smul frob g (v₀ m) (u₀ m)
    rw [hg, herm_v₀_u₀] at this
    exact this
  have hiso : herm frob (g • u₀ m) (g • u₀ m) = 0 := by rw [herm_smul_smul, herm_u₀_u₀]
  obtain ⟨E, hE, hEu⟩ := exists_mem_L_smul_u₀ hm hiso hpar
  refine ⟨E, hE, ?_, ?_⟩
  · rw [mul_smul, hg, inv_smul_eq_iff, smul_v₀_of_mem_L hE]
  · rw [mul_smul, ← hEu, inv_smul_smul]

theorem mem_L_of_mem_Stab (hm : 2 ≤ m) (hm3 : m ≠ 3) {g : SUid frob (m + 2)}
    (hg : g • v₀ m = v₀ m) : g ∈ L m := by
  obtain ⟨E, hE, hv', hu'⟩ := exists_L_mul_fix hm hg
  obtain ⟨g₀, hg₀⟩ := exists_block hv' hu'
  have hT : g₀ ∈ T frob m := by
    rw [T_eq_top isUnitaryInvolution_frob hm (fun h => absurd h hm3)]
    exact Subgroup.mem_top _
  obtain ⟨t', ht', htv, htu, htι⟩ := exists_lift hT
  have he : E⁻¹ * g = t' := eq_of_fix hv' hu' htv htu fun z => by rw [hg₀, htι]
  rw [show g = E * (E⁻¹ * g) by group, he]
  exact Subgroup.mul_mem _ hE (perpT_le_L hm ht')

theorem sq_mem_L_of_mem_Stab (hm : 2 ≤ m) (hsq : ∀ g₀ : SUid frob m, g₀ ^ 2 ∈ T frob m)
    {g : SUid frob (m + 2)} (hg : g • v₀ m = v₀ m) : g ^ 2 ∈ L m := by
  obtain ⟨E, hE, hv', hu'⟩ := exists_L_mul_fix hm hg
  generalize hg' : E⁻¹ * g = g' at hv' hu'
  have hgE : g = E * g' := by rw [← hg']; group
  obtain ⟨g₀, hg₀⟩ := exists_block hv' hu'
  obtain ⟨t', ht', htv, htu, htι⟩ := exists_lift (hsq g₀)
  have hv2 : g' ^ 2 • v₀ m = v₀ m := by rw [sq, mul_smul, hv', hv']
  have hu2 : g' ^ 2 • u₀ m = u₀ m := by rw [sq, mul_smul, hu', hu']
  have he : g' ^ 2 = t' := eq_of_fix hv2 hu2 htv htu fun z => by
    rw [htι, sq, sq, mul_smul, mul_smul, hg₀, hg₀]
  have hconj : g' * E * g'⁻¹ ∈ L m := conj_mem_L hv' hE
  rw [hgE, show (E * g') ^ 2 = E * (g' * E * g'⁻¹) * g' ^ 2 by rw [sq, sq]; group, he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hE hconj) (perpT_le_L hm ht')

end CFSG.LargeExtraspecial.AS35ZS
