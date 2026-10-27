module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_ker_act_map_iff {𝕊 : Type} [Group 𝕊] {A : Subgroup G}
    (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) {y : G} :
    y ∈ (act A ε).ker.map (normalizer (A : Set G)).subtype ↔ y ∈ coreActionKernel A := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact (act_eq_one_iff ε n).mp hn
  · intro hy
    exact ⟨⟨y, hy.1⟩, (act_eq_one_iff ε _).mpr hy, rfl⟩

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem commutator_mem_Q_of_centralizes (hD : Foote5AutData 𝕊 Lin) {P : Subgroup G}
    (hPS : P ≤ S) (hPR : ∀ a ∈ P, ∀ r ∈ S ⊓ L, a * r = r * a) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b * a⁻¹ * b⁻¹ ∈ Q := by
  have hPN : P ≤ normalizer (L : Set G) := hPS.trans h.S_le
  have hfix : ∀ α ∈ actImage L ε P, ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα ρ hρ
    obtain ⟨p, hp, rfl⟩ := (mem_actImage ε hPN).mp hα
    exact (h.actG_fix_iff ε (hPS hp)).mpr (hPR p hp) ρ hρ
  have hsq := (hD.centralizer_sylow (h.Rbar ε) (actImage L ε P)
    (isPGroup_actImage ε (h.isPGroup_S.to_le hPS)) hfix).1
  have hα := actG_mem_actImage ε hPN ha
  have hβ := actG_mem_actImage ε hPN hb
  have hai := inv_eq_of_mul_eq_one_right (hsq _ hα)
  have hbi := inv_eq_of_mul_eq_one_right (hsq _ hβ)
  have hcomm : actG L ε a * actG L ε b = actG L ε b * actG L ε a := by
    calc actG L ε a * actG L ε b = (actG L ε a * actG L ε b)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hα hβ))).symm
      _ = actG L ε b * actG L ε a := by rw [mul_inv_rev, hai, hbi]
  have haS := hPS ha
  have hbS := hPS hb
  rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem (mul_mem (mul_mem haS hbS) (inv_mem haS))
    (inv_mem hbS)), actG_mul ε (h.S_le (mul_mem (mul_mem haS hbS) (inv_mem haS)))
    (h.S_le (inv_mem hbS)), actG_mul ε (h.S_le (mul_mem haS hbS)) (h.S_le (inv_mem haS)),
    actG_mul ε (h.S_le haS) (h.S_le hbS), actG_inv ε (h.S_le haS), actG_inv ε (h.S_le hbS),
    hcomm]
  group

include ε in
theorem conj_t_eq_of_odd (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hxQ : x ∉ normalizer (Q : Set G))
    (hodd : Odd (orderOf x)) : x * t * x⁻¹ = t := by
  by_contra hxt
  have hxt' : x⁻¹ * t * x⁻¹⁻¹ ≠ t := by
    rw [inv_inv]
    intro h1
    apply hxt
    calc x * t * x⁻¹ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [h1]
      _ = t := by group
  have hR1 := h.inf_conjugate_R_eq_bot hna hx hxt
  have hR2 := h.inf_conjugate_R_eq_bot hna (inv_mem hx) hxt'
  obtain ⟨r₁, hr₁, r₂, hr₂, hr12⟩ := hna
  have hc1 : x⁻¹ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x ∈ Q := by
    have h1 := h.commutator_mem_Q_of_centralizes ε hD
      (conjugate_le_of_mem_normalizer hx inf_le_left)
      (fun a ha r hr => h.commute_of_inf_conjugate_eq_bot hx hR1 hr ha)
      (conj_mem_conjugate hr₁ x) (conj_mem_conjugate hr₂ x)
    rwa [show x⁻¹ * r₁ * x * (x⁻¹ * r₂ * x) * (x⁻¹ * r₁ * x)⁻¹ * (x⁻¹ * r₂ * x)⁻¹ =
      x⁻¹ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x by group] at h1
  have hc2 : x * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x⁻¹ ∈ Q := by
    have h1 := h.commutator_mem_Q_of_centralizes ε hD
      (conjugate_le_of_mem_normalizer (inv_mem hx) inf_le_left)
      (fun a ha r hr => h.commute_of_inf_conjugate_eq_bot (inv_mem hx) hR2 hr ha)
      (conj_mem_conjugate hr₁ x⁻¹) (conj_mem_conjugate hr₂ x⁻¹)
    rwa [show x⁻¹⁻¹ * r₁ * x⁻¹ * (x⁻¹⁻¹ * r₂ * x⁻¹) * (x⁻¹⁻¹ * r₁ * x⁻¹)⁻¹ *
      (x⁻¹⁻¹ * r₂ * x⁻¹)⁻¹ = x * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x⁻¹ by group] at h1
  have hmem : x⁻¹ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x ∈ Q ⊓ conjugate Q (x ^ 2) := by
    refine mem_inf.mpr ⟨hc1, mem_conjugate_iff.mpr ?_⟩
    rw [show x ^ 2 * (x⁻¹ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x) * (x ^ 2)⁻¹ =
      x * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x⁻¹ by group]
    exact hc2
  rw [h.inf_conjugate_eq_bot (pow_mem hx 2) (sq_not_mem_normalizer hxQ hodd), mem_bot] at hmem
  apply hr12
  have hc : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ = 1 := by
    calc r₁ * r₂ * r₁⁻¹ * r₂⁻¹ = x * (x⁻¹ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * x) * x⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  calc r₁ * r₂ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ * (r₂ * r₁) := by group
    _ = r₂ * r₁ := by rw [hc, one_mul]

include ε in
theorem nonabelian_R (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hD : Foote5AutData 𝕊 Lin) (hST : IsSylowOf 2 S ⊤) {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hxQ : x ∉ normalizer (Q : Set G)) :
    ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a := by
  by_contra hab
  have hab' : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a := by
    intro a ha b hb
    by_contra hne
    exact hab ⟨a, ha, b, hb, hne⟩
  have hRab : ∀ a ∈ (h.Rbar ε : Subgroup 𝕊), ∀ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b = b * a := by
    intro a ha b hb
    obtain ⟨r₁, hr₁, rfl⟩ := (h.mem_Rbar_iff ε).mp ha
    obtain ⟨r₂, hr₂, rfl⟩ := (h.mem_Rbar_iff ε).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hab' _ hr₁ _ hr₂)
  have h2gen := hD.two_generated (h.Rbar ε) hRab
  apply h.false_of_gen4 hGH hKG
  refine gen4_of_isSylowOf hST fun U hU => ?_
  set N := normalizer (L : Set G) with hN
  have hUN : U ≤ N := hU.trans h.S_le
  have hK : ∃ s : Finset G, s.card ≤ 2 ∧
      closure (s : Set G) = U ⊓ (act L ε).ker.map N.subtype := by
    set K := U ⊓ (act L ε).ker.map N.subtype with hKdef
    have hKQ : K ≤ Q := by
      intro y hy
      rw [← h.inf_coreActionKernel]
      exact mem_inf.mpr ⟨hU (mem_inf.mp hy).1, (mem_ker_act_map_iff ε).mp (mem_inf.mp hy).2⟩
    refine exists_finset_closure_of_conjugate x ?_
    have hK'S : conjugate K x ≤ S := conjugate_le_of_mem_normalizer hx (hKQ.trans h.QS)
    have h1 := exists_finset_closure_of_ker (act L ε) (hK'S.trans h.S_le) (a := 0) (b := 2)
      ⟨∅, le_rfl, ?_⟩ (h2gen _ (isPGroup_actImage ε (h.isPGroup_S.to_le hK'S)))
    · simpa using h1
    · rw [Finset.coe_empty, Subgroup.closure_empty, eq_comm, eq_bot_iff]
      intro y hy
      have hyQ : y ∈ Q := by
        rw [← h.inf_coreActionKernel]
        exact mem_inf.mpr ⟨hK'S (mem_inf.mp hy).1, (mem_ker_act_map_iff ε).mp (mem_inf.mp hy).2⟩
      have hyQx : y ∈ conjugate Q x := by
        have h2 := (mem_inf.mp hy).1
        rw [mem_conjugate_iff] at h2 ⊢
        exact hKQ h2
      have h3 : y ∈ Q ⊓ conjugate Q x := mem_inf.mpr ⟨hyQ, hyQx⟩
      rwa [h.inf_conjugate_eq_bot hx hxQ] at h3
  have h1 := exists_finset_closure_of_ker (act L ε) hUN (a := 2) (b := 2) hK
    (h2gen _ (isPGroup_actImage ε (h.isPGroup_S.to_le hU)))
  simpa using h1

end Sec5

end CFSG.ComponentClassification.Foote5
