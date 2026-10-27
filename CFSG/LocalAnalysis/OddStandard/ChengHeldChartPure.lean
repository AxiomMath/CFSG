module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartPos
public import CFSG.LocalAnalysis.OddStandard.ChengHeldFrameKer
public import CFSG.LocalAnalysis.OddStandard.Glue

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.UnbalancedLayer

theorem repPerm_zero : repPerm 0 = 1 := rfl

theorem repPerm_one : repPerm 1 = r₂ := by simp [repPerm, rPerm, realRepWords, genR, r₂]

theorem repPerm_two : repPerm 2 = r₃ := by simp [repPerm, rPerm, realRepWords, genR, r₃]

theorem repPerm_three : repPerm 3 = r₄ := by simp [repPerm, rPerm, realRepWords, genR, r₄]

theorem exists_cv (c : Cover) :
    ∃ w : List (Fin 2 × Bool), c = cv w := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨x.toWord, by rw [cv, FreeGroup.mk_toWord]; rfl⟩

theorem decomp_sigma0
    {r : Equiv.Perm (Fin 42)}
    (hr : r ∈ Sigma0) :
    ∃ t < 64, ∃ k < 4, r = wordPerm (tg t) * repPerm k := by
  obtain ⟨τ, hτ, v, hv, rfl⟩ := hr
  obtain ⟨t, ht, rfl⟩ := exists_tg hτ
  obtain ⟨i, rfl⟩ := exists_vFourEl hv
  refine ⟨t, ht, i.val, i.2, ?_⟩
  fin_cases i
  · simp [vFourEl, repPerm_zero]
  · simp [vFourEl, repPerm_one]
  · simp [vFourEl, repPerm_two]
  · simp [vFourEl, repPerm_three]

section PureSection

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

@[expose] def Pure (l : Cover →* Jhat A) (k : ℕ) (y : G) (hy : y ∈ d.X) : Prop :=
  ∀ w, betaHat A (d.X_sylow.le hy) (l (cv w)) = l (cv (substWord (aut k) w))


theorem real_of_pure {q : Jhat A →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat A}
    (h : IsQSetting q l) {k : ℕ} (hk : k < 36) {y : G} {hy : y ∈ d.X} (hp : Pure d l k y hy) :
    ∀ e, q (betaHat A (d.X_sylow.le hy) e) = repPerm k * q e * (repPerm k)⁻¹ := by
  intro e
  obtain ⟨c, rfl⟩ := h.lsurj e
  obtain ⟨w, rfl⟩ := exists_cv c
  obtain ⟨α, hα, hσα⟩ := exists_alpha hk
  rw [hp w, h.q_l, h.q_l, ← hα, hσα]

theorem mem_centralizer_of_betaHat_eq (h : Hyp G A) {x : G} (hx : x ∈ normalizer (A : Set G))
    (hid : ∀ e, betaHat A hx e = e) : x ∈ centralizer (A : Set G) := by
  have hperf : Group.IsPerfect ↥A := Group.isPerfect_def.mpr h.commutator_eq_top
  rw [← CFSG.OddStandard.coreActionKernel_eq_centralizer hperf h.pPrimeCore_le_center]
  refine mem_coreActionKernel.2 ⟨hx, fun j hj => ?_⟩
  have hmem : j⁻¹ * x⁻¹ * j * x ∈ A := by
    have := conj_mem_of_mem_normalizer hx hj
    rw [show j⁻¹ * x⁻¹ * j * x = j⁻¹ * (x⁻¹ * j * x) by group]
    exact A.mul_mem (A.inv_mem hj) this
  have h1 := (mem_oddIn_iff hmem).2 (by
    have e1 : (⟨j⁻¹ * x⁻¹ * j * x, hmem⟩ : A) = (⟨j, hj⟩ : A)⁻¹ * conjJ A hx ⟨j, hj⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, map_mul, map_inv, ← betaHat_jq, hid, inv_mul_cancel])
  exact h1

theorem mem_centralizer_of_pure_zero (h : Hyp G A) {q : Jhat A →* Equiv.Perm (Fin 42)}
    {l : Cover →* Jhat A} (hQ : IsQSetting q l) {y : G} {hy : y ∈ d.X} (hp : Pure d l 0 y hy) :
    y ∈ centralizer (A : Set G) := by
  have hα0 : ∀ w, cv (substWord (aut 0) w) = cv w := by
    obtain ⟨α, hα, hσα⟩ := exists_alpha (i := 0) (by norm_num)
    have hid : α = MonoidHom.id Cover := by
      refine hom_ext_of_central commutator_cover sigma ker_sigma_le_center ?_
      refine MonoidHom.ext fun c => ?_
      simp [hσα, repPerm_zero]
    intro w
    rw [← hα, hid]
    rfl
  refine mem_centralizer_of_betaHat_eq h (d.X_sylow.le hy) fun e => ?_
  obtain ⟨c, rfl⟩ := hQ.lsurj e
  obtain ⟨w, rfl⟩ := exists_cv c
  rw [hp w, hα0 w]

theorem pure_of_real (P : Pos d) {y : G} (hy : y ∈ d.X) {t k : ℕ} (ht : t < 64) (hk : k < 36)
    (hreal : ∀ e, P.q (betaHat A (d.X_sylow.le hy) e) =
      (wordPerm (tg t) * repPerm k) * P.q e * (wordPerm (tg t) * repPerm k)⁻¹) :
    ∃ s ∈ d.S, ∃ hys : y * s ∈ d.X, Pure d P.l k (y * s) hys := by
  have hβ := betaRep_of_decomp P.isQ (β := betaHat A (d.X_sylow.le hy)) ht hk hreal
  have hq : P.q (nf P.l t 0 0) ∈ T0 := by rw [q_nf P.isQ ht]; exact tg_mem_T0 t ht
  obtain ⟨p, hpS, hpA, hpe⟩ := (P.hT _).1 hq
  refine ⟨p, hpS, d.X.mul_mem hy (d.S_le_X hpS), fun w => ?_⟩
  have hpN : p ∈ normalizer (A : Set G) := le_normalizer hpA
  calc betaHat A (d.X_sylow.le (d.X.mul_mem hy (d.S_le_X hpS))) (P.l (cv w))
      = betaHat A hpN (betaHat A (d.X_sylow.le hy) (P.l (cv w))) :=
        betaHat_mul A (d.X_sylow.le hy) hpN _
    _ = (jq A ⟨p, hpA⟩)⁻¹ * betaHat A (d.X_sylow.le hy) (P.l (cv w)) * jq A ⟨p, hpA⟩ :=
        betaHat_of_mem hpA _
    _ = P.l (cv (substWord (aut k) w)) := by rw [hpe]; exact hβ w

theorem pure_exists (P : Pos d) {y : G} (hy : y ∈ d.X) :
    ∃ k < 4, ∃ t < 64, (∀ e, P.q (betaHat A (d.X_sylow.le hy) e) =
      (wordPerm (tg t) * repPerm k) * P.q e * (wordPerm (tg t) * repPerm k)⁻¹) ∧
      ∃ s ∈ d.S, ∃ hys : y * s ∈ d.X, Pure d P.l k (y * s) hys := by
  obtain ⟨r, hr, hreal⟩ := P.act y hy
  obtain ⟨t, ht, k, hk, rfl⟩ := decomp_sigma0 hr
  exact ⟨k, hk, t, ht, hreal, pure_of_real d P hy ht (by omega) hreal⟩

theorem not_mem_QS_of_pure (h : Hyp G A) {q : Jhat A →* Equiv.Perm (Fin 42)}
    {l : Cover →* Jhat A} (hQ : IsQSetting q l) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {y : G}
    {hy : y ∈ d.X} (hp : Pure d l k y hy) : y ∉ d.QS := by
  intro hyQS
  have hperf : Group.IsPerfect ↥A := Group.isPerfect_def.mpr h.commutator_eq_top
  have hmem : y ∈ withKernel A := by
    have h1 : y ∈ A ⊔ centralizer (A : Set G) :=
      (sup_le (le_sup_of_le_right d.Q_le_centralizer) (le_sup_of_le_left d.S_le_A)) hyQS
    unfold withKernel
    rwa [CFSG.OddStandard.coreActionKernel_eq_centralizer hperf h.pPrimeCore_le_center]
  obtain ⟨e₀, he₀⟩ := exists_inner hmem (d.X_sylow.le hy)
  have hreal := real_of_pure d hQ (by omega : k < 36) hp
  have hu : q e₀ * repPerm k ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_,
      R.mul_mem (S_le_R (hQ.qS e₀)) (repPerm_mem k)⟩
    obtain ⟨e, rfl⟩ := hQ.qsurj s hs
    have h1 := hreal e
    rw [he₀ e, map_mul, map_mul, map_inv] at h1
    calc q e * (q e₀ * repPerm k) = q e₀ * ((q e₀)⁻¹ * q e * q e₀) * repPerm k := by group
      _ = q e₀ * (repPerm k * q e * (repPerm k)⁻¹) * repPerm k := by rw [h1]
      _ = q e₀ * repPerm k * q e := by group
  rw [centralizer_S_inf_R, mem_bot] at hu
  have hρ : repPerm k = (q e₀)⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hρS : repPerm k ∈ S := by rw [hρ]; exact S.inv_mem (hQ.qS e₀)
  interval_cases k
  · exact not_mem_S_r₂ (repPerm_one ▸ hρS)
  · exact not_mem_S_r₃ (repPerm_two ▸ hρS)
  · exact not_mem_S_r₄ (repPerm_three ▸ hρS)

theorem pure_unique (h : Hyp G A) {l : Cover →* Jhat A} (hls : Function.Surjective l) {k : ℕ}
    {y y' : G} {hy : y ∈ d.X} {hy' : y' ∈ d.X} (hp : Pure d l k y hy) (hp' : Pure d l k y' hy') :
    y * y'⁻¹ ∈ d.Q := by
  have hyy : ∀ e, betaHat A (d.X_sylow.le hy) e = betaHat A (d.X_sylow.le hy') e := by
    intro e
    obtain ⟨c, rfl⟩ := hls e
    obtain ⟨w, rfl⟩ := exists_cv c
    rw [hp w, hp' w]
  have hinv := d.X.inv_mem hy'
  have hid : ∀ e, betaHat A (d.X_sylow.le (d.X.mul_mem hy hinv)) e = e := by
    intro e
    rw [betaHat_mul A (d.X_sylow.le hy) (d.X_sylow.le hinv), hyy e]
    have := betaHat_mul A (d.X_sylow.le hy') (d.X_sylow.le hinv) e
    rw [betaHat_eq_self A _ (mul_inv_cancel y')] at this
    exact this.symm
  exact ⟨d.X.mul_mem hy hinv, mem_centralizer_of_betaHat_eq h _ hid⟩

end PureSection

end CFSG.OddStandard.ChengHeld.M1b
