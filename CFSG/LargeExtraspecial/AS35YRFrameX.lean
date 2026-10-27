module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LargeExtraspecial.AS35YRFrameY
public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def refl1 (q : QuadraticForm (ZMod 2) V) (v : V) (hv : q v = 1) :
    V ≃ₗ[ZMod 2] V :=
  letI : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  TauCeti.QuadraticMap.reflection q v

theorem refl1_apply {v : V} (hv : q v = 1) (x : V) : refl1 q v hv x = x + polar q x v • v := by
  let _ : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  have hinv : ⅟(q v) = 1 := by rw [invOf_eq_inv, hv, inv_one]
  change TauCeti.QuadraticMap.reflection q v x = _
  rw [TauCeti.QuadraticMap.reflection_apply, hinv, one_mul, polar_comm, sub_YR]

theorem refl1_mem {v : V} (hv : q v = 1) : refl1 q v hv ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
  letI : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  TauCeti.QuadraticMap.reflection_mem_orthogonalGroup q v

theorem refl1_mul_self {v : V} (hv : q v = 1) : refl1 q v hv * refl1 q v hv = 1 :=
  letI : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  TauCeti.QuadraticMap.reflection_mul_self q v

theorem polar_self_YR (x : V) : polar q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul]
  exact CharTwo.add_self_eq_zero _

theorem finrank_commSpace_refl1 [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {v : V} (hv : q v = 1) : finrank (ZMod 2) (commSpace (refl1 q v hv)) = 1 :=
  letI : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  finrank_commSpace_reflection hq v

theorem even_finrank_commSpace_refl1_mul [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {v w : V} (hv : q v = 1) (hw : q w = 1) :
    Even (finrank (ZMod 2) (commSpace (refl1 q v hv * refl1 q w hw))) := by
  rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hq (refl1_mem hv)
    (refl1_mem hw), finrank_commSpace_refl1 hq hv, finrank_commSpace_refl1 hq hw]
  rfl

theorem polar_eq_one_of_anisotropic {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, u ≠ 0 → q u = 1) {x y : V} (hx : x ∈ U) (hy : y ∈ U) (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) (hxy : x ≠ y) : polar q x y = 1 := by
  have hxy0 : x + y ≠ 0 := by
    intro h
    apply hxy
    have := congrArg (· + y) h
    simpa [add_assoc, add_self_YR] using this
  have h1 := hU _ (U.add_mem hx hy) hxy0
  rw [QuadraticMap.map_add q, hU x hx hx0, hU y hy hy0] at h1
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rw [h11, zero_add] at h1
  exact h1

theorem finrank_le_two_of_anisotropic [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, u ≠ 0 → q u = 1) : finrank (ZMod 2) U ≤ 2 := by
  by_contra h3
  push Not at h3
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := U)
    (n := 3) (by omega)
  have hf' : LinearIndependent (ZMod 2) (fun i => (f i : V)) :=
    hf.map' U.subtype (Submodule.ker_subtype U)
  have hne : ∀ i, (f i : V) ≠ 0 := fun i => hf'.ne_zero i
  have hinj : ∀ i j, i ≠ j → (f i : V) ≠ (f j : V) := fun i j hij h => hij (hf'.injective h)
  have hsum : (f 1 : V) + (f 2 : V) ≠ (f 0 : V) := by
    intro h
    have hrel : (1 : ZMod 2) • (f 0 : V) + (1 : ZMod 2) • (f 1 : V) + (1 : ZMod 2) • (f 2 : V) =
        0 := by
      rw [one_smul, one_smul, one_smul, ← h, add_comm (f 1 : V) (f 2 : V),
        add_assoc (f 2 : V) (f 1 : V) (f 1 : V), add_self_YR, add_zero, add_self_YR]
    have := Fintype.linearIndependent_iff.mp hf' ![1, 1, 1] (by
      simpa [Fin.sum_univ_three] using hrel) 0
    exact absurd this (by decide)
  have hsum0 : (f 1 : V) + (f 2 : V) ≠ 0 := by
    intro h
    apply hinj 1 2 (by decide)
    have := congrArg (· + (f 2 : V)) h
    simpa [add_assoc, add_self_YR] using this
  have h01 := polar_eq_one_of_anisotropic hU (f 0).2 (f 1).2 (hne 0) (hne 1) (hinj 0 1 (by decide))
  have h02 := polar_eq_one_of_anisotropic hU (f 0).2 (f 2).2 (hne 0) (hne 2) (hinj 0 2 (by decide))
  have h012 := polar_eq_one_of_anisotropic hU (f 0).2 (U.add_mem (f 1).2 (f 2).2) (hne 0) hsum0
    (Ne.symm hsum)
  rw [polar_add_right, h01, h02] at h012
  exact absurd h012 (by decide)

theorem exists_two_of_two_le_finrank [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (hU : 2 ≤ finrank (ZMod 2) U) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := U) (n := 2) hU
  have hf' : LinearIndependent (ZMod 2) (fun i => (f i : V)) :=
    hf.map' U.subtype (Submodule.ker_subtype U)
  exact ⟨f 0, (f 0).2, f 1, (f 1).2, hf'.ne_zero 0, hf'.ne_zero 1,
    fun h => absurd (hf'.injective h) (by decide)⟩

namespace Frame

variable (F : Frame q)

abbrev Xp : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {F.a, F.b, F.c, F.c'})

variable {F}

theorem mem_Xp {x : V} : x ∈ F.Xp ↔
    polar q x F.a = 0 ∧ polar q x F.b = 0 ∧ polar q x F.c = 0 ∧ polar q x F.c' = 0 := by
  rw [OrthoF2.mem_orthogonal_iff_polar]
  constructor
  · intro h
    exact ⟨h _ (Submodule.subset_span (by simp)), h _ (Submodule.subset_span (by simp)),
      h _ (Submodule.subset_span (by simp)), h _ (Submodule.subset_span (by simp))⟩
  · rintro ⟨ha, hb, hc, hc'⟩ u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      rcases hu with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hc'
    | zero => exact polar_zero_right _ _
    | add u v _ _ hu hv => rw [polar_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [polar_smul_right, hu, smul_zero]

theorem finrank_Xp_add [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate) :
    finrank (ZMod 2) V ≤ finrank (ZMod 2) F.Xp + 4 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hq]
  have hspan : Submodule.span (ZMod 2) ({F.a, F.b, F.c, F.c'} : Set V) =
      Submodule.span (ZMod 2) (Set.range ![F.a, F.b, F.c, F.c']) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.exists_fin_zero]
    tauto
  have h4 := finrank_range_le_card (R := ZMod 2) ![F.a, F.b, F.c, F.c']
  change finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![F.a, F.b, F.c, F.c'])) ≤ _
    at h4
  rw [← hspan, Fintype.card_fin] at h4
  omega

theorem refl1_fix {v : V} (hvX : v ∈ F.Xp) (hv : q v = 1) :
    refl1 q v hv F.a = F.a ∧ refl1 q v hv F.b = F.b ∧ refl1 q v hv F.c = F.c ∧
      refl1 q v hv F.c' = F.c' := by
  obtain ⟨ha, hb, hc, hc'⟩ := mem_Xp.mp hvX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [refl1_apply, polar_comm]
  · rw [ha, zero_smul, add_zero]
  · rw [hb, zero_smul, add_zero]
  · rw [hc, zero_smul, add_zero]
  · rw [hc', zero_smul, add_zero]

theorem siegel_fix {u w : V} (huX : u ∈ F.Xp) (hwX : w ∈ F.Xp) (hu : q u = 0) (hw : q w = 0)
    (huw : polar q u w = 0) :
    eichler q u w F.a = F.a ∧ eichler q u w F.b = F.b ∧ eichler q u w F.c = F.c ∧
      eichler q u w F.c' = F.c' := by
  obtain ⟨hua, hub, huc, huc'⟩ := mem_Xp.mp huX
  obtain ⟨hwa, hwb, hwc, hwc'⟩ := mem_Xp.mp hwX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [siegel_apply hu hw huw, polar_comm _ _ u, polar_comm _ _ w]
  · rw [hua, hwa, zero_smul, zero_smul, add_zero, add_zero]
  · rw [hub, hwb, zero_smul, zero_smul, add_zero, add_zero]
  · rw [huc, hwc, zero_smul, zero_smul, add_zero, add_zero]
  · rw [huc', hwc', zero_smul, zero_smul, add_zero, add_zero]

namespace RadHyp

variable {P : Subgroup (V ≃ₗ[ZMod 2] V)} (h : F.RadHyp P)
include h

theorem false_of_omega [FiniteDimensional (ZMod 2) V] [Finite P]
    (hq : q.polarBilin.Nondegenerate) {n : ℕ} (hn : 4 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) (hcard : Nat.card P = 2 ^ (2 * n - 3))
    (hrefl : ∀ v ∈ F.Xp, ∀ w ∈ F.Xp, ∀ (hv : q v = 1) (hw : q w = 1), ∀ p ∈ P,
      refl1 q v hv * refl1 q w hw * p * (refl1 q v hv * refl1 q w hw)⁻¹ ∈ P)
    (hsieg : ∀ u ∈ F.Xp, ∀ w ∈ F.Xp, q u = 0 → q w = 0 → polar q u w = 0 → ∀ p ∈ P,
      eichler q u w * p * (eichler q u w)⁻¹ ∈ P) : False := by
  set Y := F.Y P h.inU with hYdef
  have hYX : ∀ y ∈ Y, y ∈ F.Xp := fun y hy => mem_Xp.mpr (h.polar_of_mem_Y hy)
  have hnd : ∀ y ∈ Y, (∀ y' ∈ Y, polar q y y' = 0) → y = 0 :=
    fun y hy => h.eq_zero_of_polar_eq_zero hy
  have h2n : 2 < 2 ^ (2 * n - 3) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ (2 * n - 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨p, hp, hp1, hpt⟩ := exists_ne_one_ne_t (F := F) (P := P) (by rw [hcard]; exact h2n)
  obtain ⟨y, hyY, hy0⟩ := h.exists_ne_zero_mem_Y hp hp1 hpt
  have hdimY : finrank (ZMod 2) Y ≤ n - 2 := by
    have hle := h.card_Y_mul_le
    change Nat.card Y * Nat.card Y ≤ _ at hle
    rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    omega
  obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y₀ ∈ Y, q y₀ = 1 := by
    obtain ⟨y', hy'Y, hyy'⟩ : ∃ y' ∈ Y, polar q y y' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy0 (hnd y hyY hcon)
    have h1 : polar q y y' = 1 := (zmod2_cases_YR _).resolve_left hyy'
    rcases zmod2_cases_YR (q y) with hq0 | hq1
    · rcases zmod2_cases_YR (q y') with hq0' | hq1'
      · refine ⟨y + y', Y.add_mem hyY hy'Y, ?_⟩
        rw [QuadraticMap.map_add q, hq0, hq0', h1, zero_add, zero_add]
      · exact ⟨y', hy'Y, hq1'⟩
    · exact ⟨y, hyY, hq1⟩
  have hy₀X := hYX y₀ hy₀Y
  have hr₀ : ∀ z ∈ Y, refl1 q y₀ hy₀ z ∈ Y := fun z hz => by
    rw [refl1_apply]
    exact Y.add_mem hz (Y.smul_mem _ hy₀Y)
  have hreflY : ∀ w ∈ F.Xp, ∀ hw : q w = 1, ∀ z ∈ Y, refl1 q w hw z ∈ Y := by
    intro w hwX hw z hz
    obtain ⟨g0a, g0b, g0c, g0c'⟩ := refl1_fix hy₀X hy₀
    obtain ⟨g1a, g1b, g1c, g1c'⟩ := refl1_fix hwX hw
    have hgY := h.apply_mem_Y (g := refl1 q y₀ hy₀ * refl1 q w hw)
      (mul_mem (refl1_mem _) (refl1_mem _)) (by simp [g1a, g0a]) (by simp [g1b, g0b])
      (by simp [g1c, g0c]) (by simp [g1c', g0c']) (hrefl y₀ hy₀X w hwX hy₀ hw) hz
    have := hr₀ _ hgY
    rwa [LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (refl1 q y₀ hy₀), refl1_mul_self,
      LinearEquiv.coe_one, id] at this
  have hdich : ∀ w ∈ F.Xp, q w = 1 → w ∈ Y ∨ ∀ z ∈ Y, polar q z w = 0 := by
    intro w hwX hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hwY, z, hz, hzw⟩ := hcon
    have hz1 : polar q z w = 1 := (zmod2_cases_YR _).resolve_left hzw
    have := Y.sub_mem (hreflY w hwX hw z hz) hz
    rw [refl1_apply, hz1, one_smul, add_sub_cancel_left] at this
    exact hwY this
  set W : Submodule (ZMod 2) V := F.Xp ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y with hW
  have hmemW : ∀ x ∈ W, x ∈ F.Xp ∧ ∀ z ∈ Y, polar q x z = 0 := fun x hx =>
    ⟨hx.1, OrthoF2.mem_orthogonal_iff_polar.mp hx.2⟩
  have hYnd : (LinearMap.BilinForm.restrict q.polarBilin Y).Nondegenerate := by
    refine ⟨fun z hz => Subtype.ext (hnd z z.2 fun y' hy' => ?_), fun z hz =>
      Subtype.ext (hnd z z.2 fun y' hy' => ?_)⟩
    · have := hz ⟨y', hy'⟩
      simpa [polarBilin_apply_apply] using this
    · have := hz ⟨y', hy'⟩
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using this
  have hcompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (QuadraticMap.isSymm_polarBilin q).isRefl hYnd
  have hXle : F.Xp ≤ Y ⊔ W := by
    intro x hx
    have hx' : x ∈ Y ⊔ LinearMap.BilinForm.orthogonal q.polarBilin Y :=
      hcompl.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨z, hz, z', hz', rfl⟩ := Submodule.mem_sup.mp hx'
    refine Submodule.mem_sup.mpr ⟨z, hz, z', ⟨?_, hz'⟩, rfl⟩
    have := F.Xp.sub_mem hx (hYX z hz)
    rwa [add_sub_cancel_left] at this
  have hdimX := F.finrank_Xp_add hq
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq Y W
  have hXle' := Submodule.finrank_mono hXle
  have hdimW : 2 ≤ finrank (ZMod 2) W := by omega
  obtain ⟨w₀, hw₀W, w₁, hw₁W, hw₀0, hw₁0, hw₀₁⟩ := exists_two_of_two_le_finrank hdimW
  have hconst : ∀ z ∈ Y, z ≠ 0 → ∀ z' ∈ W, z' ≠ 0 → q z = q z' := by
    intro z hz hz0 z' hz' hz'0
    by_contra hne
    obtain ⟨hz'X, hz'Y⟩ := hmemW z' hz'
    have hpol : polar q z z' = 0 := by rw [polar_comm]; exact hz'Y z hz
    have hsum : q (z + z') = 1 := by
      rw [QuadraticMap.map_add q, hpol, add_zero]
      rcases zmod2_cases_YR (q z) with h0 | h1 <;> rcases zmod2_cases_YR (q z') with h0' | h1'
      · exact absurd (h0.trans h0'.symm) hne
      · rw [h0, h1', zero_add]
      · rw [h1, h0', add_zero]
      · exact absurd (h1.trans h1'.symm) hne
    rcases hdich _ (F.Xp.add_mem (hYX z hz) hz'X) hsum with hmem | hperp
    · have hz'Ymem : z' ∈ Y := by
        have := Y.sub_mem hmem hz
        rwa [add_sub_cancel_left] at this
      exact hz'0 (hnd z' hz'Ymem hz'Y)
    · apply hz0
      refine hnd z hz fun y' hy' => ?_
      have := hperp y' hy'
      rw [polar_add_right, polar_comm q y' z', hz'Y y' hy', add_zero] at this
      rw [polar_comm]
      exact this
  have hqY : ∀ z ∈ Y, z ≠ 0 → q z = 1 := by
    intro z hz hz0
    rcases zmod2_cases_YR (q z) with h0 | h1
    · exfalso
      have hall : ∀ x ∈ Y, q x = 0 := fun x hx => by
        by_cases hx0 : x = 0
        · rw [hx0, QuadraticMap.map_zero]
        · rw [hconst x hx hx0 w₀ hw₀W hw₀0, ← hconst z hz hz0 w₀ hw₀W hw₀0, h0]
      refine hz0 (hnd z hz fun y' hy' => ?_)
      have := hall _ (Y.add_mem hz hy')
      rwa [QuadraticMap.map_add q, hall z hz, hall y' hy', zero_add, zero_add] at this
    · exact h1
  have hqW : ∀ z' ∈ W, z' ≠ 0 → q z' = 1 := fun z' hz' hz'0 =>
    (hconst y hyY hy0 z' hz' hz'0).symm.trans (hqY y hyY hy0)
  have hY2 := finrank_le_two_of_anisotropic hqY
  have hW2 := finrank_le_two_of_anisotropic hqW
  have hdimY2 : 2 ≤ finrank (ZMod 2) Y := by omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁0, hy₂0, hy₁₂⟩ := exists_two_of_two_le_finrank hdimY2
  obtain ⟨hw₀X, hw₀Y⟩ := hmemW w₀ hw₀W
  obtain ⟨hw₁X, hw₁Y⟩ := hmemW w₁ hw₁W
  have hp₁₂ := polar_eq_one_of_anisotropic hqY hy₁ hy₂ hy₁0 hy₂0 hy₁₂
  have hp₀₁ := polar_eq_one_of_anisotropic hqW hw₀W hw₁W hw₀0 hw₁0 hw₀₁
  set u := y₁ + w₀ with hu
  set w := y₂ + w₁ with hw
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hqu : q u = 0 := by
    rw [hu, QuadraticMap.map_add q, hqY y₁ hy₁ hy₁0, hqW w₀ hw₀W hw₀0, polar_comm,
      hw₀Y y₁ hy₁, add_zero, h11]
  have hqw : q w = 0 := by
    rw [hw, QuadraticMap.map_add q, hqY y₂ hy₂ hy₂0, hqW w₁ hw₁W hw₁0, polar_comm,
      hw₁Y y₂ hy₂, add_zero, h11]
  have huw : polar q u w = 0 := by
    rw [hu, hw, polar_add_left, polar_add_right, polar_add_right, hp₁₂, hp₀₁, polar_comm q y₁ w₁,
      hw₁Y y₁ hy₁, hw₀Y y₂ hy₂, add_zero, zero_add, h11]
  have huX : u ∈ F.Xp := F.Xp.add_mem (hYX y₁ hy₁) hw₀X
  have hwX : w ∈ F.Xp := F.Xp.add_mem (hYX y₂ hy₂) hw₁X
  obtain ⟨sa, sb, sc, sc'⟩ := siegel_fix huX hwX hqu hqw huw
  have hS := h.apply_mem_Y (eichler_mem_orthogonalGroup q u w) sa sb sc sc'
    (hsieg u huX w hwX hqu hqw huw) hy₁
  have hpu : polar q y₁ u = 0 := by
    rw [hu, polar_add_right, polar_self_YR, polar_comm, hw₀Y y₁ hy₁, add_zero]
  have hpw : polar q y₁ w = 1 := by
    rw [hw, polar_add_right, hp₁₂, polar_comm, hw₁Y y₁ hy₁, add_zero]
  rw [siegel_apply hqu hqw huw, hpu, hpw, zero_smul, add_zero, one_smul, hu, ← add_assoc,
    add_self_YR, zero_add] at hS
  exact hw₀0 (hnd w₀ hS hw₀Y)

end RadHyp

end Frame

end AS35YR

end CFSG.LargeExtraspecial
