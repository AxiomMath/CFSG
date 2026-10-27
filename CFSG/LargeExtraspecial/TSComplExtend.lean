module

public import CFSG.LargeExtraspecial.TSComplements
public import CFSG.LargeExtraspecial.OrthoF2Eichler
public import CFSG.LargeExtraspecial.OrthoF2Alt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule QuadraticMap
open LinearMap (BilinForm)
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.RankThree.OrthogonalInvolutions

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {q : QuadraticForm (ZMod 2) E}

private theorem polar_eq_zero_of_forall_q_eq_zero {U : Submodule (ZMod 2) E}
    (hU : ∀ u ∈ U, q u = 0) {u v : E} (hu : u ∈ U) (hv : v ∈ U) : polar q u v = 0 :=
  (LinearMap.BilinForm.mem_orthogonal_iff.mp (le_orthogonal_of_totallySingular hU hv)) u hu

theorem exists_extend_of_inf_eq_bot (hq : q.polarBilin.Nondegenerate) {U Y : Submodule (ZMod 2) E}
    (hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U) (hU : ∀ u ∈ U, q u = 0)
    (hY : ∀ y ∈ Y, q y = 0) (hYU : Y ⊓ U = ⊥)
    (hlt : finrank (ZMod 2) Y < finrank (ZMod 2) U) :
    ∃ Y' : Submodule (ZMod 2) E, Y ≤ Y' ∧ finrank (ZMod 2) Y' = finrank (ZMod 2) Y + 1 ∧
      (∀ y ∈ Y', q y = 0) ∧ Y' ⊓ U = ⊥ := by
  set P : Submodule (ZMod 2) E := LinearMap.BilinForm.orthogonal q.polarBilin Y with hP
  have hPfr : finrank (ZMod 2) P = finrank (ZMod 2) E - finrank (ZMod 2) Y :=
    LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq Y
  have hpos : 0 < finrank (ZMod 2) ↥(U ⊓ P) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U P
    have h1 : finrank (ZMod 2) ↥(U ⊔ P) ≤ finrank (ZMod 2) E := Submodule.finrank_le _
    have h2 : finrank (ZMod 2) Y ≤ finrank (ZMod 2) E := Submodule.finrank_le Y
    omega
  have hne : U ⊓ P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨x, hxUP, hx0⟩ := (Submodule.ne_bot_iff (U ⊓ P)).mp hne
  obtain ⟨hxU, hxP⟩ := Submodule.mem_inf.mp hxUP
  have hxY : x ∉ Y := by
    intro hxY
    refine hx0 ?_
    have hmem : x ∈ Y ⊓ U := Submodule.mem_inf.mpr ⟨hxY, hxU⟩
    rwa [hYU, Submodule.mem_bot] at hmem
  have hxnot : x ∉ LinearMap.BilinForm.orthogonal q.polarBilin P := by
    rw [hP, LinearMap.BilinForm.orthogonal_orthogonal (B := q.polarBilin) hq
      (isRefl_polarBilin q)]
    exact hxY
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxnot
  push Not at hxnot
  obtain ⟨v, hvP, hvx⟩ := hxnot
  have hvx1 : polar q v x = 1 := by
    refine zmod2_eq_one_of_ne_zero ?_
    intro h0
    exact hvx (by rw [polarBilin_apply_apply]; exact h0)
  have hqx : q x = 0 := hU x hxU
  have hβP : v + q v • x ∈ P := P.add_mem hvP (P.smul_mem (q v) hxP)
  have hqβ : q (v + q v • x) = 0 := by
    rw [QuadraticMap.map_add (f := ⇑q), map_smul_zmod2 q, hqx, mul_zero, polar_smul_right, hvx1,
      smul_eq_mul, mul_one, add_zero]
    exact zmod2_add_self (q v)
  have hβx : polar q (v + q v • x) x = 1 := by
    rw [polar_add_left, polar_smul_left, polar_self_eq_zero q x, smul_zero, add_zero, hvx1]
  have hβ0 : v + q v • x ≠ 0 := by
    intro h
    rw [h, polar_zero_left] at hβx
    exact zero_ne_one hβx
  have hβnotY : v + q v • x ∉ Y := by
    intro hmem
    have h0 : polar q (v + q v • x) x = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hxP) _ hmem
    rw [h0] at hβx
    exact zero_ne_one hβx
  have hdisj : Y ⊓ Submodule.span (ZMod 2) {v + q v • x} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzY, hzspan⟩ := Submodule.mem_inf.mp hz
    rcases mem_span_singleton_iff.mp hzspan with h | h
    · exact h
    · exact absurd (h ▸ hzY) hβnotY
  refine ⟨Y ⊔ Submodule.span (ZMod 2) {v + q v • x}, le_sup_left, ?_, ?_, ?_⟩
  · have h :=
      Submodule.finrank_sup_add_finrank_inf_eq Y (Submodule.span (ZMod 2) {v + q v • x})
    rw [hdisj, finrank_bot, finrank_span_singleton hβ0, add_zero] at h
    omega
  · intro z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    rcases mem_span_singleton_iff.mp hw with rfl | rfl
    · simpa using hY y hy
    · have hyβ : polar q y (v + q v • x) = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hβP) y hy
      rw [QuadraticMap.map_add (f := ⇑q), hY y hy, hqβ, hyβ]
      simp
  · rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzY', hzU⟩ := Submodule.mem_inf.mp hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hzY'
    rcases mem_span_singleton_iff.mp hw with rfl | rfl
    · have hyU : y ∈ U := by simpa using hzU
      have hmem : y ∈ Y ⊓ U := Submodule.mem_inf.mpr ⟨hy, hyU⟩
      rw [hYU, Submodule.mem_bot] at hmem
      simpa using hmem
    · have h0 : polar q (y + (v + q v • x)) x = 0 :=
        polar_eq_zero_of_forall_q_eq_zero hU hzU hxU
      have hyx : polar q y x = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hxP) y hy
      rw [polar_add_left, hyx, zero_add, hβx] at h0
      exact absurd h0 one_ne_zero

private theorem exists_mem_tsCompl_of_finrank_add_eq (hq : q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) E} (hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U)
    (hU : ∀ u ∈ U, q u = 0) (k : ℕ) :
    ∀ Y : Submodule (ZMod 2) E, finrank (ZMod 2) Y + k = finrank (ZMod 2) U →
      (∀ y ∈ Y, q y = 0) → Y ⊓ U = ⊥ → ∃ B ∈ tsCompl q U, Y ≤ B := by
  induction k with
  | zero =>
    intro Y hk hY hYU
    have hYfr : finrank (ZMod 2) Y = finrank (ZMod 2) U := by omega
    have hsup : U ⊔ Y = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq U Y
      rw [inf_comm, hYU, finrank_bot, add_zero] at h1
      have h2 := LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq U
      rw [hUU] at h2
      have h3 : finrank (ZMod 2) U ≤ finrank (ZMod 2) E := Submodule.finrank_le U
      omega
    refine ⟨Y, ⟨IsCompl.of_eq (by simpa [inf_comm] using hYU) hsup, hY⟩, le_rfl⟩
  | succ k ih =>
    intro Y hk hY hYU
    have hlt : finrank (ZMod 2) Y < finrank (ZMod 2) U := by omega
    obtain ⟨Y', hYY', hfr, hY', hY'U⟩ := exists_extend_of_inf_eq_bot hq hUU hU hY hYU hlt
    obtain ⟨B, hB, hY'B⟩ := ih Y' (by omega) hY' hY'U
    exact ⟨B, hB, hYY'.trans hY'B⟩

theorem exists_mem_tsCompl_of_le (hq : q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) E} (hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U)
    (hU : ∀ u ∈ U, q u = 0) {Y : Submodule (ZMod 2) E} (hY : ∀ y ∈ Y, q y = 0)
    (hYU : Y ⊓ U = ⊥) : ∃ B ∈ tsCompl q U, Y ≤ B := by
  have hle : finrank (ZMod 2) Y ≤ finrank (ZMod 2) U := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U Y
    rw [inf_comm, hYU, finrank_bot, add_zero] at h1
    have h2 := LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq U
    rw [hUU] at h2
    have h3 : finrank (ZMod 2) ↥(U ⊔ Y) ≤ finrank (ZMod 2) E := Submodule.finrank_le _
    have h4 : finrank (ZMod 2) U ≤ finrank (ZMod 2) E := Submodule.finrank_le U
    omega
  obtain ⟨k, hk⟩ := Nat.le.dest hle
  exact exists_mem_tsCompl_of_finrank_add_eq hq hUU hU k Y hk hY hYU

section DimensionSix

variable {t : E ≃ₗ[ZMod 2] E}

private abbrev TMap (t : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E := (t : E →ₗ[ZMod 2] E) - 1

private theorem TMap_TMap_eq_zero {t : E ≃ₗ[ZMod 2] E} (htt : t * t = 1) (v : E) :
    t (t v - v) - (t v - v) = 0 := by
  have h := commSpace_le_fixSpace htt (sub_mem_commSpace t v)
  rw [mem_fixSpace] at h
  rw [h, sub_self]

private theorem orthogonal_eq_self_of_finrank_three (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E}
    (hU3 : finrank (ZMod 2) U = 3) (hU : ∀ u ∈ U, q u = 0) :
    LinearMap.BilinForm.orthogonal q.polarBilin U = U := by
  have hfr := LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq U
  rw [hE, hU3] at hfr
  have hEq : U = LinearMap.BilinForm.orthogonal q.polarBilin U :=
    Submodule.eq_of_le_of_finrank_eq (le_orthogonal_of_totallySingular hU) (by omega)
  exact hEq.symm

private theorem polar_sub_self_eq_map_sub {t : E ≃ₗ[ZMod 2] E}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) (x : E) :
    polar q (t x - x) x = q (t x - x) := by
  rw [map_sub_eq_polar ht]
  conv_rhs => rw [show t x = (t x - x) + x by abel]
  rw [polar_add_left, polar_self_eq_zero q x, add_zero]

theorem exists_commSpace_eq_span_pair_of_stabilizes (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {t : E ≃ₗ[ZMod 2] E}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) (htt : t * t = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (ht1 : ∃ u ∈ U, t u ≠ u) :
    ∃ c ∈ U, ∃ ℓ ∉ U, c ≠ 0 ∧ commSpace t = Submodule.span (ZMod 2) {c, ℓ} := by
  classical
  have hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U :=
    orthogonal_eq_self_of_finrank_three hq hE hU3 hU
  obtain ⟨u₀, hu₀, htu₀⟩ := ht1
  set c : E := t u₀ - u₀ with hcdef
  have hcU : c ∈ U := U.sub_mem (htU u₀ hu₀) hu₀
  have hc0 : c ≠ 0 := by
    intro h
    exact htu₀ (sub_eq_zero.mp h)
  let TU : U →ₗ[ZMod 2] U :=
    ((TMap t).comp U.subtype).codRestrict U (fun u => by
      rw [LinearMap.comp_apply, TMap]
      exact U.sub_mem (htU _ u.2) u.2)
  have hTU_apply : ∀ u : U, ((TU u : U) : E) = t (u : E) - (u : E) := by
    intro u
    rfl
  have hTU_sq : ∀ u : U, TU (TU u) = 0 := by
    intro u
    apply Subtype.ext
    rw [hTU_apply, hTU_apply, Submodule.coe_zero]
    exact TMap_TMap_eq_zero htt (u : E)
  have hTU_ne : TU ≠ 0 := by
    intro h
    have hz : TU ⟨u₀, hu₀⟩ = 0 := by rw [h, LinearMap.zero_apply]
    have hzE : ((TU ⟨u₀, hu₀⟩ : U) : E) = 0 := by rw [hz]; rfl
    rw [hTU_apply] at hzE
    exact htu₀ (sub_eq_zero.mp hzE)
  have hTU_le : LinearMap.range TU ≤ LinearMap.ker TU := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    exact hTU_sq u
  have hTU_fr : finrank (ZMod 2) (LinearMap.range TU) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker TU
    have h2 : finrank (ZMod 2) (LinearMap.range TU) ≤ finrank (ZMod 2) (LinearMap.ker TU) :=
      Submodule.finrank_mono hTU_le
    have h3 : 1 ≤ finrank (ZMod 2) (LinearMap.range TU) := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      exact hTU_ne (LinearMap.range_eq_bot.mp hbot)
    rw [hU3] at h1
    omega
  have hc_range : (⟨c, hcU⟩ : U) ∈ LinearMap.range TU :=
    ⟨⟨u₀, hu₀⟩, by
      apply Subtype.ext
      rw [hTU_apply]⟩
  have hc_span : LinearMap.range TU = Submodule.span (ZMod 2) {⟨c, hcU⟩} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hTU_fr hc_range (by
      intro h
      exact hc0 (congrArg Subtype.val h))
  have hTU_span : ∀ u : E, u ∈ U → t u - u ∈ Submodule.span (ZMod 2) {c} := by
    intro u hu
    have hmem : (⟨t u - u, U.sub_mem (htU u hu) hu⟩ : U) ∈ LinearMap.range TU :=
      ⟨⟨u, hu⟩, by
        apply Subtype.ext
        rw [hTU_apply]⟩
    rw [hc_span] at hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact Submodule.mem_span_singleton.mpr ⟨a, congrArg Subtype.val ha⟩
  have hmemU : ∀ v : E, t v - v ∈ U ↔ polar q v c = 0 := by
    intro v
    rw [← hUU, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have h1 : polar q u₀ (t v - v) = 0 := by simpa using h u₀ hu₀
      have h2 : polar q (t v - v) u₀ = 0 := by rwa [polar_comm] at h1
      rw [polar_sub_eq_polar_sub ht htt] at h2
      exact h2
    · intro h y hy
      have hgoal : polar q (t v - v) y = 0 := by
        rw [polar_sub_eq_polar_sub ht htt]
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hTU_span y hy)
        rw [← ha, polar_smul_right, h, smul_zero]
      rwa [polar_comm] at hgoal
  have hsep : ∃ γ : E, polar q γ c ≠ 0 := by
    by_contra h
    push Not at h
    refine hc0 (hq.2 c ?_)
    intro y
    rw [polarBilin_apply_apply]
    exact h y
  obtain ⟨γ, hγc⟩ := hsep
  have hγc1 : polar q γ c = 1 := zmod2_eq_one_of_ne_zero hγc
  set ℓ : E := t γ - γ with hℓdef
  have hℓc : polar q ℓ c = 0 := by
    rw [hℓdef, polar_sub_eq_polar_sub ht htt]
    have hc : t c - c = 0 := by
      rw [hcdef]
      exact TMap_TMap_eq_zero htt u₀
    rw [hc, polar_zero_right]
  have hℓU : ℓ ∉ U := by
    intro hℓ
    have h0 : polar q γ c = 0 := (hmemU γ).mp (by rwa [hℓdef] at hℓ)
    rw [hγc1] at h0
    exact one_ne_zero h0
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    exact hℓU (by rw [h]; exact U.zero_mem)
  set C : Submodule (ZMod 2) E :=
    LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {c}) with hC
  have hCfr : finrank (ZMod 2) C = 5 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq
      (Submodule.span (ZMod 2) {c})
    rw [hE, finrank_span_singleton hc0] at h
    rw [hC]
    omega
  have hcC : c ∈ C := by
    rw [hC, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polarBilin_apply_apply, polar_smul_left, polar_self_eq_zero q c, smul_zero]
  have hUC : U ≤ C := by
    intro u hu
    rw [hC, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polarBilin_apply_apply, polar_smul_left,
      polar_eq_zero_of_forall_q_eq_zero hU hcU hu, smul_zero]
  have hℓC : ℓ ∈ C := by
    rw [hC, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polarBilin_apply_apply, polar_smul_left, polar_comm, hℓc, smul_zero]
  set L : Submodule (ZMod 2) E := Submodule.span (ZMod 2) {ℓ} with hL
  have hUdisjL : U ⊓ L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzU, hzL⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzL
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact ha.symm
    · rw [one_smul] at ha
      exact absurd (ha ▸ hzU) hℓU
  have hMfr : finrank (ZMod 2) ↥(U ⊔ L) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U L
    rw [hUdisjL, finrank_bot, hL, finrank_span_singleton hℓ0, hU3, add_zero] at h
    omega
  have hMleC : U ⊔ L ≤ C := sup_le hUC (by
    rw [hL, Submodule.span_le]
    rintro z rfl
    exact hℓC)
  have hMltC : U ⊔ L < C := by
    rcases lt_or_eq_of_le hMleC with h | h
    · exact h
    · rw [← h, hMfr] at hCfr
      omega
  obtain ⟨μ, hμC, hμM⟩ := SetLike.exists_of_lt hMltC
  have hμ0 : μ ≠ 0 := by
    intro h
    exact hμM (h ▸ (U ⊔ L).zero_mem)
  have hspanC : (U ⊔ L) ⊔ Submodule.span (ZMod 2) {μ} = C := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hMleC ?_) ?_
    · rw [Submodule.span_le]
      rintro z rfl
      exact hμC
    · have hdisj : (U ⊔ L) ⊓ Submodule.span (ZMod 2) {μ} = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro z hz
        obtain ⟨hzM, hzμ⟩ := Submodule.mem_inf.mp hz
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzμ
        rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
        · rw [zero_smul] at ha
          exact ha.symm
        · rw [one_smul] at ha
          exact absurd (ha ▸ hzM) hμM
      have h := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ L) (Submodule.span (ZMod 2) {μ})
      rw [hdisj, finrank_bot, finrank_span_singleton hμ0, add_zero, hMfr] at h
      rw [hCfr]
      omega
  have hCorth : LinearMap.BilinForm.orthogonal q.polarBilin C = Submodule.span (ZMod 2) {c} := by
    rw [hC, LinearMap.BilinForm.orthogonal_orthogonal (B := q.polarBilin) hq
      (isRefl_polarBilin q)]
  have hμc' : polar q c μ = 0 := by
    simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp hμC) c
      (Submodule.mem_span_singleton_self c)
  have hμc : polar q μ c = 0 := by rwa [polar_comm] at hμc'
  have hTμU : t μ - μ ∈ U := (hmemU μ).mpr hμc
  have hTℓ : t ℓ - ℓ = 0 := by
    rw [hℓdef]
    exact TMap_TMap_eq_zero htt γ
  have hTU_L : ∀ r : E, r ∈ U ⊔ L → t r - r ∈ Submodule.span (ZMod 2) {c} := by
    intro r hr
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hr
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have h1 : t (u + b • ℓ) - (u + b • ℓ) = (t u - u) + b • (t ℓ - ℓ) := by
      rw [map_add, map_smul]
      module
    rw [h1, hTℓ, smul_zero, add_zero]
    exact hTU_span u hu
  have hTμ_span : t μ - μ ∈ Submodule.span (ZMod 2) {c} := by
    rw [← hCorth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hself : polar q y (t μ - μ) = polar q (t y - y) μ :=
      (polar_sub_eq_polar_sub ht htt y μ).symm
    rw [polarBilin_apply_apply, hself]
    rw [← hspanC] at hy
    obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have h1 : t (r + a • μ) - (r + a • μ) = (t r - r) + a • (t μ - μ) := by
      rw [map_add, map_smul]
      module
    rw [h1, polar_add_left, polar_smul_left]
    have h2 : polar q (t r - r) μ = 0 := by
      simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp hμC) _ (hTU_L r hr)
    have h3 : polar q (t μ - μ) μ = 0 := by
      rw [polar_sub_self_eq_map_sub ht]
      exact hU _ hTμU
    rw [h2, h3, smul_zero, add_zero]
  have hkey : ∀ v : E, v ∈ C → t v - v ∈ Submodule.span (ZMod 2) {c} := by
    intro v hv
    rw [← hspanC] at hv
    obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have h1 : t (r + a • μ) - (r + a • μ) = (t r - r) + a • (t μ - μ) := by
      rw [map_add, map_smul]
      module
    rw [h1]
    exact Submodule.add_mem _ (hTU_L r hr) (Submodule.smul_mem _ a hTμ_span)
  have hγC : γ ∉ C := by
    intro hγ
    have h0 : polar q c γ = 0 := by
      simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp hγ) c
        (Submodule.mem_span_singleton_self c)
    rw [polar_comm, hγc1] at h0
    exact one_ne_zero h0
  have hγ0 : γ ≠ 0 := by
    intro h
    exact hγC (by rw [h]; exact C.zero_mem)
  have hCγ : C ⊔ Submodule.span (ZMod 2) {γ} = ⊤ := by
    have hdisj : C ⊓ Submodule.span (ZMod 2) {γ} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨hzC, hzγ⟩ := Submodule.mem_inf.mp hz
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzγ
      rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
      · rw [zero_smul] at ha
        exact ha.symm
      · rw [one_smul] at ha
        exact absurd (ha ▸ hzC) hγC
    have h := Submodule.finrank_sup_add_finrank_inf_eq C (Submodule.span (ZMod 2) {γ})
    rw [hdisj, finrank_bot, finrank_span_singleton hγ0, hCfr, add_zero] at h
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [h, hE]
  have hcomm_le : commSpace t ≤ Submodule.span (ZMod 2) {c, ℓ} := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have hw : w ∈ C ⊔ Submodule.span (ZMod 2) {γ} := by
      rw [hCγ]
      exact Submodule.mem_top
    obtain ⟨x, hxC, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    have h1 : t (x + a • γ) - (x + a • γ) = (t x - x) + a • (t γ - γ) := by
      rw [map_add, map_smul]
      module
    rw [h1]
    have hx' : t x - x ∈ Submodule.span (ZMod 2) ({c, ℓ} : Set E) := by
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hkey x hxC)
      exact Submodule.mem_span_pair.mpr ⟨b, 0, by rw [← hb, zero_smul, add_zero]⟩
    have hℓ' : ℓ ∈ Submodule.span (ZMod 2) ({c, ℓ} : Set E) :=
      Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
    exact Submodule.add_mem _ hx' (Submodule.smul_mem _ a hℓ')
  have hcomm_ge : Submodule.span (ZMod 2) {c, ℓ} ≤ commSpace t := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact sub_mem_commSpace t u₀
    · exact sub_mem_commSpace t γ
  exact ⟨c, hcU, ℓ, hℓU, hc0, le_antisymm hcomm_le hcomm_ge⟩

theorem finrank_commSpace_eq_two_of_stabilizes (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {t : E ≃ₗ[ZMod 2] E}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) (htt : t * t = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (ht1 : ∃ u ∈ U, t u ≠ u) :
    finrank (ZMod 2) (commSpace t) = 2 := by
  obtain ⟨c, hcU, ℓ, hℓU, hc0, hspan⟩ :=
    exists_commSpace_eq_span_pair_of_stabilizes hq hE hU3 hU ht htt htU ht1
  rw [hspan]
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    exact hℓU (by rw [h]; exact U.zero_mem)
  have hcℓ : c ≠ ℓ := by
    intro h
    exact hℓU (by rw [← h]; exact hcU)
  have hli : LinearIndependent (ZMod 2) ![c, ℓ] :=
    linearIndependent_pair_iff.mpr ⟨hc0, hℓ0, hcℓ⟩
  exact finrank_span_pair hli

theorem finrank_fixSpace_eq_four_of_stabilizes (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {t : E ≃ₗ[ZMod 2] E}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) (htt : t * t = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (ht1 : ∃ u ∈ U, t u ≠ u) :
    finrank (ZMod 2) (fixSpace t) = 4 := by
  have h1 := finrank_commSpace_add_finrank_fixSpace t
  have h2 := finrank_commSpace_eq_two_of_stabilizes hq hE hU3 hU ht htt htU ht1
  omega

theorem exists_mem_tsCompl_map_eq (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {t : E ≃ₗ[ZMod 2] E}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) (htt : t * t = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (ht1 : ∃ u ∈ U, t u ≠ u)
    (hts : ∀ v ∈ commSpace t, q v = 0) :
    ∃ B ∈ tsCompl q U, B.map (t : E →ₗ[ZMod 2] E) = B := by
  classical
  obtain ⟨c, hcU, ℓ, hℓU, hc0, hspan⟩ :=
    exists_commSpace_eq_span_pair_of_stabilizes hq hE hU3 hU ht htt htU ht1
  have hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U :=
    orthogonal_eq_self_of_finrank_three hq hE hU3 hU
  have hc_comm : c ∈ commSpace t := by
    rw [hspan]
    exact Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hℓ_comm : ℓ ∈ commSpace t := by
    rw [hspan]
    exact Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
  have hqc : q c = 0 := hts c hc_comm
  have hqℓ : q ℓ = 0 := hts ℓ hℓ_comm
  have hcℓ : polar q c ℓ = 0 := polar_commSpace_eq_zero ht htt hc_comm hℓ_comm
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    exact hℓU (by rw [h]; exact U.zero_mem)
  have hcℓne : c ≠ ℓ := by
    intro h
    exact hℓU (by rw [← h]; exact hcU)
  have hli : LinearIndependent (ZMod 2) ![c, ℓ] :=
    linearIndependent_pair_iff.mpr ⟨hc0, hℓ0, hcℓne⟩
  have hfix : ∀ x : E, polar q c x = 0 → polar q ℓ x = 0 → t x = x := by
    intro x hxc hxℓ
    have hx : x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace t) := by
      rw [hspan]
      exact mem_orthogonal_span_pair_iff.mpr ⟨hxc, hxℓ⟩
    have hx' : x ∈ fixSpace t := by
      rw [fixSpace_eq_orthogonal_commSpace hq ht htt]
      exact hx
    rwa [mem_fixSpace] at hx'
  have hcomm : commSpace t ≤ Submodule.span (ZMod 2) {c, ℓ} := by rw [hspan]
  have hcases := eq_one_or_eq_eichler_of_totallySingular hq hli hqc hqℓ hcℓ ht hcomm hfix
  have ht_ne_one : t ≠ 1 := by
    obtain ⟨u, hu, htu⟩ := ht1
    intro h
    exact htu (by rw [h]; rfl)
  have hteil : t = CFSG.ClassicalGroups.Orthogonal.eichler q c ℓ :=
    hcases.resolve_left ht_ne_one
  have hY : ∀ y ∈ Submodule.span (ZMod 2) {ℓ}, q y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul_zmod2 q, hqℓ, mul_zero]
  have hYU : Submodule.span (ZMod 2) {ℓ} ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzU⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzL
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact ha.symm
    · rw [one_smul] at ha
      exact absurd (ha ▸ hzU) hℓU
  obtain ⟨B, hB, hYB⟩ := exists_mem_tsCompl_of_le hq hUU hU hY hYU
  refine ⟨B, hB, ?_⟩
  have hℓB : ℓ ∈ B := hYB (Submodule.mem_span_singleton_self ℓ)
  have hmaple : B.map (t : E →ₗ[ZMod 2] E) ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    have htb : CFSG.ClassicalGroups.Orthogonal.eichler q c ℓ b =
        b + polar q b c • ℓ + (polar q b ℓ + q ℓ * polar q b c) • c :=
      eichler_apply_zmod2 (a := c) (u := ℓ) hqc hcℓ b
    have htbeq : (t : E →ₗ[ZMod 2] E) b = CFSG.ClassicalGroups.Orthogonal.eichler q c ℓ b := by
      have h := congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E → E) b) hteil
      simpa using h
    have hbℓ : polar q b ℓ = 0 := polar_eq_zero_of_forall_q_eq_zero hB.2 hb hℓB
    rw [htbeq, htb, hbℓ, hqℓ]
    simpa using B.add_mem hb (B.smul_mem (polar q b c) hℓB)
  exact Submodule.eq_of_le_of_finrank_eq hmaple (LinearEquiv.finrank_map_eq t B)

private theorem finrank_ker_eq_pred {ψ : E →ₗ[ZMod 2] ZMod 2} (hψ : ψ ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker ψ) = finrank (ZMod 2) E - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have hne : LinearMap.range ψ ≠ ⊥ := fun h => hψ (LinearMap.range_eq_bot.mp h)
  have hpos : 0 < finrank (ZMod 2) (LinearMap.range ψ) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hne
  have hle : finrank (ZMod 2) (LinearMap.range ψ) ≤ finrank (ZMod 2) (ZMod 2) :=
    Submodule.finrank_le _
  rw [Module.finrank_self] at hle
  omega

private theorem finrank_inf_orthogonal_span_eq_two (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {B : Submodule (ZMod 2) E}
    (hB3 : finrank (ZMod 2) B = 3) (hBtot : ∀ b ∈ B, q b = 0) {x : E} (hx0 : x ≠ 0)
    (hxB : x ∉ B) :
    finrank (ZMod 2) ↥(B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {x})) = 2 := by
  set P : Submodule (ZMod 2) E :=
    LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}) with hP
  have hPfr : finrank (ZMod 2) P = 5 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := q.polarBilin) hq
      (Submodule.span (ZMod 2) {x})
    rw [hE, finrank_span_singleton hx0] at h
    rw [hP]
    omega
  have hBB : LinearMap.BilinForm.orthogonal q.polarBilin B = B :=
    orthogonal_eq_self_of_finrank_three hq hE hB3 hBtot
  have hnotle : ¬ B ≤ P := by
    intro hle
    have hxorth : x ∈ LinearMap.BilinForm.orthogonal q.polarBilin B := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b hb
      have hbP : b ∈ P := hle hb
      rw [hP] at hbP
      have h0 : polar q b x = 0 := by
        rw [polar_comm]
        exact mem_orthogonal_span_singleton_iff.mp hbP
      simpa using h0
    rw [hBB] at hxorth
    exact hxB hxorth
  have hlt : P < B ⊔ P := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro h
    exact hnotle (by rw [h]; exact le_sup_left)
  have hsup : B ⊔ P = ⊤ := by
    have h1 : finrank (ZMod 2) P < finrank (ZMod 2) ↥(B ⊔ P) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank (ZMod 2) ↥(B ⊔ P) ≤ finrank (ZMod 2) E := Submodule.finrank_le _
    refine Submodule.eq_top_of_finrank_eq ?_
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq B P
  rw [hsup, finrank_top, hB3, hPfr, hE] at h
  omega

private theorem exists_pair_span_sup_span_singleton (hE : finrank (ZMod 2) E = 6)
    {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3) {x : E} (hxU : x ∈ U)
    (hx0 : x ≠ 0) :
    ∃ u w : E, u ∈ U ∧ w ∈ U ∧ LinearIndependent (ZMod 2) ![u, w] ∧
      Submodule.span (ZMod 2) {x} ⊔ Submodule.span (ZMod 2) {u, w} = U ∧
      Submodule.span (ZMod 2) {x} ⊓ Submodule.span (ZMod 2) {u, w} = ⊥ := by
  obtain ⟨ψ, hψx, -⟩ :=
    Submodule.exists_le_ker_of_notMem (p := (⊥ : Submodule (ZMod 2) E)) (v := x)
      (by simpa using hx0)
  set K : Submodule (ZMod 2) E := LinearMap.ker ψ with hK
  have hψne : ψ ≠ 0 := by
    intro h0
    rw [h0] at hψx
    exact hψx rfl
  have hψx1 : ψ x = 1 := zmod2_eq_one_of_ne_zero hψx
  have hKfr : finrank (ZMod 2) K = 5 := by
    have h := finrank_ker_eq_pred hψne
    rw [hE] at h
    rw [hK]
    omega
  have hxK : x ∉ K := by
    rw [hK, LinearMap.mem_ker]
    exact hψx
  have hUK : U ⊔ K = ⊤ := by
    have hne : U ⊔ K ≠ K := by
      intro h
      exact hxK (by rw [← h]; exact Submodule.mem_sup_left hxU)
    have hlt : K < U ⊔ K := lt_of_le_of_ne le_sup_right (Ne.symm hne)
    have h1 : finrank (ZMod 2) K < finrank (ZMod 2) ↥(U ⊔ K) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank (ZMod 2) ↥(U ⊔ K) ≤ finrank (ZMod 2) E := Submodule.finrank_le _
    refine Submodule.eq_top_of_finrank_eq ?_
    omega
  have hVfr : finrank (ZMod 2) ↥(U ⊓ K) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U K
    rw [hUK, finrank_top, hU3, hKfr, hE] at h
    omega
  have hVU : U ⊓ K ≤ U := inf_le_left
  have hxV : x ∉ U ⊓ K := fun h => hxK (Submodule.mem_inf.mp h).2
  obtain ⟨u, w, hli, hspanuw⟩ := exists_pair_of_finrank_eq_two hVfr
  have huV : u ∈ U ⊓ K := by rw [← hspanuw]; exact Submodule.subset_span (by simp)
  have hwV : w ∈ U ⊓ K := by rw [← hspanuw]; exact Submodule.subset_span (by simp)
  have hdisj : Submodule.span (ZMod 2) {x} ⊓ (U ⊓ K) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzV⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzX
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact ha.symm
    · rw [one_smul] at ha
      exact absurd (ha ▸ hzV) hxV
  have hfr : finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {x} ⊔ (U ⊓ K)) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {x}) (U ⊓ K)
    rw [hdisj, finrank_bot, finrank_span_singleton hx0, hVfr, add_zero] at h
    omega
  refine ⟨u, w, hVU huV, hVU hwV, hli, ?_, ?_⟩
  · rw [hspanuw]
    refine Submodule.eq_of_le_of_finrank_eq (sup_le ?_ hVU) (by rw [hfr, hU3])
    rw [Submodule.span_le]
    rintro z rfl
    exact hxU
  · rw [hspanuw]
    exact hdisj

theorem exists_mem_tsCompl_inf_le (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {x : E} (hxU : x ∈ U) (hx0 : x ≠ 0)
    {W : Submodule (ZMod 2) E} (hW3 : finrank (ZMod 2) W = 3) (hW : ∀ w ∈ W, q w = 0)
    (hWU : W ⊓ U = Submodule.span (ZMod 2) {x}) :
    ∃ B ∈ tsCompl q U,
      B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}) ≤ W := by
  classical
  have hUU := orthogonal_eq_self_of_finrank_three hq hE hU3 hU
  have hxW : x ∈ W := by
    have h : x ∈ W ⊓ U := by rw [hWU]; exact Submodule.mem_span_singleton_self x
    exact (Submodule.mem_inf.mp h).1
  obtain ⟨ψ, hψx, -⟩ :=
    Submodule.exists_le_ker_of_notMem (p := (⊥ : Submodule (ZMod 2) E)) (v := x)
      (by simpa using hx0)
  set K : Submodule (ZMod 2) E := LinearMap.ker ψ with hK
  have hψne : ψ ≠ 0 := by
    intro h0
    rw [h0] at hψx
    exact hψx rfl
  have hψx1 : ψ x = 1 := zmod2_eq_one_of_ne_zero hψx
  have hKfr : finrank (ZMod 2) K = 5 := by
    have h := finrank_ker_eq_pred hψne
    rw [hE] at h
    rw [hK]
    omega
  have hxK : x ∉ K := by
    rw [hK, LinearMap.mem_ker]
    exact hψx
  have hWK : W ⊔ K = ⊤ := by
    have hne : W ⊔ K ≠ K := by
      intro h
      exact hxK (by rw [← h]; exact Submodule.mem_sup_left hxW)
    have hlt : K < W ⊔ K := lt_of_le_of_ne le_sup_right (Ne.symm hne)
    have h1 : finrank (ZMod 2) K < finrank (ZMod 2) ↥(W ⊔ K) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank (ZMod 2) ↥(W ⊔ K) ≤ finrank (ZMod 2) E := Submodule.finrank_le _
    refine Submodule.eq_top_of_finrank_eq ?_
    omega
  have hYfr : finrank (ZMod 2) ↥(W ⊓ K) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W K
    rw [hWK, finrank_top, hW3, hKfr, hE] at h
    omega
  have hXK : Submodule.span (ZMod 2) {x} ⊓ K = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzK⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzX
    rw [hK, LinearMap.mem_ker, ← ha, map_smul, smul_eq_mul, hψx1, mul_one] at hzK
    rw [hzK, zero_smul] at ha
    exact ha.symm
  have hYU : (W ⊓ K) ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzWK, hzU⟩ := Submodule.mem_inf.mp hz
    obtain ⟨hzW, hzK⟩ := Submodule.mem_inf.mp hzWK
    have hzX : z ∈ Submodule.span (ZMod 2) {x} := by
      rw [← hWU]
      exact Submodule.mem_inf.mpr ⟨hzW, hzU⟩
    have hzbot : z ∈ Submodule.span (ZMod 2) {x} ⊓ K := Submodule.mem_inf.mpr ⟨hzX, hzK⟩
    rwa [hXK, Submodule.mem_bot] at hzbot
  have hYtot : ∀ y ∈ W ⊓ K, q y = 0 := fun y hy => hW y (Submodule.mem_inf.mp hy).1
  have hYperp :
      W ⊓ K ≤ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}) := by
    intro y hy
    have hyW : y ∈ W := (Submodule.mem_inf.mp hy).1
    have h := hW (x + y) (W.add_mem hxW hyW)
    rw [QuadraticMap.map_add (f := ⇑q), hW x hxW, hW y hyW, zero_add, zero_add] at h
    exact mem_orthogonal_span_singleton_iff.mpr h
  obtain ⟨B, hB, hYB⟩ := exists_mem_tsCompl_of_le hq hUU hU hYtot hYU
  refine ⟨B, hB, ?_⟩
  have hB3 : finrank (ZMod 2) B = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hB.1
    rw [hU3, hE] at h
    omega
  have hxB : x ∉ B := by
    intro hxB'
    have h : x ∈ U ⊓ B := Submodule.mem_inf.mpr ⟨hxU, hxB'⟩
    rw [hB.1.inf_eq_bot, Submodule.mem_bot] at h
    exact hx0 h
  have hBinf : finrank (ZMod 2) ↥(B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {x})) = 2 :=
    finrank_inf_orthogonal_span_eq_two hq hE hB3 hB.2 hx0 hxB
  have hYle : W ⊓ K ≤ B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {x}) := le_inf hYB hYperp
  have heq : W ⊓ K = B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {x}) :=
    Submodule.eq_of_le_of_finrank_eq hYle (by rw [hYfr, hBinf])
  rw [← heq]
  exact inf_le_left

private theorem coeff_eq_zero_of_smul_add_smul_eq_zero {a b : ZMod 2} {u w : E}
    (hli : LinearIndependent (ZMod 2) ![u, w]) (h : a • w + b • u = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨hu0, hw0, huw⟩ := linearIndependent_pair_iff.mp hli
  have hwu : w ≠ u := fun h' => huw h'.symm
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
  · rw [zero_smul, zero_add] at h
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [one_smul] at h
      exact absurd h hu0
  · rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
    · rw [one_smul, zero_smul, add_zero] at h
      exact absurd h hw0
    · exfalso
      rw [one_smul, one_smul] at h
      have h' : w = u := by
        have h'' := eq_neg_of_add_eq_zero_left h
        rwa [ZModModule.neg_eq_self] at h''
      exact hwu h'

theorem exists_mem_tsCompl_not_inf_le (hq : q.polarBilin.Nondegenerate)
    (hE : finrank (ZMod 2) E = 6) {U : Submodule (ZMod 2) E} (hU3 : finrank (ZMod 2) U = 3)
    (hU : ∀ u ∈ U, q u = 0) {x : E} (hxU : x ∈ U) (hx0 : x ≠ 0)
    {W : Submodule (ZMod 2) E} (hW3 : finrank (ZMod 2) W = 3) (hW : ∀ w ∈ W, q w = 0)
    (hWU : W ⊓ U = Submodule.span (ZMod 2) {x}) :
    ∃ B ∈ tsCompl q U,
      ¬ B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}) ≤ W := by
  classical
  have hUU := orthogonal_eq_self_of_finrank_three hq hE hU3 hU
  have hxW : x ∈ W := by
    have h : x ∈ W ⊓ U := by rw [hWU]; exact Submodule.mem_span_singleton_self x
    exact (Submodule.mem_inf.mp h).1
  obtain ⟨u, w, hu, hw, hli, hspanuw, hdisjXuw⟩ :=
    exists_pair_span_sup_span_singleton hE hU3 hxU hx0
  have hqu : q u = 0 := hU u hu
  have hqw : q w = 0 := hU w hw
  have huw : polar q u w = 0 := polar_eq_zero_of_forall_q_eq_zero hU hu hw
  set e : E ≃ₗ[ZMod 2] E := CFSG.ClassicalGroups.Orthogonal.eichler q u w with he
  have he_mem : e ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
    CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup q u w
  have heq : ∀ y : E, q (e y) = q y := fun y =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup he_mem y
  have hee : ∀ y : E, e (e y) = y := by
    intro y
    have h1 : e * e = 1 := CFSG.LargeExtraspecial.eichler_mul_self huw
    rw [← LinearEquiv.mul_apply, h1]
    rfl
  have heU : ∀ y ∈ U, e y = y := by
    intro y hy
    have hyu : polar q y u = 0 := polar_eq_zero_of_forall_q_eq_zero hU hy hu
    have hyw : polar q y w = 0 := polar_eq_zero_of_forall_q_eq_zero hU hy hw
    rw [he, CFSG.LargeExtraspecial.eichler_apply_zmod2 (a := u) (u := w) hqu huw]
    rw [hyu, hyw, hqw]
    simp
  have hwrite : ∀ v : E, (e : E →ₗ[ZMod 2] E) v - v
      = polar q v u • w + (polar q v w + q w * polar q v u) • u := by
    intro v
    have h := CFSG.LargeExtraspecial.eichler_apply_zmod2 (a := u) (u := w) hqu huw v
    show CFSG.ClassicalGroups.Orthogonal.eichler q u w v - v = _
    rw [h]
    abel
  let W' : Submodule (ZMod 2) E := W.map (e : E →ₗ[ZMod 2] E)
  have hW'3 : finrank (ZMod 2) W' = 3 := by
    have h : finrank (ZMod 2) (W.map (e : E →ₗ[ZMod 2] E)) = finrank (ZMod 2) W :=
      LinearEquiv.finrank_map_eq e W
    rw [hW3] at h
    exact h
  have hW'tot : ∀ z ∈ W', q z = 0 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    show q (e y) = 0
    rw [heq]
    exact hW y hy
  have hxW' : x ∈ W' :=
    Submodule.mem_map.mpr ⟨x, hxW, by show e x = x; rw [heU x hxU]⟩
  have hW'U : W' ⊓ U = Submodule.span (ZMod 2) {x} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzW', hzU⟩ := Submodule.mem_inf.mp hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hzW'
      show e y ∈ Submodule.span (ZMod 2) {x}
      have hmem : e (e y) ∈ U := by
        rw [heU (e y) hzU]
        exact hzU
      have hyU : y ∈ U := by
        rwa [hee y] at hmem
      have hyX : y ∈ Submodule.span (ZMod 2) {x} := by
        rw [← hWU]
        exact Submodule.mem_inf.mpr ⟨hy, hyU⟩
      have hyU' : y ∈ U := by
        rw [← hspanuw]
        exact Submodule.mem_sup_left hyX
      rw [heU y hyU']
      exact hyX
    · rw [Submodule.span_le]
      rintro z rfl
      exact Submodule.mem_inf.mpr ⟨hxW', hxU⟩
  have hW'ne : W' ≠ W := by
    intro hEq
    have hinv : ∀ v ∈ W, (e : E →ₗ[ZMod 2] E) v ∈ W := by
      intro v hv
      rw [← hEq]
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    have huwU : Submodule.span (ZMod 2) ({u, w} : Set E) ≤ U := by
      rw [← hspanuw]
      exact le_sup_right
    have hzero : ∀ v ∈ W, (e : E →ₗ[ZMod 2] E) v - v = 0 := by
      intro v hv
      have hmemW : (e : E →ₗ[ZMod 2] E) v - v ∈ W := W.sub_mem (hinv v hv) hv
      have hmem_uw : polar q v u • w + (polar q v w + q w * polar q v u) • u
          ∈ Submodule.span (ZMod 2) ({u, w} : Set E) := by
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (s := ({u, w} : Set E)) (by simp))
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (s := ({u, w} : Set E)) (by simp))
      have hmemU : (e : E →ₗ[ZMod 2] E) v - v ∈ U := by
        rw [hwrite v]
        exact huwU hmem_uw
      have hmemX : (e : E →ₗ[ZMod 2] E) v - v ∈ Submodule.span (ZMod 2) {x} := by
        rw [← hWU]
        exact Submodule.mem_inf.mpr ⟨hmemW, hmemU⟩
      have hmem : (e : E →ₗ[ZMod 2] E) v - v ∈
          Submodule.span (ZMod 2) {x} ⊓ Submodule.span (ZMod 2) ({u, w} : Set E) := by
        refine Submodule.mem_inf.mpr ⟨hmemX, ?_⟩
        rw [hwrite v]
        exact hmem_uw
      rw [hdisjXuw, Submodule.mem_bot] at hmem
      exact hmem
    have hWUle : W ≤ Submodule.span (ZMod 2) {x} := by
      intro v hv
      have hz : (e : E →ₗ[ZMod 2] E) v - v = 0 := hzero v hv
      obtain ⟨ha, hb⟩ := coeff_eq_zero_of_smul_add_smul_eq_zero hli (hwrite v ▸ hz)
      have hvq : polar q v w = 0 := by
        rw [ha, mul_zero, add_zero] at hb
        exact hb
      have hvx : polar q v x = 0 := by
        have h := hW (v + x) (W.add_mem hv hxW)
        rw [QuadraticMap.map_add (f := ⇑q), hW v hv, hW x hxW, zero_add, zero_add] at h
        exact h
      have hvx' : polar q x v = 0 := by rwa [polar_comm] at hvx
      have hux' : polar q u v = 0 := by rwa [polar_comm] at ha
      have hwx' : polar q w v = 0 := by rwa [polar_comm] at hvq
      have hvU : v ∈ U := by
        rw [← hUU, LinearMap.BilinForm.mem_orthogonal_iff]
        intro y hy
        rw [← hspanuw] at hy
        obtain ⟨r, hr, z, hz', rfl⟩ := Submodule.mem_sup.mp hy
        obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hr
        obtain ⟨β, γ, rfl⟩ := Submodule.mem_span_pair.mp hz'
        rw [polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_add_left,
          polar_smul_left, polar_smul_left, hvx', hux', hwx']
        simp
      rw [← hWU]
      exact Submodule.mem_inf.mpr ⟨hv, hvU⟩
    have hle := Submodule.finrank_mono hWUle
    rw [hW3, finrank_span_singleton hx0] at hle
    omega
  obtain ⟨B, hB, hBle⟩ := exists_mem_tsCompl_inf_le hq hE hU3 hU hxU hx0 hW'3 hW'tot hW'U
  refine ⟨B, hB, ?_⟩
  intro hBW
  have hxB : x ∉ B := by
    intro hxB'
    have h : x ∈ U ⊓ B := Submodule.mem_inf.mpr ⟨hxU, hxB'⟩
    rw [hB.1.inf_eq_bot, Submodule.mem_bot] at h
    exact hx0 h
  have hB3 : finrank (ZMod 2) B = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hB.1
    rw [hU3, hE] at h
    omega
  have hBinf : finrank (ZMod 2) ↥(B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {x})) = 2 :=
    finrank_inf_orthogonal_span_eq_two hq hE hB3 hB.2 hx0 hxB
  have hleWW' : B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x})
      ≤ W ⊓ W' := le_inf hBW hBle
  have hxYB : x ∉ B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}) :=
    fun h => hxB (Submodule.mem_inf.mp h).1
  have hspanYB : Submodule.span (ZMod 2) {x} ⊓
      (B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x})) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzB⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzX
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact ha.symm
    · rw [one_smul] at ha
      have hzB' : z ∈ B := (Submodule.mem_inf.mp hzB).1
      rw [← ha] at hzB'
      exact absurd hzB' hxB
  have hfr3 : finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {x} ⊔
      (B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}))) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {x})
      (B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}))
    rw [hspanYB, finrank_bot, finrank_span_singleton hx0, hBinf, add_zero] at h
    omega
  have hle3 : Submodule.span (ZMod 2) {x} ⊔
      (B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x})) ≤
        W ⊓ W' := by
    refine sup_le ?_ hleWW'
    rw [Submodule.span_le]
    rintro z rfl
    exact Submodule.mem_inf.mpr ⟨hxW, hxW'⟩
  have hWinW' : W ≤ W' := by
    have hfr : finrank (ZMod 2) ↥(W ⊓ W') = 3 := by
      have h1 : finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {x} ⊔
          (B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {x}))) ≤
          finrank (ZMod 2) ↥(W ⊓ W') := Submodule.finrank_mono hle3
      have h2 : finrank (ZMod 2) ↥(W ⊓ W') ≤ finrank (ZMod 2) W :=
        Submodule.finrank_mono inf_le_left
      omega
    have hEq : W ⊓ W' = W := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hfr, hW3])
    rw [← hEq]
    exact inf_le_right
  have hWWeq : W = W' := Submodule.eq_of_le_of_finrank_eq hWinW' (by rw [hW3, hW'3])
  exact hW'ne hWWeq.symm

end DimensionSix

end CFSG.LargeExtraspecial.DW
