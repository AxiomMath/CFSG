module

public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksGeo
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
open CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag}

@[expose] def perpChar
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (v : Fin τ.rank → ℤ) :
    Multiplicative (Fin τ.rank → ℤ) →* M × Multiplicative ℤ where
  toFun x := (χ x, Multiplicative.ofAdd (iform (Multiplicative.toAdd x) v))
  map_one' := by simp [iform]
  map_mul' x y := by
    rw [toAdd_mul, iform_add_left, map_mul, ofAdd_add]
    rfl

theorem kernelRoots_perpChar
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (v : Fin τ.rank → ℤ) :
    kernelRoots (perpChar χ v) = {δ | δ ∈ kernelRoots χ ∧ iform δ v = 0} := by
  ext δ
  simp [kernelRoots, perpChar, Prod.mk_eq_one, and_assoc]

theorem exists_iform_eq_det_mul_height (τ : Tag) :
    ∃ h₀ : Fin τ.rank → ℤ, ∃ c : ℤ, 0 < c ∧ ∀ δ, iform δ h₀ = c * height δ := by
  classical
  have hdet : 0 < τ.symmetrizedCartan.det := by
    have h := (posDef_symmetrizedCartan τ).det_pos
    rw [← Int.cast_det (τ.symmetrizedCartan)] at h
    exact_mod_cast h
  refine ⟨Matrix.mulVec τ.symmetrizedCartan.adjugate (fun _ => 1),
    τ.symmetrizedCartan.det, hdet, fun δ => ?_⟩
  have hmul : Matrix.mulVec τ.symmetrizedCartan
      (Matrix.mulVec τ.symmetrizedCartan.adjugate (fun _ => (1 : ℤ))) =
      τ.symmetrizedCartan.det • (fun _ => (1 : ℤ)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← dotProduct_mulVec_eq_iform, hmul, dotProduct_smul]
  simp [dotProduct, height, Finset.mul_sum]

theorem smul_eq_of_mem_closure_rootReflection_of_iform_eq_zero
    {S : Set (Fin τ.rank → ℤ)} {v : Fin τ.rank → ℤ} (hroot : ∀ δ ∈ S, IsRoot τ δ)
    (hS : ∀ δ ∈ S, iform δ v = 0) {r : WeylGroup τ}
    (hr : r ∈ Subgroup.closure (rootReflection '' S)) : r • v = v := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨δ, hδ, rfl⟩ := hx
      exact rootReflection_smul_of_iform_eq_zero (hroot δ hδ) (hS δ hδ)
  | one => exact one_smul _ _
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff, hx]

theorem pos_add_mul_of_abs_lt {a b N : ℤ} (h : |a| < N * |b|) :
    0 < N * b + a ↔ 0 < b := by
  constructor
  · intro hpos
    by_contra hb
    have hb' : b ≤ 0 := le_of_not_gt hb
    rw [abs_of_nonpos hb', mul_neg] at h
    have ha : a ≤ |a| := le_abs_self a
    linarith
  · intro hb
    rw [abs_of_pos hb] at h
    have ha : -|a| ≤ a := neg_abs_le a
    linarith

theorem neg_add_mul_of_abs_lt {a b N : ℤ} (h : |a| < N * |b|) :
    N * b + a < 0 ↔ b < 0 := by
  constructor
  · intro hsum
    by_contra hb
    have hb' : 0 ≤ b := le_of_not_gt hb
    rw [abs_of_nonneg hb'] at h
    have ha : -|a| ≤ a := neg_abs_le a
    linarith
  · intro hb
    rw [abs_of_nonpos hb.le, mul_neg] at h
    have ha : a ≤ |a| := le_abs_self a
    linarith

theorem exists_fixed_forall_iform_ne_zero
    {S : Set (Fin τ.rank → ℤ)} {u : WeylGroup τ} {v' : Fin τ.rank → ℤ}
    (hreg : ∀ α ∈ S, iform α v' ≠ 0)
    (hpres : ∀ α ∈ S, u⁻¹ • α ∈ S)
    (hsame : ∀ α ∈ S, 0 < iform α (u • v') ↔ 0 < iform α v') :
    ∃ v'', u • v'' = v'' ∧ ∀ α ∈ S, iform α v'' ≠ 0 := by
  classical
  let P : Set (Fin τ.rank → ℤ) := {α | α ∈ S ∧ 0 < iform α v'}
  have hPinv : ∀ β ∈ P, u⁻¹ • β ∈ P := by
    intro β hβ
    refine ⟨hpres β hβ.1, ?_⟩
    have e : iform (u⁻¹ • β) v' = iform β (u • v') := by
      rw [← iform_smul u, smul_inv_smul]
    rw [e]
    exact (hsame β hβ.1).2 hβ.2
  have hiter_inv : ∀ n β, β ∈ P → (u⁻¹) ^ n • β ∈ P := by
    intro n
    induction n with
    | zero => intro β hβ; simpa using hβ
    | succ n ih =>
        intro β hβ
        rw [pow_succ, mul_smul]
        exact ih _ (hPinv β hβ)
  have hm : 0 < orderOf u := orderOf_pos u
  have hu_eq : u = (u⁻¹) ^ (orderOf u - 1) := by
    have h2 : u ^ (orderOf u - 1) * u = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hm, pow_orderOf_eq_one u]
    calc u = (u⁻¹)⁻¹ := (inv_inv u).symm
      _ = (u ^ (orderOf u - 1))⁻¹ := by rw [eq_inv_of_mul_eq_one_left h2]
      _ = (u⁻¹) ^ (orderOf u - 1) := by rw [inv_pow]
  have huP : ∀ β ∈ P, u • β ∈ P := by
    intro β hβ
    rw [hu_eq]
    exact hiter_inv (orderOf u - 1) β hβ
  have hiter_u : ∀ n β, β ∈ P → u ^ n • β ∈ P := by
    intro n
    induction n with
    | zero => intro β hβ; simpa using hβ
    | succ n ih =>
        intro β hβ
        rw [pow_succ, mul_smul]
        exact ih _ (huP β hβ)
  let m := orderOf u
  let v'' : Fin τ.rank → ℤ := ∑ k ∈ Finset.range m, u ^ k • v'
  refine ⟨v'', ?_, ?_⟩
  · have hpow : u ^ m = 1 := pow_orderOf_eq_one u
    have hshift : ∀ k : ℕ, u • (u ^ k • v') = u ^ (k + 1) • v' := by
      intro k
      rw [← mul_smul, ← pow_succ']
    dsimp only [v'']
    rw [Finset.smul_sum]
    simp only [hshift]
    let F : ℕ → Fin τ.rank → ℤ := fun k => u ^ k • v'
    change (∑ k ∈ Finset.range m, F (k + 1)) = ∑ k ∈ Finset.range m, F k
    have hm' : m = (m - 1) + 1 := (Nat.succ_pred_eq_of_pos hm).symm
    have hF : F ((m - 1) + 1) = F 0 := by
      rw [← hm']
      simp [F, hpow]
    conv_lhs =>
      rw [hm']
      rw [Finset.sum_range_succ]
    conv_rhs =>
      rw [hm']
      rw [Finset.sum_range_succ']
    rw [hF]
  · intro α hα
    have hSin : ∀ n, (u⁻¹) ^ n • α ∈ S := by
      intro n
      induction n with
      | zero => simpa using hα
      | succ n ih =>
          rw [pow_succ', mul_smul]
          exact hpres _ ih
    have hsum : iform α v'' = ∑ k ∈ Finset.range m, iform α (u ^ k • v') := by
      dsimp only [v'']
      rw [iform_finset_sum_right]
    have hterm : ∀ k, iform α (u ^ k • v') = iform ((u ^ k)⁻¹ • α) v' := by
      intro k
      conv_lhs => rw [← smul_inv_smul (u ^ k) α]
      rw [iform_smul (u ^ k)]
    by_cases hpos : 0 < iform α v'
    · refine ne_of_gt ?_
      rw [hsum]
      refine Finset.sum_pos (fun k _ => ?_) ⟨0, Finset.mem_range.2 hm⟩
      rw [hterm k]
      have hβ := hiter_inv k α ⟨hα, hpos⟩
      simpa [inv_pow] using hβ.2
    · refine ne_of_lt ?_
      rw [hsum]
      have hpos' : 0 < ∑ k ∈ Finset.range m, -iform α (u ^ k • v') := by
        refine Finset.sum_pos (fun k _ => ?_) ⟨0, Finset.mem_range.2 hm⟩
        rw [hterm k]
        have hnot : (u ^ k)⁻¹ • α ∉ P := by
          intro hβ
          have hmem := hiter_u k ((u ^ k)⁻¹ • α) hβ
          rw [smul_inv_smul] at hmem
          exact hpos hmem.2
        have hmemS : (u ^ k)⁻¹ • α ∈ S := by
          rw [← inv_pow]
          exact hSin k
        have hle : ¬ 0 < iform ((u ^ k)⁻¹ • α) v' := fun hp => hnot ⟨hmemS, hp⟩
        have hlt : iform ((u ^ k)⁻¹ • α) v' < 0 :=
          lt_of_le_of_ne (le_of_not_gt hle) (hreg _ hmemS)
        exact neg_pos.2 hlt
      have hneg := hpos'
      rw [Finset.sum_neg_distrib] at hneg
      linarith

theorem exists_mem_closure_rootReflection_forall_height_sign
    {M : Type*} [CommGroup M] (ψ : Multiplicative (Fin τ.rank → ℤ) →* M)
    {h₀ : Fin τ.rank → ℤ} {c : ℤ} (hc : 0 < c)
    (hheight : ∀ δ, iform δ h₀ = c * height δ)
    {x : Fin τ.rank → ℤ} (hx : ∀ α ∈ kernelRoots ψ, iform α x ≠ 0) :
    ∃ r ∈ Subgroup.closure (rootReflection '' kernelRoots ψ),
      ∀ δ ∈ kernelRoots ψ, 0 < height δ → 0 < iform δ (r • x) := by
  classical
  obtain ⟨r, hr⟩ := Finite.exists_max fun r :
      Subgroup.closure (rootReflection '' kernelRoots ψ) =>
        iform h₀ ((r : WeylGroup τ) • x)
  refine ⟨r, r.2, fun δ hδ hpos => ?_⟩
  have hδr : IsRoot τ δ := hδ.1
  have hmem : rootReflection δ ∈ Subgroup.closure (rootReflection '' kernelRoots ψ) :=
    Subgroup.subset_closure ⟨δ, hδ, rfl⟩
  have hle := hr (⟨rootReflection δ, hmem⟩ * r)
  change iform h₀ ((rootReflection δ * (r : WeylGroup τ)) • x) ≤
    iform h₀ ((r : WeylGroup τ) • x) at hle
  rw [mul_smul, rootReflection_smul hδr, iform_sub_right, iform_smul_right] at hle
  have hnonneg : 0 ≤ corootPair δ ((r : WeylGroup τ) • x) * iform h₀ δ := by
    linarith
  rw [iform_comm h₀ δ, hheight δ] at hnonneg
  have hcδ : 0 < c * height δ := mul_pos hc hpos
  have hcp : 0 ≤ corootPair δ ((r : WeylGroup τ) • x) :=
    nonneg_of_mul_nonneg_left hnonneg hcδ
  have hsq : 0 ≤ iform δ ((r : WeylGroup τ) • x) := by
    have hm := corootPair_mul hδr ((r : WeylGroup τ) • x)
    have hself : 0 < iform δ δ := iform_self_pos_of_isRoot hδr
    nlinarith
  have hrkw : (r : WeylGroup τ) ∈ kernelWeylGroup ψ := by
    rw [kernelWeylGroup_eq_closure]
    exact r.2
  have hp : (r : WeylGroup τ)⁻¹ • δ ∈ kernelRoots ψ :=
    smul_mem_kernelRoots (kernelWeylGroup_le (inv_mem hrkw)) hδ
  have hne : iform δ ((r : WeylGroup τ) • x) ≠ 0 := by
    have hxne := hx ((r : WeylGroup τ)⁻¹ • δ) hp
    rwa [← iform_smul (r : WeylGroup τ), smul_inv_smul] at hxne
  exact lt_of_le_of_ne hsq hne.symm

theorem exists_regular_shift
    {S T : Set (Fin τ.rank → ℤ)} {v : Fin τ.rank → ℤ} {u : WeylGroup τ}
    (hSroot : ∀ δ ∈ S, IsRoot τ δ) (hTdef : ∀ δ ∈ S, δ ∈ T ↔ iform δ v = 0)
    (huv : u • v = v) {h₀ : Fin τ.rank → ℤ} {c : ℤ} (hc : 0 < c)
    (hheight : ∀ δ, iform δ h₀ = c * height δ)
    (hsign : ∀ δ ∈ T, (0 < height δ → 0 < iform δ (u • h₀)) ∧
      (height δ < 0 → iform δ (u • h₀) < 0)) :
    ∃ v' : Fin τ.rank → ℤ,
      (∀ δ ∈ S, iform δ v' ≠ 0) ∧
      (∀ δ ∈ S, 0 < iform δ (u • v') ↔ 0 < iform δ v') := by
  classical
  let roots : Finset (Fin τ.rank → ℤ) := (finite_setOf_isRoot τ).toFinset
  let N : ℤ := 1 + ∑ δ ∈ roots, (|iform δ h₀| + |iform δ (u • h₀)|)
  let v' : Fin τ.rank → ℤ := N • v + h₀
  have hNpos : 0 < N := by
    have hnonneg : 0 ≤ ∑ δ ∈ roots, (|iform δ h₀| + |iform δ (u • h₀)|) :=
      Finset.sum_nonneg fun δ _ => by positivity
    dsimp only [N]
    omega
  have hNbound : ∀ δ ∈ roots, |iform δ h₀| < N ∧ |iform δ (u • h₀)| < N := by
    intro δ hδ
    have hsingle : |iform δ h₀| + |iform δ (u • h₀)| ≤
        ∑ ε ∈ roots, (|iform ε h₀| + |iform ε (u • h₀)|) :=
      Finset.single_le_sum (s := roots)
        (f := fun ε => |iform ε h₀| + |iform ε (u • h₀)|)
        (fun ε _ => by positivity) hδ
    have hlt : (∑ ε ∈ roots, (|iform ε h₀| + |iform ε (u • h₀)|)) < N := by
      dsimp only [N]
      omega
    constructor
    · exact lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) (lt_of_le_of_lt hsingle hlt)
    · exact lt_of_le_of_lt (le_add_of_nonneg_left (abs_nonneg _)) (lt_of_le_of_lt hsingle hlt)
  have hbound : ∀ δ ∈ S, iform δ v ≠ 0 →
      |iform δ h₀| < N * |iform δ v| ∧ |iform δ (u • h₀)| < N * |iform δ v| := by
    intro δ hδ hz
    have hδroot : δ ∈ roots := by
      dsimp only [roots]
      rw [Set.Finite.mem_toFinset]
      exact hSroot δ hδ
    obtain ⟨hb1, hb2⟩ := hNbound δ hδroot
    have h1 : 1 ≤ |iform δ v| := Int.one_le_abs hz
    have hNle : N ≤ N * |iform δ v| := by
      nth_rewrite 1 [← mul_one N]
      exact mul_le_mul_of_nonneg_left h1 hNpos.le
    exact ⟨lt_of_lt_of_le hb1 hNle, lt_of_lt_of_le hb2 hNle⟩
  have hv'_form : ∀ δ, iform δ v' = N * iform δ v + iform δ h₀ := by
    intro δ
    dsimp only [v']
    rw [iform_add_right, iform_smul_right]
  have hu_form : ∀ δ, iform δ (u • v') = N * iform δ v + iform δ (u • h₀) := by
    intro δ
    have e : u • v' = N • v + u • h₀ := by
      dsimp only [v']
      rw [smul_add, smul_comm, huv]
    rw [e, iform_add_right, iform_smul_right]
  have hv'_zero : ∀ δ, iform δ v = 0 → iform δ v' = iform δ h₀ := by
    intro δ hz
    rw [hv'_form δ, hz, mul_zero, zero_add]
  have hu_zero : ∀ δ, iform δ v = 0 → iform δ (u • v') = iform δ (u • h₀) := by
    intro δ hz
    rw [hu_form δ, hz, mul_zero, zero_add]
  have hv'_pos : ∀ δ ∈ S, iform δ v ≠ 0 → (0 < iform δ v' ↔ 0 < iform δ v) := by
    intro δ hδ hz
    rw [hv'_form δ]
    exact pos_add_mul_of_abs_lt (hbound δ hδ hz).1
  have hu_pos : ∀ δ ∈ S, iform δ v ≠ 0 → (0 < iform δ (u • v') ↔ 0 < iform δ v) := by
    intro δ hδ hz
    rw [hu_form δ]
    exact pos_add_mul_of_abs_lt (hbound δ hδ hz).2
  have hzero : ∀ δ ∈ S, iform δ v = 0 → (0 < iform δ v' ↔ 0 < height δ) := by
    intro δ hδ hz
    rw [hv'_zero δ hz, hheight δ]
    exact mul_pos_iff_of_pos_left hc
  have hzero_u : ∀ δ ∈ S, iform δ v = 0 → (0 < iform δ (u • v') ↔ 0 < height δ) := by
    intro δ hδ hz
    rw [hu_zero δ hz]
    have hT : δ ∈ T := (hTdef δ hδ).2 hz
    rcases IsRoot.height_pos_or_neg (hSroot δ hδ) with hpos | hneg
    · exact ⟨fun _ => hpos, fun _ => (hsign δ hT).1 hpos⟩
    · have h1 := (hsign δ hT).2 hneg
      constructor <;> intro h <;> linarith
  refine ⟨v', ?_, ?_⟩
  · intro δ hδ
    by_cases hz : iform δ v = 0
    · rcases IsRoot.height_pos_or_neg (hSroot δ hδ) with hpos | hneg
      · rw [hv'_zero δ hz, hheight δ]
        exact (mul_pos hc hpos).ne'
      · rw [hv'_zero δ hz, hheight δ]
        exact (mul_neg_of_pos_of_neg hc hneg).ne
    · rcases lt_or_gt_of_ne hz with hneg | hpos
      · rw [hv'_form δ]
        exact (neg_add_mul_of_abs_lt (hbound δ hδ hz).1).2 hneg |>.ne
      · rw [hv'_form δ]
        exact (pos_add_mul_of_abs_lt (hbound δ hδ hz).1).2 hpos |>.ne'
  · intro δ hδ
    by_cases hz : iform δ v = 0
    · exact (hzero_u δ hδ hz).trans (hzero δ hδ hz).symm
    · exact (hu_pos δ hδ hz).trans (hv'_pos δ hδ hz).symm

theorem mem_closure_rootReflection_orthogonal_of_smul_eq
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure (rootReflection '' kernelRoots χ))
    {v : Fin τ.rank → ℤ} (hwv : w • v = v) :
    w ∈ Subgroup.closure (rootReflection '' {δ | δ ∈ kernelRoots χ ∧ iform δ v = 0}) := by
  classical
  let ψ := perpChar χ v
  have hroots : kernelRoots ψ = {δ | δ ∈ kernelRoots χ ∧ iform δ v = 0} :=
    kernelRoots_perpChar χ v
  rw [← hroots]
  have hsub : kernelRoots ψ ⊆ kernelRoots χ := by
    intro δ hδ
    rw [hroots] at hδ
    exact hδ.1
  obtain ⟨h₀, c, hc, hheight⟩ := exists_iform_eq_det_mul_height τ
  have hreg₀ : ∀ α, IsRoot τ α → iform α h₀ ≠ 0 := by
    intro α hα
    rw [hheight α]
    refine mul_ne_zero hc.ne' ?_
    rcases IsRoot.height_pos_or_neg hα with h | h
    · exact h.ne'
    · exact h.ne
  have hwχ : w ∈ kernelWeylGroup χ := by
    rw [kernelWeylGroup_eq_closure]
    exact hw
  have hxreg : ∀ α ∈ kernelRoots ψ, iform α (w • h₀) ≠ 0 := by
    intro α hα
    have hroot : IsRoot τ (w⁻¹ • α) := IsRoot.smul hα.1 w⁻¹
    have e : iform α (w • h₀) = iform (w⁻¹ • α) h₀ := by
      conv_lhs => rw [← smul_inv_smul w α]
      rw [iform_smul w]
    rw [e]
    exact hreg₀ _ hroot
  obtain ⟨r, hrW, hsign⟩ :=
    exists_mem_closure_rootReflection_forall_height_sign ψ hc hheight hxreg
  let u : WeylGroup τ := r * w
  have hrχ : r ∈ kernelWeylGroup χ := by
    rw [kernelWeylGroup_eq_closure]
    exact Subgroup.closure_mono (Set.image_mono hsub) hrW
  have huχ : u ∈ kernelWeylGroup χ := by
    dsimp only [u]
    exact mul_mem hrχ hwχ
  have huv : u • v = v := by
    dsimp only [u]
    rw [mul_smul, hwv]
    exact smul_eq_of_mem_closure_rootReflection_of_iform_eq_zero
      (S := kernelRoots ψ) (v := v) (fun δ hδ => hδ.1)
      (fun δ hδ => by rw [hroots] at hδ; exact hδ.2) hrW
  have husign : ∀ δ ∈ kernelRoots ψ, 0 < height δ → 0 < iform δ (u • h₀) := by
    intro δ hδ hpos
    have h := hsign δ hδ hpos
    simpa [u, mul_smul] using h
  have husign_neg : ∀ δ ∈ kernelRoots ψ, height δ < 0 → iform δ (u • h₀) < 0 := by
    intro δ hδ hneg
    have hnegroot : -δ ∈ kernelRoots ψ := ⟨IsRoot.neg hδ.1, chi_neg hδ.2⟩
    have hpos := husign (-δ) hnegroot (by rw [height_neg]; omega)
    have e : iform (-δ) (u • h₀) = -iform δ (u • h₀) := by
      rw [← neg_one_smul ℤ δ, iform_smul_left, neg_one_mul]
    rw [e] at hpos
    linarith
  have hTdef : ∀ δ ∈ kernelRoots χ, δ ∈ kernelRoots ψ ↔ iform δ v = 0 := by
    intro δ hδ
    rw [hroots]
    exact ⟨fun h => h.2, fun h => ⟨hδ, h⟩⟩
  have hsignT : ∀ δ ∈ kernelRoots ψ,
      (0 < height δ → 0 < iform δ (u • h₀)) ∧
      (height δ < 0 → iform δ (u • h₀) < 0) :=
    fun δ hδ => ⟨husign δ hδ, husign_neg δ hδ⟩
  obtain ⟨v', hv'reg, hv'same⟩ := exists_regular_shift
    (S := kernelRoots χ) (T := kernelRoots ψ) (v := v) (u := u)
    (h₀ := h₀) (c := c) (fun δ hδ => hδ.1) hTdef huv hc hheight hsignT
  have hpres : ∀ δ ∈ kernelRoots χ, u⁻¹ • δ ∈ kernelRoots χ := fun δ hδ =>
    smul_mem_kernelRoots (kernelWeylGroup_le (inv_mem huχ)) hδ
  obtain ⟨v'', huv'', hv''reg⟩ :=
    exists_fixed_forall_iform_ne_zero hv'reg hpres hv'same
  have hu_one : u = 1 :=
    eq_one_of_mem_kernelWeylGroup_of_smul_eq huχ huv'' hv''reg
  have hwu : w = r⁻¹ := by
    dsimp only [u] at hu_one
    exact eq_inv_of_mul_eq_one_right hu_one
  rw [hwu]
  exact inv_mem hrW

theorem exists_mem_closure_rootReflection_smul_eq_of_mem_componentRoots
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {γ α : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) (hα : α ∈ componentRoots χ i) :
    ∃ w ∈ Subgroup.closure (rootReflection '' kernelRoots χ), w • γ = α := by
  obtain ⟨hγk, hγi⟩ := hγ
  obtain ⟨hαk, hαi⟩ := hα
  have key : ∀ x y : kernelRoots χ,
      Relation.EqvGen (fun a b : kernelRoots χ =>
        (a : Fin τ.rank → ℤ) ⬝ᵥ Matrix.mulVec τ.symmetrizedCartan
          (b : Fin τ.rank → ℤ) ≠ 0) x y →
      ∃ w ∈ Subgroup.closure (rootReflection '' kernelRoots χ),
        w • (x : Fin τ.rank → ℤ) = (y : Fin τ.rank → ℤ) := by
    intro x y hxy
    induction hxy with
    | rel x y h =>
        exact exists_mem_closure_smul_eq_of_iform_ne_zero_simplyLaced hτ x.2 y.2
          (by rwa [dotProduct_mulVec_eq_iform] at h)
    | refl x => exact ⟨1, one_mem _, one_smul _ _⟩
    | symm x y _ ih =>
        obtain ⟨w, hw, hwx⟩ := ih
        exact ⟨w⁻¹, inv_mem hw, by rw [← hwx, inv_smul_smul]⟩
    | trans x y z _ _ ih1 ih2 =>
        obtain ⟨w, hw, hwx⟩ := ih1
        obtain ⟨u, hu, huy⟩ := ih2
        exact ⟨u * w, mul_mem hu hw, by rw [mul_smul, hwx, huy]⟩
  exact key ⟨γ, hγk⟩ ⟨α, hαk⟩ (Quotient.exact (hγi.trans hαi.symm))

end CFSG.LieType.Chevalley

end
