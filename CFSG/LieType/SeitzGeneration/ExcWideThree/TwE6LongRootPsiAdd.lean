module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootAdj
public import CFSG.LieType.Chevalley.GraphFixedParabolicRootFactors
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

@[expose] def Qbar (K : Type) [Field K] :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  parabolicRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J0)

theorem Psi.mem_orbitUnion_J0 {i : Fin TwistTag.E6.tag.rank} :
    i ∈ TwistTag.E6.orbitUnion J0 ↔ i ≠ e6Idx 1 := by
  rw [TwistTag.mem_orbitUnion]
  simp only [J0, a2, Set.mem_setOf_eq]
  revert i
  decide

theorem Psi.mem_S_iff {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ insert e6HighestRoot degOneRoots ↔
      IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ 0 < α (e6Idx 1) := by
  rw [← filter_pos_coord_pos, Finset.mem_filter, mem_rootFinset]

theorem Psi.mem_Qbar_roots_iff {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0) ↔
      α ∈ insert e6HighestRoot degOneRoots := by
  rw [mem_S_iff]
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hr, hp⟩, hnot⟩
    refine ⟨hr, hp, ?_⟩
    have h1 : α (e6Idx 1) ≠ 0 := fun h0 => hnot ⟨⟨hr, fun i hi => by
      have : i = e6Idx 1 := by_contra fun hne => hi (mem_orbitUnion_J0.2 hne)
      rw [this, h0]⟩, hr, hp⟩
    have h2 : 0 ≤ α (e6Idx 1) := by
      rcases hr.nonneg_or_nonpos with h | h
      · exact h _
      · exfalso
        have : height α ≤ 0 := Finset.sum_nonpos fun j _ => h j
        omega
    omega
  · rintro ⟨hr, hp, hpos⟩
    refine ⟨⟨hr, hp⟩, fun ⟨⟨_, hall⟩, _⟩ => ?_⟩
    have := hall (e6Idx 1) fun hmem => (mem_orbitUnion_J0.1 hmem) rfl
    omega

variable {K : Type} [Field K]

@[expose] def Psi.Fil (K : Type) [Field K] (i : ℤ) : Submodule K (RootModule TwistTag.E6.tag K) :=
  Finsupp.supported K K {b | i ≤ lblDeg b}

@[expose] def Psi.IsUni (f : Module.End K (RootModule TwistTag.E6.tag K)) : Prop :=
  ∀ i : ℤ, ∀ x ∈ Fil K i, f x - x ∈ Fil K (i + 1)

theorem Psi.Fil_mono {i j : ℤ} (h : i ≤ j) : Fil K j ≤ Fil K i :=
  Finsupp.supported_mono fun _ hb => le_trans h hb

theorem Psi.isUni_one : IsUni (1 : Module.End K (RootModule TwistTag.E6.tag K)) := fun i x _ => by
  simp

theorem Psi.isUni_mul {f g : Module.End K (RootModule TwistTag.E6.tag K)} (hf : IsUni f)
    (hg : IsUni g) : IsUni (f * g) := by
  intro i x hx
  have h1 : g x - x ∈ Fil K (i + 1) := hg i x hx
  have h2 : g x ∈ Fil K i := by
    have : g x = x + (g x - x) := by abel
    rw [this]
    exact add_mem hx (Fil_mono (by omega) h1)
  have h3 := hf i (g x) h2
  have : (f * g) x - x = (f (g x) - g x) + (g x - x) := by
    rw [Module.End.mul_apply]
    abel
  rw [this]
  exact add_mem h3 h1

theorem Psi.isUni_of_entries (f : Module.End K (RootModule TwistTag.E6.tag K))
    (h : ∀ a b : Label TwistTag.E6.tag,
      f (Finsupp.single b 1) a ≠ (Finsupp.single b (1 : K) : RootModule TwistTag.E6.tag K) a →
        lblDeg b < lblDeg a) : IsUni f := by
  intro i x hx
  have hx' : x ∈ Submodule.span K
      ((fun b => (Finsupp.single b (1 : K) : RootModule TwistTag.E6.tag K)) ''
        {b | i ≤ lblDeg b}) := by
    rwa [← Finsupp.supported_eq_span_single]
  refine Submodule.span_induction (p := fun x _ => f x - x ∈ Fil K (i + 1)) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨b, hb, rfl⟩
    rw [Fil, Finsupp.mem_supported' K]
    intro a ha
    by_contra hne
    have hne' : f (Finsupp.single b 1) a ≠ (Finsupp.single b (1 : K) :
        RootModule TwistTag.E6.tag K) a := fun e => hne (by simp [e])
    have := h a b hne'
    exact ha (by simp only [Set.mem_setOf_eq] at hb ⊢; omega)
  · simp
  · intro x y _ _ hx hy
    have : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
      rw [map_add]
      abel
    rw [this]
    exact add_mem hx hy
  · intro a x _ hx
    have : f (a • x) - a • x = a • (f x - x) := by
      rw [map_smul, smul_sub]
    rw [this]
    exact Submodule.smul_mem _ _ hx

@[expose] def Psi.Uni (K : Type) [Field K] : Subgroup (ModGL TwistTag.E6.tag K) where
  carrier := {z | IsUni (z : Module.End K (RootModule TwistTag.E6.tag K)) ∧
    IsUni ((z⁻¹ : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact isUni_mul ha.1 hb.1
    · rw [mul_inv_rev, Units.val_mul]
      exact isUni_mul hb.2 ha.2
  one_mem' := ⟨by rw [Units.val_one]; exact isUni_one,
    by rw [inv_one, Units.val_one]; exact isUni_one⟩
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem Psi.pinnedX_isUni
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (h1 : 1 ≤ α (e6Idx 1))
    (c : K) :
    IsUni (pinnedX TwistTag.E6.tag K α c : Module.End K (RootModule TwistTag.E6.tag K)) := by
  refine isUni_of_entries _ fun a b hne => ?_
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift hα c a b hne
  have h2 := congrFun hw (e6Idx 1)
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Pi.mul_apply,
    Pi.natCast_apply] at h2
  have h3 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  unfold lblDeg
  rw [h2]
  nlinarith

theorem Psi.pinnedX_mem_Uni
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (h1 : 1 ≤ α (e6Idx 1))
    (c : K) : pinnedX TwistTag.E6.tag K α c ∈ Uni K := by
  refine ⟨pinnedX_isUni hα h1 c, ?_⟩
  rw [pinnedX_neg]
  exact pinnedX_isUni hα h1 (-c)

theorem pinnedX_mem_Qbar
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ insert e6HighestRoot degOneRoots) (c : K) :
    pinnedX TwistTag.E6.tag K δ c ∈ Qbar K :=
  Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem (mem_Qbar_roots_iff.2 hδ)
    (Subgroup.subset_closure ⟨c, rfl⟩))

theorem Psi.Qbar_le_Uni :
    Qbar K ≤ Uni K := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨hr, -, hpos⟩ := mem_S_iff.1 (mem_Qbar_roots_iff.1 hα)
  exact pinnedX_mem_Uni hr (by omega) c

theorem psi_mul
    {z z' : ModGL TwistTag.E6.tag K} (hz : z ∈ Qbar K) (hz' : z' ∈ Qbar K) :
    psi K (z * z') = psi K z + psi K z' := by
  have hu := (Qbar_le_Uni hz).1
  have hu' := (Qbar_le_Uni hz').1
  have hv0 : v0 K ∈ Fil K (-2) := by
    rw [v0_eq]
    exact Finsupp.single_mem_supported K _ (by simp [lblDeg_lab0])
  have h1 : (z' : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) - v0 K ∈ Fil K (-1) := by
    have := hu' (-2) _ hv0
    norm_num at this
    exact this
  have h2 := hu (-1) _ h1
  ext γ
  have h3 := (Finsupp.mem_supported' K _).1 h2 (lab γ) (by simp [lblDeg_lab])
  have h4 : v0 K (lab γ) = 0 := by
    rw [v0_eq, Finsupp.single_apply, if_neg (lab_ne_lab0 γ).symm]
  simp only [psi_apply, Units.val_mul, Module.End.mul_apply, Pi.add_apply]
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply, h4] at h3
  linear_combination h3

theorem psi_inv
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ Qbar K) : psi K z⁻¹ = -psi K z := by
  have h := psi_mul (inv_mem hz) hz
  rw [inv_mul_cancel, psi_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem Psi.psi_list_prod
    {L : List (ModGL TwistTag.E6.tag K)} (hL : ∀ x ∈ L, x ∈ Qbar K) :
    psi K L.prod = (L.map (psi K)).sum := by
  induction L with
  | nil => simp [psi_one]
  | cons x L ih =>
    rw [List.prod_cons, psi_mul (hL x (by simp)) (Subgroup.list_prod_mem _ fun y hy =>
      hL y (List.mem_cons_of_mem _ hy)), ih fun y hy => hL y (List.mem_cons_of_mem _ hy),
      List.map_cons, List.sum_cons]

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
