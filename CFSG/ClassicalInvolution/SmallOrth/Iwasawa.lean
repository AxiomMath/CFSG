module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import CFSG.ClassicalGroups.Orthogonal.Lines

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rootGroup_smul {c : K} (hc : c ≠ 0) (x : V) : rootGroup Q (c • x) = rootGroup Q x := by
  ext g
  rw [mem_rootGroup, mem_rootGroup]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c • w, ?_, by rw [eichler_smul_left]⟩
    rw [polar_smul_left_eq] at hw
    rw [polar_smul_right_eq, (mul_eq_zero.mp hw).resolve_left hc, mul_zero]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c⁻¹ • w, ?_, ?_⟩
    · rw [polar_smul_left_eq, polar_smul_right_eq, hw, mul_zero, mul_zero]
    · rw [eichler_smul_left, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem rootGroup_apply {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x : V) : rootGroup Q (g x) = (rootGroup Q x).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hy
    have hw' : polar Q x (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hg, LinearEquiv.apply_inv_apply']
      exact hw
    rw [Subgroup.mem_map]
    refine ⟨eichler Q x (g⁻¹ w), eichler_mem_rootGroup hw', ?_⟩
    change g * eichler Q x (g⁻¹ w) * g⁻¹ = eichler Q (g x) w
    rw [eichler_conj hg, LinearEquiv.apply_inv_apply']
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact conj_mem_rootGroup hg hz

variable (Q) in
noncomputable def rootT (p : singularLines Q) : Subgroup (elementaryGroup Q) :=
  (rootGroup Q p.1.rep).subgroupOf (elementaryGroup Q)

theorem mem_rootT {p : singularLines Q} {y : elementaryGroup Q} :
    y ∈ rootT Q p ↔ (y : V ≃ₗ[K] V) ∈ rootGroup Q p.1.rep :=
  Subgroup.mem_subgroupOf

theorem rep_smul_eq (g : elementaryGroup Q) (p : singularLines Q) :
    ∃ c : K, c ≠ 0 ∧ (g • p).1.rep = c • (g : V ≃ₗ[K] V) p.1.rep := by
  have hp : p.1 = Projectivization.mk K p.1.rep p.1.rep_nonzero :=
    (Projectivization.mk_rep p.1).symm
  have hne : (g : V ≃ₗ[K] V) p.1.rep ≠ 0 := fun h =>
    p.1.rep_nonzero ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h)
  have hgp : (g • p).1 = Projectivization.mk K ((g : V ≃ₗ[K] V) p.1.rep) hne := by
    have h1 : (g • p).1 = g • p.1 := rfl
    rw [h1]
    conv_lhs => rw [hp]
    exact smul_projectivization_mk g p.1.rep_nonzero
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K ((g : V ≃ₗ[K] V) p.1.rep) hne
  refine ⟨a, a.ne_zero, ?_⟩
  rw [hgp]
  exact ha.symm.trans (Units.smul_def a _)

theorem rootT_smul (g : elementaryGroup Q) (p : singularLines Q) :
    rootT Q (g • p) = MulAut.conj g • rootT Q p := by
  obtain ⟨c, hc, hrep⟩ := rep_smul_eq g p
  have hgO := elementaryGroup_le_orthogonalGroup Q g.2
  have h1 : rootGroup Q (g • p).1.rep =
      (rootGroup Q p.1.rep).map (MulAut.conj (g : V ≃ₗ[K] V)).toMonoidHom := by
    rw [hrep, rootGroup_smul hc, rootGroup_apply hgO]
  ext y
  rw [mem_rootT, h1, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hy : (y : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V) * z * (g : V ≃ₗ[K] V)⁻¹ := hzy.symm
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · rw [mem_rootT]
      have : ((g⁻¹ * y * g : elementaryGroup Q) : V ≃ₗ[K] V) = z := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hy]
        group
      rw [this]
      exact hz
    · rw [MulAut.smul_def, MulAut.conj_apply]
      group
  · rintro ⟨s, hs, hsy⟩
    refine ⟨(s : V ≃ₗ[K] V), mem_rootT.mp hs, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply] at hsy
    have := congrArg Subtype.val hsy
    simpa using this

theorem rep_lineMk {u : V} (hu0 : u ≠ 0) (hu : Q u = 0) :
    ∃ c : K, c ≠ 0 ∧ (lineMk u hu0 hu).1.rep = c • u := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu0
  exact ⟨a, a.ne_zero, ha.symm.trans (Units.smul_def a u)⟩

theorem iSup_rootT_eq_top : ⨆ p : singularLines Q, rootT Q p = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact Subgroup.one_mem _
    · refine Subgroup.mem_iSup_of_mem (lineMk u hu0 hu) ?_
      rw [mem_rootT]
      obtain ⟨c, hc, hr⟩ := rep_lineMk hu0 hu
      rw [hr, rootGroup_smul hc]
      exact eichler_mem_rootGroup hw
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx => exact Subgroup.inv_mem _ ihx

variable (Q) in
noncomputable def iwasawa : MulAction.IwasawaStructure (elementaryGroup Q) (singularLines Q) where
  T := rootT Q
  is_comm _ := IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
    (rootGroup_commute (mem_rootT.mp a.2) (mem_rootT.mp b.2)))
  is_conj g p := rootT_smul g p
  is_generator := iSup_rootT_eq_top

theorem commutator_le_of_not_fixed
    [MulAction.IsQuasiPreprimitive (elementaryGroup Q) (singularLines Q)]
    (N : Subgroup (elementaryGroup Q)) [N.Normal]
    (hN : MulAction.fixedPoints N (singularLines Q) ≠ Set.univ) :
    commutator (elementaryGroup Q) ≤ N :=
  (iwasawa Q).commutator_le N hN

end CFSG.ClassicalGroups.Orthogonal.Small
