module

public import CFSG.ClassicalGroups.Orthogonal.Lines
public import CFSG.ClassicalGroups.Orthogonal.Perfect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_12
import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
abbrev ProjElementary : Type _ :=
  elementaryGroup Q ⧸ (scalars K V).subgroupOf (elementaryGroup Q)

theorem normalClosure_rootGroup_eq_top (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (h : P.Orth P') :
    Subgroup.normalClosure
      (((rootGroup Q P.e).subgroupOf (elementaryGroup Q) : Subgroup (elementaryGroup Q)) :
        Set (elementaryGroup Q)) = ⊤ := by
  set N := Subgroup.normalClosure
    (((rootGroup Q P.e).subgroupOf (elementaryGroup Q) : Subgroup (elementaryGroup Q)) :
      Set (elementaryGroup Q))
  have hN : N.Normal := Subgroup.normalClosure_normal
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq hQ h P.e_ne_zero hu0
      (by rw [P.Q_e, hu])
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q P.e (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_inv_apply', hw]
    have hmemU : (⟨eichler Q P.e (g⁻¹ w), eichler_mem_elementaryGroup Q _ _⟩ :
        elementaryGroup Q) ∈ N :=
      Subgroup.subset_normalClosure (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact eichler_mem_rootGroup hv)
    have hmem := hN.conj_mem _ hmemU ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q P.e (g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, LinearEquiv.apply_inv_apply']
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

theorem isSimpleGroup_projElementary_of_hypPairs (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    IsSimpleGroup (ProjElementary Q) := by
  let G := elementaryGroup Q
  let X := singularLines Q
  let Z := (scalars K V).subgroupOf G
  have hZ : Z ≤ (MulAction.toPermHom G X).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun p => ?_
    rw [Subgroup.mem_subgroupOf, mem_scalars] at hg
    obtain ⟨c, hc⟩ := hg
    obtain ⟨v, hv, hQv, rfl⟩ := exists_eq_lineMk p
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := hc v
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
      exact hv this
    exact smul_lineMk_of_apply_eq_smul hv hv hQv hQv (hc v)
  let ρ : ProjElementary Q →* Equiv.Perm X := QuotientGroup.lift Z (MulAction.toPermHom G X) hZ
  let _ : MulAction (ProjElementary Q) X := MulAction.compHom X ρ
  have hsmul : ∀ (g : G) (x : X), ((g : ProjElementary Q)) • x = g • x := fun _ _ => rfl
  have : FaithfulSMul (ProjElementary Q) X := faithfulSMul_iff.mpr (by
    intro p hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    apply mem_scalars_of_forall_singular h₁₂ (elementaryGroup_le_orthogonalGroup Q g.2)
    intro v hv hQv
    have := hp (lineMk v hv hQv)
    rw [hsmul, smul_lineMk, lineMk_eq_lineMk_iff] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩)
  have : MulAction.IsPreprimitive G X := isPreprimitive_singularLines h₁₂ h₁₃ h₂₃ hQ
  have : MulAction.IsPreprimitive (ProjElementary Q) X :=
    MulAction.IsPreprimitive.of_surjective
      (f := (⟨id, fun _ _ => rfl⟩ : X →ₑ[(QuotientGroup.mk : G → ProjElementary Q)] X))
      Function.surjective_id
  have : Nontrivial (ProjElementary Q) := by
    obtain ⟨g, hg, hgf⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ P₁.f_ne_zero
      P₁.e_ne_zero (by rw [P₁.Q_f, P₁.Q_e])
    refine ⟨⟨((⟨g, hg⟩ : G) : ProjElementary Q), 1, fun h1 => ?_⟩⟩
    have hx := congrArg (· • lineMk P₁.f P₁.f_ne_zero P₁.Q_f) h1
    simp only [one_smul] at hx
    rw [hsmul, smul_lineMk_of_apply_eq_smul P₁.f_ne_zero P₁.e_ne_zero P₁.Q_f P₁.Q_e (c := 1)
      (by rw [one_smul]; exact hgf), lineMk_eq_lineMk_iff] at hx
    obtain ⟨a, ha⟩ := hx
    have := congrArg (fun z => polar Q z P₁.e) ha
    simp only [polar_smul_left_eq, P₁.polar_fe, P₁.polar_ee, mul_one] at this
    rw [this, zero_smul] at ha
    exact P₁.e_ne_zero ha.symm
  have hperfect : commutator (ProjElementary Q) = ⊤ := by
    have : Group.IsPerfect G :=
      Group.isPerfect_def.mpr (commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ)
    exact Group.IsPerfect.commutator_eq_top
  let U : Subgroup G := (rootGroup Q P₁.e).subgroupOf G
  let T : Subgroup (ProjElementary Q) := U.map (QuotientGroup.mk' Z)
  set α : X := lineMk P₁.e P₁.e_ne_zero P₁.Q_e
  have hTle : T ≤ MulAction.stabilizer (ProjElementary Q) α := by
    rintro _ ⟨u, hu, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change u • α = α
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_rootGroup] at hu
    obtain ⟨w, -, hw⟩ := hu
    exact smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1)
      (by rw [one_smul, ← hw, eichler_apply_self])
  have hTnormal : (T.subgroupOf (MulAction.stabilizer (ProjElementary Q) α)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTle]
    rintro _ p ⟨u, hu, rfl⟩ hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [MulAction.mem_stabilizer_iff, hsmul, smul_lineMk, lineMk_eq_lineMk_iff] at hp
    obtain ⟨c, hc⟩ := hp
    refine ⟨g * u * g⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
    exact conj_mem_rootGroup_of_apply_eq_smul (elementaryGroup_le_orthogonalGroup Q g.2)
      hc.symm hu
  have hTsolv : Group.IsSolvable T := by
    apply Group.isSolvable_of_comm
    rintro ⟨_, ⟨u, hu, rfl⟩⟩ ⟨_, ⟨v, hv, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu hv
    exact rootGroup_commute hu hv
  have hTgen : Subgroup.normalClosure (T : Set (ProjElementary Q)) = ⊤ := by
    have hset : (T : Set (ProjElementary Q)) = QuotientGroup.mk' Z '' (U : Set G) :=
      Subgroup.coe_map _ _
    rw [hset, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective Z),
      normalClosure_rootGroup_eq_top hQ h₁₂,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
  exact CFSG.BenderSuzuki.External.huppert_II_6_12 hperfect α T hTle hTnormal hTsolv hTgen

theorem isSimpleGroup_projElementary [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T) (hTQ : ∀ x ∈ T, Q x = 0) :
    IsSimpleGroup (ProjElementary Q) := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ hT hTQ
  exact isSimpleGroup_projElementary_of_hypPairs hQ h₁₂ h₁₃ h₂₃

theorem commutator_elementaryGroup_eq_top' [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) : commutator (elementaryGroup Q) = ⊤ := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ hT hTQ
  exact commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ

end CFSG.ClassicalGroups.Orthogonal
