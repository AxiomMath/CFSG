module

public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.Blueprint.ChevalleyRootGroups
public import CFSG.LieType.Chevalley.Braid

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable (τ : Tag) (R : Type*) [CommRing R]

@[expose] def torusGroup
    : Subgroup (Module.End R (RootModule τ R))ˣ :=
  Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2)

@[expose] def monomialSubgroup
    : Subgroup (Module.End R (RootModule τ R))ˣ :=
  torusGroup τ R ⊔ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ R i 1)

@[expose] def borelGroup
    : Subgroup (Module.End R (RootModule τ R))ˣ :=
  torusGroup τ R ⊔ posUnipotent τ R

@[expose] def IsUpperTriangular (A : Module.End R (RootModule τ R)) : Prop :=
  ∀ a b : Label τ, b.Precedes a → A (Finsupp.single b 1) a = 0

variable {τ R}

@[expose] def diagonalGroup : Subgroup (Module.End R (RootModule τ R))ˣ where
  carrier := {g | (∀ j, (g : Module.End R (RootModule τ R)) (hVec τ R j) = hVec τ R j) ∧
    ∀ α, IsRoot τ α → ∃ c : Rˣ, (g : Module.End R (RootModule τ R)) (rootVec τ R α) =
      (c : R) • rootVec τ R α}
  one_mem' := ⟨fun _ => rfl, fun _ _ => ⟨1, by simp⟩⟩
  mul_mem' {g g'} hg hg' := ⟨fun j => by
      rw [Units.val_mul, Module.End.mul_apply, hg'.1, hg.1],
    fun α hα => by
      obtain ⟨c, hc⟩ := hg.2 α hα
      obtain ⟨c', hc'⟩ := hg'.2 α hα
      refine ⟨c * c', ?_⟩
      rw [Units.val_mul, Module.End.mul_apply, hc', map_smul, hc, smul_smul, Units.val_mul,
        mul_comm]⟩
  inv_mem' {g} hg := ⟨fun j => by
      conv_lhs => rw [← hg.1 j]
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply],
    fun α hα => by
      obtain ⟨c, hc⟩ := hg.2 α hα
      refine ⟨c⁻¹, ?_⟩
      have h := congrArg (fun v => ((c⁻¹ : Rˣ) : R) • ((g⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) v) hc
      simp only [map_smul, smul_smul, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Module.End.one_apply, one_smul] at h
      exact h.symm⟩

theorem torusGroup_le_diagonalGroup
    : torusGroup τ R ≤ diagonalGroup := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact ⟨fun j => torusElt_hVec i j t, fun α hα => ⟨_, torusElt_rootVec i t hα⟩⟩

theorem exists_apply_single_of_mem_diagonalGroup {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) (b : Label τ) :
    ∃ c : Rˣ, (g : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
      (c : R) • Finsupp.single b 1 := by
  rcases b with j | ⟨α, hα⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact hg.1 j⟩
  · obtain ⟨c, hc⟩ := hg.2 α hα
    rw [← rootVec_eq_single_of_isRoot hα]
    exact ⟨c, hc⟩

theorem apply_apply_of_mem_diagonalGroup {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) (a : Label τ) {c : Rˣ}
    (hc : (g : Module.End R (RootModule τ R)) (Finsupp.single a 1) = (c : R) • Finsupp.single a 1)
    (x : RootModule τ R) : (g : Module.End R (RootModule τ R)) x a = (c : R) * x a := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single b r =>
    obtain ⟨c', hc'⟩ := exists_apply_single_of_mem_diagonalGroup hg b
    have hsingle : Finsupp.single b r = r • Finsupp.single b (1 : R) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, hc', smul_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases hab : b = a
    · subst hab
      rw [hc] at hc'
      have := congrArg (fun v => v b) hc'
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
      rw [this, Finsupp.single_eq_same]
      ring
    · rw [Finsupp.single_eq_of_ne (Ne.symm hab), mul_zero, mul_zero, mul_zero]

theorem mul_comm_of_mem_diagonalGroup
    {g g' : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) (hg' : g' ∈ diagonalGroup) : g * g' = g' * g := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) (fun α hα => ?_))
  · rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hg.1, hg'.1,
      hg.1]
  · obtain ⟨c, hc⟩ := hg.2 α hα
    obtain ⟨c', hc'⟩ := hg'.2 α hα
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hc', map_smul,
      hc, map_smul, hc', smul_smul, smul_smul, mul_comm]

theorem torusElt_mem_torusGroup
    (i : Fin τ.rank) (t : Rˣ) : torusElt τ R i t ∈ torusGroup τ R :=
  Subgroup.subset_closure ⟨(i, t), rfl⟩

theorem posUnipotent_le_comap_conj_torusElt
    (i : Fin τ.rank) (t : Rˣ) :
    posUnipotent τ R ≤ (posUnipotent τ R).comap (MulAut.conj (torusElt τ R i t)).toMonoidHom := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [root_torus_conjugation i hα.1 t c]
  exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨_, rfl⟩))

theorem torusElt_mem_normalizer_posUnipotent
    (i : Fin τ.rank) (t : Rˣ) :
    torusElt τ R i t ∈ Subgroup.normalizer (SetLike.coe (posUnipotent τ R)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨fun hh => posUnipotent_le_comap_conj_torusElt i t hh, fun hh => ?_⟩
  have h1 := posUnipotent_le_comap_conj_torusElt i t⁻¹ hh
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hinv : torusElt τ R i t⁻¹ = (torusElt τ R i t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
  rw [hinv] at h1
  convert h1 using 1
  group

theorem torusGroup_le_normalizer_posUnipotent :
    torusGroup τ R ≤ Subgroup.normalizer (SetLike.coe (posUnipotent τ R)) :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_normalizer_posUnipotent i t)

theorem torusGroup_inf_posUnipotent
    : torusGroup τ R ⊓ posUnipotent τ R = ⊥ := by
  refine eq_bot_iff.2 fun g ⟨hgH, hgU⟩ => Subgroup.mem_bot.2 ?_
  have hd := torusGroup_le_diagonalGroup hgH
  have hu := isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ R hgU)
  have hone : ∀ b : Label τ, (g : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
      Finsupp.single b 1 := fun b => by
    obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hd b
    have h1 := hu.1 b
    rw [hc, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
    rw [hc, h1, one_smul]
  refine Units.ext (rootModule_end_ext (fun j => ?_) (fun α hα => ?_))
  · exact hone (Sum.inl j)
  · rw [Units.val_one, Module.End.one_apply, rootVec_eq_single_of_isRoot hα]
    exact hone _

theorem triangular_borel_structure
    (τ : Tag) (R : Type*) [CommRing R] :
    (∀ g ∈ torusGroup τ R, ∀ g' ∈ torusGroup τ R, g * g' = g' * g) ∧
    (∀ g ∈ torusGroup τ R,
      (∀ j, (g : Module.End R (RootModule τ R)) (hVec τ R j) = hVec τ R j) ∧
      ∀ α, IsRoot τ α → ∃ c : Rˣ, (g : Module.End R (RootModule τ R)) (rootVec τ R α) =
        (c : R) • rootVec τ R α) ∧
    torusGroup τ R ≤ Subgroup.normalizer (SetLike.coe (posUnipotent τ R)) ∧
    torusGroup τ R ⊓ posUnipotent τ R = ⊥ ∧
    ((borelGroup τ R : Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (torusGroup τ R) * SetLike.coe (posUnipotent τ R)) ∧
    ((borelGroup τ R : Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (posUnipotent τ R) * SetLike.coe (torusGroup τ R)) ∧
    (∀ h₁ ∈ torusGroup τ R, ∀ h₂ ∈ torusGroup τ R, ∀ u₁ ∈ posUnipotent τ R,
      ∀ u₂ ∈ posUnipotent τ R, h₁ * u₁ = h₂ * u₂ → h₁ = h₂ ∧ u₁ = u₂) ∧
    (∀ h₁ ∈ torusGroup τ R, ∀ h₂ ∈ torusGroup τ R, ∀ u₁ ∈ posUnipotent τ R,
      ∀ u₂ ∈ posUnipotent τ R, u₁ * h₁ = u₂ * h₂ → u₁ = u₂ ∧ h₁ = h₂) ∧
    ((posUnipotent τ R).subgroupOf (borelGroup τ R)).Normal ∧
    (∀ b ∈ borelGroup τ R, IsUpperTriangular τ R (b : Module.End R (RootModule τ R))) ∧
    ((torusGroup τ R).subgroupOf (monomialSubgroup τ R)).Normal ∧
    ∀ (K : Type*) [Field K], borelGroup τ K ≤ adjointGroup τ K ∧
      monomialSubgroup τ K ≤ adjointGroup τ K := by
  have hN := torusGroup_le_normalizer_posUnipotent (τ := τ) (R := R)
  have hinf := torusGroup_inf_posUnipotent (τ := τ) (R := R)
  have hHU : (borelGroup τ R : Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (torusGroup τ R) * SetLike.coe (posUnipotent τ R) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  have hUH : (borelGroup τ R : Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (posUnipotent τ R) * SetLike.coe (torusGroup τ R) := by
    rw [show borelGroup τ R = posUnipotent τ R ⊔ torusGroup τ R from sup_comm _ _]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN
  refine ⟨fun g hg g' hg' => mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hg)
      (torusGroup_le_diagonalGroup hg'), fun g hg => torusGroup_le_diagonalGroup hg, hN, hinf,
    hHU, hUH, ?_, ?_, ?_, ?_, ?_, fun K _ => ⟨?_, ?_⟩⟩
  · intro h₁ hh₁ h₂ hh₂ u₁ hu₁ u₂ hu₂ heq
    have hmem : h₂⁻¹ * h₁ ∈ torusGroup τ R ⊓ posUnipotent τ R := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hh₂) hh₁, ?_⟩
      have : h₂⁻¹ * h₁ = u₂ * u₁⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq, mul_inv_cancel_right]
      rw [this]
      exact mul_mem hu₂ (inv_mem hu₁)
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    subst hmem
    exact ⟨rfl, mul_left_cancel heq⟩
  · intro h₁ hh₁ h₂ hh₂ u₁ hu₁ u₂ hu₂ heq
    have hmem : u₂⁻¹ * u₁ ∈ torusGroup τ R ⊓ posUnipotent τ R := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hu₂) hu₁⟩
      have : u₂⁻¹ * u₁ = h₂ * h₁⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq, mul_inv_cancel_right]
      rw [this]
      exact mul_mem hh₂ (inv_mem hh₁)
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    subst hmem
    exact ⟨rfl, mul_left_cancel heq⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le hN Subgroup.le_normalizer)
  · intro b hb
    have hb' : b ∈ SetLike.coe (torusGroup τ R) * SetLike.coe (posUnipotent τ R) := by
      rw [← hHU]
      exact hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    intro a c hca
    have hd := torusGroup_le_diagonalGroup hh
    obtain ⟨e, he⟩ := exists_apply_single_of_mem_diagonalGroup hd a
    rw [Units.val_mul, Module.End.mul_apply, apply_apply_of_mem_diagonalGroup hd a he,
      (isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ R hu)).2 a c hca, mul_zero]
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer ((Subgroup.closure_le _).2 ?_))
    rintro _ ⟨i, rfl⟩
    exact weylElt_mem_normalizer_torus τ R i 1
  · refine sup_le ((Subgroup.closure_le _).2 ?_)
      (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t
  · refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup i t
    · rintro _ ⟨i, rfl⟩
      exact weylElt_mem_adjointGroup i 1

end CFSG.LieType.Chevalley
