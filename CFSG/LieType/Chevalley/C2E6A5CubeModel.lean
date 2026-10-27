module

public import CFSG.LieType.Chevalley.C2E6ExteriorCubeKernel
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots
public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def restrictEndA
    : groupA →* Module.End K moduleA where
  toFun g := ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)).restrict
    (mem_moduleA_of_mem_groupA g.2)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem restrictEndA_apply
    (g : groupA) (v : moduleA) :
    ((restrictEndA g v : moduleA) : RootModule Tag.E6 K) =
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v := rfl

@[expose] def psiA
    : groupA →* (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ :=
  (Units.map phiA.conjRingEquiv.toMonoidHom).comp restrictEndA.toHomUnits

theorem psiA_apply
    (g : groupA) (x : ⋀[K]^3 (Fin 6 → K)) :
    (psiA g : Module.End K (⋀[K]^3 (Fin 6 → K))) x = phiA (restrictEndA g (phiA.symm x)) :=
  rfl

theorem psiA_eq_one_iff (g : groupA) :
    psiA g = 1 ↔
      ∀ v ∈ moduleA, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v = v := by
  constructor
  · intro h v hv
    have h1 := LinearMap.congr_fun (congrArg Units.val h) (phiA ⟨v, hv⟩)
    rw [psiA_apply, LinearEquiv.symm_apply_apply, Units.val_one, Module.End.one_apply] at h1
    exact congrArg Subtype.val (phiA.injective h1)
  · intro h
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [psiA_apply, Units.val_one, Module.End.one_apply]
    have : restrictEndA g (phiA.symm x) = phiA.symm x :=
      Subtype.ext (h _ (phiA.symm x).2)
    rw [this, LinearEquiv.apply_symm_apply]

theorem jA_mem_setA (t : Fin 5) : jA t ∈ setA := by
  fin_cases t
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
    Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr rfl)))]

theorem xUnit_mem_groupA
    (t : Fin 5) (c : K) : xUnit Tag.E6 K (jA t) c ∈ groupA :=
  Subgroup.subset_closure ⟨jA t, jA_mem_setA t, c, Or.inl rfl⟩

theorem yUnit_mem_groupA
    (t : Fin 5) (c : K) : yUnit Tag.E6 K (jA t) c ∈ groupA :=
  Subgroup.subset_closure ⟨jA t, jA_mem_setA t, c, Or.inr rfl⟩

abbrev upAdj (t : Fin 5) (c : K) : SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne c

abbrev downAdj (t : Fin 5) (c : K) : SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := t)).ne' c

theorem psiA_xUnit (t : Fin 5) (c : K) :
    psiA ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ = cubeHom (upAdj t c) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [psiA_apply, coe_cubeHom]
  have h := phiA_xOp t c (phiA.symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans rfl

theorem psiA_yUnit (t : Fin 5) (c : K) :
    psiA ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ = cubeHom (downAdj t c) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [psiA_apply, coe_cubeHom]
  have h := phiA_yOp t c (phiA.symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans rfl

@[expose] def adjSet : Set (SpecialLinearGroup (Fin 6) K) :=
  {g | ∃ (t : Fin 5) (c : K), g = upAdj t c ∨ g = downAdj t c}

@[expose] def upAdjSet : Set (SpecialLinearGroup (Fin 6) K) :=
  {g | ∃ (t : Fin 5) (c : K), g = upAdj t c}

theorem commutator_mem_closure {G : Type*} [Group G] {S : Set G} {a b : G}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) : ⁅a, b⁆ ∈ Subgroup.closure S := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem upper_mem_closure_upAdjSet : ∀ (d : ℕ) {i j : Fin 6} (hij : i < j),
    j.val = i.val + d + 1 → ∀ c : K,
      SpecialLinearGroup.transvection hij.ne c ∈ Subgroup.closure upAdjSet := by
  intro d
  induction d with
  | zero =>
    intro i j hij hd c
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : j = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [hd])
    have : SpecialLinearGroup.transvection hij.ne c = upAdj ⟨i.val, hi⟩ c := Subtype.ext (by
      rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, rfl⟩
  | succ d ih =>
    intro i j hij hd c
    have hk : i.val + 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val + 1, hk⟩
    have hik : i < k := Fin.lt_def.mpr (by simp [k])
    have hkj : k < j := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hik.ne hkj.ne hij.ne c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure ?_ (ih hkj (by simp [k]; omega) 1)
    have hi : i.val < 5 := by omega
    have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have e2 : k = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp [k])
    have : SpecialLinearGroup.transvection hik.ne c = upAdj ⟨i.val, hi⟩ c := Subtype.ext (by
      simp only [SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨i.val, hi⟩, c, rfl⟩

theorem lower_mem_closure_adjSet : ∀ (d : ℕ) {i j : Fin 6} (hji : j < i),
    i.val = j.val + d + 1 → ∀ c : K,
      SpecialLinearGroup.transvection hji.ne' c ∈ Subgroup.closure adjSet := by
  intro d
  induction d with
  | zero =>
    intro i j hji hd c
    have hj : j.val < 5 := by omega
    have e1 : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨j.val, hj⟩ := Fin.ext (by simp [hd])
    have : SpecialLinearGroup.transvection hji.ne' c = downAdj ⟨j.val, hj⟩ c := Subtype.ext (by
      rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨j.val, hj⟩, c, Or.inr rfl⟩
  | succ d ih =>
    intro i j hji hd c
    have hk : i.val - 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val - 1, hk⟩
    have hki : k < i := Fin.lt_def.mpr (by simp [k]; omega)
    have hjk : j < k := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hki.ne' hjk.ne' hji.ne' c 1
    rw [mul_one] at h
    rw [← h]
    refine commutator_mem_closure ?_ (ih hjk (by simp [k]; omega) 1)
    have hk5 : k.val < 5 := by simp [k]; omega
    have e1 : k = Fin.castSucc ⟨k.val, hk5⟩ := Fin.ext rfl
    have e2 : i = Fin.succ ⟨k.val, hk5⟩ := Fin.ext (by simp [k]; omega)
    have : SpecialLinearGroup.transvection hki.ne' c = downAdj ⟨k.val, hk5⟩ c := Subtype.ext (by
      simp only [SpecialLinearGroup.transvection_coe, ← e1, ← e2])
    rw [this]
    exact Subgroup.subset_closure ⟨⟨k.val, hk5⟩, c, Or.inr rfl⟩

theorem closure_upAdjSet_le_closure_adjSet :
    Subgroup.closure upAdjSet ≤ Subgroup.closure adjSet :=
  Subgroup.closure_mono fun _ ⟨t, c, h⟩ => ⟨t, c, Or.inl h⟩

theorem transvection_mem_closure_adjSet {i j : Fin 6} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ Subgroup.closure adjSet := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact closure_upAdjSet_le_closure_adjSet
      (upper_mem_closure_upAdjSet (j.val - i.val - 1) h (by omega) c)
  · exact lower_mem_closure_adjSet (i.val - j.val - 1) h (by omega) c

theorem closure_adjSet : Subgroup.closure adjSet = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact transvection_mem_closure_adjSet hij c

theorem unitriangular_le_closure_upAdjSet :
    LinearFlag.unitriangular 6 K ≤ Subgroup.closure upAdjSet := by
  refine (LinearCover.unitriangular_le_closure_rootElt (K := K) (n := 6)).trans
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, j, a, hij, rfl⟩
  rw [LinearCover.rootElt_of_ne hij.ne]
  exact upper_mem_closure_upAdjSet (j.val - i.val - 1) hij (by omega) a

theorem psiA_range_le
    : psiA.range ≤ (cubeHom (K := K)).range := by
  have htop : (⊤ : Subgroup groupA) = Subgroup.closure (((↑) : groupA → ModGL Tag.E6 K) ⁻¹'
      {g | ∃ i ∈ setA, ∃ c : K, g = xUnit Tag.E6 K i c ∨ g = yUnit Tag.E6 K i c}) :=
    Subgroup.closure_closure_coe_preimage.symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, hi, c, hg | hg⟩, rfl⟩
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    have e : g = ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ := Subtype.ext hg
    rw [e, psiA_xUnit]
    exact ⟨_, rfl⟩
  · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    have e : g = ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ := Subtype.ext hg
    rw [e, psiA_yUnit]
    exact ⟨_, rfl⟩

theorem cubeHom_adjSet_subset
    : cubeHom '' adjSet ⊆ (psiA.range : Set _) := by
  rintro _ ⟨g, ⟨t, c, rfl | rfl⟩, rfl⟩
  · exact ⟨_, psiA_xUnit t c⟩
  · exact ⟨_, psiA_yUnit t c⟩

theorem range_psiA
    : psiA.range = (cubeHom (K := K)).range := by
  refine le_antisymm psiA_range_le ?_
  rw [MonoidHom.range_eq_map, ← closure_adjSet, MonoidHom.map_closure, Subgroup.closure_le]
  exact cubeHom_adjSet_subset

theorem units_pow_three (l : Kˣ) : l ^ 3 = 1 := by
  obtain ⟨m, rfl⟩ := exists_omegaUnit_pow_eq l
  rw [← pow_mul, mul_comm, pow_mul, omegaUnit_pow_three, one_pow]

theorem ker_cubeHom : (cubeHom (K := K)).ker = LinearFlag.scalars 6 K := by
  ext g
  rw [MonoidHom.mem_ker, cubeHom_eq_one_iff, LinearFlag.mem_scalars]
  constructor
  · rintro ⟨l, hl, hg⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact zero_ne_one (by rw [← hl]; ring)
    refine ⟨Units.mk0 l hl0, ?_, ?_⟩
    · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul]
      have : Units.mk0 l hl0 ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val,
        Units.val_mk0, hl, Units.val_one])
      rw [this, one_pow]
    · rw [hg, Units.val_mk0, Matrix.smul_one_eq_diagonal]
      rfl
  · rintro ⟨c, -, hc⟩
    refine ⟨c, by rw [← Units.val_pow_eq_pow_val, units_pow_three, Units.val_one], ?_⟩
    rw [hc, Matrix.smul_one_eq_diagonal]
    rfl

theorem cubeHom_eq_cubeHom_iff (h h' : SpecialLinearGroup (Fin 6) K) :
    cubeHom h = cubeHom h' ↔ h⁻¹ * h' ∈ LinearFlag.scalars 6 K := by
  rw [← ker_cubeHom, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

end CFSG.LieType.Chevalley.C2E6Std
