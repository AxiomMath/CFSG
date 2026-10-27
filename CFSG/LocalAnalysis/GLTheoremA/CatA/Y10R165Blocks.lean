module

public import CFSG.LieType.SeitzGeneration.HyperAnisoBlocks
public import CFSG.RankThree.LocalRank.HyperplaneDecomposition
public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.BorelTits.CompleteFlag

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.LocalRank (natCast_card_subgroup_ne_zero)
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open CFSG.RankThree.PartOne.LIT (restrictAction restrictAction_apply)
open scoped DirectSum

attribute [local instance] Classical.decEq

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def actionEnd (A : Subgroup (V ≃ₗ[F] V)) : ↥A →* Module.End F V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp A.subtype

@[simp] theorem actionEnd_apply (A : Subgroup (V ≃ₗ[F] V)) (a : ↥A) (v : V) :
    actionEnd A a v = (a : V ≃ₗ[F] V) v := rfl

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]

scoped instance fintypeSubgroupOfFintype (D : Subgroup ↥A) : Fintype ↥D := Fintype.ofFinite _

abbrev fixedSpaceOf : Submodule F V := fixSub (actionEnd A) ⊤

abbrev commutatorSpaceOf : Submodule F V := LinearMap.ker (sumOp (actionEnd A) ⊤)

abbrev blockSpace (D : Subgroup ↥A) : Submodule F V := block (actionEnd A) ⊤ D

abbrev Hyperplane (p : ℕ) : Type _ := {D : Subgroup ↥A // D.index = p}

@[simp] theorem mem_fixedSpaceOf {v : V} :
    v ∈ fixedSpaceOf A ↔ ∀ a : ↥A, (a : V ≃ₗ[F] V) v = v := by
  simp [fixedSpaceOf, fixSub, stabVec]

@[simp] theorem mem_commutatorSpaceOf {v : V} :
    v ∈ commutatorSpaceOf A ↔ sumOp (actionEnd A) ⊤ v = 0 :=
  Iff.rfl

@[simp] theorem mem_blockSpace {D : Subgroup ↥A} {v : V} :
    v ∈ blockSpace A D ↔ (∀ d ∈ D, (d : V ≃ₗ[F] V) v = v) ∧ v ∈ commutatorSpaceOf A := by
  simp [blockSpace, block, mem_commutatorSpaceOf, fixSub, stabVec]

theorem blockSpace_le_commutatorSpaceOf (D : Subgroup ↥A) :
    blockSpace A D ≤ commutatorSpaceOf A := fun _ hv => (mem_blockSpace A).mp hv |>.2

theorem natCast_card_ne_zero {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) : ((Fintype.card A : ℕ) : F) ≠ 0 := by
  have hpow : ∀ g : ↥A, g ^ p = 1 := fun g => Subtype.ext (by
    simpa using hA.2 (g : V ≃ₗ[F] V) g.2)
  have h := natCast_card_subgroup_ne_zero (G := ↥A) hp hpow hpF ⊤
  rwa [Nat.card_eq_fintype_card,
    Fintype.card_congr (Subgroup.topEquiv (G := ↥A)).toEquiv] at h

theorem pow_eq_one {p : ℕ} (hA : IsElemAbelian p A) (a : ↥A) : a ^ p = 1 :=
  Subtype.ext (by simpa using hA.2 (a : V ≃ₗ[F] V) a.2)

private theorem sumOp_top_apply (v : V) :
    sumOp (actionEnd A) ⊤ v = ∑ a : ↥A, (a : V ≃ₗ[F] V) v := by
  rw [sumOp, LinearMap.sum_apply]
  exact Fintype.sum_equiv (Subgroup.topEquiv (G := ↥A)).toEquiv _ _ (fun a => rfl)

theorem fixedSpaceOf_inf_commutatorSpaceOf {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) : fixedSpaceOf A ⊓ commutatorSpaceOf A = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hvC, hvU⟩
  have h1 : sumOp (actionEnd A) ⊤ v = (Fintype.card A : F) • v := by
    have h := sumOp_apply_of_fix (actionEnd A) (⊤ : Subgroup ↥A) hvC
    rwa [Fintype.card_congr (Subgroup.topEquiv (G := ↥A)).toEquiv] at h
  simp only [SetLike.mem_coe, mem_commutatorSpaceOf] at hvU
  rw [hvU] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left (natCast_card_ne_zero A hp hpF hA)

theorem sup_fixedSpaceOf_commutatorSpaceOf {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) : fixedSpaceOf A ⊔ commutatorSpaceOf A = ⊤ := by
  have hcard := natCast_card_ne_zero A hp hpF hA
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = (((Fintype.card A : ℕ) : F))⁻¹ • sumOp (actionEnd A) ⊤ v +
      (v - (((Fintype.card A : ℕ) : F))⁻¹ • sumOp (actionEnd A) ⊤ v) := by abel
  rw [hv]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_))
    (Submodule.mem_sup_right ?_)
  · exact sumOp_mem_fixSub (actionEnd A) (⊤ : Subgroup ↥A) v
  · rw [mem_commutatorSpaceOf]
    rw [LinearMap.map_sub, LinearMap.map_smul,
      sumOp_apply_of_fix (actionEnd A) ⊤ (sumOp_mem_fixSub _ ⊤ v),
      Fintype.card_congr (Subgroup.topEquiv (G := ↥A)).toEquiv, smul_smul,
      inv_mul_cancel₀ hcard, one_smul, sub_self]

theorem isCompl_fixedSpaceOf_commutatorSpaceOf {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) : IsCompl (fixedSpaceOf A) (commutatorSpaceOf A) :=
  ⟨disjoint_iff_inf_le.mpr (le_of_eq (fixedSpaceOf_inf_commutatorSpaceOf A hp hpF hA)),
    codisjoint_iff_le_sup.mpr (le_of_eq (sup_fixedSpaceOf_commutatorSpaceOf A hp hpF hA).symm)⟩

theorem commutatorSpaceOf_eq_span {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    commutatorSpaceOf A =
      Submodule.span F {w : V | ∃ (a : ↥A) (v : V), (a : V ≃ₗ[F] V) v - v = w} := by
  have hcard := natCast_card_ne_zero A hp hpF hA
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
  · have hzero : (∑ a : ↥A, (a : V ≃ₗ[F] V) w) = 0 := by
      simp only [SetLike.mem_coe, mem_commutatorSpaceOf] at hw
      rwa [← sumOp_top_apply A w]
    have hsum : (∑ a : ↥A, (w - (a : V ≃ₗ[F] V) w)) = (Fintype.card A : F) • w := by
      rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul]
    have hw' : w = (((Fintype.card A : ℕ) : F))⁻¹ • ∑ a : ↥A, (w - (a : V ≃ₗ[F] V) w) := by
      rw [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    rw [hw']
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
    have : w - (a : V ≃ₗ[F] V) w = -((a : V ≃ₗ[F] V) w - w) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, w, rfl⟩)
  · rintro w ⟨a, v, rfl⟩
    rw [SetLike.mem_coe, mem_commutatorSpaceOf]
    rw [LinearMap.map_sub]
    rw [show sumOp (actionEnd A) ⊤ ((a : V ≃ₗ[F] V) v) = sumOp (actionEnd A) ⊤ v from ?_]
    rw [sub_self]
    have h2 : (sumOp (actionEnd A) ⊤ * actionEnd A a) v = sumOp (actionEnd A) ⊤ v := by
      rw [sumOp_mul (actionEnd A) ⊤ (Subgroup.mem_top a)]
    rwa [Module.End.mul_apply] at h2

@[expose] def restrictEnd (U : Submodule F V) (hU : ∀ a : ↥A, ∀ u ∈ U, (a : V ≃ₗ[F] V) u ∈ U) :
    ↥A →* Module.End F U :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (restrictAction A.subtype U hU)

theorem restrictEnd_apply (U : Submodule F V) (hU : ∀ a : ↥A, ∀ u ∈ U, (a : V ≃ₗ[F] V) u ∈ U)
    (a : ↥A) (u : U) : ((restrictEnd A U hU a u : U) : V) = (a : V ≃ₗ[F] V) u :=
  restrictAction_apply A.subtype U hU a u

theorem commutatorSpaceOf_invariant {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (a : ↥A) :
    ∀ u ∈ commutatorSpaceOf A, (a : V ≃ₗ[F] V) u ∈ commutatorSpaceOf A := by
  intro u hu
  have hu' : sumOp (actionEnd A) ⊤ u = 0 := hu
  have h2 : (sumOp (actionEnd A) ⊤ * actionEnd A a) u = sumOp (actionEnd A) ⊤ u := by
    rw [sumOp_mul (actionEnd A) ⊤ (Subgroup.mem_top a)]
  rw [Module.End.mul_apply] at h2
  show sumOp (actionEnd A) ⊤ (actionEnd A a u) = 0
  rw [h2, hu']

theorem invariants_restrictEnd {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (D : Subgroup ↥A) :
    Representation.invariants
        (MonoidHom.comp (restrictEnd A (commutatorSpaceOf A)
          (commutatorSpaceOf_invariant A hp hpF hA)) D.subtype)
      = (blockSpace A D).comap (commutatorSpaceOf A).subtype := by
  ext u
  rw [Representation.mem_invariants, Submodule.mem_comap]
  constructor
  · intro h
    refine (mem_blockSpace A).mpr ⟨fun d hd => ?_, u.2⟩
    have h1 := h ⟨d, hd⟩
    have h2 := congrArg (fun x : ↥(commutatorSpaceOf A) => (x : V)) h1
    simpa [MonoidHom.comp_apply, restrictEnd_apply] using h2
  · rintro ⟨h1, -⟩ d
    refine Subtype.ext ?_
    rw [MonoidHom.comp_apply, restrictEnd_apply]
    exact h1 d d.2

abbrev blockSpaceU {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (D : Hyperplane A p) :
    Submodule F ↥(commutatorSpaceOf A) :=
  Representation.invariants
    (MonoidHom.comp (restrictEnd A (commutatorSpaceOf A)
      (commutatorSpaceOf_invariant A hp hpF hA)) D.1.subtype)

private theorem span_diff_commutatorSpaceOf {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    Submodule.span F {v : ↥(commutatorSpaceOf A) | ∃ (a : ↥A) (u : ↥(commutatorSpaceOf A)),
      (restrictEnd A (commutatorSpaceOf A) (commutatorSpaceOf_invariant A hp hpF hA) a) u - u
        = v} = ⊤ := by
  set U := commutatorSpaceOf A with hUdef
  set hU := commutatorSpaceOf_invariant A hp hpF hA
  have hcard := natCast_card_ne_zero A hp hpF hA
  refine eq_top_iff.mpr fun u _ => ?_
  have hzero : (∑ a : ↥A, (restrictEnd A U hU a) u) = 0 := by
    have h : sumOp (actionEnd A) ⊤ (u : V) = 0 := u.2
    rw [sumOp_top_apply A (u : V)] at h
    exact Subtype.ext (by simpa [restrictEnd_apply] using h)
  have hsum : (∑ a : ↥A, (u - (restrictEnd A U hU a) u)) = (Fintype.card A : F) • u := by
    rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  have hu' : u = (((Fintype.card A : ℕ) : F))⁻¹ •
      ∑ a : ↥A, (u - (restrictEnd A U hU a) u) := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hu']
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
  have : u - (restrictEnd A U hU a) u = -((restrictEnd A U hU a) u - u) := by abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, u, rfl⟩)

theorem blockSpace_eq_map_blockSpaceU {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (D : Hyperplane A p) :
    blockSpace A D.1 = (blockSpaceU A hp hpF hA D).map (commutatorSpaceOf A).subtype := by
  rw [blockSpaceU, invariants_restrictEnd A hp hpF hA, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_comm,
    inf_eq_left.mpr (blockSpace_le_commutatorSpaceOf A D.1)]

theorem isInternal_blockSpaceU {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    DirectSum.IsInternal (blockSpaceU A hp hpF hA) := by
  haveI : IsMulCommutative ↥A := hA.1
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun a b => mul_comm' a b }
  let α : ↥A →* Module.End F ↥(commutatorSpaceOf A) :=
    restrictEnd A (commutatorSpaceOf A) (commutatorSpaceOf_invariant A hp hpF hA)
  exact (CFSG.RankThree.LocalRank.coprime_hyperplane_module_decomposition
    (p := p) (α := α) hp (fun a => pow_eq_one A hA a) hpF
    (span_diff_commutatorSpaceOf A hp hpF hA)).1

theorem iSupIndep_blockSpace {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    iSupIndep (fun D : Hyperplane A p => blockSpace A D.1) := by
  classical
  have hIntU := isInternal_blockSpaceU A hp hpF hA
  have hIndepU : iSupIndep (blockSpaceU A hp hpF hA) := hIntU.submodule_iSupIndep
  have hmaps : (fun D : Hyperplane A p => blockSpace A D.1)
      = fun D => (blockSpaceU A hp hpF hA D).map (commutatorSpaceOf A).subtype :=
    funext (blockSpace_eq_map_blockSpaceU A hp hpF hA)
  rw [hmaps]
  rw [iSupIndep_def] at hIndepU ⊢
  intro D
  have hi : blockSpaceU A hp hpF hA D ⊓
      (⨆ E, ⨆ (_ : E ≠ D), blockSpaceU A hp hpF hA E) = ⊥ :=
    le_bot_iff.mp (disjoint_iff_inf_le.mp (hIndepU D))
  rw [disjoint_iff_inf_le]
  have h1 : (⨆ E, ⨆ (_ : E ≠ D), (blockSpaceU A hp hpF hA E).map (commutatorSpaceOf A).subtype)
      = (⨆ E, ⨆ (_ : E ≠ D), blockSpaceU A hp hpF hA E).map (commutatorSpaceOf A).subtype := by
    rw [Submodule.map_iSup]
    simp only [Submodule.map_iSup]
  rw [h1, ← Submodule.map_inf _ (Submodule.subtype_injective (commutatorSpaceOf A)), hi,
    Submodule.map_bot]

theorem iSup_blockSpace_eq_commutatorSpaceOf {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    (⨆ D : Hyperplane A p, blockSpace A D.1) = commutatorSpaceOf A := by
  classical
  have hIntU := isInternal_blockSpaceU A hp hpF hA
  have hSupU : (⨆ D : Hyperplane A p, blockSpaceU A hp hpF hA D) = ⊤ :=
    hIntU.submodule_iSup_eq_top
  have hmaps : (fun D : Hyperplane A p => blockSpace A D.1) =
      fun D => (blockSpaceU A hp hpF hA D).map (commutatorSpaceOf A).subtype :=
    funext (blockSpace_eq_map_blockSpaceU A hp hpF hA)
  rw [hmaps, ← Submodule.map_iSup, hSupU, Submodule.map_top, Submodule.range_subtype]

theorem sup_fixedSpaceOf_iSup_blockSpace {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) :
    fixedSpaceOf A ⊔ (⨆ D : Hyperplane A p, blockSpace A D.1) = ⊤ := by
  rw [iSup_blockSpace_eq_commutatorSpaceOf A hp hpF hA,
    sup_fixedSpaceOf_commutatorSpaceOf A hp hpF hA]

theorem blockSpace_invariant {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {D : Subgroup ↥A} {a : ↥A} {v : V}
    (hv : v ∈ blockSpace A D) : (a : V ≃ₗ[F] V) v ∈ blockSpace A D := by
  haveI : IsMulCommutative ↥A := hA.1
  obtain ⟨hvD, hvU⟩ := (mem_blockSpace A).mp hv
  refine (mem_blockSpace A).mpr ⟨fun d hd => ?_,
    commutatorSpaceOf_invariant A hp hpF hA a v hvU⟩
  have h1 : ((d * a : ↥A) : V ≃ₗ[F] V) = (d : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V) :=
    map_mul A.subtype d a
  have h2 : (d * a : ↥A) = a * d := mul_comm' d a
  have h3 : ((a * d : ↥A) : V ≃ₗ[F] V) = (a : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) :=
    map_mul A.subtype a d
  have key : (d : V ≃ₗ[F] V) ((a : V ≃ₗ[F] V) v) = (a : V ≃ₗ[F] V) v := by
    calc (d : V ≃ₗ[F] V) ((a : V ≃ₗ[F] V) v)
        = ((d : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V)) v := (LinearEquiv.mul_apply ..).symm
      _ = ((d * a : ↥A) : V ≃ₗ[F] V) v := by rw [h1]
      _ = ((a * d : ↥A) : V ≃ₗ[F] V) v := by rw [h2]
      _ = ((a : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V)) v := by rw [h3]
      _ = (a : V ≃ₗ[F] V) ((d : V ≃ₗ[F] V) v) := LinearEquiv.mul_apply ..
      _ = (a : V ≃ₗ[F] V) v := by rw [hvD d hd]
  exact key

theorem natCast_card_top_ne_zero {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) : ((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F) ≠ 0 := by
  rw [Fintype.card_congr (Subgroup.topEquiv (G := ↥A)).toEquiv]
  exact natCast_card_ne_zero A hp hpF hA

theorem eq_zero_of_fixed_mem_blockSpace {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {D : Hyperplane A p} {x : ↥A} (hx : x ∉ D.1)
    {v : V} (hv : v ∈ blockSpace A D.1) (hfix : (x : V ≃ₗ[F] V) v = v) : v = 0 := by
  refine block_fixed_eq_zero (actionEnd A) (A := (⊤ : Subgroup ↥A))
    (natCast_card_top_ne_zero A hp hpF hA) (F := D.1) (x := x) ?_ hv hfix
  refine HyperBlocks.sup_zpowers_eq hp le_top ?_ (Subgroup.mem_top x) hx
  rw [Subgroup.relIndex_top_right]
  exact D.2

theorem blockSpace_pow_mem {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {D : Subgroup ↥A} (a : ↥A) {n : ℕ} {u : V}
    (hu : u ∈ blockSpace A D) : ((a : V ≃ₗ[F] V) ^ n) u ∈ blockSpace A D := by
  induction n with
  | zero => simpa using hu
  | succ m ihm => rw [pow_succ', LinearEquiv.mul_apply]; exact blockSpace_invariant A hp hpF hA ihm

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
