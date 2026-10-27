module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped TensorProduct

set_option linter.unusedSectionVars false

section Fixed

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiag_coord (a : Fin τ.rank → Kˣ) (v : RootModule τ K) (b : Label τ) :
    rootDiag a v b = ((rootChar a (labelWt τ b) : Kˣ) : K) * v b := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
  | single c r =>
    have hs : Finsupp.single c r = r • Finsupp.single c (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, rootDiag_single, smul_smul, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · ring

theorem ker_rootDiag_sub_one (a : Fin τ.rank → Kˣ) :
    LinearMap.ker (rootDiag a - 1) =
      Finsupp.supported K K {b : Label τ | rootChar a (labelWt τ b) = 1} := by
  ext v
  rw [LinearMap.mem_ker, Finsupp.mem_supported]
  constructor
  · intro h b hb
    have h1 := congrArg (fun w : RootModule τ K => w b) h
    simp only [LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, rootDiag_coord,
      Module.End.one_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have hv : v b ≠ 0 := Finsupp.mem_support_iff.1 hb
    have h2 : (((rootChar a (labelWt τ b) : Kˣ) : K) - 1) * v b = 0 := by
      rw [sub_mul, one_mul]
      exact h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Units.ext (sub_eq_zero.1 h3)
    · exact absurd h3 hv
  · intro h
    ext b
    simp only [LinearMap.sub_apply, Finsupp.coe_sub, Pi.sub_apply, rootDiag_coord,
      Module.End.one_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hb : v b = 0
    · rw [hb, mul_zero, sub_zero]
    · have : rootChar a (labelWt τ b) = 1 := h (Finsupp.mem_support_iff.2 hb)
      rw [this, Units.val_one, one_mul, sub_self]

theorem finrank_ker_rootDiag_sub_one (a : Fin τ.rank → Kˣ) [Finite (Label τ)] :
    Module.finrank K (LinearMap.ker (rootDiag a - 1)) =
      Nat.card {b : Label τ // rootChar a (labelWt τ b) = 1} := by
  classical
  rw [ker_rootDiag_sub_one]
  haveI : Fintype ↥{b : Label τ | rootChar a (labelWt τ b) = 1} := Fintype.ofFinite _
  rw [(Finsupp.supportedEquivFinsupp (M := K) (R := K) _).finrank_eq,
    Module.finrank_finsupp_self]
  exact Nat.card_eq_fintype_card.symm


open scoped Classical in
theorem finrank_ker_rootDiag_sub_one_card (a : Fin τ.rank → Kˣ) :
    Module.finrank K (LinearMap.ker (rootDiag a - 1)) =
      τ.rank + ((rootFinset τ).filter fun α => rootChar a α = 1).card := by
  rw [finrank_ker_rootDiag_sub_one]
  have e : {b : Label τ // rootChar a (labelWt τ b) = 1} ≃
      Fin τ.rank ⊕ {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // rootChar a α.1 = 1} :=
    Equiv.subtypeSum.trans (Equiv.sumCongr
      (Equiv.subtypeUnivEquiv (fun i => by
        change rootChar a (0 : Fin τ.rank → ℤ) = 1
        exact rootChar_zero a))
      (Equiv.refl _))
  have e2 : {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // rootChar a α.1 = 1} ≃
      {v : Fin τ.rank → ℤ // v ∈ (rootFinset τ).filter fun α => rootChar a α = 1} :=
    { toFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨mem_rootFinset.2 p.1.2, p.2⟩⟩
      invFun := fun p =>
        ⟨⟨p.1, mem_rootFinset.1 (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sum, Nat.card_congr e2, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]

end Fixed

section Line

variable {K : Type} [Field K] {ω : Kˣ}

open scoped Classical in
theorem filter_rootFinset_e6LineChar (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    (rootFinset .E6).filter (fun α => rootChar (e6LineChar ω) α = 1) =
      Finset.univ.biUnion e6LineRoots := by
  ext α
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
    rootChar_e6LineChar, e6Line_zpow_eq_one_iff_three_dvd h3 h1, mem_rootFinset]
  constructor
  · rintro ⟨hα, hd⟩
    exact (three_dvd_iff_mem_e6LineRoots hα).1 hd
  · rintro ⟨i, hi⟩
    have hα := isRoot_of_mem_e6LineRoots hi
    exact ⟨hα, (three_dvd_iff_mem_e6LineRoots hα).2 ⟨i, hi⟩⟩

theorem e6Line_finrank_fixed_aux (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    Module.finrank K (LinearMap.ker (rootDiag (e6LineChar ω) - 1)) = 24 := by
  rw [finrank_ker_rootDiag_sub_one_card, filter_rootFinset_e6LineChar h3 h1,
    card_biUnion_e6LineRoots]
  rfl

end Line

section BaseChange

variable {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L]

omit [Field L] [Algebra K L] in
theorem baseChangeEnd_one_aux {L : Type} [Field L] (f : K →+* L) :
    baseChangeEnd f (1 : Module.End K (RootModule τ K)) = 1 := by
  refine end_ext_single fun b => ?_
  rw [baseChangeEnd_single, Module.End.one_apply, Module.End.one_apply]
  ext c
  simp [Finsupp.single_apply]

theorem baseChangeEnd_sub_aux (f : K →+* L) (A B : Module.End K (RootModule τ K)) :
    baseChangeEnd f (A - B) = baseChangeEnd f A - baseChangeEnd f B := by
  refine end_ext_single fun b => ?_
  rw [baseChangeEnd_single, LinearMap.sub_apply, LinearMap.sub_apply, baseChangeEnd_single,
    baseChangeEnd_single]
  ext c
  simp

theorem baseChangeEnd_mapRange_aux (f : K →+* L) (A : Module.End K (RootModule τ K))
    (v : RootModule τ K) :
    baseChangeEnd f A (Finsupp.mapRange f f.map_zero v) =
      Finsupp.mapRange f f.map_zero (A v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add f), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add f)]
  | single b r =>
    have h1 : Finsupp.mapRange f f.map_zero (Finsupp.single b r) =
        f r • Finsupp.single b (1 : L) := by
      simp
    have h2 : Finsupp.single b r = r • Finsupp.single b (1 : K) := by simp
    rw [h1, map_smul, baseChangeEnd_single, h2, map_smul]
    ext c
    simp

@[expose] def scalarExtEquiv (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L] :
    L ⊗[K] RootModule τ K ≃ₗ[L] RootModule τ L :=
  letI := Classical.decEq (Label τ)
  TensorProduct.finsuppScalarRight K L L (Label τ)

theorem scalarExtEquiv_tmul (c : L) (v : RootModule τ K) :
    scalarExtEquiv τ K L (c ⊗ₜ[K] v) =
      c • Finsupp.mapRange (algebraMap K L) (map_zero _) v := by
  classical
  ext b
  simp [scalarExtEquiv, Algebra.smul_def, mul_comm]

theorem baseChangeEnd_scalarExtEquiv (A : Module.End K (RootModule τ K))
    (t : L ⊗[K] RootModule τ K) :
    baseChangeEnd (algebraMap K L) A (scalarExtEquiv τ K L t) =
      scalarExtEquiv τ K L (A.baseChange L t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, scalarExtEquiv_tmul, scalarExtEquiv_tmul, map_smul,
      baseChangeEnd_mapRange_aux]

theorem finrank_ker_baseChangeEnd (A : Module.End K (RootModule τ K)) :
    Module.finrank L (LinearMap.ker (baseChangeEnd (algebraMap K L) A)) =
      Module.finrank K (LinearMap.ker A) := by
  have hker : LinearMap.ker (baseChangeEnd (algebraMap K L) A) =
      (LinearMap.ker (A.baseChange L)).map (scalarExtEquiv τ K L).toLinearMap := by
    ext w
    rw [LinearMap.mem_ker, Submodule.mem_map_equiv]
    set t := (scalarExtEquiv τ K L).symm w with ht
    have hw : w = scalarExtEquiv τ K L t := by rw [ht]; simp
    rw [hw, baseChangeEnd_scalarExtEquiv, LinearEquiv.map_eq_zero_iff, LinearMap.mem_ker]
  rw [hker, LinearEquiv.finrank_map_eq]
  have h1 : A.baseChange L = TensorProduct.AlgebraTensorModule.lTensor L L A := rfl
  rw [h1, Module.Flat.ker_lTensor_eq]
  have hinj : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor L L (LinearMap.ker A).subtype) := fun x y h =>
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) _
      (LinearMap.ker A).injective_subtype (by simpa using h)
  haveI : Module.Free K ↥(LinearMap.ker A) := Module.Free.of_divisionRing K ↥(LinearMap.ker A)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end BaseChange

section Conj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

theorem finrank_ker_conj_sub_one (y t : LinearMap.GeneralLinearGroup F V) :
    Module.finrank F (LinearMap.ker (((y * t * y⁻¹ : LinearMap.GeneralLinearGroup F V) :
        Module.End F V) - 1)) =
      Module.finrank F (LinearMap.ker ((t : Module.End F V) - 1)) := by
  let e : V ≃ₗ[F] V := LinearMap.GeneralLinearGroup.toLinearEquiv y
  have hker : LinearMap.ker (((y * t * y⁻¹ : LinearMap.GeneralLinearGroup F V) :
      Module.End F V) - 1) = (LinearMap.ker ((t : Module.End F V) - 1)).map e.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    change e ((t : Module.End F V) (e.symm v)) - v = 0 ↔
      (t : Module.End F V) (e.symm v) - e.symm v = 0
    rw [sub_eq_zero, sub_eq_zero]
    constructor
    · intro h
      apply e.injective
      rw [h, e.apply_symm_apply]
    · intro h
      rw [h, e.apply_symm_apply]
  rw [hker, LinearEquiv.finrank_map_eq]

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
