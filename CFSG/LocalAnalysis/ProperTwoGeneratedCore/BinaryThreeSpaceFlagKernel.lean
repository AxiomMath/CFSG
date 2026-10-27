module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceSevenPoint
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Module

private theorem zmod2_eq_zero_or_one' : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

section Eight

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
theorem exists_dual_eq_one {w : W} (hw : w ≠ 0) : ∃ f : Module.Dual (ZMod 2) W, f w = 1 := by
  by_contra h
  push Not at h
  refine hw ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) w).mp fun f => ?_)
  rcases zmod2_eq_zero_or_one' (f w) with h0 | h1
  · exact h0
  · exact absurd h1 (h f)

omit [Fintype W] [DecidableEq W] in
theorem exists_eq_one_of_ne_zero {f : Module.Dual (ZMod 2) W} (hf : f ≠ 0) : ∃ w, f w = 1 := by
  by_contra h
  push Not at h
  refine hf (LinearMap.ext fun w => ?_)
  rcases zmod2_eq_zero_or_one' (f w) with h0 | h1
  · exact h0
  · exact absurd h1 (h w)

omit [DecidableEq W] in
theorem card_filter_eq_zero (hW : Fintype.card W = 8) (φ : Module.Dual (ZMod 2) W) {w : W}
    (hw : φ w = 1) : (Finset.univ.filter fun v => φ v = 0).card = 4 := by
  have h1 := two_mul_card_fiber_one φ hw
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset W)) (fun v => φ v = 1)
  have hneg : (Finset.univ.filter fun v => ¬φ v = 1) = Finset.univ.filter fun v => φ v = 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one' (φ v) with h | h <;> simp [h]
  rw [hneg, Finset.card_univ, hW] at hpart
  rw [hW] at h1
  omega

omit [Module (ZMod 2) W] in
theorem sum_points_add_zero {M : Type*} [AddCommMonoid M] (g : W → M) :
    ∑ p : Points W, g p + g 0 = ∑ v, g v := by
  rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ 0)]
  congr 1
  exact (Finset.sum_subtype _ (fun v => by simp) g).symm

theorem card_points_filter_eq_zero (hW : Fintype.card W = 8) (φ : Module.Dual (ZMod 2) W)
    {w : W} (hw : φ w = 1) : (Finset.univ.filter fun v : Points W => φ v = 0).card = 3 := by
  have h4 := card_filter_eq_zero hW φ hw
  rw [Finset.card_filter, ← sum_points_add_zero] at h4
  rw [Finset.card_filter]
  simp only [map_zero, ↓reduceIte] at h4
  omega

omit [DecidableEq W] in
theorem sum_filter_eq_zero (hW : Fintype.card W = 8) (φ : Module.Dual (ZMod 2) W) {w : W}
    (hw : φ w = 1) : ∑ v ∈ Finset.univ.filter (fun v => φ v = 0), v = 0 := by
  have : DecidablePred (· ∈ LinearMap.ker φ) := fun v =>
    decidable_of_iff (φ v = 0) LinearMap.mem_ker.symm
  have hmem : ∀ v, v ∈ Finset.univ.filter (fun v => φ v = 0) ↔ v ∈ LinearMap.ker φ := fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker]
  have hcard : Fintype.card (LinearMap.ker φ) = 4 := by
    rw [Fintype.card_subtype, ← card_filter_eq_zero hW φ hw]
    congr 1
    ext v
    rw [hmem]
    simp
  rw [Finset.sum_subtype _ hmem, ← Submodule.coe_sum, sum_univ_eq_zero (by rw [hcard]),
    Submodule.coe_zero]

omit [DecidableEq W] in
theorem exists_ne_zero_ker (hW : Fintype.card W = 8) (φ ψ : Module.Dual (ZMod 2) W) :
    ∃ w : W, w ≠ 0 ∧ φ w = 0 ∧ ψ w = 0 := by
  let Θ := φ.prod ψ
  have hker := AddSubgroup.card_ker_mul_card_range Θ.toAddMonoidHom
  rw [Nat.card_eq_fintype_card (α := W), hW] at hker
  have hrange : Nat.card Θ.toAddMonoidHom.range ≤ 4 := by
    have := Nat.card_le_card_of_injective _ (Subtype.val_injective (p := (· ∈
      Θ.toAddMonoidHom.range)))
    rwa [Nat.card_prod, Nat.card_zmod] at this
  have hpos : 0 < Nat.card Θ.toAddMonoidHom.range := Nat.card_pos
  have h2 : 1 < Nat.card Θ.toAddMonoidHom.ker := by
    by_contra h
    push Not at h
    have : Nat.card Θ.toAddMonoidHom.ker * Nat.card Θ.toAddMonoidHom.range ≤ 1 * 4 :=
      Nat.mul_le_mul h hrange
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨a, ha⟩ := exists_ne (0 : Θ.toAddMonoidHom.ker)
  have hΘ : Θ a = 0 := AddMonoidHom.mem_ker.mp a.2
  exact ⟨a, fun h => ha (Subtype.ext h), congrArg Prod.fst hΘ, congrArg Prod.snd hΘ⟩

end Eight

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

variable (V) in
abbrev Flags : Type _ :=
  {pf : Points V × Points (Module.Dual (ZMod 2) V) // (pf.2 : Module.Dual (ZMod 2) V) pf.1 = 0}

@[expose] def flagAct (g : V ≃ₗ[ZMod 2] V) (pf : Flags V) : Flags V :=
  ⟨(pointAct g pf.1.1, pointAct g.symm.dualMap pf.1.2), by
    change (pf.1.2 : Module.Dual (ZMod 2) V) (g.symm (g pf.1.1)) = 0
    rw [g.symm_apply_apply]
    exact pf.2⟩

theorem flagAct_symm_flagAct (g : V ≃ₗ[ZMod 2] V) (pf : Flags V) :
    flagAct g.symm (flagAct g pf) = pf := by
  refine Subtype.ext (Prod.ext (Subtype.ext (g.symm_apply_apply _)) (Subtype.ext ?_))
  ext v
  change (pf.1.2 : Module.Dual (ZMod 2) V) (g.symm (g v)) = _
  rw [g.symm_apply_apply]

@[expose] def flagPerm (g : V ≃ₗ[ZMod 2] V) : Equiv.Perm (Flags V) where
  toFun := flagAct g
  invFun := flagAct g.symm
  left_inv := flagAct_symm_flagAct g
  right_inv := flagAct_symm_flagAct g.symm

@[expose] def flagPermAct (g : V ≃ₗ[ZMod 2] V) (z : Flags V → ZMod 2) : Flags V → ZMod 2 :=
  fun pf => z (flagAct g.symm pf)

variable (V) in
@[expose] noncomputable def traceZeroEnd : Submodule (ZMod 2) (Module.End (ZMod 2) V) :=
  LinearMap.ker (LinearMap.trace (ZMod 2) V)

variable [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)]

omit [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
@[expose] noncomputable def flagEnd (pf : Flags V) : traceZeroEnd V :=
  ⟨LinearMap.smulRight (pf.1.2 : Module.Dual (ZMod 2) V) (pf.1.1 : V), by
    rw [traceZeroEnd, LinearMap.mem_ker, LinearMap.trace_smulRight]
    exact pf.2⟩

omit [DecidableEq V] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem card_dual (hV : finrank (ZMod 2) V = 3) : Fintype.card (Module.Dual (ZMod 2) V) = 8 := by
  rw [← Nat.card_eq_fintype_card, natCard_dual hV]

omit [DecidableEq V] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem finrank_dual (hV : finrank (ZMod 2) V = 3) :
    finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 := by
  have h := FiniteField.pow_finrank_eq_natCard 2 (Module.Dual (ZMod 2) V)
  rw [natCard_dual hV] at h
  exact Nat.pow_right_injective le_rfl (h.trans (by norm_num))

variable (V) in
@[expose] noncomputable def flagPsi : (Flags V → ZMod 2) →ₗ[ZMod 2] traceZeroEnd V :=
  Fintype.linearCombination (ZMod 2) flagEnd

variable (V) in
@[expose] def flagIota :
    ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V) →ₗ[ZMod 2]
      (Flags V → ZMod 2) where
  toFun t pf := t.1 + (t.2.1 : Points V → ZMod 2) pf.1.1 +
    (t.2.2 : Points (Module.Dual (ZMod 2) V) → ZMod 2) pf.1.2
  map_add' s t := by
    funext pf
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c t := by
    funext pf
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem flagPsi_apply (z : Flags V → ZMod 2) (v : V) :
    ((flagPsi V z : traceZeroEnd V) : Module.End (ZMod 2) V) v =
      ∑ pf : Flags V, z pf • ((pf.1.2 : Module.Dual (ZMod 2) V) v • (pf.1.1 : V)) := by
  rw [flagPsi, Fintype.linearCombination_apply, Submodule.coe_sum, LinearMap.sum_apply]
  rfl

theorem flagPsi_single (pf : Flags V) (v : V) :
    ((flagPsi V (Pi.single pf 1) : traceZeroEnd V) : Module.End (ZMod 2) V) v =
      (pf.1.2 : Module.Dual (ZMod 2) V) v • (pf.1.1 : V) := by
  rw [flagPsi, Fintype.linearCombination_apply_single, one_smul]
  rfl

theorem sum_flags {M : Type*} [AddCommMonoid M]
    (G : Points V → Points (Module.Dual (ZMod 2) V) → M) :
    ∑ pf : Flags V, G pf.1.1 pf.1.2 =
      ∑ p : Points V, ∑ q : Points (Module.Dual (ZMod 2) V),
        if (q : Module.Dual (ZMod 2) V) p = 0 then G p q else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun pf : Points V × Points (Module.Dual (ZMod 2) V)
      => (pf.2 : Module.Dual (ZMod 2) V) pf.1 = 0) (by simp) (fun pf => G pf.1 pf.2),
    Finset.sum_filter, Fintype.sum_prod_type]

theorem flagIota_equivariant (g : V ≃ₗ[ZMod 2] V)
    (t : ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V)) :
    flagIota V (t.1, permActU g t.2.1, permActU g.symm.dualMap t.2.2) =
      flagPermAct g (flagIota V t) :=
  rfl

theorem flagPsi_equivariant (g : V ≃ₗ[ZMod 2] V) (z : Flags V → ZMod 2) :
    ((flagPsi V (flagPermAct g z) : traceZeroEnd V) : Module.End (ZMod 2) V) =
      (g : V →ₗ[ZMod 2] V) ∘ₗ (flagPsi V z : Module.End (ZMod 2) V) ∘ₗ
        (g.symm : V →ₗ[ZMod 2] V) := by
  ext v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, flagPsi_apply, flagPsi_apply, map_sum,
    ← Equiv.sum_comp (flagPerm g)]
  refine Finset.sum_congr rfl fun pf _ => ?_
  change z (flagAct g.symm (flagAct g pf)) • ((pf.1.2 : Module.Dual (ZMod 2) V) (g.symm v) •
    g (pf.1.1 : V)) = _
  rw [flagAct_symm_flagAct, map_smul, map_smul]
  rfl

omit [DecidableEq V] in
theorem sum_dualPoints_ker (hV : finrank (ZMod 2) V = 3) (p : Points V) :
    ∑ q : Points (Module.Dual (ZMod 2) V),
      (if (q : Module.Dual (ZMod 2) V) p = 0 then (q : Module.Dual (ZMod 2) V) else 0) = 0 := by
  obtain ⟨f, hf⟩ := exists_dual_eq_one p.2
  rw [sum_points (V := Module.Dual (ZMod 2) V) (fun f => if f p = 0 then f else 0) (by simp),
    ← Finset.sum_filter]
  exact sum_filter_eq_zero (card_dual hV) (Module.Dual.eval (ZMod 2) V p) hf

omit [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem sum_points_ker (hV : finrank (ZMod 2) V = 3) (q : Points (Module.Dual (ZMod 2) V)) :
    ∑ p : Points V, (if (q : Module.Dual (ZMod 2) V) p = 0 then (p : V) else 0) = 0 := by
  obtain ⟨w, hw⟩ := exists_eq_one_of_ne_zero q.2
  rw [sum_points (fun v => if (q : Module.Dual (ZMod 2) V) v = 0 then v else 0) (by simp),
    ← Finset.sum_filter]
  exact sum_filter_eq_zero (card_eq_eight hV) _ hw

theorem flagPsi_flagIota (hV : finrank (ZMod 2) V = 3)
    (t : ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V)) :
    flagPsi V (flagIota V t) = 0 := by
  obtain ⟨c, ⟨x, hx⟩, ⟨y, hy⟩⟩ := t
  apply Subtype.ext
  ext v
  rw [flagPsi_apply]
  let T : Points V → Points (Module.Dual (ZMod 2) V) → V := fun p q =>
    if (q : Module.Dual (ZMod 2) V) p = 0 then
      (q : Module.Dual (ZMod 2) V) v • (p : V) else 0
  have hrow : ∀ p, ∑ q, T p q = 0 := fun p => by
    calc ∑ q, T p q = ((∑ q : Points (Module.Dual (ZMod 2) V),
          if (q : Module.Dual (ZMod 2) V) p = 0 then (q : Module.Dual (ZMod 2) V) else 0) v) •
            (p : V) := by
          rw [LinearMap.sum_apply, Finset.sum_smul]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [T]
          split_ifs <;> simp
      _ = 0 := by rw [sum_dualPoints_ker hV p, LinearMap.zero_apply, zero_smul]
  have hcol : ∀ q, ∑ p, T p q = 0 := fun q => by
    calc ∑ p, T p q = (q : Module.Dual (ZMod 2) V) v •
          ∑ p : Points V, (if (q : Module.Dual (ZMod 2) V) p = 0 then (p : V) else 0) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [T]
          split_ifs <;> simp
      _ = 0 := by rw [sum_points_ker hV q, smul_zero]
  refine (sum_flags (fun p q => (c + x p + y q) •
      ((q : Module.Dual (ZMod 2) V) v • (p : V)))).trans ?_
  have hsplit : ∀ (p : Points V) (q : Points (Module.Dual (ZMod 2) V)),
      (if (q : Module.Dual (ZMod 2) V) p = 0 then
        (c + x p + y q) • ((q : Module.Dual (ZMod 2) V) v • (p : V)) else 0) =
      c • T p q + x p • T p q + y q • T p q := fun p q => by
    simp only [T]
    split_ifs <;> simp [add_smul]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun p q => y q • T p q)]
  simp only [← Finset.smul_sum, hrow, hcol, smul_zero, Finset.sum_const_zero, add_zero]
  rfl

theorem range_flagIota_le (hV : finrank (ZMod 2) V = 3) :
    LinearMap.range (flagIota V) ≤ LinearMap.ker (flagPsi V) := by
  rintro _ ⟨t, rfl⟩
  exact flagPsi_flagIota hV t

theorem flagIota_injective (hV : finrank (ZMod 2) V = 3) : Function.Injective (flagIota V) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨c, ⟨x, hx⟩, ⟨y, hy⟩⟩ h
  have hflag : ∀ (p : Points V) (q : Points (Module.Dual (ZMod 2) V)),
      (q : Module.Dual (ZMod 2) V) p = 0 → c + x p + y q = 0 :=
    fun p q hpq => congrFun h ⟨(p, q), hpq⟩
  have h7 : ∀ a : ZMod 2, (7 : ℕ) • a = a := by decide
  have hyc : ∀ q q' : Points (Module.Dual (ZMod 2) V), y q = y q' := fun q q' => by
    obtain ⟨w, hw0, h1, h2⟩ := exists_ne_zero_ker (card_eq_eight hV)
      (q : Module.Dual (ZMod 2) V) q'
    exact add_left_cancel ((hflag ⟨w, hw0⟩ q h1).trans (hflag ⟨w, hw0⟩ q' h2).symm)
  have hxc : ∀ p p' : Points V, x p = x p' := fun p p' => by
    obtain ⟨f, hf0, h1, h2⟩ := exists_ne_zero_ker (card_dual hV)
      (Module.Dual.eval (ZMod 2) V p) (Module.Dual.eval (ZMod 2) V p')
    have e := (hflag p ⟨f, hf0⟩ h1).trans (hflag p' ⟨f, hf0⟩ h2).symm
    exact add_left_cancel (add_right_cancel e)
  have hy0 : ∀ q, y q = 0 := fun q => by
    have hs := mem_augmentation.mp hy
    rwa [Finset.sum_congr rfl fun q' _ => hyc q' q, Finset.sum_const, Finset.card_univ,
      card_points (finrank_dual hV), h7] at hs
  have hx0 : ∀ p, x p = 0 := fun p => by
    have hs := mem_augmentation.mp hx
    rwa [Finset.sum_congr rfl fun p' _ => hxc p' p, Finset.sum_const, Finset.card_univ,
      card_points hV, h7] at hs
  have hpos : 0 < Fintype.card (Points V) := by rw [card_points hV]; norm_num
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨f, hf0, h1, -⟩ := exists_ne_zero_ker (card_dual hV)
    (Module.Dual.eval (ZMod 2) V p) (Module.Dual.eval (ZMod 2) V p)
  have hc := hflag p ⟨f, hf0⟩ h1
  rw [hx0, hy0, add_zero, add_zero] at hc
  exact Prod.ext hc (Prod.ext (Subtype.ext (funext hx0)) (Subtype.ext (funext hy0)))

@[expose] def flagData : Fin 8 → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  ![(![1, 0, 0], ![0, 1, 0]), (![1, 0, 0], ![0, 0, 1]), (![0, 1, 0], ![1, 0, 0]),
    (![0, 1, 0], ![0, 0, 1]), (![0, 0, 1], ![1, 0, 0]), (![0, 0, 1], ![0, 1, 0]),
    (![1, 0, 1], ![1, 0, 1]), (![0, 1, 1], ![0, 1, 1])]

theorem flagData_spec : ∀ k : Fin 8, (flagData k).1 ≠ 0 ∧ (flagData k).2 ≠ 0 ∧
    dotProduct (flagData k).1 (flagData k).2 = 0 := by
  decide

@[expose] def flagCoeff (M : Mat3) : Fin 8 → ZMod 2 :=
  ![M 0 1, M 0 2 + M 0 0, M 1 0, M 1 2 + M 1 1, M 2 0 + M 0 0, M 2 1 + M 1 1, M 0 0, M 1 1]

theorem sum_flagCoeff_traceZeroMat : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2,
    ∑ k, flagCoeff (traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7) k •
      Matrix.vecMulVec (flagData k).1 (flagData k).2 = traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 := by
  decide +kernel

theorem sum_flagCoeff {M : Mat3} (hM : M ∈ traceZero) :
    ∑ k, flagCoeff M k • Matrix.vecMulVec (flagData k).1 (flagData k).2 = M := by
  rw [eq_traceZeroMat hM]
  exact sum_flagCoeff_traceZeroMat _ _ _ _ _ _ _ _

section Basis

variable (b : Module.Basis (Fin 3) (ZMod 2) V)

omit [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem repr_equivFun_symm (u : Fin 3 → ZMod 2) : ⇑(b.repr (b.equivFun.symm u)) = u := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem dualBasis_equivFun_symm_basis (w : Fin 3 → ZMod 2) (j : Fin 3) :
    b.dualBasis.equivFun.symm w (b j) = w j := by
  rw [Module.Basis.equivFun_symm_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

omit [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem dualBasis_equivFun_symm_apply (w : Fin 3 → ZMod 2) (v : V) :
    b.dualBasis.equivFun.symm w v = dotProduct (b.repr v) w := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, dualBasis_equivFun_symm_basis, smul_eq_mul]

@[expose] noncomputable def basisFlag (k : Fin 8) : Flags V :=
  ⟨(⟨b.equivFun.symm (flagData k).1, fun h =>
      (flagData_spec k).1 (b.equivFun.symm.map_eq_zero_iff.mp h)⟩,
    ⟨b.dualBasis.equivFun.symm (flagData k).2, fun h =>
      (flagData_spec k).2.1 (b.dualBasis.equivFun.symm.map_eq_zero_iff.mp h)⟩), by
    change b.dualBasis.equivFun.symm (flagData k).2 (b.equivFun.symm (flagData k).1) = 0
    rw [dualBasis_equivFun_symm_apply, repr_equivFun_symm]
    exact (flagData_spec k).2.2⟩

omit [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem toMatrix_basisFlag (k : Fin 8) :
    LinearMap.toMatrix b b ((flagEnd (basisFlag b k) : traceZeroEnd V) : Module.End (ZMod 2) V) =
      Matrix.vecMulVec (flagData k).1 (flagData k).2 := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.vecMulVec_apply]
  change b.repr (b.dualBasis.equivFun.symm (flagData k).2 (b j) •
    b.equivFun.symm (flagData k).1) i = _
  rw [map_smul, Finsupp.smul_apply, repr_equivFun_symm, dualBasis_equivFun_symm_basis,
    smul_eq_mul, mul_comm]

end Basis

theorem flagPsi_surjective (hV : finrank (ZMod 2) V = 3) : Function.Surjective (flagPsi V) := by
  intro X
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
  set M := LinearMap.toMatrix b b (X : Module.End (ZMod 2) V) with hM
  have hMtr : M ∈ traceZero := by
    rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply, hM,
      ← LinearMap.trace_eq_matrix_trace]
    exact LinearMap.mem_ker.mp X.2
  refine ⟨∑ k, flagCoeff M k • Pi.single (basisFlag b k) 1, ?_⟩
  apply Subtype.ext
  apply (LinearMap.toMatrix b b).injective
  rw [← hM]
  conv_rhs => rw [← sum_flagCoeff hMtr]
  rw [map_sum, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Submodule.coe_smul, map_smul, flagPsi, Fintype.linearCombination_apply_single,
    one_smul, toMatrix_basisFlag]

theorem card_flags (hV : finrank (ZMod 2) V = 3) : Fintype.card (Flags V) = 21 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have h3 : ∀ p : Points V, ∑ q : Points (Module.Dual (ZMod 2) V),
      (if (q : Module.Dual (ZMod 2) V) p = 0 then 1 else 0) = 3 := fun p => by
    obtain ⟨f, hf⟩ := exists_dual_eq_one p.2
    rw [← Finset.card_filter]
    exact card_points_filter_eq_zero (card_dual hV) (Module.Dual.eval (ZMod 2) V p) hf
  rw [Finset.sum_congr rfl fun p _ => h3 p, Finset.sum_const, Finset.card_univ, card_points hV]
  rfl

omit [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem natCard_traceZeroEnd (hV : finrank (ZMod 2) V = 3) :
    Nat.card (traceZeroEnd V) = 256 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
  have hsurj : Function.Surjective (LinearMap.trace (ZMod 2) V) := by
    intro c
    rcases zmod2_eq_zero_or_one' c with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · refine ⟨1, ?_⟩
      rw [LinearMap.trace_one, hV]
      decide
  have hEnd : Nat.card (Module.End (ZMod 2) V) = 512 := by
    rw [Nat.card_congr (LinearMap.toMatrix b b).toEquiv]
    change Nat.card (Fin 3 → Fin 3 → ZMod 2) = 512
    rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hker := AddSubgroup.card_ker_mul_card_range (LinearMap.trace (ZMod 2) V).toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_zmod, hEnd] at hker
  have heq : Nat.card (traceZeroEnd V) =
      Nat.card (LinearMap.trace (ZMod 2) V).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]; exact LinearMap.mem_ker)
  rw [heq]
  omega

theorem natCard_ker_flagPsi (hV : finrank (ZMod 2) V = 3) :
    Nat.card (LinearMap.ker (flagPsi V)) = 8192 := by
  have hker := AddSubgroup.card_ker_mul_card_range (flagPsi V).toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr (flagPsi_surjective hV), AddSubgroup.card_top,
    natCard_traceZeroEnd hV, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Flags V),
    card_flags hV] at hker
  have heq : Nat.card (LinearMap.ker (flagPsi V)) = Nat.card (flagPsi V).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]; exact LinearMap.mem_ker)
  rw [heq]
  omega

theorem natCard_range_flagIota (hV : finrank (ZMod 2) V = 3) :
    Nat.card (LinearMap.range (flagIota V)) = 8192 := by
  have h1 : Nat.card (LinearMap.range (flagIota V)) =
      Nat.card (ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V)) := by
    rw [← Nat.card_range_of_injective (flagIota_injective hV)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [LinearMap.mem_range]; rfl)
  rw [h1, Nat.card_prod, Nat.card_prod, Nat.card_zmod, natCard_augmentation hV,
    natCard_augmentation (finrank_dual hV)]

theorem ker_flagPsi_eq (hV : finrank (ZMod 2) V = 3) :
    LinearMap.ker (flagPsi V) = LinearMap.range (flagIota V) := by
  refine (SetLike.coe_injective (Set.eq_of_subset_of_ncard_le (range_flagIota_le hV) ?_)).symm
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card (LinearMap.ker (flagPsi V)) ≤ Nat.card (LinearMap.range (flagIota V))
  rw [natCard_ker_flagPsi hV, natCard_range_flagIota hV]

theorem finrank_range_flagIota (hV : finrank (ZMod 2) V = 3) :
    finrank (ZMod 2) (LinearMap.range (flagIota V)) = 13 := by
  have h := FiniteField.pow_finrank_eq_natCard 2 (LinearMap.range (flagIota V))
  rw [natCard_range_flagIota hV] at h
  exact Nat.pow_right_injective le_rfl (h.trans (by norm_num))

omit [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem finrank_traceZeroEnd (hV : finrank (ZMod 2) V = 3) :
    finrank (ZMod 2) (traceZeroEnd V) = 8 := by
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_equiv _ (LinearMap.toMatrix (Module.finBasisOfFinrankEq (ZMod 2) V hV)
      (Module.finBasisOfFinrankEq (ZMod 2) V hV)).toEquiv.symm
  have h := FiniteField.pow_finrank_eq_natCard 2 (traceZeroEnd V)
  rw [natCard_traceZeroEnd hV] at h
  exact Nat.pow_right_injective le_rfl (h.trans (by norm_num))

theorem flag_permutation_kernel (hV : finrank (ZMod 2) V = 3) :
    (∀ (pf : Flags V) (v : V),
      ((flagPsi V (Pi.single pf 1) : traceZeroEnd V) : Module.End (ZMod 2) V) v =
        (pf.1.2 : Module.Dual (ZMod 2) V) v • (pf.1.1 : V)) ∧
    (∀ (t : ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V)) (pf : Flags V),
      flagIota V t pf = t.1 + (t.2.1 : Points V → ZMod 2) pf.1.1 +
        (t.2.2 : Points (Module.Dual (ZMod 2) V) → ZMod 2) pf.1.2) ∧
    (∀ (g : V ≃ₗ[ZMod 2] V) (t : ZMod 2 × augmentation V × augmentation (Module.Dual (ZMod 2) V)),
      flagIota V (t.1, permActU g t.2.1, permActU g.symm.dualMap t.2.2) =
        flagPermAct g (flagIota V t)) ∧
    (∀ (g : V ≃ₗ[ZMod 2] V) (z : Flags V → ZMod 2),
      ((flagPsi V (flagPermAct g z) : traceZeroEnd V) : Module.End (ZMod 2) V) =
        (g : V →ₗ[ZMod 2] V) ∘ₗ (flagPsi V z : Module.End (ZMod 2) V) ∘ₗ
          (g.symm : V →ₗ[ZMod 2] V)) ∧
    Function.Injective (flagIota V) ∧ Function.Surjective (flagPsi V) ∧
    LinearMap.ker (flagPsi V) = LinearMap.range (flagIota V) ∧
    finrank (ZMod 2) (LinearMap.range (flagIota V)) = 13 ∧
    finrank (ZMod 2) (traceZeroEnd V) = 8 :=
  ⟨flagPsi_single, fun _ _ => rfl, flagIota_equivariant, flagPsi_equivariant,
    flagIota_injective hV, flagPsi_surjective hV, ker_flagPsi_eq hV, finrank_range_flagIota hV,
    finrank_traceZeroEnd hV⟩

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
