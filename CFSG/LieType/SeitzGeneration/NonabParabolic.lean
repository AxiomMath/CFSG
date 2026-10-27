module

public import CFSG.LieType.SeitzGeneration.NonabAveraging
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LieType.SeitzGeneration

open Module Matrix Finset
open scoped commutatorElement

section Radical

variable {F : Type*} [Field F] {n : ℕ}

def thetaSpace (W : Submodule F (Fin n → F)) : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {φ | (∀ v, φ.mulVec v ∈ W) ∧ ∀ w ∈ W, φ.mulVec w = 0}
  add_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun v => by rw [Matrix.add_mulVec]; exact W.add_mem (h1 v) (h3 v),
      fun w hw => by rw [Matrix.add_mulVec, h2 w hw, h4 w hw, add_zero]⟩
  zero_mem' := ⟨fun v => by simp, fun w _ => by simp⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2⟩
    exact ⟨fun v => by rw [Matrix.smul_mulVec]; exact W.smul_mem c (h1 v),
      fun w hw => by rw [Matrix.smul_mulVec, h2 w hw, smul_zero]⟩

theorem mem_thetaSpace {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F} :
    φ ∈ thetaSpace W ↔ (∀ v, φ.mulVec v ∈ W) ∧ ∀ w ∈ W, φ.mulVec w = 0 := Iff.rfl

theorem thetaSpace_mul {W : Submodule F (Fin n → F)} {φ ψ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) (hψ : ψ ∈ thetaSpace W) : φ * ψ = 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, hφ.2 _ (hψ.1 v), Matrix.zero_mulVec]

theorem det_one_add_eq_one [Finite F] {φ : Matrix (Fin n) (Fin n) F} (h : φ * φ = 0) :
    (1 + φ).det = 1 := by
  have hrp : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  have hpow : ∀ m : ℕ, (1 + φ) ^ m = 1 + (m : F) • φ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_succ, add_smul, one_smul, add_mul, mul_add, Matrix.mul_one,
        Matrix.one_mul, Matrix.smul_mul, h, smul_zero, add_zero]
      abel
  have h1 : (1 + φ) ^ ringChar F = 1 := by
    rw [hpow, ringChar.Nat.cast_ringChar, zero_smul, add_zero]
  have h2 : ((1 + φ).det) ^ ringChar F = 1 := by
    rw [← Matrix.det_pow, h1, Matrix.det_one]
  have h3 : ((1 + φ).det - 1) ^ ringChar F = 0 := by
    rw [sub_pow_char, h2, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff hrp.out.ne_zero |>.mp h3)


@[expose] def unipSL [Finite F] {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) : SpecialLinearGroup (Fin n) F :=
  ⟨1 + φ, det_one_add_eq_one (thetaSpace_mul hφ hφ)⟩

theorem coe_unipSL [Finite F] {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) : (unipSL hφ : Matrix (Fin n) (Fin n) F) = 1 + φ := rfl

theorem commute_unipSL [Finite F] {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) {x : SpecialLinearGroup (Fin n) F}
    (hx : (x : Matrix (Fin n) (Fin n) F) * φ = φ * x) : Commute x (unipSL hφ) := by
  apply Subtype.ext
  show (x : Matrix (Fin n) (Fin n) F) * (1 + φ) = (1 + φ) * x
  rw [Matrix.mul_add, Matrix.add_mul, hx, Matrix.mul_one, Matrix.one_mul]

@[expose] def conjAction :
    SpecialLinearGroup (Fin n) F →* Module.End F (Matrix (Fin n) (Fin n) F) where
  toFun x := (LinearMap.mulLeft F (x : Matrix (Fin n) (Fin n) F)).comp
    (LinearMap.mulRight F ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F))
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' x y := LinearMap.ext fun φ => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc]

theorem conjAction_apply (x : SpecialLinearGroup (Fin n) F) (φ : Matrix (Fin n) (Fin n) F) :
    conjAction x φ = (x : Matrix (Fin n) (Fin n) F) * φ *
      ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  simp [conjAction, Matrix.mul_assoc]

theorem commute_of_conjAction_eq {x : SpecialLinearGroup (Fin n) F}
    {φ : Matrix (Fin n) (Fin n) F} (h : conjAction x φ = φ) :
    (x : Matrix (Fin n) (Fin n) F) * φ = φ * x := by
  have h1 := congrArg (fun M => M * (x : Matrix (Fin n) (Fin n) F)) h
  simp only [conjAction_apply, Matrix.mul_assoc] at h1
  have h2 : ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (x : Matrix (Fin n) (Fin n) F) = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel x)
  rw [h2, Matrix.mul_one] at h1
  exact h1

theorem conjAction_mem_thetaSpace {W : Submodule F (Fin n → F)}
    {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    {x : SpecialLinearGroup (Fin n) F} (hx : x ∈ H) {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) : conjAction x φ ∈ thetaSpace W := by
  rw [conjAction_apply]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hW x hx _ (hφ.1 _)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hφ.2 _ (hW _ (H.inv_mem hx) w hw),
      Matrix.mulVec_zero]

end Radical



open Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_invariant_compl [Finite F] {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hH : (Nat.card H : F) ≠ 0) {W : Submodule F (Fin n → F)}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    ∃ W' : Submodule F (Fin n → F), IsCompl W W' ∧
      ∀ x ∈ H, ∀ w ∈ W', (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W' := by
  have : NeZero (Nat.card H : F) := ⟨hH⟩
  let ρ : Representation F H (Fin n → F) :=
    { toFun := fun h => Matrix.toLin' (h.1 : Matrix (Fin n) (Fin n) F)
      map_one' := LinearMap.ext fun v => by simp
      map_mul' := fun a b => LinearMap.ext fun v => by
        simp [Matrix.toLin'_mul] }
  let σ : Subrepresentation ρ := ⟨W, fun g v hv => hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => σ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hσ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hσ'.2)
    exact this


section Main

variable {F : Type*} [Field F] {n : ℕ}

theorem conjAction_eq_one_of_mem_center {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) : conjAction z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  refine LinearMap.ext fun φ => ?_
  have hc : (z : Matrix (Fin n) (Fin n) F) * φ = φ * z := by
    rw [← hr]
    exact (Matrix.scalar_commute r (fun r' => Commute.all r r') φ).eq
  have h2 : (z : Matrix (Fin n) (Fin n) F) *
      ((z⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
    congrArg Subtype.val (mul_inv_cancel z)
  rw [conjAction_apply, hc, Matrix.mul_assoc, h2, Matrix.mul_one]
  rfl

def centralizerGens (H : Subgroup (SpecialLinearGroup (Fin n) F)) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {g | ∃ x ∈ H, x ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
    ⁅g, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)}

theorem unip_mem_closure_centralizerGens [Finite F] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    {H : Subgroup (SpecialLinearGroup (Fin n) F)} {a b : SpecialLinearGroup (Fin n) F}
    (ha : a ∈ H) (hb : b ∈ H) (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbp : b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hab : ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hline : ∀ j : ℕ, a * b ^ j ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbc : b ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {W : Submodule F (Fin n → F)}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    (g : SpecialLinearGroup (Fin n) F) (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    g ∈ Subgroup.closure (centralizerGens H) := by
  classical
  set K := Subgroup.closure (centralizerGens H) with hK
  set φ : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1 with hφ
  have hA : conjAction a ^ p = 1 := by
    rw [← map_pow]; exact conjAction_eq_one_of_mem_center hap
  have hB : conjAction b ^ p = 1 := by
    rw [← map_pow]; exact conjAction_eq_one_of_mem_center hbp
  have hAB : Commute (conjAction a) (conjAction b) := by
    have h1 : a * b = ⁅a, b⁆ * (b * a) := by
      simp only [commutatorElement_def]; group
    show conjAction a * conjAction b = conjAction b * conjAction a
    rw [← map_mul, ← map_mul, h1, map_mul, conjAction_eq_one_of_mem_center hab, one_mul]
  obtain ⟨u, v, hu, hv, hsum, hmem⟩ := exists_decomp_lines hpF hAB hA hB φ
  have hAS : ∀ x ∈ thetaSpace W, conjAction a x ∈ thetaSpace W := fun x hx =>
    conjAction_mem_thetaSpace hW ha hx
  have hBS : ∀ x ∈ thetaSpace W, conjAction b x ∈ thetaSpace W := fun x hx =>
    conjAction_mem_thetaSpace hW hb hx
  obtain ⟨huS, hvS⟩ := hmem (thetaSpace W) hAS hBS hg
  have hu_mem : ∀ j : ZMod p, ∃ h : u j ∈ thetaSpace W, unipSL h ∈ K := fun j => by
    refine ⟨huS j, Subgroup.subset_closure ⟨a * b ^ j.val,
      H.mul_mem ha (H.pow_mem hb _), hline _, ?_⟩⟩
    have hfix : conjAction (a * b ^ j.val) (u j) = u j := by
      simpa only [map_mul, map_pow] using hu j
    have hcomm := commute_unipSL (huS j) (commute_of_conjAction_eq hfix)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm.eq]
    exact one_mem _
  have hv_mem : ∃ h : v ∈ thetaSpace W, unipSL h ∈ K := by
    refine ⟨hvS, Subgroup.subset_closure ⟨b, hb, hbc, ?_⟩⟩
    have hcomm := commute_unipSL hvS (commute_of_conjAction_eq hv)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm.eq]
    exact one_mem _
  let T : AddSubmonoid (Matrix (Fin n) (Fin n) F) :=
    { carrier := {ψ | ∃ h : ψ ∈ thetaSpace W, unipSL h ∈ K}
      zero_mem' := ⟨(thetaSpace W).zero_mem, by
        have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
        rw [this]; exact K.one_mem⟩
      add_mem' := by
        rintro ψ ψ' ⟨h, hKψ⟩ ⟨h', hKψ'⟩
        refine ⟨(thetaSpace W).add_mem h h', ?_⟩
        have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
          show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
          simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h',
            add_zero]
          abel)
        rw [this]; exact K.mul_mem hKψ hKψ' }
  have hφT : φ ∈ T := by
    rw [hsum]
    exact T.add_mem (T.sum_mem fun j _ => hu_mem j) hv_mem
  obtain ⟨h, hKφ⟩ := hφT
  have : unipSL h = g := Subtype.ext (by
    show 1 + φ = (g : Matrix (Fin n) (Fin n) F)
    rw [hφ]; abel)
  rwa [this] at hKφ

end Main


section Adapted



variable {F : Type*} [Field F] {n : ℕ}

theorem exists_adapted_basis {W W' : Submodule F (Fin n → F)} (hc : IsCompl W W') :
    ∃ b : Basis (Fin n) F (Fin n → F),
      (∀ i : Fin n, i.val < finrank F W → b i ∈ W) ∧
      (∀ i : Fin n, finrank F W ≤ i.val → b i ∈ W') ∧
      (∀ w ∈ W, ∀ j : Fin n, finrank F W ≤ j.val → b.repr w j = 0) ∧
      (∀ w ∈ W', ∀ j : Fin n, j.val < finrank F W → b.repr w j = 0) := by
  classical
  have hdim : finrank F W + finrank F W' = n := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  let b₀ : Basis (Fin (finrank F W) ⊕ Fin (finrank F W')) F (Fin n → F) :=
    ((finBasis F W).prod (finBasis F W')).map (Submodule.prodEquivOfIsCompl W W' hc)
  let e : (Fin (finrank F W) ⊕ Fin (finrank F W')) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr hdim)
  have he1 : ∀ a : Fin (finrank F W), (e (Sum.inl a)).val = a.val := fun a => by
    simp [e]
  have he2 : ∀ a : Fin (finrank F W'), (e (Sum.inr a)).val = finrank F W + a.val := fun a => by
    simp [e]
  have hk : ∀ i : Fin n, finrank F W ≤ i.val → ∃ a : Fin (finrank F W'), e (Sum.inr a) = i :=
    fun i hi => ⟨⟨i.val - finrank F W, by omega⟩, Fin.ext (by rw [he2]; simp; omega)⟩
  refine ⟨b₀.reindex e, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : e (Sum.inl ⟨i.val, hi⟩) = i := Fin.ext (he1 _)
    rw [Basis.reindex_apply, ← this, Equiv.symm_apply_apply]
    simp [b₀, Basis.map_apply]
  · intro i hi
    obtain ⟨a, ha⟩ := hk i hi
    rw [Basis.reindex_apply, ← ha, Equiv.symm_apply_apply]
    simp [b₀, Basis.map_apply]
  · intro w hw j hj
    obtain ⟨a, ha⟩ := hk j hj
    rw [Basis.repr_reindex_apply, ← ha, Equiv.symm_apply_apply]
    simp only [b₀, Basis.map_repr, LinearEquiv.trans_apply]
    have : (Submodule.prodEquivOfIsCompl W W' hc).symm w = (⟨w, hw⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left W W' hc ⟨w, hw⟩
    rw [this, Basis.prod_repr_inr]
    simp
  · intro w hw j hj
    have : e (Sum.inl ⟨j.val, hj⟩) = j := Fin.ext (he1 _)
    rw [Basis.repr_reindex_apply, ← this, Equiv.symm_apply_apply]
    simp only [b₀, Basis.map_repr, LinearEquiv.trans_apply]
    have : (Submodule.prodEquivOfIsCompl W W' hc).symm w = (0, ⟨w, hw⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right W W' hc ⟨w, hw⟩
    rw [this, Basis.prod_repr_inl]
    simp






@[expose] noncomputable def basisUnit (b : Basis (Fin n) F (Fin n → F)) : GL (Fin n) F :=
  ⟨(Pi.basisFun F (Fin n)).toMatrix b, b.toMatrix (Pi.basisFun F (Fin n)),
    (Pi.basisFun F (Fin n)).toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip (Pi.basisFun F (Fin n))⟩

theorem basisUnit_inv_mulVec (b : Basis (Fin n) F (Fin n → F)) (v : Fin n → F) :
    (((basisUnit b)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v = b.repr v := by
  have h := Basis.toMatrix_mulVec_repr (Pi.basisFun F (Fin n)) b v
  have e : ⇑((Pi.basisFun F (Fin n)).repr v) = v := by ext i; simp
  rw [e] at h
  exact h

theorem basisUnit_mulVec_single (b : Basis (Fin n) F (Fin n → F)) (i : Fin n) (x : F) :
    ((basisUnit b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single i x) =
      x • b i := by
  ext r
  simp [basisUnit, Matrix.mulVec_single, Basis.toMatrix_apply, mul_comm]

@[expose] def conjUnit (g : GL (Fin n) F) :
    SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F where
  toFun h := ⟨(g : Matrix (Fin n) (Fin n) F) * h *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), by
    rw [Matrix.det_mul, Matrix.det_mul, h.2, mul_one, ← Matrix.det_mul, Units.mul_inv,
      Matrix.det_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    have hgi : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) =
        1 := Units.inv_mul g
    show (g : Matrix (Fin n) (Fin n) F) * ((a : Matrix (Fin n) (Fin n) F) * b) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : Matrix (Fin n) (Fin n) F) * a * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        ((g : Matrix (Fin n) (Fin n) F) * b * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    calc _ = (g : Matrix (Fin n) (Fin n) F) * a * (1 : Matrix (Fin n) (Fin n) F) * b *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hgi]; simp only [Matrix.mul_assoc])

theorem conjUnit_coe (g : GL (Fin n) F) (h : SpecialLinearGroup (Fin n) F) :
    ((conjUnit g h : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * h * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem conjUnit_transvection_mulVec (b : Basis (Fin n) F (Fin n → F)) {i j : Fin n} (hij : i ≠ j)
    (c : F) (v : Fin n → F) :
    ((conjUnit (basisUnit b) (SpecialLinearGroup.transvection hij c) :
        SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v =
      v + (c * b.repr v j) • b i := by
  have h1 : ((basisUnit b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec
      ((((basisUnit b)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [conjUnit_coe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq, Matrix.mulVec_add, Matrix.mulVec_smul, basisUnit_mulVec_single, h1,
    basisUnit_inv_mulVec, one_smul]


theorem eq_top_of_unip_isCompl {K : Subgroup (SpecialLinearGroup (Fin n) F)}
    {W W' : Submodule F (Fin n → F)} (hc : IsCompl W W') (hW : W ≠ ⊥) (hW' : W' ≠ ⊥)
    (hKW : ∀ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W → g ∈ K)
    (hKW' : ∀ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W' → g ∈ K) : K = ⊤ := by
  obtain ⟨b, hb1, hb2, hb3, hb4⟩ := exists_adapted_basis hc
  have hdim : finrank F W + finrank F W' = n := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  have hk0 : 1 ≤ finrank F W := Submodule.one_le_finrank_iff.2 hW
  have hk1 : 1 ≤ finrank F W' := Submodule.one_le_finrank_iff.2 hW'
  set k := finrank F W with hk
  let P : GL (Fin n) F := basisUnit b
  have key : ∀ (S : Submodule F (Fin n → F)) (i j : Fin n) (hij : i ≠ j), b i ∈ S →
      (∀ w ∈ S, b.repr w j = 0) →
      (∀ g : SpecialLinearGroup (Fin n) F, (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace S →
        g ∈ K) → ∀ c : F, conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K := by
    intro S i j hij hbi hrep hKS c
    apply hKS
    have hmv : ∀ v, (((conjUnit P (SpecialLinearGroup.transvection hij c) :
        SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1).mulVec v =
        (c * b.repr v j) • b i := fun v => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, conjUnit_transvection_mulVec, add_sub_cancel_left]
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [hmv]; exact S.smul_mem _ hbi
    · rw [hmv, hrep w hw, mul_zero, zero_smul]
  have hA : ∀ (i j : Fin n) (hij : i ≠ j), i.val < k → k ≤ j.val → ∀ c : F,
      conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K := fun i j hij hi hj c =>
    key W i j hij (hb1 i hi) (fun w hw => hb3 w hw j hj) hKW c
  have hB : ∀ (i j : Fin n) (hij : i ≠ j), j.val < k → k ≤ i.val → ∀ c : F,
      conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K := fun i j hij hj hi c =>
    key W' i j hij (hb2 i hi) (fun w hw => hb4 w hw j hj) hKW' c
  have hcomm : ∀ (i l j : Fin n) (hil : i ≠ l) (hlj : l ≠ j) (hij : i ≠ j) (c : F),
      conjUnit P (SpecialLinearGroup.transvection hil c) ∈ K →
      conjUnit P (SpecialLinearGroup.transvection hlj 1) ∈ K →
      conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K := by
    intro i l j hil hlj hij c h1 h2
    have := SpecialLinearGroup.commutatorElement_transvection hil hlj hij c (1 : F)
    rw [mul_one] at this
    rw [← this, map_commutatorElement, commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem h1 h2) (K.inv_mem h1)) (K.inv_mem h2)
  have hall : ∀ (i j : Fin n) (hij : i ≠ j) (c : F),
      conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K := by
    intro i j hij c
    by_cases hi : i.val < k <;> by_cases hj : j.val < k
    ·
      have hkn : k < n := by omega
      let l : Fin n := ⟨k, hkn⟩
      have hil : i ≠ l := fun h => by have := congrArg Fin.val h; simp [l] at this; omega
      have hlj : l ≠ j := fun h => by have := congrArg Fin.val h; simp [l] at this; omega
      exact hcomm i l j hil hlj hij c (hA i l hil hi (by simp [l]) c)
        (hB l j hlj hj (by simp [l]) 1)
    · exact hA i j hij hi (by omega) c
    · exact hB i j hij hj (by omega) c
    ·
      have hn0 : 0 < n := by omega
      let l : Fin n := ⟨0, hn0⟩
      have hil : i ≠ l := fun h => by have := congrArg Fin.val h; simp [l] at this; omega
      have hlj : l ≠ j := fun h => by have := congrArg Fin.val h; simp [l] at this; omega
      exact hcomm i l j hil hlj hij c (hB i l hil (by simp [l]; omega) (by omega) c)
        (hA l j hlj (by simp [l]; omega) (by omega) 1)
  rw [eq_top_iff]
  intro g _
  have htop : (Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin n) (F := F)))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hK' : K.comap (conjUnit P) = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact hall t.i t.j t.hij t.c
  have hg : (conjUnit P) (conjUnit P⁻¹ g) = g := by
    apply Subtype.ext
    simp only [conjUnit_coe, Matrix.mul_assoc, inv_inv, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [← hg]
  exact (Subgroup.mem_comap.1 (hK' ▸ Subgroup.mem_top (conjUnit P⁻¹ g)))

theorem closure_centralizerGens_eq_top_of_invariant [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : (p : F) ≠ 0) {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hH : (Nat.card H : F) ≠ 0) {a b : SpecialLinearGroup (Fin n) F} (ha : a ∈ H) (hb : b ∈ H)
    (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbp : b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hab : ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hline : ∀ j : ℕ, a * b ^ j ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbc : b ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWH : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    Subgroup.closure (centralizerGens H) = ⊤ := by
  obtain ⟨W', hc, hW'H⟩ := exists_invariant_compl hH hWH
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  exact eq_top_of_unip_isCompl hc hW0 hW'0
    (unip_mem_closure_centralizerGens hpF ha hb hap hbp hab hline hbc hWH)
    (unip_mem_closure_centralizerGens hpF ha hb hap hbp hab hline hbc hW'H)


end Adapted

section Psl

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_independent_pair {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    ∃ x ∈ E, ∃ y ∈ E, y ≠ 1 ∧ x ∉ Subgroup.zpowers y := by
  have hp2 : 2 ≤ p := hp.two_le
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨y, hyE, hy1⟩ : ∃ y ∈ E, y ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [this, Subgroup.card_bot] at hcard
    nlinarith
  have hord : orderOf y = p := orderOf_eq_prime (hexp y hyE) hy1
  by_contra h
  push Not at h
  have hle : E ≤ Subgroup.zpowers y := fun x hx => by
    by_contra hx'
    obtain ⟨x', hx'E, hx'y⟩ := (⟨x, hx, hx'⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers y)
    exact absurd (h x' hx'E y hyE hy1) (by simpa using hx'y)
  have heq : E = Subgroup.zpowers y := le_antisymm hle (Subgroup.zpowers_le.2 hyE)
  rw [heq, Nat.card_zpowers, hord] at hcard
  nlinarith

theorem closure_centralizers_psl_of_reducible [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : (p : F) ≠ 0)
    (hZF : (Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) : F) ≠ 0)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : ∀ x : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) F) with hZ
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  set H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π with hH
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hexp hcard
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  have hmemZ : ∀ g : SpecialLinearGroup (Fin n) F, g ∈ Z ↔ π g = 1 := fun g => by
    rw [← hker, MonoidHom.mem_ker]
  have hcardH : Nat.card H = Nat.card E * Nat.card Z := by
    let φ : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
    have hφ : Function.Surjective φ := fun e => by
      obtain ⟨g, hg⟩ := hπ (e : ProjectiveSpecialLinearGroup (Fin n) F)
      exact ⟨⟨g, by simp [hH, hg]⟩, Subtype.ext hg⟩
    have hker_le : π.ker ≤ H := fun z hz => by
      rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact E.one_mem
    have hφker : φ.ker = π.ker.subgroupOf H := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hN : Nat.card φ.ker = Nat.card Z := by
      rw [hφker, ← hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    rw [← Subgroup.card_ker_mul_card_of_surjective hφ, hN, mul_comm]
  have hHF : (Nat.card H : F) ≠ 0 := by
    rw [hcardH, hcard, Nat.cast_mul, Nat.cast_pow]
    exact mul_ne_zero (pow_ne_zero 2 hpF) hZF
  have hgen : Subgroup.closure (centralizerGens H) = ⊤ := by
    refine closure_centralizerGens_eq_top_of_invariant hpF hHF (a := a) (b := b)
      (Subgroup.mem_comap.2 hxE) (Subgroup.mem_comap.2 hyE) ?_ ?_ ?_ ?_ ?_ hW0 hWt ?_
    · rw [hmemZ, map_pow]; exact hexp _ hxE
    · rw [hmemZ, map_pow]; exact hexp _ hyE
    · rw [hmemZ, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hxE _ hyE)
    · intro j hj
      rw [hmemZ, map_mul, map_pow] at hj
      apply hxy
      have : π a = ((π b) ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hj
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
    · intro hb
      exact hy1 ((hmemZ b).1 hb)
    · exact fun g hg => hWE g hg
  rw [eq_top_iff]
  have hle : (Subgroup.closure (centralizerGens H)).map π ≤ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin n) F | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨c, hcH, hcZ, hgc⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π c, hcH, fun h1 => hcZ ((hmemZ c).2 h1), ?_⟩
    have h1 : ⁅π g, π c⁆ = 1 := by
      rw [← map_commutatorElement]; exact (hmemZ _).1 hgc
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  rw [hgen, Subgroup.map_top_of_surjective π hπ] at hle
  exact hle


end Psl


end CFSG.LieType.SeitzGeneration
