module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.NoPSUThree
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFourRecog
public import CFSG.ClassicalInvolution.Phan.TorusAgree
public import CFSG.Mathlib.LinearAlgebra.DeterminantFixedSubspace
public import CFSG.Fischer.Classification.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits Matrix
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "σ" => unitaryInvolution K 2 1

private noncomputable def toLinEquiv (t : Su K 2 1 4) :
    (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
  LinearEquiv.ofLinear
    (Matrix.toLin' (((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (Matrix.toLin' (((t : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])

private theorem toLinEquiv_apply (t : Su K 2 1 4) (y : Fin 4 → K) :
    toLinEquiv t y = t • y := by
  change Matrix.toLin' (((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) y = t • y
  rw [Matrix.toLin'_apply, smul_def]

private theorem toLinEquiv_det (t : Su K 2 1 4) : LinearEquiv.det (toLinEquiv t) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det (Matrix.toLin' (((t : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K))) = 1
  rw [LinearMap.det_toLin']
  exact (mem_SUid.mp t.2).1

private theorem toLinEquiv_pow_three (t : Su K 2 1 4) (h : t ^ 3 = 1) :
    toLinEquiv t ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro y
  change toLinEquiv t (toLinEquiv t (toLinEquiv t y)) = y
  rw [toLinEquiv_apply, toLinEquiv_apply, toLinEquiv_apply]
  rw [← mul_smul, ← mul_smul]
  have h3 : t * t * t = 1 := by simpa [pow_three, mul_assoc] using h
  rw [h3, one_smul]

private theorem toLinEquiv_ne_one (t : Su K 2 1 4) (h : t ≠ 1) : toLinEquiv t ≠ 1 := by
  intro ht
  apply h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h' := congrFun (congrArg (fun T : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) =>
    T (Pi.single j 1)) ht) i
  rw [toLinEquiv_apply, smul_def, Matrix.mulVec_single_one] at h'
  simpa [Pi.single_apply, Matrix.one_apply] using h'

omit [Finite K] in
private theorem eq_one_of_pow_three_of_fix_hyperplane
    (T : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (S : Submodule K (Fin 4 → K))
    (hcodim : Module.finrank K (Fin 4 → K) ≤ Module.finrank K S + 1)
    (hfix : ∀ v ∈ S, T v = v) (hdet : (LinearEquiv.det T : Kˣ) = 1)
    (h3 : T ^ 3 = 1) : T = 1 := by
  have hdisp :=
    LinearEquiv.displacement_mem_of_fix_submodule_of_det_one (k := K)
      (V := (Fin 4 → K)) (T := T) (S := S) hcodim hfix hdet
  have h2 : ∀ y, T (T y) = y := by
    intro y
    have hs := hdisp y
    calc T (T y) = T (y + (T y - y)) := by rw [add_sub_cancel]
      _ = T y + T (T y - y) := map_add T y (T y - y)
      _ = T y + (T y - y) := by rw [hfix _ hs]
      _ = y := by
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        rw [← sub_eq_zero]
        rw [show T y + (T y - y) - y = (2 : K) • (T y - y) by module]
        rw [h2, zero_smul]
  have h3v : ∀ y, T (T (T y)) = y := by
    intro y
    have := congrArg (fun f : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) => f y) h3
    simpa [pow_three] using this
  apply LinearEquiv.ext
  intro v
  have h := h3v v
  rw [h2 (T v)] at h
  exact h

private theorem linearIndependent_pair_of_orthonormal (hσ : IsUnitaryInvolution σ)
    {v x : Fin 4 → K} (hv : herm σ v v = 1) (hx : herm σ x x = 1)
    (hvx : herm σ v x = 0) : LinearIndependent K ![v, x] := by
  rw [linearIndependent_fin2]
  constructor
  · rintro rfl
    rw [herm_zero_right] at hx
    exact zero_ne_one hx
  · intro a ha
    have ha' : a • x = v := by simpa using ha
    have h0 : herm σ x (a • x) = herm σ x v := by rw [ha']
    rw [herm_smul_right, hx, mul_one, herm_eq_zero_comm σ hσ.invol hvx] at h0
    have : a = 0 := h0
    rw [this, zero_smul] at ha
    have hv0 : v = 0 := ha.symm
    rw [hv0, herm_zero_left] at hv
    exact zero_ne_one hv

omit [Finite K] in
private theorem fixedSubmodule_le_span_pair (T : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K))
    {v x : Fin 4 → K} (hTv : T v = v) (hTx : T x = x)
    (hli : LinearIndependent K ![v, x]) (hdet : (LinearEquiv.det T : Kˣ) = 1)
    (h3 : T ^ 3 = 1) (hne : T ≠ 1) :
    (LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) ≤
      Submodule.span K ({v, x} : Set (Fin 4 → K)) := by
  intro y hy
  by_contra hyout
  have hyout' : y ∉ Submodule.span K (Set.range ![v, x]) := by
    rwa [show Set.range ![v, x] = ({v, x} : Set (Fin 4 → K)) by
      ext z; simp [or_comm]]
  have hli3 : LinearIndependent K ![v, x, y] := by
    rw [show ![v, x, y] = Fin.snoc ![v, x] y by ext i; fin_cases i <;> simp]
    exact hli.finSnoc hyout'
  have hfin3 : Module.finrank K (Submodule.span K ({v, x, y} : Set (Fin 4 → K))) = 3 := by
    have h := finrank_span_eq_card hli3
    rwa [show Set.range ![v, x, y] = ({v, x, y} : Set (Fin 4 → K)) by
      ext z; simp [or_comm, or_left_comm]] at h
  have hle : Submodule.span K ({v, x, y} : Set (Fin 4 → K)) ≤
      LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl | rfl)
    · simpa using hTv
    · simpa using hTx
    · simpa using hy
  have h3le : 3 ≤ Module.finrank K
      (LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) := by
    calc 3 = Module.finrank K (Submodule.span K ({v, x, y} : Set (Fin 4 → K))) := hfin3.symm
      _ ≤ Module.finrank K
          (LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) :=
        Submodule.finrank_mono hle
  have hV : Module.finrank K (Fin 4 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    norm_num
  have hcodim : Module.finrank K (Fin 4 → K) ≤
      Module.finrank K (LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) + 1 := by
    omega
  have hone := eq_one_of_pow_three_of_fix_hyperplane T
    (LinearMap.fixedSubmodule (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) hcodim
    (fun s hs => by simpa using hs) hdet h3
  exact hne hone


private theorem smul_eq_self_iff_mem_span_pair (hK : Nat.card K = 4) (t : Su K 2 1 4)
    {v x : Fin 4 → K} (hv : herm σ v v = 1) (hx : herm σ x x = 1)
    (hvx : herm σ v x = 0) (htv : t • v = v) (htx : t • x = x)
    (ht3 : t ^ 3 = 1) (htne : t ≠ 1) (y : Fin 4 → K) :
    t • y = y ↔ y ∈ Submodule.span K ({v, x} : Set (Fin 4 → K)) := by
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  constructor
  · intro hy
    have hle := fixedSubmodule_le_span_pair (toLinEquiv t)
      (by rw [toLinEquiv_apply]; exact htv)
      (by rw [toLinEquiv_apply]; exact htx)
      (linearIndependent_pair_of_orthonormal hσ hv hx hvx)
      (toLinEquiv_det t) (toLinEquiv_pow_three t ht3) (toLinEquiv_ne_one t htne)
    exact hle (by
      rw [LinearMap.mem_fixedSubmodule_iff]
      change toLinEquiv t y = y
      rw [toLinEquiv_apply]
      exact hy)
  · intro hy
    refine Submodule.span_induction (p := fun y _ => t • y = y) ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | rfl)
      · exact htv
      · exact htx
    · simp
    · intro a b _ _ ha hb; rw [smul_add, ha, hb]
    · intro a b _ hb; rw [smul_smul_vector, hb]

private theorem embSUid_range_two_ne_zero :
    (embSUid σ (2 : Fin 3)).range ≠ (embSUid σ (0 : Fin 3)).range := by
  intro h
  have ht : embSUid σ (2 : Fin 3) (rotSU σ) ∈ (embSUid σ (0 : Fin 3)).range := by
    rw [← h]
    exact ⟨rotSU σ, rfl⟩
  obtain ⟨A, hA⟩ := ht
  have h00 := congrFun (congrFun (congrArg (fun g : Su K 2 1 3 =>
    (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) hA) 0) 0
  rw [coe_embSUid, coe_embSUid] at h00
  simp [embPair, rotSU, rotMat] at h00

private theorem fixSU_pair (v x : Fin 4 → K) :
    fixSU ({v, x} : Set (Fin 4 → K)) = fixSU {v} ⊓ fixSU {x} := by
  change (⨅ y ∈ ({v, x} : Set (Fin 4 → K)),
      MulAction.stabilizer (Su K 2 1 4) y) =
    (⨅ y ∈ ({v} : Set (Fin 4 → K)), MulAction.stabilizer (Su K 2 1 4) y) ⊓
      (⨅ y ∈ ({x} : Set (Fin 4 → K)), MulAction.stabilizer (Su K 2 1 4) y)
  rw [show ({v, x} : Set (Fin 4 → K)) = insert v {x} by rfl,
    iInf_insert, iInf_singleton, iInf_singleton]

private noncomputable def mulEquiv_of_standardBlock (hK : Nat.card K = 4)
    {X : Subgroup (Su K 2 1 4)} {θ : Su K 2 1 3 →* Su K 2 1 4} {c : Su K 2 1 3}
    (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3)) (i : Fin 3)
    (hX : (((embSUid σ i).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X) :
    Su K 2 1 2 ≃* X := by
  have hθinj : Function.Injective θ := injective_of_ker_le_center hK θ hker
  let ψ : Su K 2 1 3 →* Su K 2 1 4 := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hψinj : Function.Injective ψ := hθinj.comp (MulAut.conj c⁻¹).injective
  have hX' : ((embSUid σ i).range).map ψ = X := by
    change ((embSUid σ i).range).map (θ.comp (MulAut.conj c⁻¹).toMonoidHom) = X
    rw [← Subgroup.map_map]
    exact hX
  exact (MonoidHom.ofInjective (embSUid_injective σ i)).trans
    ((Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr hX'))

private noncomputable def blockTorusElement (u : normOne σ)
    (θ : Su K 2 1 3 →* Su K 2 1 4) (c : Su K 2 1 3) (i : Fin 3) : Su K 2 1 4 :=
  θ (c⁻¹ * embSUid σ i (torusTwo σ u) * c)

private theorem blockTorusElement_pow_three {u : normOne σ}
    (hu3 : (torusTwo σ u) ^ 3 = 1) (θ : Su K 2 1 3 →* Su K 2 1 4)
    (c : Su K 2 1 3) (i : Fin 3) : blockTorusElement u θ c i ^ 3 = 1 := by
  change (θ (c⁻¹ * embSUid σ i (torusTwo σ u) * c)) ^ 3 = 1
  rw [← map_pow]
  have hd3 : embSUid σ i (torusTwo σ u) ^ 3 = 1 := by
    rw [← map_pow, hu3, map_one]
  have hconj : (c⁻¹ * embSUid σ i (torusTwo σ u) * c) ^ 3 =
      c⁻¹ * embSUid σ i (torusTwo σ u) ^ 3 * c := by
    have h := map_pow (MulAut.conj c⁻¹) (embSUid σ i (torusTwo σ u)) 3
    simpa [MulAut.conj_apply, mul_assoc] using h.symm
  rw [hconj, hd3, mul_one, inv_mul_cancel, map_one]

private theorem blockTorusElement_ne_one {u : normOne σ}
    {θ : Su K 2 1 3 →* Su K 2 1 4} (hθinj : Function.Injective θ)
    (hu_ne : torusTwo σ u ≠ 1)
    (c : Su K 2 1 3) (i : Fin 3) : blockTorusElement u θ c i ≠ 1 := by
  intro h
  have hc1 : c⁻¹ * embSUid σ i (torusTwo σ u) * c = 1 := by
    apply hθinj
    rw [map_one]
    exact h
  have hd1 : embSUid σ i (torusTwo σ u) = 1 := by
    have := congrArg (fun x : Su K 2 1 3 => c * x * c⁻¹) hc1
    simpa [mul_assoc] using this
  have hu : torusTwo σ u = 1 := embSUid_injective σ i (by simpa using hd1)
  exact hu_ne hu

private theorem blockTorusElement_commute (u : normOne σ)
    (θ : Su K 2 1 3 →* Su K 2 1 4) (c : Su K 2 1 3) (i₁ i₂ : Fin 3)
    (hi₁ : i₁ = 2 ∨ i₁ = 0) (hi₂ : i₂ = 2 ∨ i₂ = 0) (hne : i₁ ≠ i₂) :
    blockTorusElement u θ c i₁ * blockTorusElement u θ c i₂ =
      blockTorusElement u θ c i₂ * blockTorusElement u θ c i₁ := by
  have hdcomm : embSUid σ i₁ (torusTwo σ u) * embSUid σ i₂ (torusTwo σ u) =
      embSUid σ i₂ (torusTwo σ u) * embSUid σ i₁ (torusTwo σ u) := by
    fin_cases i₁ <;> fin_cases i₂ <;> simp at hi₁ hi₂ hne ⊢
    · simpa using (embSUid_two_torus_comm u u).symm
    · simpa using embSUid_two_torus_comm u u
  change θ (c⁻¹ * embSUid σ i₁ (torusTwo σ u) * c) *
      θ (c⁻¹ * embSUid σ i₂ (torusTwo σ u) * c) =
    θ (c⁻¹ * embSUid σ i₂ (torusTwo σ u) * c) *
      θ (c⁻¹ * embSUid σ i₁ (torusTwo σ u) * c)
  rw [← map_mul, ← map_mul]
  congr 1
  calc c⁻¹ * embSUid σ i₁ (torusTwo σ u) * c *
        (c⁻¹ * embSUid σ i₂ (torusTwo σ u) * c)
      = c⁻¹ * (embSUid σ i₁ (torusTwo σ u) * embSUid σ i₂ (torusTwo σ u)) * c := by
        group
    _ = c⁻¹ * (embSUid σ i₂ (torusTwo σ u) * embSUid σ i₁ (torusTwo σ u)) * c := by
        rw [hdcomm]
    _ = c⁻¹ * embSUid σ i₂ (torusTwo σ u) * c *
        (c⁻¹ * embSUid σ i₁ (torusTwo σ u) * c) := by group

private theorem blockTorusElement_mem (u : normOne σ)
    (θ : Su K 2 1 3 →* Su K 2 1 4) (c : Su K 2 1 3) (i : Fin 3)
    {X : Subgroup (Su K 2 1 4)}
    (hX : (((embSUid σ i).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X) :
    blockTorusElement u θ c i ∈ X := by
  rw [← hX]
  exact Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem
    (MulAut.conj c⁻¹).toMonoidHom ⟨torusTwo σ u, rfl⟩)

private theorem fixed_lines_of_standardPair (hK : Nat.card K = 4) {v : Fin 4 → K}
    (hv : herm σ v v = 1) {A X₁ X₂ : Subgroup (Su K 2 1 4)} (hA : A = fixSU {v})
    {θ : Su K 2 1 3 →* Su K 2 1 4} {c : Su K 2 1 3}
    (hrange : θ.range = A) (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3))
    (i₁ i₂ : Fin 3) (_hi₁ : i₁ = 2 ∨ i₁ = 0) (_hi₂ : i₂ = 2 ∨ i₂ = 0) (_hne : i₁ ≠ i₂)
    (hX1 : (((embSUid σ i₁).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₁)
    (hX2 : (((embSUid σ i₂).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₂) :
    ∃ x₁ x₂ : Fin 4 → K, herm σ x₁ x₁ = 1 ∧ herm σ x₂ x₂ = 1 ∧
      herm σ v x₁ = 0 ∧ herm σ v x₂ = 0 ∧ X₁ = fixSU {v, x₁} ∧ X₂ = fixSU {v, x₂} := by
  classical
  have hθinj : Function.Injective θ := injective_of_ker_le_center hK θ hker
  let ψ : Su K 2 1 3 →* Su K 2 1 4 := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hψinj : Function.Injective ψ := hθinj.comp (MulAut.conj c⁻¹).injective
  have hX1' : ((embSUid σ i₁).range).map ψ = X₁ := by
    change ((embSUid σ i₁).range).map (θ.comp (MulAut.conj c⁻¹).toMonoidHom) = X₁
    rw [← Subgroup.map_map]
    exact hX1
  have hX2' : ((embSUid σ i₂).range).map ψ = X₂ := by
    change ((embSUid σ i₂).range).map (θ.comp (MulAut.conj c⁻¹).toMonoidHom) = X₂
    rw [← Subgroup.map_map]
    exact hX2
  let eB₁ : Su K 2 1 2 ≃* (embSUid σ i₁).range :=
    MonoidHom.ofInjective (embSUid_injective σ i₁)
  let eMap₁ : (embSUid σ i₁).range ≃* ((embSUid σ i₁).range).map ψ :=
    Subgroup.equivMapOfInjective _ ψ hψinj
  let e₁ : Su K 2 1 2 ≃* X₁ := eB₁.trans (eMap₁.trans (MulEquiv.subgroupCongr hX1'))
  let eB₂ : Su K 2 1 2 ≃* (embSUid σ i₂).range :=
    MonoidHom.ofInjective (embSUid_injective σ i₂)
  let eMap₂ : (embSUid σ i₂).range ≃* ((embSUid σ i₂).range).map ψ :=
    Subgroup.equivMapOfInjective _ ψ hψinj
  let e₂ : Su K 2 1 2 ≃* X₂ := eB₂.trans (eMap₂.trans (MulEquiv.subgroupCongr hX2'))
  have hXle₁ : X₁ ≤ fixSU {v} := by
    rw [← hA, ← hrange, ← hX1']
    calc ((embSUid σ i₁).range).map ψ
        = ((embSUid σ i₁).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [Subgroup.map_map]
      _ ≤ θ.range := Subgroup.map_le_range θ _
  have hXle₂ : X₂ ≤ fixSU {v} := by
    rw [← hA, ← hrange, ← hX2']
    calc ((embSUid σ i₂).range).map ψ
        = ((embSUid σ i₂).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [Subgroup.map_map]
      _ ≤ θ.range := Subgroup.map_le_range θ _
  obtain ⟨x₁, hx₁, hvx₁, hX₁eq⟩ := eq_fixSU_pair hK hv e₁ hXle₁
  obtain ⟨x₂, hx₂, hvx₂, hX₂eq⟩ := eq_fixSU_pair hK hv e₂ hXle₂
  exact ⟨x₁, x₂, hx₁, hx₂, hvx₁, hvx₂, hX₁eq, hX₂eq⟩

private theorem exists_torus_elements_of_standardPair (hK : Nat.card K = 4)
    {v : Fin 4 → K} {X₁ X₂ : Subgroup (Su K 2 1 4)}
    {θ : Su K 2 1 3 →* Su K 2 1 4} {c : Su K 2 1 3}
    (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3))
    (i₁ i₂ : Fin 3) (hi₁ : i₁ = 2 ∨ i₁ = 0) (hi₂ : i₂ = 2 ∨ i₂ = 0) (hne : i₁ ≠ i₂)
    (hX1 : (((embSUid σ i₁).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₁)
    (hX2 : (((embSUid σ i₂).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₂)
    {x₁ x₂ : Fin 4 → K} (hX₁eq : X₁ = fixSU {v, x₁}) (hX₂eq : X₂ = fixSU {v, x₂}) :
    ∃ t₁ t₂ : Su K 2 1 4, t₁ ∈ X₁ ∧ t₂ ∈ X₂ ∧ t₁ * t₂ = t₂ * t₁ ∧
      t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧ t₁ ≠ 1 ∧ t₂ ≠ 1 ∧
      t₁ • v = v ∧ t₁ • x₁ = x₁ ∧ t₂ • v = v ∧ t₂ • x₂ = x₂ := by
  classical
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  have hθinj : Function.Injective θ := injective_of_ker_le_center hK θ hker
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := by
    have h : unitaryInvolution K 2 1 ω = ω ^ 2 := by
      rw [unitaryInvolution_apply]; norm_num
    rw [h] at hω
    calc ω ^ 3 = ω ^ 2 * ω := by ring
      _ = 1 := hω
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  let u : normOne σ := ⟨Units.mk0 ω hω0, by
    change σ ω * ω = 1
    exact hω⟩
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((Units.mk0 ω hω0 : Kˣ) : K) ^ 3 = 1
    simp [hω3]
  have htorus3 : (torusTwo σ u) ^ 3 = 1 := by
    rw [← map_pow, hu3, map_one]
  have htorus_ne : torusTwo σ u ≠ 1 := by
    intro h
    have hu : u = 1 := torusTwo_injective σ (by simpa using h)
    apply hω1
    have huK : ((u : Kˣ) : K) = 1 := by
      rw [show (u : Kˣ) = 1 from congrArg Subtype.val hu, Units.val_one]
    simpa [u] using huK
  let t₁ : Su K 2 1 4 := blockTorusElement u θ c i₁
  let t₂ : Su K 2 1 4 := blockTorusElement u θ c i₂
  have ht1X1 : t₁ ∈ X₁ := blockTorusElement_mem u θ c i₁ hX1
  have ht2X2 : t₂ ∈ X₂ := blockTorusElement_mem u θ c i₂ hX2
  have ht1_fix (y : Fin 4 → K) (hy : y = v ∨ y = x₁) : t₁ • y = y := by
    have h := ht1X1
    rw [hX₁eq] at h
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff] at h
    exact h y (by simpa using hy)
  have ht2_fix (y : Fin 4 → K) (hy : y = v ∨ y = x₂) : t₂ • y = y := by
    have h := ht2X2
    rw [hX₂eq] at h
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff] at h
    exact h y (by simpa using hy)
  exact ⟨t₁, t₂, ht1X1, ht2X2,
    blockTorusElement_commute u θ c i₁ i₂ hi₁ hi₂ hne,
    blockTorusElement_pow_three htorus3 θ c i₁,
    blockTorusElement_pow_three htorus3 θ c i₂,
    blockTorusElement_ne_one hθinj htorus_ne c i₁,
    blockTorusElement_ne_one hθinj htorus_ne c i₂,
    ht1_fix v (Or.inl rfl), ht1_fix x₁ (Or.inr rfl),
    ht2_fix v (Or.inl rfl), ht2_fix x₂ (Or.inr rfl)⟩

private theorem herm_eq_zero_of_commuting_fixed_lines {t₁ t₂ : Su K 2 1 4}
    {v x₁ x₂ : Fin 4 → K} {X₁ X₂ : Subgroup (Su K 2 1 4)}
    (hcomm : t₁ * t₂ = t₂ * t₁) (ht1x : t₁ • x₁ = x₁)
    (ht2v : t₂ • v = v) (ht2x : t₂ • x₂ = x₂)
    (hfix₁ : ∀ y, t₁ • y = y ↔ y ∈ Submodule.span K ({v, x₁} : Set (Fin 4 → K)))
    (hfix₂ : ∀ y, t₂ • y = y ↔ y ∈ Submodule.span K ({v, x₂} : Set (Fin 4 → K)))
    (hX₁eq : X₁ = fixSU {v, x₁}) (hX₂eq : X₂ = fixSU {v, x₂}) (hXne : X₁ ≠ X₂)
    (hv : herm σ v v = 1) (hx₁ : herm σ x₁ x₁ = 1) (_hx₂ : herm σ x₂ x₂ = 1)
    (hvx₁ : herm σ v x₁ = 0) (hvx₂ : herm σ v x₂ = 0) (ht2pow3 : t₂ ^ 3 = 1) :
    herm σ x₁ x₂ = 0 := by
  have ht2x1_mem : t₂ • x₁ ∈ Submodule.span K ({v, x₁} : Set (Fin 4 → K)) := by
    apply (hfix₁ _).mp
    calc t₁ • (t₂ • x₁) = (t₁ * t₂) • x₁ := by rw [mul_smul]
      _ = (t₂ * t₁) • x₁ := by rw [hcomm]
      _ = t₂ • (t₁ • x₁) := by rw [mul_smul]
      _ = t₂ • x₁ := by rw [ht1x]
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp ht2x1_mem
  have ha0 : a = 0 := by
    have hiso : herm σ (t₂ • v) (t₂ • x₁) = herm σ v x₁ := by
      rw [smul_def, smul_def, herm_mulVec, (mem_SUid.mp t₂.2).2, Matrix.one_mulVec]
    rw [ht2v, hvx₁] at hiso
    rw [← hab, herm_add_right, herm_smul_right, herm_smul_right, hv, hvx₁] at hiso
    simpa using hiso
  have ht2x1 : t₂ • x₁ = b • x₁ := by rw [← hab, ha0, zero_smul, zero_add]
  have hx1ne : x₁ ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hx₁
    exact zero_ne_one hx₁
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    have hx1_fixed : t₂ • x₁ = x₁ := by rw [ht2x1, hb1, one_smul]
    have hx1_mem : x₁ ∈ Submodule.span K ({v, x₂} : Set (Fin 4 → K)) :=
      (hfix₂ x₁).mp hx1_fixed
    obtain ⟨a₂, b₂, hab₂⟩ := Submodule.mem_span_pair.mp hx1_mem
    have ha₂ : a₂ = 0 := by
      have h0 : herm σ v x₁ = 0 := hvx₁
      rw [← hab₂, herm_add_right, herm_smul_right, herm_smul_right, hv, hvx₂] at h0
      simpa using h0
    have hx1_eq : x₁ = b₂ • x₂ := by rw [← hab₂, ha₂, zero_smul, zero_add]
    have hb₂0 : b₂ ≠ 0 := by
      intro hb₂
      have hx0 : x₁ = 0 := by rw [hx1_eq, hb₂, zero_smul]
      exact hx1ne hx0
    have hXeq : X₁ = X₂ := by
      rw [hX₁eq, hX₂eq, hx1_eq, fixSU_pair, fixSU_pair, fixSU_smul_single hb₂0 x₂]
    exact hXne hXeq
  have hb3 : b ^ 3 = 1 := by
    have h1 : (t₂ ^ 3) • x₁ = (b ^ 3) • x₁ := by
      rw [pow_three, mul_smul, mul_smul, ht2x1]
      calc t₂ • t₂ • (b • x₁)
          = t₂ • (b • (t₂ • x₁)) := by rw [smul_smul_vector]
        _ = t₂ • (b • (b • x₁)) := by rw [ht2x1]
        _ = b • (t₂ • (b • x₁)) := by rw [smul_smul_vector]
        _ = b • (b • (t₂ • x₁)) := by rw [smul_smul_vector]
        _ = b • (b • (b • x₁)) := by rw [ht2x1]
        _ = b ^ 3 • x₁ := by rw [pow_three, mul_smul, mul_smul]
    have h : (b ^ 3) • x₁ = x₁ := by
      rw [← h1, ht2pow3, one_smul]
    have hcoef : (b ^ 3 - 1) • x₁ = 0 := by rw [sub_smul, h, one_smul, sub_self]
    have hb3sub : b ^ 3 - 1 = 0 := (smul_eq_zero.mp hcoef).resolve_right hx1ne
    exact sub_eq_zero.mp hb3sub
  have hb2ne : b ^ 2 ≠ 1 := by
    intro hb2
    have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb3
    have hb1 : b = 1 := by
      calc b = b ^ 3 * (b ^ 2)⁻¹ := by field_simp
        _ = 1 := by rw [hb3, hb2, inv_one, mul_one]
    exact hb_ne_one hb1
  have hσb : unitaryInvolution K 2 1 b ≠ 1 := by
    have h2 : unitaryInvolution K 2 1 b = b ^ 2 := by
      rw [unitaryInvolution_apply]; norm_num
    rw [h2]
    exact hb2ne
  have hiso : herm σ (t₂ • x₁) (t₂ • x₂) = herm σ x₁ x₂ := by
    rw [smul_def, smul_def, herm_mulVec, (mem_SUid.mp t₂.2).2, Matrix.one_mulVec]
  rw [ht2x1, ht2x, herm_smul_left] at hiso
  have hcoef : (unitaryInvolution K 2 1 b - 1) * herm σ x₁ x₂ = 0 := by
    rw [sub_mul, one_mul, hiso]
    exact sub_self _
  exact (mul_eq_zero.mp hcoef).resolve_left (sub_ne_zero.mpr hσb)

private theorem exists_perpendicular_fixed_lines (hK : Nat.card K = 4) {v : Fin 4 → K}
    (hv : herm σ v v = 1) {A X₁ X₂ : Subgroup (Su K 2 1 4)} (hA : A = fixSU {v})
    {θ : Su K 2 1 3 →* Su K 2 1 4} {c : Su K 2 1 3}
    (hrange : θ.range = A) (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3))
    (i₁ i₂ : Fin 3) (hi₁ : i₁ = 2 ∨ i₁ = 0) (hi₂ : i₂ = 2 ∨ i₂ = 0) (hne : i₁ ≠ i₂)
    (hX1 : (((embSUid σ i₁).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₁)
    (hX2 : (((embSUid σ i₂).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ = X₂) :
    ∃ x₁ x₂ : Fin 4 → K, herm σ x₁ x₁ = 1 ∧ herm σ x₂ x₂ = 1 ∧
      herm σ v x₁ = 0 ∧ herm σ v x₂ = 0 ∧ herm σ x₁ x₂ = 0 ∧
      X₁ = fixSU {v, x₁} ∧ X₂ = fixSU {v, x₂} := by
  obtain ⟨x₁, x₂, hx₁, hx₂, hvx₁, hvx₂, hX₁eq, hX₂eq⟩ :=
    fixed_lines_of_standardPair hK hv hA hrange hker i₁ i₂ hi₁ hi₂ hne hX1 hX2
  have hθinj : Function.Injective θ := injective_of_ker_le_center hK θ hker
  let ψ : Su K 2 1 3 →* Su K 2 1 4 := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hψinj : Function.Injective ψ := hθinj.comp (MulAut.conj c⁻¹).injective
  have hX1' : ((embSUid σ i₁).range).map ψ = X₁ := by
    change ((embSUid σ i₁).range).map (θ.comp (MulAut.conj c⁻¹).toMonoidHom) = X₁
    rw [← Subgroup.map_map]
    exact hX1
  have hX2' : ((embSUid σ i₂).range).map ψ = X₂ := by
    change ((embSUid σ i₂).range).map (θ.comp (MulAut.conj c⁻¹).toMonoidHom) = X₂
    rw [← Subgroup.map_map]
    exact hX2
  have hXne : X₁ ≠ X₂ := by
    intro hEq
    have hmap : ((embSUid σ i₁).range).map ψ = ((embSUid σ i₂).range).map ψ := by
      rw [hX1', hX2', hEq]
    have hsub : (embSUid σ i₁).range = (embSUid σ i₂).range :=
      Subgroup.map_injective hψinj hmap
    have hne' : (embSUid σ i₁).range ≠ (embSUid σ i₂).range := by
      fin_cases i₁ <;> fin_cases i₂ <;> simp at hi₁ hi₂ hne ⊢
      · exact fun h => embSUid_range_two_ne_zero h.symm
      · exact embSUid_range_two_ne_zero
    exact hne' hsub
  obtain ⟨t₁, t₂, ht1X1, ht2X2, htcomm, ht1pow3, ht2pow3, ht1ne, ht2ne,
    ht1v, ht1x, ht2v, ht2x⟩ :=
    exists_torus_elements_of_standardPair hK hker i₁ i₂ hi₁ hi₂ hne hX1 hX2
      hX₁eq hX₂eq
  have ht1_fix_iff (y : Fin 4 → K) :
      t₁ • y = y ↔ y ∈ Submodule.span K ({v, x₁} : Set (Fin 4 → K)) :=
    smul_eq_self_iff_mem_span_pair hK t₁ hv hx₁ hvx₁ ht1v ht1x ht1pow3 ht1ne y
  have ht2_fix_iff (y : Fin 4 → K) :
      t₂ • y = y ↔ y ∈ Submodule.span K ({v, x₂} : Set (Fin 4 → K)) :=
    smul_eq_self_iff_mem_span_pair hK t₂ hv hx₂ hvx₂ ht2v ht2x ht2pow3 ht2ne y
  exact ⟨x₁, x₂, hx₁, hx₂, hvx₁, hvx₂,
    herm_eq_zero_of_commuting_fixed_lines htcomm ht1x ht2v ht2x ht1_fix_iff ht2_fix_iff
      hX₁eq hX₂eq hXne hv hx₁ hx₂ hvx₁ hvx₂ ht2pow3,
    hX₁eq, hX₂eq⟩

private theorem mem_span_pair_of_fixed (hK : Nat.card K = 4) {v x y : Fin 4 → K}
    (hv : herm σ v v = 1) (hx : herm σ x x = 1) (hvx : herm σ v x = 0)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X) (hX : X = fixSU {v, x})
    (hy : ∀ g ∈ X, g • y = y) :
    y ∈ Submodule.span K ({v, x} : Set (Fin 4 → K)) := by
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := by
    have h : unitaryInvolution K 2 1 ω = ω ^ 2 := by
      rw [unitaryInvolution_apply]; norm_num
    rw [h] at hω
    calc ω ^ 3 = ω ^ 2 * ω := by ring
      _ = 1 := hω
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  let u : normOne σ := ⟨Units.mk0 ω hω0, by
    change σ ω * ω = 1
    exact hω⟩
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((Units.mk0 ω hω0 : Kˣ) : K) ^ 3 = 1
    simp [hω3]
  have htorus3 : (torusTwo σ u) ^ 3 = 1 := by
    rw [← map_pow, hu3, map_one]
  let t : Su K 2 1 4 := e (torusTwo σ u)
  have htX : t ∈ X := (e (torusTwo σ u)).2
  have ht3X : e (torusTwo σ u) ^ 3 = 1 := by
    rw [← map_pow, htorus3, map_one]
  have ht3 : t ^ 3 = 1 := by
    change (↑(e (torusTwo σ u)) : Su K 2 1 4) ^ 3 = 1
    simpa using congrArg (fun z : X => (z : Su K 2 1 4)) ht3X
  have htne : t ≠ 1 := by
    intro h
    have h1 : torusTwo σ u = 1 := e.injective (by simpa [t] using h)
    have hu : u = 1 := torusTwo_injective σ (by simpa using h1)
    apply hω1
    have : ((u : Kˣ) : K) = 1 := by
      rw [show (u : Kˣ) = 1 from congrArg Subtype.val hu, Units.val_one]
    simpa [u] using this
  have htfix (z : Fin 4 → K) (hz : z = v ∨ z = x) : t • z = z := by
    have h := htX
    rw [hX] at h
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff] at h
    exact h z (by simpa using hz)
  have htv : t • v = v := htfix v (Or.inl rfl)
  have htx : t • x = x := htfix x (Or.inr rfl)
  exact (smul_eq_self_iff_mem_span_pair hK t hv hx hvx htv htx ht3 htne y).mp
    (hy t htX)

private theorem exists_orthonormal_four_of_three (hK : Nat.card K = 4) {v x y : Fin 4 → K}
    (hv : herm σ v v = 1) (hx : herm σ x x = 1) (hy : herm σ y y = 1)
    (hvx : herm σ v x = 0) (hvy : herm σ v y = 0) (hxy : herm σ x y = 0) :
    ∃ w : Fin 4 → K, herm σ w w = 1 ∧ herm σ v w = 0 ∧ herm σ x w = 0 ∧
      herm σ y w = 0 := by
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  let hh : CFSG.Fischer.Classification.Herm.IsHermForm σ
      (herm σ (n := 4)) :=
    { add_left := fun x x' y => herm_add_left _ x x' y
      smul_left := fun c x y => herm_smul_left _ c x y
      conj := fun x y => herm_conj _ hσ.invol x y }
  let B : (Fin 4 → K) →ₛₗ[((σ : K ≃+* K) : K →+* K)]
      (Fin 4 → K) →ₗ[K] K := CFSG.Fischer.Classification.Herm.mkForm hσ.invol hh
  have hB : B.IsSymm := CFSG.Fischer.Classification.Herm.isSymm_mkForm hσ.invol hh
  have hnd : B.SeparatingLeft := by
    intro z hz
    refine eq_zero_of_herm σ fun w => ?_
    have hzw := hz w
    change herm σ z w = 0 at hzw
    exact hzw
  let b : Fin 3 → (Fin 4 → K) := ![v, x, y]
  have hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    change herm σ (b i) (b j) = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [b]
    all_goals first
      | exact hv
      | exact hx
      | exact hy
      | exact hvx
      | exact hvy
      | exact hxy
      | exact herm_eq_zero_comm σ hσ.invol hvx
      | exact herm_eq_zero_comm σ hσ.invol hvy
      | exact herm_eq_zero_comm σ hσ.invol hxy
  obtain ⟨w, hw, hww⟩ :=
    CFSG.Fischer.Classification.Herm.exists_norm_one_perp (B := B) hb hσ hB hnd
      (k := 3) (by simp)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · simpa [B, CFSG.Fischer.Classification.Herm.mkForm] using hww
  · have := hw 0
    simpa [B, CFSG.Fischer.Classification.Herm.mkForm, b] using this
  · have := hw 1
    simpa [B, CFSG.Fischer.Classification.Herm.mkForm, b] using this
  · have := hw 2
    simpa [B, CFSG.Fischer.Classification.Herm.mkForm, b] using this

theorem fix_perp_of_standardPair (hK : Nat.card K = 4) {v : Fin 4 → K} (hv : herm σ v v = 1)
    {A X₁ X₂ : Subgroup (Su K 2 1 4)} (hA : A = fixSU {v})
    (hP : UnitaryBlockStandardPair K 2 1 A X₁ X₂) :
    ∃ x₁ x₂ : Fin 4 → K, herm σ x₁ x₁ = 1 ∧ herm σ x₂ x₂ = 1 ∧
      herm σ v x₁ = 0 ∧ herm σ v x₂ = 0 ∧ herm σ x₁ x₂ = 0 ∧
      X₁ = fixSU {v, x₁} ∧ X₂ = fixSU {v, x₂} := by
  obtain ⟨θ, c, hrange, hker, hor⟩ := hP
  rcases hor with ⟨hX1, hX2⟩ | ⟨hX1, hX2⟩
  · refine exists_perpendicular_fixed_lines (c := c) hK hv hA hrange hker 2 0
      (Or.inl rfl) (Or.inr rfl) (by decide) ?_ ?_
    · simpa [B12] using hX1
    · simpa [B23] using hX2
  · refine exists_perpendicular_fixed_lines (c := c) hK hv hA hrange hker 0 2
      (Or.inr rfl) (Or.inl rfl) (by decide) ?_ ?_
    · simpa [B23] using hX2
    · simpa [B12] using hX1

private theorem exists_frame_element {vA x₁ x₂ w : Fin 4 → K}
    (hon : ∀ j k : Fin 4, herm σ ((![x₂, w, x₁, vA] : Fin 4 → Fin 4 → K) j)
      ((![x₂, w, x₁, vA] : Fin 4 → Fin 4 → K) k) = if j = k then 1 else 0) :
    ∃ g : Su K 2 1 4, ∃ a0 : Fin 4 → K, (∀ i, a0 i ≠ 0) ∧
      g • ({Pi.single (0 : Fin 4) 1} : Set (Fin 4 → K)) = {a0 0 • x₂} ∧
      g • ({Pi.single (1 : Fin 4) 1} : Set (Fin 4 → K)) = {a0 1 • w} ∧
      g • ({Pi.single (3 : Fin 4) 1} : Set (Fin 4 → K)) = {a0 3 • vA} ∧
      g • ({Pi.single (2 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 2 • x₁, a0 3 • vA} ∧
      g • ({Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 0 • x₂, a0 3 • vA} ∧
      g • ({Pi.single (0 : Fin 4) 1, Pi.single (1 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 0 • x₂, a0 1 • w} := by
  let u : Fin 4 → Fin 4 → K := ![x₂, w, x₁, vA]
  obtain ⟨g, hg⟩ := exists_mem_SUid_smul_single (n := 3) (v := u) hon
  choose a0 ha0 hg0 using hg
  let gs : Su K 2 1 4 := g
  have hg0' : gs • (Pi.single (0 : Fin 4) 1 : Fin 4 → K) = a0 0 • x₂ := by
    simpa [u] using hg0 0
  have hg1' : gs • (Pi.single (1 : Fin 4) 1 : Fin 4 → K) = a0 1 • w := by
    simpa [u] using hg0 1
  have hg2' : gs • (Pi.single (2 : Fin 4) 1 : Fin 4 → K) = a0 2 • x₁ := by
    simpa [u] using hg0 2
  have hg3' : gs • (Pi.single (3 : Fin 4) 1 : Fin 4 → K) = a0 3 • vA := by
    simpa [u] using hg0 3
  refine ⟨gs, a0, ha0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.smul_set_singleton, hg0']
  · rw [Set.smul_set_singleton, hg1']
  · rw [Set.smul_set_singleton, hg3']
  · rw [show ({Pi.single (2 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = insert (Pi.single (2 : Fin 4) 1) {Pi.single (3 : Fin 4) 1} by rfl,
      Set.smul_set_insert, Set.smul_set_singleton, hg2', hg3']
  · rw [show ({Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = insert (Pi.single (0 : Fin 4) 1) {Pi.single (3 : Fin 4) 1} by rfl,
      Set.smul_set_insert, Set.smul_set_singleton, hg0', hg3']
  · rw [show ({Pi.single (0 : Fin 4) 1, Pi.single (1 : Fin 4) 1} :
        Set (Fin 4 → K)) = insert (Pi.single (0 : Fin 4) 1) {Pi.single (1 : Fin 4) 1} by rfl,
      Set.smul_set_insert, Set.smul_set_singleton, hg0', hg1']

private theorem frame_element_images (g : Su K 2 1 4) (a0 : Fin 4 → K)
    {A B X₁ X₂ X₃ : Subgroup (Su K 2 1 4)} {vA x₁ x₂ w : Fin 4 → K}
    (hAfix : A = fixSU {vA}) (hBfix : B = fixSU {x₂})
    (hX₁eq : X₁ = fixSU {vA, x₁}) (hX₂eq : X₂ = fixSU {vA, x₂})
    (hX₃fix : X₃ = fixSU {x₂, w})
    (hset0 : g • ({Pi.single (0 : Fin 4) 1} : Set (Fin 4 → K)) = {a0 0 • x₂})
    (hset3s : g • ({Pi.single (3 : Fin 4) 1} : Set (Fin 4 → K)) = {a0 3 • vA})
    (hset2 : g • ({Pi.single (2 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 2 • x₁, a0 3 • vA})
    (hset3 : g • ({Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 0 • x₂, a0 3 • vA})
    (hset4 : g • ({Pi.single (0 : Fin 4) 1, Pi.single (1 : Fin 4) 1} :
        Set (Fin 4 → K)) = {a0 0 • x₂, a0 1 • w})
    (ha0 : ∀ i, a0 i ≠ 0) :
    A = (blk012 K).range.map (MulAut.conj g).toMonoidHom ∧
      B = (blk123 K).range.map (MulAut.conj g).toMonoidHom ∧
      X₁ = ((B12 K 2 1).map (blk012 K)).map (MulAut.conj g).toMonoidHom ∧
      X₂ = ((B23 K 2 1).map (blk012 K)).map (MulAut.conj g).toMonoidHom ∧
      X₃ = ((B23 K 2 1).map (blk123 K)).map (MulAut.conj g).toMonoidHom := by
  let cc := (MulAut.conj g).toMonoidHom
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc A = fixSU {vA} := hAfix
      _ = fixSU {a0 3 • vA} := by rw [fixSU_smul_single (ha0 3) vA]
      _ = fixSU (g • ({Pi.single (3 : Fin 4) 1} : Set (Fin 4 → K))) := by rw [← hset3s]
      _ = (fixSU {Pi.single (3 : Fin 4) 1}).map cc := fixSU_smul g _
      _ = (blk012 K).range.map cc := by rw [fixSU_std.1]
  · calc B = fixSU {x₂} := hBfix
      _ = fixSU {a0 0 • x₂} := by rw [fixSU_smul_single (ha0 0) x₂]
      _ = fixSU (g • ({Pi.single (0 : Fin 4) 1} : Set (Fin 4 → K))) := by rw [← hset0]
      _ = (fixSU {Pi.single (0 : Fin 4) 1}).map cc := fixSU_smul g _
      _ = (blk123 K).range.map cc := by rw [fixSU_std.2.1]
  · calc X₁ = fixSU {vA, x₁} := hX₁eq
      _ = fixSU {a0 3 • vA, a0 2 • x₁} := by
        rw [fixSU_smul_pair (a := a0 3) (b := a0 2) (ha0 3) (ha0 2) vA x₁]
      _ = fixSU (g • ({Pi.single (2 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
          Set (Fin 4 → K))) := by
        rw [hset2]
        congr 1
        ext z; simp [or_comm]
      _ = (fixSU {Pi.single (2 : Fin 4) 1,
          Pi.single (3 : Fin 4) 1}).map cc := fixSU_smul g _
      _ = ((B12 K 2 1).map (blk012 K)).map cc := by rw [fixSU_std.2.2.1]
  · calc X₂ = fixSU {vA, x₂} := hX₂eq
      _ = fixSU {a0 3 • vA, a0 0 • x₂} := by
        rw [fixSU_smul_pair (a := a0 3) (b := a0 0) (ha0 3) (ha0 0) vA x₂]
      _ = fixSU (g • ({Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1} :
          Set (Fin 4 → K))) := by
        rw [hset3]
        congr 1
        ext z; simp [or_comm]
      _ = (fixSU {Pi.single (0 : Fin 4) 1,
          Pi.single (3 : Fin 4) 1}).map cc := fixSU_smul g _
      _ = ((B23 K 2 1).map (blk012 K)).map cc := by rw [fixSU_std.2.2.2.1]
  · calc X₃ = fixSU {x₂, w} := hX₃fix
      _ = fixSU {a0 0 • x₂, a0 1 • w} := by
        rw [fixSU_smul_pair (a := a0 0) (b := a0 1) (ha0 0) (ha0 1) x₂ w]
      _ = fixSU (g • ({Pi.single (0 : Fin 4) 1, Pi.single (1 : Fin 4) 1} :
          Set (Fin 4 → K))) := by
        rw [hset4]
      _ = (fixSU {Pi.single (0 : Fin 4) 1,
          Pi.single (1 : Fin 4) 1}).map cc := fixSU_smul g _
      _ = ((B23 K 2 1).map (blk123 K)).map cc := by rw [fixSU_std.2.2.2.2]

private theorem second_standardPair_line (hK : Nat.card K = 4)
    {vA x₂ w vB : Fin 4 → K} (hvA : herm σ vA vA = 1) (hx₂ : herm σ x₂ x₂ = 1)
    (hvx₂ : herm σ vA x₂ = 0) (hx2w : herm σ x₂ w = 0) (hw : herm σ w w = 1)
    (hvw : herm σ vA w = 0) (hwvA : herm σ w vA = 0) (hwx₂ : herm σ w x₂ = 0)
    {B X₂ X₃ : Subgroup (Su K 2 1 4)} (hBfix : B = fixSU {vB})
    (hX2B : X₂ ≤ B) (hX3B : X₃ ≤ B) (e₂ : Su K 2 1 2 ≃* X₂)
    (e₃ : Su K 2 1 2 ≃* X₃) (hX₂eq : X₂ = fixSU {vA, x₂})
    (hX₃fix : X₃ = fixSU {x₂, w}) (hvB : herm σ vB vB = 1) :
    B = fixSU {x₂} := by
  have hvB_fix₂ : ∀ g ∈ X₂, g • vB = vB := by
    intro g hg
    have hgB : g ∈ B := hX2B hg
    rw [hBfix] at hgB
    simp only [fixSU, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff] at hgB
    exact hgB vB (by simp)
  have hvB_fix₃ : ∀ g ∈ X₃, g • vB = vB := by
    intro g hg
    have hgB : g ∈ B := hX3B hg
    rw [hBfix] at hgB
    simp only [fixSU, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff] at hgB
    exact hgB vB (by simp)
  have hvB_mem₂ : vB ∈ Submodule.span K ({vA, x₂} : Set (Fin 4 → K)) :=
    mem_span_pair_of_fixed hK hvA hx₂ hvx₂ e₂ hX₂eq hvB_fix₂
  have hvB_mem₃ : vB ∈ Submodule.span K ({x₂, w} : Set (Fin 4 → K)) :=
    mem_span_pair_of_fixed hK hx₂ hw hx2w e₃ hX₃fix hvB_fix₃
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hvB_mem₂
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hvB_mem₃
  have ha0 : a = 0 := by
    have heq : a • vA + b • x₂ = c • x₂ + d • w := by rw [hab, ← hcd]
    have h := congrArg (herm σ vA) heq
    simp only [herm_add_right, herm_smul_right, hvA, hvx₂, hvw, mul_one, mul_zero,
      add_zero] at h
    simpa using h
  have hd0 : d = 0 := by
    have heq : a • vA + b • x₂ = c • x₂ + d • w := by rw [hab, ← hcd]
    have h := congrArg (herm σ w) heq
    simp only [herm_add_right, herm_smul_right, hw, hwvA, hwx₂, mul_zero, mul_one,
      add_zero] at h
    simpa using h.symm
  have hvB_eq : vB = b • x₂ := by rw [← hab, ha0, zero_smul, zero_add]
  have hb0 : b ≠ 0 := by
    intro hb
    have hvB0 : vB = 0 := by rw [hvB_eq, hb, zero_smul]
    rw [hvB0, herm_zero_left] at hvB
    exact zero_ne_one hvB
  rw [hBfix, hvB_eq, fixSU_smul_single hb0 x₂]

private theorem standardPair_fixed_vector (hK : Nat.card K = 4)
    {A X₁ X₂ : Subgroup (Su K 2 1 4)} (hP : UnitaryBlockStandardPair K 2 1 A X₁ X₂) :
    ∃ v : Fin 4 → K, herm σ v v = 1 ∧ A = fixSU {v} := by
  obtain ⟨θ, c, hrange, hker, hor⟩ := hP
  have hθinj : Function.Injective θ := injective_of_ker_le_center hK θ hker
  let e : Su K 2 1 3 ≃* A :=
    (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hrange)
  exact eq_fixSU_of_mulEquiv hK e

private theorem standardPair_le {A X₁ X₂ : Subgroup (Su K 2 1 4)}
    (hP : UnitaryBlockStandardPair K 2 1 A X₁ X₂) : X₁ ≤ A ∧ X₂ ≤ A := by
  obtain ⟨θ, c, hrange, hker, hor⟩ := hP
  constructor
  · rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h12, ← hrange]; exact Subgroup.map_le_range θ _
    · rw [← h23, ← hrange]; exact Subgroup.map_le_range θ _
  · rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h23, ← hrange]; exact Subgroup.map_le_range θ _
    · rw [← h12, ← hrange]; exact Subgroup.map_le_range θ _

private theorem standardPair_block_equiv (hK : Nat.card K = 4)
    {A X₁ X₂ : Subgroup (Su K 2 1 4)} (hP : UnitaryBlockStandardPair K 2 1 A X₁ X₂) :
    ∃ _e₁ : Su K 2 1 2 ≃* X₁, ∃ _e₂ : Su K 2 1 2 ≃* X₂, True := by
  obtain ⟨θ, c, hrange, hker, hor⟩ := hP
  rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
  · exact ⟨mulEquiv_of_standardBlock hK hker 2 (by simpa [B12] using h12),
      mulEquiv_of_standardBlock hK hker 0 (by simpa [B23] using h23), trivial⟩
  · exact ⟨mulEquiv_of_standardBlock hK hker 0 (by simpa [B23] using h23),
      mulEquiv_of_standardBlock hK hker 2 (by simpa [B12] using h12), trivial⟩

theorem a3_frame (hK : Nat.card K = 4) {A B X₁ X₂ X₃ : Subgroup (Su K 2 1 4)}
    (hA : UnitaryBlockStandardPair K 2 1 A X₁ X₂)
    (hB : UnitaryBlockStandardPair K 2 1 B X₂ X₃)
    (hAc : Nat.card A = 216)
    (hc : ∀ x ∈ X₁, ∀ y ∈ X₃, x * y = y * x) :
    ∃ g : Su K 2 1 4, let c := (MulAut.conj g).toMonoidHom
      A = (blk012 K).range.map c ∧ B = (blk123 K).range.map c ∧
      X₁ = ((B12 K 2 1).map (blk012 K)).map c ∧
      X₂ = ((B23 K 2 1).map (blk012 K)).map c ∧
      X₃ = ((B23 K 2 1).map (blk123 K)).map c := by
  classical
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨vA, hvA, hAfix⟩ := standardPair_fixed_vector hK hA
  obtain ⟨x₁, x₂, hx₁, hx₂, hvx₁, hvx₂, hx₁x₂, hX₁eq, hX₂eq⟩ :=
    fix_perp_of_standardPair hK hvA hAfix hA
  obtain ⟨_, e₂, -⟩ := standardPair_block_equiv hK hA
  obtain ⟨vB, hvB, hBfix⟩ := standardPair_fixed_vector hK hB
  obtain ⟨_, e₃, -⟩ := standardPair_block_equiv hK hB
  have hX2B : X₂ ≤ B := (standardPair_le hB).1
  have hX3B : X₃ ≤ B := (standardPair_le hB).2
  have _ := hAc
  obtain ⟨w, hw, hvw, hx1w, hx2w⟩ :=
    exists_orthonormal_four_of_three hK hvA hx₁ hx₂ hvx₁ hvx₂ hx₁x₂
  let u : Fin 4 → Fin 4 → K := ![x₂, w, x₁, vA]
  have hx₂vA : herm σ x₂ vA = 0 := herm_eq_zero_comm σ hσ.invol hvx₂
  have hx₂x₁ : herm σ x₂ x₁ = 0 := herm_eq_zero_comm σ hσ.invol hx₁x₂
  have hwx₁ : herm σ w x₁ = 0 := herm_eq_zero_comm σ hσ.invol hx1w
  have hwx₂ : herm σ w x₂ = 0 := herm_eq_zero_comm σ hσ.invol hx2w
  have hwvA : herm σ w vA = 0 := herm_eq_zero_comm σ hσ.invol hvw
  have hx₁vA : herm σ x₁ vA = 0 := herm_eq_zero_comm σ hσ.invol hvx₁
  have hon : ∀ j k : Fin 4, herm σ (u j) (u k) = if j = k then 1 else 0 := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      first
        | exact hvA | exact hx₁ | exact hx₂ | exact hw
        | exact hvx₁ | exact hvx₂ | exact hx₁x₂ | exact hvw
        | exact hx1w | exact hx2w | exact hx₂vA | exact hx₂x₁
        | exact hwx₁ | exact hwx₂ | exact hwvA | exact hx₁vA
  have hfixX1 : fixSU {u 2, u 3} = X₁ := by
    have hset : ({u 2, u 3} : Set (Fin 4 → K)) = {vA, x₁} := by
      ext z; simp [u, or_comm]
    rw [hset, ← hX₁eq]
  have hcomm : ∀ x ∈ X₃, ∀ y ∈ fixSU {u 2, u 3}, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ X₁ := by rwa [hfixX1] at hy
    exact (hc y hy' x hx).symm
  have hX₃eq : X₃ = fixSU {u 0, u 1} := eq_fixSU_of_commute hK hon e₃ hcomm
  have hX₃fix : X₃ = fixSU {x₂, w} := by
    rw [hX₃eq]
    congr 1
  have hBfix2 : B = fixSU {x₂} :=
    second_standardPair_line hK hvA hx₂ hvx₂ hx2w hw hvw hwvA hwx₂ hBfix hX2B hX3B e₂ e₃
      hX₂eq hX₃fix hvB
  obtain ⟨g, a0, ha0, hset0, hset1, hset3s, hset2, hset3, hset4⟩ := exists_frame_element hon
  refine ⟨g, ?_⟩
  dsimp only
  exact frame_element_images g a0 hAfix hBfix2 hX₁eq hX₂eq hX₃fix hset0 hset3s
    hset2 hset3 hset4 ha0

private theorem exists_lift_hom {G : Type*} [Group G] {θ : Su K 2 1 4 →* G}
    (hθinj : Function.Injective θ) {W : Subgroup G} (hW : W ≤ θ.range)
    {φ : Su K 2 1 3 →* G} (hφ : φ.range = W)
    (hker : φ.ker ≤ Subgroup.center (Su K 2 1 3)) :
    ∃ φ' : Su K 2 1 3 →* Su K 2 1 4, θ.comp φ' = φ ∧ φ'.range = W.comap θ ∧
      φ'.ker ≤ Subgroup.center (Su K 2 1 3) := by
  let eθ : Su K 2 1 4 ≃* θ.range := MonoidHom.ofInjective hθinj
  let φc : Su K 2 1 3 →* θ.range :=
    φ.codRestrict θ.range fun x => hW (hφ ▸ ⟨x, rfl⟩)
  let φ' : Su K 2 1 3 →* Su K 2 1 4 := eθ.symm.toMonoidHom.comp φc
  have hcomp : θ.comp φ' = φ := by
    ext x
    change θ (eθ.symm (φc x)) = φ x
    rw [← MonoidHom.ofInjective_apply hθinj (x := eθ.symm (φc x))]
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hrange' : φ'.range = W.comap θ := by
    apply Subgroup.map_injective hθinj
    rw [← MonoidHom.range_comp θ φ', hcomp, hφ, Subgroup.map_comap_eq_self hW]
  have hker' : φ'.ker ≤ Subgroup.center (Su K 2 1 3) := by
    intro x hx
    apply hker
    have hx' : (θ.comp φ') x = 1 := by rw [MonoidHom.comp_apply, show φ' x = 1 from hx,
      map_one]
    rw [hcomp] at hx'
    exact hx'
  exact ⟨φ', hcomp, hrange', hker'⟩

private theorem theta_injective_of_standardPair (hK : Nat.card K = 4) {G : Type} [Group G]
    {U₁ U₂ W₁₂ : Subgroup G}
    (hP₁ : UnitaryBlockStandardPair K 2 1 W₁₂ U₁ U₂)
    {θ : Su K 2 1 4 →* G} (hW : W₁₂ ≤ θ.range) : Function.Injective θ := by
  classical
  obtain ⟨θ₁, c₁, hrange₁, hker₁, hor₁⟩ := hP₁
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := by
    have h : unitaryInvolution K 2 1 ω = ω ^ 2 := by
      rw [unitaryInvolution_apply]; norm_num
    rw [h] at hω
    calc ω ^ 3 = ω ^ 2 * ω := by ring
      _ = 1 := hω
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  let uω : normOne σ := ⟨Units.mk0 ω hω0, by
    change σ ω * ω = 1
    exact hω⟩
  have huω3 : uω ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((Units.mk0 ω hω0 : Kˣ) : K) ^ 3 = 1
    simp [hω3]
  have htorus3 : (torusTwo σ uω) ^ 3 = 1 := by
    rw [← map_pow, huω3, map_one]
  have htorus_ne : torusTwo σ uω ≠ 1 := by
    intro h
    have hu : uω = 1 := torusTwo_injective _ (by simpa using h)
    apply hω1
    have huK : ((uω : Kˣ) : K) = 1 := by
      rw [show (uω : Kˣ) = 1 from congrArg Subtype.val hu, Units.val_one]
    simpa [uω] using huK
  have hinj1 : Function.Injective (θ₁.comp (embSUid σ 2)) :=
    comp_embSUid_injective (p := 2) (f := 1) hK hker₁ 2
  have hyne : θ₁ (embSUid σ 2 (torusTwo σ uω)) ≠ 1 := by
    intro h
    have h1 : (θ₁.comp (embSUid σ 2)) (torusTwo σ uω) =
        (θ₁.comp (embSUid σ 2)) 1 := by
      simpa using h
    exact htorus_ne (hinj1 h1)
  have hymem : θ₁ (embSUid σ 2 (torusTwo σ uω)) ∈ W₁₂ := by
    rw [← hrange₁]
    exact ⟨_, rfl⟩
  have hyrange : θ₁ (embSUid σ 2 (torusTwo σ uω)) ∈ θ.range := hW hymem
  obtain ⟨x, hx⟩ := hyrange
  exact injective_of_exists_ne_one hK θ ⟨x, by rw [hx]; exact hyne⟩

private theorem pullback_standardPair {G : Type} [Group G] {θ : Su K 2 1 4 →* G}
    (hθinj : Function.Injective θ) {W U V : Subgroup G} (hW : W ≤ θ.range)
    (hP : UnitaryBlockStandardPair K 2 1 W U V) :
    ∃ φ : Su K 2 1 3 →* Su K 2 1 4, φ.range = W.comap θ ∧
      φ.ker ≤ Subgroup.center (Su K 2 1 3) ∧
      UnitaryBlockStandardPair K 2 1 (W.comap θ) (U.comap θ) (V.comap θ) := by
  classical
  obtain ⟨θ₀, c, hrange, hker, hor⟩ := hP
  have hUW : U ≤ W := by
    rw [← hrange]
    rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h12]; exact Subgroup.map_le_range θ₀ _
    · rw [← h23]; exact Subgroup.map_le_range θ₀ _
  have hVW : V ≤ W := by
    rw [← hrange]
    rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h23]; exact Subgroup.map_le_range θ₀ _
    · rw [← h12]; exact Subgroup.map_le_range θ₀ _
  have hUle : U ≤ θ.range := le_trans hUW hW
  have hVle : V ≤ θ.range := le_trans hVW hW
  obtain ⟨φ, hcomp, hrange', hker'⟩ := exists_lift_hom hθinj hW hrange hker
  have pull_image {i : Fin 3} {T : Subgroup G} (hTle : T ≤ θ.range)
      (h : (((embSUid σ i).range).map (MulAut.conj c⁻¹).toMonoidHom).map θ₀ = T) :
      (((embSUid σ i).range).map (MulAut.conj c⁻¹).toMonoidHom).map φ = T.comap θ := by
    apply Subgroup.map_injective hθinj
    rw [Subgroup.map_map, hcomp, h, Subgroup.map_comap_eq_self hTle]
  refine ⟨φ, hrange', hker', ?_⟩
  refine ⟨φ, c, hrange', hker', ?_⟩
  rcases hor with ⟨h12, h23⟩ | ⟨h12, h23⟩
  · exact Or.inl ⟨pull_image hUle h12, pull_image hVle h23⟩
  · exact Or.inr ⟨pull_image hVle h12, pull_image hUle h23⟩

private theorem a3_marking_labelling {G : Type} [Group G] {θ : Su K 2 1 4 →* G}
    (hθinj : Function.Injective θ)
    {A B X₁ X₂ X₃ : Subgroup (Su K 2 1 4)}
    {W₁₂ W₂₃ U₁ U₂ U₃ : Subgroup G}
    (hA : A = W₁₂.comap θ) (hB : B = W₂₃.comap θ)
    (hX₁ : X₁ = U₁.comap θ) (hX₂ : X₂ = U₂.comap θ) (hX₃ : X₃ = U₃.comap θ)
    (hW₁₂ : W₁₂ ≤ θ.range) (hW₂₃ : W₂₃ ≤ θ.range)
    (hU₁ : U₁ ≤ θ.range) (hU₂ : U₂ ≤ θ.range) (hU₃ : U₃ ≤ θ.range)
    (g : Su K 2 1 4)
    (hAimg : A = ((blk012 K).range).map (MulAut.conj g).toMonoidHom)
    (hBimg : B = ((blk123 K).range).map (MulAut.conj g).toMonoidHom)
    (hX₁img : X₁ = (((B12 K 2 1).map (blk012 K)).map
      (MulAut.conj g).toMonoidHom))
    (hX₂img : X₂ = (((B23 K 2 1).map (blk012 K)).map
      (MulAut.conj g).toMonoidHom))
    (hX₃img : X₃ = (((B23 K 2 1).map (blk123 K)).map
      (MulAut.conj g).toMonoidHom)) :
    ∃ κ : Su K 2 1 4 →* G, Function.Injective κ ∧
      (κ.comp (blk012 K)).range = W₁₂ ∧
      (κ.comp (blk123 K)).range = W₂₃ ∧
      (B12 K 2 1).map (κ.comp (blk012 K)) = U₁ ∧
      (B23 K 2 1).map (κ.comp (blk012 K)) = U₂ ∧
      (B23 K 2 1).map (κ.comp (blk123 K)) = U₃ := by
  let κ : Su K 2 1 4 →* G := θ.comp (MulAut.conj g).toMonoidHom
  have hκinj : Function.Injective κ := hθinj.comp (MulAut.conj g).injective
  refine ⟨κ, hκinj, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (κ.comp (blk012 K)).range =
        (((blk012 K).range).map (MulAut.conj g).toMonoidHom).map θ := by
      rw [MonoidHom.range_comp, Subgroup.map_map]
    rw [h, ← hAimg, hA, Subgroup.map_comap_eq_self hW₁₂]
  · have h : (κ.comp (blk123 K)).range =
        (((blk123 K).range).map (MulAut.conj g).toMonoidHom).map θ := by
      rw [MonoidHom.range_comp, Subgroup.map_map]
    rw [h, ← hBimg, hB, Subgroup.map_comap_eq_self hW₂₃]
  · have h : (B12 K 2 1).map (κ.comp (blk012 K)) =
        ((((B12 K 2 1).map (blk012 K)).map
          (MulAut.conj g).toMonoidHom)).map θ := by
      rw [show κ.comp (blk012 K) =
        (θ.comp (MulAut.conj g).toMonoidHom).comp (blk012 K) by rfl]
      rw [Subgroup.map_map, Subgroup.map_map]
    rw [h, ← hX₁img, hX₁, Subgroup.map_comap_eq_self hU₁]
  · have h : (B23 K 2 1).map (κ.comp (blk012 K)) =
        ((((B23 K 2 1).map (blk012 K)).map
          (MulAut.conj g).toMonoidHom)).map θ := by
      rw [show κ.comp (blk012 K) =
        (θ.comp (MulAut.conj g).toMonoidHom).comp (blk012 K) by rfl]
      rw [Subgroup.map_map, Subgroup.map_map]
    rw [h, ← hX₂img, hX₂, Subgroup.map_comap_eq_self hU₂]
  · have h : (B23 K 2 1).map (κ.comp (blk123 K)) =
        ((((B23 K 2 1).map (blk123 K)).map
          (MulAut.conj g).toMonoidHom)).map θ := by
      rw [show κ.comp (blk123 K) =
        (θ.comp (MulAut.conj g).toMonoidHom).comp (blk123 K) by rfl]
      rw [Subgroup.map_map, Subgroup.map_map]
    rw [h, ← hX₃img, hX₃, Subgroup.map_comap_eq_self hU₃]

theorem qTwoA3Mark_holds : QTwoA3Mark := by
  intro K _ _ _ hK G _ U₁ U₂ U₃ W₁₂ W₂₃ hP₁ hP₂ hc θrange
  obtain ⟨θ, hrange⟩ := θrange
  classical
  have hW12le : W₁₂ ≤ θ.range := by rw [hrange]; exact le_sup_left
  have hW23le : W₂₃ ≤ θ.range := by rw [hrange]; exact le_sup_right
  have hθinj : Function.Injective θ := theta_injective_of_standardPair hK hP₁ hW12le
  obtain ⟨φ₁, hrange₁', hker₁', hP₁'⟩ := pullback_standardPair hθinj hW12le hP₁
  obtain ⟨φ₂, hrange₂', hker₂', hP₂'⟩ := pullback_standardPair hθinj hW23le hP₂
  let A : Subgroup (Su K 2 1 4) := W₁₂.comap θ
  let B : Subgroup (Su K 2 1 4) := W₂₃.comap θ
  let X₁ : Subgroup (Su K 2 1 4) := U₁.comap θ
  let X₂ : Subgroup (Su K 2 1 4) := U₂.comap θ
  let X₃ : Subgroup (Su K 2 1 4) := U₃.comap θ
  obtain ⟨θ₁, c₁, hrange₁, hker₁, hor₁⟩ := hP₁
  obtain ⟨θ₂, c₂, hrange₂, hker₂, hor₂⟩ := hP₂
  have hU1W : U₁ ≤ W₁₂ := by
    rcases hor₁ with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h12, ← hrange₁]; exact Subgroup.map_le_range θ₁ _
    · rw [← h23, ← hrange₁]; exact Subgroup.map_le_range θ₁ _
  have hU2W : U₂ ≤ W₁₂ := by
    rcases hor₁ with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h23, ← hrange₁]; exact Subgroup.map_le_range θ₁ _
    · rw [← h12, ← hrange₁]; exact Subgroup.map_le_range θ₁ _
  have hU3W : U₃ ≤ W₂₃ := by
    rcases hor₂ with ⟨h12, h23⟩ | ⟨h12, h23⟩
    · rw [← h23, ← hrange₂]; exact Subgroup.map_le_range θ₂ _
    · rw [← h12, ← hrange₂]; exact Subgroup.map_le_range θ₂ _
  have hU1le : U₁ ≤ θ.range := le_trans hU1W hW12le
  have hU2le : U₂ ≤ θ.range := le_trans hU2W hW12le
  have hU3le : U₃ ≤ θ.range := le_trans hU3W hW23le
  have hAinj : Function.Injective φ₁ := injective_of_ker_le_center hK φ₁ hker₁'
  have hAc : Nat.card A = 216 := by
    calc Nat.card A = Nat.card φ₁.range := by rw [hrange₁']
      _ = Nat.card (Su K 2 1 3) :=
        (Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv).symm
      _ = 216 := CFSG.StandardType.QTwo.qTwoS34_card_Su_three hK
  have hc' : ∀ x ∈ X₁, ∀ y ∈ X₃, x * y = y * x := by
    intro x hx y hy
    apply hθinj
    rw [map_mul, map_mul]
    exact hc (θ x) hx (θ y) hy
  obtain ⟨g, hgA, hgB, hgX₁, hgX₂, hgX₃⟩ :=
    a3_frame hK hP₁' hP₂' hAc hc'
  exact a3_marking_labelling hθinj rfl rfl rfl rfl rfl hW12le hW23le hU1le hU2le hU3le
    g hgA hgB hgX₁ hgX₂ hgX₃

end CFSG.ClassicalInvolution.PhanDn.QTwo
