module

public import CFSG.CGT.Stroth77.Types3Exclusion
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitGL
public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {k : Fin 3 → ℕ}

theorem exists_intertwiner_uv_u_of_gl32 {G : Type} [Group G] {D : Subgroup G}
    (A : SigmaFourAction k) (e : Additive D ≃+ Torus k) {uv u : G}
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D, e (Additive.ofMul (conjBy huv x)) = A.φuv (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D, e (Additive.ofMul (conjBy hu x)) = A.φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (hu2 : u * u = 1) (huv1 : A.φuv ≠ AddMonoidHom.id _)
    (hu1 : A.φu ≠ AddMonoidHom.id _)
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) :
    ∃ g : Torus k ≃+ Torus k, ∀ x, g (A.φuv x) = A.φu (g x) := by
  have hcent : ∀ y : Subgroup.normalizer (D : Set G), φ y = 1 →
      ∀ x ∈ D, x * (y : G) = (y : G) * x := by
    intro y hy x hx
    have hy' : y ∈ (Subgroup.centralizer (D : Set G)).subgroupOf
        (Subgroup.normalizer (D : Set G)) := by
      rw [← hker]
      exact hy
    exact (Subgroup.mem_centralizer_iff.mp hy') x hx
  have hne : ∀ {w : G} (hw : w ∈ Subgroup.normalizer (D : Set G)) {f : Torus k →+ Torus k},
      (∀ x : D, e (Additive.ofMul (conjBy hw x)) = f (e (Additive.ofMul x))) →
      f ≠ AddMonoidHom.id _ → φ ⟨w, hw⟩ ≠ 1 := by
    intro w hw f hconj hf h1
    apply hf
    refine AddMonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ : ∃ x : D, e (Additive.ofMul x) = z :=
      ⟨Additive.toMul (e.symm z), by simp⟩
    rw [← hconj, AddMonoidHom.id_apply]
    congr 1
    apply Subtype.ext
    change w⁻¹ * (x : G) * w = x
    rw [mul_assoc, hcent ⟨w, hw⟩ h1 x x.2, inv_mul_cancel_left]
  have hsq : ∀ {w : G} (hw : w ∈ Subgroup.normalizer (D : Set G)), w * w = 1 →
      φ ⟨w, hw⟩ * φ ⟨w, hw⟩ = 1 := by
    intro w hw h
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext h
  obtain ⟨c, hc⟩ := CFSG.OddStandard.ChengHeld.GL32Inv.GL3_involutions_conjugate
    (φ ⟨uv, huv⟩) (φ ⟨u, hu⟩) (hne huv huv_conj huv1) (hsq huv huv2) (hne hu hu_conj hu1)
    (hsq hu hu2)
  obtain ⟨h, rfl⟩ := hφ c
  have hz : φ ((h⁻¹ * ⟨uv, huv⟩ * h)⁻¹ * ⟨u, hu⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
  have hzc := hcent _ hz
  have huz : u = (h : G)⁻¹ * uv * h *
      (((h⁻¹ * ⟨uv, huv⟩ * h)⁻¹ * ⟨u, hu⟩ : Subgroup.normalizer (D : Set G)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hh : (h : G) ∈ Subgroup.normalizer (D : Set G) := h.2
  let cH : D ≃* D :=
    { toFun := conjBy hh
      invFun := conjBy (Subgroup.inv_mem _ hh)
      left_inv := fun x => Subtype.ext (by simp [conjBy, mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [conjBy, mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [conjBy, mul_assoc]) }
  refine ⟨e.symm.trans ((MulEquiv.toAdditive cH).trans e), fun w => ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x : D, e (Additive.ofMul x) = w :=
    ⟨Additive.toMul (e.symm w), by simp⟩
  rw [← huv_conj]
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul]
  rw [← hu_conj]
  congr 2
  apply Subtype.ext
  change (h : G)⁻¹ * (uv⁻¹ * (x : G) * uv) * h = u⁻¹ * ((h : G)⁻¹ * (x : G) * h) * u
  have hy : (h : G)⁻¹ * (uv⁻¹ * (x : G) * uv) * h ∈ D :=
    (conjBy hh (conjBy huv x)).2
  set z : G := (((h⁻¹ * ⟨uv, huv⟩ * h)⁻¹ * ⟨u, hu⟩ : Subgroup.normalizer (D : Set G)) : G)
  have key : z⁻¹ * ((h : G)⁻¹ * (uv⁻¹ * (x : G) * uv) * h) * z =
      (h : G)⁻¹ * (uv⁻¹ * (x : G) * uv) * h := by
    rw [mul_assoc, hzc _ hy, inv_mul_cancel_left]
  rw [huz, ← key]
  group

theorem matAct_ne_id {M : IntMat} (hM : Compat k M) {i j : Fin 3} (hj : 1 ≤ k j)
    (hodd : ¬ 2 ∣ (Pi.single i 1 : Fin 3 → ℤ) j - (M *ᵥ Pi.single i 1) j) :
    matAct k M hM ≠ AddMonoidHom.id _ := by
  intro h
  have h1 := DFunLike.congr_fun h (vecZ k (Pi.single i 1))
  rw [matAct_vecZ, AddMonoidHom.id_apply, vecZ_eq_iff] at h1
  exact hodd ((dvd_pow_self 2 (by omega : k j ≠ 0)).trans (h1 j))

variable {G : Type} [Group G] {D : Subgroup G} {uv u : G}

theorem false_of_gl32_type300 {n : ℕ} (hn : 2 ≤ n) (e : Additive D ≃+ Torus (Type300.k n))
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D,
      e (Additive.ofMul (conjBy huv x)) = (Type300.action n).φuv (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type300.action n).φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (hu2 : u * u = 1)
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) : False := by
  have hk : ∀ i, 1 ≤ Type300.k n i := fun i => by fin_cases i <;> (change 1 ≤ n; omega)
  obtain ⟨g, hg⟩ := exists_intertwiner_uv_u_of_gl32 (Type300.action n) e huv hu huv_conj hu_conj
    huv2 hu2 (matAct_ne_id _ (i := 0) (j := 2) (hk 2) (by
      simp [Type300.action, SigmaFourAction.ofMatEq, Type300.uvM, Type300.uvA, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]))
    (matAct_ne_id _ (i := 1) (j := 1) (hk 1) (by
      simp [Type300.action, SigmaFourAction.ofMatEq, Type300.uM, uMat, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three])) φ hφ hker
  exact not_intertwine_uv_u_type300 hn g hg

theorem false_of_gl32_type310 {m : ℕ} (hm : 3 ≤ m) (e : Additive D ≃+ Torus (Type310.k m))
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D, e (Additive.ofMul (conjBy huv x)) =
      (Type310.action m (by omega)).φuv (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D, e (Additive.ofMul (conjBy hu x)) =
      (Type310.action m (by omega)).φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (hu2 : u * u = 1)
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) : False := by
  have hk : ∀ i, 1 ≤ Type310.k m i := fun i => by fin_cases i <;> (change 1 ≤ m; omega)
  obtain ⟨g, hg⟩ := exists_intertwiner_uv_u_of_gl32 (Type310.action m (by omega)) e huv hu
    huv_conj hu_conj huv2 hu2 (matAct_ne_id _ (i := 0) (j := 2) (hk 2) (by
      simp [Type310.action, SigmaFourAction.ofMatEq, Type310.uvM, Type310.uvA, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]))
    (matAct_ne_id _ (i := 1) (j := 1) (hk 1) (by
      simp [Type310.action, SigmaFourAction.ofMatEq, Type310.uM, uMat, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three])) φ hφ hker
  exact not_intertwine_uv_u_type310 hm g hg

theorem false_of_gl32_type330 {m : ℕ} (hm : 3 ≤ m) (e : Additive D ≃+ Torus (Type330.k m))
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D,
      e (Additive.ofMul (conjBy huv x)) = (Type330.actionPaper m hm).φuv (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type330.actionPaper m hm).φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (hu2 : u * u = 1)
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) : False := by
  have hk : ∀ i, 1 ≤ Type330.k m i := fun i => by fin_cases i <;> (change 1 ≤ m; omega)
  obtain ⟨g, hg⟩ := exists_intertwiner_uv_u_of_gl32 (Type330.actionPaper m hm) e huv hu
    huv_conj hu_conj huv2 hu2 (matAct_ne_id _ (i := 0) (j := 2) (hk 2) (by
      simp [Type330.actionPaper, Type330.action, SigmaFourAction.ofMatEq, Type330.uvM,
        Type330.uvA, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]))
    (matAct_ne_id _ (i := 1) (j := 1) (hk 1) (by
      simp [Type330.actionPaper, Type330.action, SigmaFourAction.ofMatEq, Type330.uM, uMat,
        ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three])) φ hφ hker
  exact not_intertwine_uv_u_type330 hm g hg

theorem false_of_gl32_type331 (e : Additive D ≃+ Torus Type331.k)
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D,
      e (Additive.ofMul (conjBy huv x)) = Type331.action.φuv (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = Type331.action.φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (hu2 : u * u = 1)
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) : False := by
  have hk : ∀ i, 1 ≤ Type331.k i := fun i => by fin_cases i <;> decide
  obtain ⟨g, hg⟩ := exists_intertwiner_uv_u_of_gl32 Type331.action e huv hu huv_conj hu_conj
    huv2 hu2 (matAct_ne_id _ (i := 0) (j := 2) (hk 2) (by
      simp [Type331.action, SigmaFourAction.ofMatEq, Type331.uvM, Type331.uvA, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]))
    (matAct_ne_id _ (i := 1) (j := 1) (hk 1) (by
      simp [Type331.action, SigmaFourAction.ofMatEq, Type331.uM, uMat, ofCols_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three])) φ hφ hker
  exact not_intertwine_uv_u_type331 g hg

end CFSG.CGT.Stroth77
