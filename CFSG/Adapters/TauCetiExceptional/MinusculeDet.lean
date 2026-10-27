module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdInv
public import CFSG.LieType.Steinberg.CoreBasic

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid)
include hV

theorem deg_of_rootMat_ne_zero
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {a b : Fin D.d}
    (h : rootMat D γ b a ≠ 0) : D.deg b = D.deg a + D.scale * ht γ :=
  hV.deg_eq_add (rootMat_ne_zero hV hγ h).1

theorem det_natMat_rootUnit
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hht : ht γ ≠ 0)
    (R : Type*) [CommRing R] (c : R) :
    (natMat R (rootUnit hV R γ c : Module.End R (Fin D.d →₀ R))).det = 1 := by
  classical
  set b : Fin D.d → ℤ := fun a => -(ht γ) * D.deg a with hb
  have hlt : ∀ i j : Fin D.d, rootMat D γ i j ≠ 0 → b i < b j := by
    intro i j h
    have e := deg_of_rootMat_ne_zero hV hγ h
    have h2 : 0 < (D.scale : ℤ) * (ht γ * ht γ) :=
      mul_pos (by exact_mod_cast hV.scale_pos) (mul_self_pos.2 hht)
    simp only [hb, e]
    nlinarith
  rw [natMat_rootUnit]
  have hM : (1 + c • (rootMat D γ).map (Int.cast : ℤ → R)).BlockTriangular b := by
    intro i j hji
    have hij : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.smul_apply, Matrix.map_apply]
    by_cases h : rootMat D γ i j = 0
    · rw [h, Int.cast_zero, smul_zero, zero_add]
    · exact absurd (hlt i j h) (not_lt.2 hji.le)
  rw [hM.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have : (1 + c • (rootMat D γ).map (Int.cast : ℤ → R)).toSquareBlock b k = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, Subtype.mk.injEq]
    by_cases h : rootMat D γ i j = 0
    · simp [h]
    · exact absurd (hlt i j h) (by rw [hi, hj]; exact lt_irrefl _)
  rw [this, Matrix.det_one]

theorem det_natMat_eq_one
    (K : Type*) [Field K] (g : hV.minGroup K) :
    (natMat K (hV.endo K g)).det = 1 := by
  let f : Module.End K (Fin D.d →₀ K) →* K :=
    { toFun := fun x => (natMat K x).det
      map_one' := by rw [map_one, Matrix.det_one]
      map_mul' := fun x y => by rw [map_mul, Matrix.det_mul] }
  have hf : ∀ x : (Module.End K (Fin D.d →₀ K))ˣ, x ∈ (Units.map f).ker ↔
      (natMat K (x : Module.End K (Fin D.d →₀ K))).det = 1 := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
    rfl
  have hle : hV.minGroup K ≤ (Units.map f).ker := minGroup_le_of_simple hV K fun i c =>
    ⟨(hf _).2 (det_natMat_rootUnit hV (IsRoot.basis i) (by rw [ht_single]; norm_num) K c),
      (hf _).2 (det_natMat_rootUnit hV (isRoot_neg_single τ i)
        (by rw [ht_neg, ht_single]; norm_num) K c)⟩
  exact (hf _).1 (hle g.2)

end CFSG.TauCetiBridge.Minuscule
