module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerpIsotropicLe
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] {n f : ℕ}

theorem exists_statedSU_eichler (h : UnitaryFieldData 2 f K) {a b : Fin n → K} {c : K}
    (ha : stdHermForm h n a a = 0) (hab : stdHermForm h n a b = 0)
    (hc : c + h.bar c + stdHermForm h n b b = 0) :
    ∃ y : StatedSU n (2 ^ f) K, ∀ x, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      eichlerMap (stdHermForm h n) a b c x := by
  have hB := stdHermForm_isSymm h n
  have hba : stdHermForm h n b a = 0 := by rw [← hB.eq a b, hab, map_zero]
  have hiso := eichlerMap_isometry hB ha hab hc
  have hdet := det_eichlerMap ha hab hba c
  set g := eichlerMap (stdHermForm h n) a b c with hg
  have hMdet : (LinearMap.toMatrix' g).det = 1 := by rw [LinearMap.det_toMatrix']; exact hdet
  have hM : ∀ x, LinearMap.toMatrix' g *ᵥ x = g x := LinearMap.toMatrix'_mulVec g
  let y : GL (Fin n) K :=
    Matrix.GeneralLinearGroup.mk'' (LinearMap.toMatrix' g) (by rw [hMdet]; exact isUnit_one)
  have hy : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' g := rfl
  refine ⟨⟨y, ?_⟩, fun x => by rw [hy]; exact hM x⟩
  rw [mem_unitarySU_iff_isometry h]
  refine ⟨by rw [hy]; exact hMdet, fun x x' => ?_⟩
  rw [hy, hM, hM]
  exact hiso x x'

theorem eq_of_stable_isotropic (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {I : Set ℕ} (hIfin : I.Finite) {W : ℕ → Submodule K (Fin n → K)}
    (hWiso : ∀ i ∈ I, IsTotallyIsotropicSU (2 ^ f) (W i))
    (hWle : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j)
    (hWdim : ∀ i ∈ I, Module.finrank K (W i) = i)
    {T : Submodule K (Fin n → K)} (hTiso : IsTotallyIsotropicSU (2 ^ f) T)
    (hT : ∀ y : StatedSU n (2 ^ f) K,
      (∀ i ∈ I, ∀ w ∈ W i, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i) →
      ∀ x ∈ T, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ T)
    {k : ℕ} (hk : k ∈ I) (hTdim : Module.finrank K T = k) : T = W k := by
  classical
  set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
  have hchar : CharP K 2 := h.charP
  have hB : (stdHermForm h n).IsSymm := stdHermForm_isSymm h n
  have hBs : (stdHermForm h n).SeparatingLeft := stdHermForm_separatingLeft h n
  have hsymm : ∀ a b, (stdHermForm h n) a b = 0 → (stdHermForm h n) b a = 0 := fun a b hab => by
    rw [← hB.eq a b, hab, map_zero]
  have hWiso' : ∀ i ∈ I, ∀ v ∈ W i, ∀ w ∈ W i, (stdHermForm h n) v w = 0 := fun i hi =>
    (ToralCensus.isTotallyIsotropicSU_iff h (W i)).mp (hWiso i hi)
  have hTiso' : ∀ v ∈ T, ∀ w ∈ T, (stdHermForm h n) v w = 0 :=
    (ToralCensus.isTotallyIsotropicSU_iff h T).mp hTiso
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image I id hIfin ⟨k, hk⟩
  have hcancel : ∀ (a : Fin n → K) (s : K), a ∉ T → s • a ∈ T → s = 0 := by
    intro a s haT hax
    by_contra hne
    exact haT (by simpa [smul_smul, inv_mul_cancel₀ hne] using T.smul_mem s⁻¹ hax)
  have hTm : T ≤ W m := by
    refine le_of_isotropic_orthogonal h hB hBs (hWiso' m hm) (fun v hv => hTiso' v hv v hv) ?_
    intro b hb0 hbX v hv
    obtain ⟨y, hy⟩ := exists_statedSU_eichler h (a := b) (b := 0) (c := 1) hb0
      (by simp) (by simp [CharTwo.add_self_eq_zero] )
    have hstab : ∀ i ∈ I, ∀ w ∈ W i,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i := by
      intro i hi w hw
      rw [hy, eichlerMap_apply]
      have : (stdHermForm h n) b w = 0 := hsymm _ _ (hbX w (hWle i hi m hm (hmax i hi) hw))
      simpa [this] using hw
    have h1 := hT y hstab v hv
    rw [hy, eichlerMap_apply] at h1
    have h2 : v + (stdHermForm h n) b v • b ∈ T := by simpa using h1
    have h3 : (stdHermForm h n) b v • b ∈ T := by simpa using T.sub_mem h2 hv
    by_cases hbT : b ∈ T
    · exact hTiso' b hbT v hv
    · exact hcancel b _ hbT h3
  have hWkT : W k ≤ T := by
    by_contra hnle
    obtain ⟨a, haW, haT⟩ := Set.not_subset.mp hnle
    have hTk : T ≤ W k := by
      refine le_of_isotropic_orthogonal h hB hBs (hWiso' k hk) (fun v hv => hTiso' v hv v hv) ?_
      intro b hb0 hbX v hv
      have hab : (stdHermForm h n) a b = 0 := hbX a haW
      obtain ⟨y, hy⟩ := exists_statedSU_eichler h (a := a) (b := b) (c := 0)
        (hWiso' k hk a haW a haW) hab (by simp [hb0])
      have hstab : ∀ i ∈ I, ∀ w ∈ W i,
          ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i := by
        intro i hi w hw
        rw [hy, eichlerMap_apply]
        rcases le_total i k with hik | hki
        · have hwk : w ∈ W k := hWle i hi k hk hik hw
          have h1 : (stdHermForm h n) a w = 0 := hWiso' k hk a haW w hwk
          have h2 : (stdHermForm h n) b w = 0 := hsymm _ _ (hbX w hwk)
          simpa [h1, h2] using hw
        · have hak : a ∈ W i := hWle k hk i hi hki haW
          have h1 : (stdHermForm h n) a w = 0 := hWiso' i hi a hak w hw
          simpa [h1] using W i |>.sub_mem hw (W i |>.smul_mem ((stdHermForm h n) b w) hak)
      have h1 := hT y hstab v hv
      rw [hy, eichlerMap_apply] at h1
      have hav : (stdHermForm h n) a v = 0 := hWiso' m hm a (hWle k hk m hm (hmax k hk) haW) v (hTm hv)
      have h2 : v - (stdHermForm h n) b v • a ∈ T := by simpa [hav] using h1
      have h3 : (stdHermForm h n) b v • a ∈ T := by
        have := T.sub_mem hv h2
        simpa using this
      exact hcancel a _ haT h3
    exact haT ((Submodule.eq_of_le_of_finrank_eq hTk (by rw [hTdim, hWdim k hk])).symm ▸ haW)
  exact (Submodule.eq_of_le_of_finrank_eq hWkT (by rw [hTdim, hWdim k hk])).symm

theorem inv_mul_mul_mem_statedSU (h : UnitaryFieldData 2 f K) {u : GL (Fin n) K}
    (hu : ∀ x y : Fin n → K, stdHermForm h n ((u : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((u : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    {y : GL (Fin n) K} (hy : y ∈ StatedSU n (2 ^ f) K) :
    u⁻¹ * y * u ∈ StatedSU n (2 ^ f) K := by
  have hy' := (mem_unitarySU_iff_isometry h).mp hy
  have hinv : ∀ a b : Fin n → K, stdHermForm h n (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a)
      (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b) = stdHermForm h n a b := by
    intro a b
    have := hu (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a)
      (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b)
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, one_mulVec] at this
    exact this.symm
  rw [mem_unitarySU_iff_isometry h]
  refine ⟨?_, fun x x' => ?_⟩
  · have h1 : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
        (u : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    simp only [Units.val_mul, det_mul, hy'.1]
    linear_combination h1
  · simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hinv, hy'.2, hu]

theorem stabilizes_of_normalizes (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {I : Set ℕ} (hIfin : I.Finite) {W : ℕ → Submodule K (Fin n → K)}
    (hWiso : ∀ i ∈ I, IsTotallyIsotropicSU (2 ^ f) (W i))
    (hWle : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j)
    (hWdim : ∀ i ∈ I, Module.finrank K (W i) = i)
    (J : Subgroup (StatedSU n (2 ^ f) K))
    (hJ : ∀ y : StatedSU n (2 ^ f) K, y ∈ J ↔
      ∀ i ∈ I, ∀ w ∈ W i, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i)
    (u : GL (Fin n) K)
    (hu : ∀ x y : Fin n → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) n
        ((u : Matrix (Fin n) (Fin n) K) *ᵥ x) ((u : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) n x y)
    (hnorm : ∀ y y' : StatedSU n (2 ^ f) K, (y' : GL (Fin n) K) = u * y * u⁻¹ →
      (y ∈ J ↔ y' ∈ J)) :
    ∀ i ∈ I, ∀ w ∈ W i, ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i := by
  classical
  set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
  set U : Matrix (Fin n) (Fin n) K := (u : Matrix (Fin n) (Fin n) K) with hU
  intro i hi w hw
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofLinearMap (mulVecLin U)
      (mulVecLin ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (by rw [← mulVecLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mulVecLin_one])
      (by rw [← mulVecLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulVecLin_one])
  set T : Submodule K (Fin n → K) := (W i).map (mulVecLin U) with hT
  have hTiso : IsTotallyIsotropicSU (2 ^ f) T := by
    rw [ToralCensus.isTotallyIsotropicSU_iff h]
    rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hu]
    exact (ToralCensus.isTotallyIsotropicSU_iff h (W i)).mp (hWiso i hi) v hv v' hv'
  have hTdim : Module.finrank K T = i := by
    rw [← hWdim i hi]
    exact LinearEquiv.finrank_map_eq e (W i)
  have hTstab : ∀ y : StatedSU n (2 ^ f) K,
      (∀ j ∈ I, ∀ w ∈ W j, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W j) →
      ∀ x ∈ T, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ T := by
    intro y hy x hx
    obtain ⟨v, hv, rfl⟩ := hx
    set y'' : StatedSU n (2 ^ f) K :=
      ⟨u⁻¹ * (y : GL (Fin n) K) * u, inv_mul_mul_mem_statedSU h hu y.2⟩ with hy''
    have hyy : ((y : GL (Fin n) K)) = u * (y'' : GL (Fin n) K) * u⁻¹ := by
      simp only [hy'']
      group
    have h1 : y'' ∈ J := (hnorm y'' y hyy).mpr ((hJ y).mpr hy)
    have h2 := (hJ y'').mp h1 i hi v hv
    refine ⟨_, h2, ?_⟩
    simp only [mulVecLin_apply, hy'', hU, Units.val_mul, ← mulVec_mulVec]
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hTW := eq_of_stable_isotropic hK hf hIfin hWiso hWle hWdim hTiso hTstab hi hTdim
  rw [← hTW]
  exact ⟨w, hw, rfl⟩

end CFSG.HardMathSupport.Curtis.UnitaryLevi
