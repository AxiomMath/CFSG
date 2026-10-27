module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalEichler
public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [CharP K 2] {t : V ≃ₗ[K] V}

theorem polar_sub_self_eq (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (w : V) :
    polar Q (t w - w) w = Q (t w - w) := by
  rw [polar_sub_left, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero, sub_zero,
    ← map_sub_eq_polar htO]

theorem eichler_sub_mul_comm (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {w : V} (hw : Q (t w - w) = 0) :
    eichler Q (t w - w) w * t = t * eichler Q (t w - w) w := by
  have h := eichler_conj htO (t w - w) w
  have h1 : t (t w - w) = t w - w :=
    mem_fixSpace.mp (commSpace_le_fixSpace htt (sub_mem_commSpace t w))
  have h3 : eichler Q (t w - w) (t w) = eichler Q (t w - w) w := by
    calc eichler Q (t w - w) (t w) = eichler Q (t w - w) (w + (1 : K) • (t w - w)) := by
          congr 1
          rw [one_smul]
          abel
      _ = eichler Q (t w - w) w := eichler_add_smul_self hw w 1
  rw [h1, h3] at h
  calc eichler Q (t w - w) w * t = (t * eichler Q (t w - w) w * t⁻¹) * t := by rw [h]
    _ = t * eichler Q (t w - w) w := by group

theorem eichler_apply_commSpace (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {w : V} (hw : Q (t w - w) = 0) {z : V} (hz : z ∈ commSpace t) :
    eichler Q (t w - w) w z = z - polar Q z w • (t w - w) := by
  have hpol : polar Q (t w - w) w = 0 := by rw [polar_sub_self_eq htO, hw]
  rw [eichler_apply hw hpol, polar_commSpace_eq_zero htO htt hz (sub_mem_commSpace t w),
    zero_smul, add_zero, mul_zero, add_zero]

theorem exists_polar_ne_zero_of_odd [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) (hodd : Odd (finrank K (commSpace t))) {u : V} (hu : u ∈ commSpace t)
    (hQu : Q u = 0) (hu0 : u ≠ 0) : ∃ w, Q (t w - w) = 0 ∧ polar Q u w ≠ 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := (fixSpace t).exists_isCompl
  have hX' : IsCompl X (fixSpace t) := hX.symm
  set B := (wallForm Q t).restrict X with hB
  have hBs : B.IsSymm := (wallForm_isSymm htO htt).restrict X
  have hBn : B.Nondegenerate := wallForm_restrict_nondegenerate hQ htO htt hX'
  have hBa : B.IsAlt → B = 0 := fun h => by
    have hzero := (wallForm_restrict_isAlt_iff htO hX').mp h
    exact absurd (even_finrank_commSpace_of_forall_eq_zero hQ htO htt hzero)
      (Nat.not_even_iff_odd.mpr hodd)
  obtain ⟨b, hb⟩ := hBs.exists_basis_toMatrix_eq_one isSquare_of_charTwo' hBn hBa
  have hdot : ∀ x y : X, B x y = ∑ i, b.repr x i * b.repr y i := by
    intro x y
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B x y, hb, Matrix.one_mulVec]
    rfl
  have hentry : ∀ k l, B (b k) (b l) = if k = l then 1 else 0 := fun k l => by
    rw [← LinearMap.BilinForm.toMatrix_apply b B, hb, Matrix.one_apply]
  have hcoord : ∀ (x : X) l, B x (b l) = b.repr x l := fun x l => by
    rw [hdot, b.repr_self]
    simp [Finsupp.single_apply]
  obtain ⟨x, hxX, hxu⟩ := exists_mem_compl_of_mem_commSpace hX' hu
  set c := b.repr ⟨x, hxX⟩ with hc
  have hsum : ∑ i, c i = 0 := by
    have h1 : B ⟨x, hxX⟩ ⟨x, hxX⟩ = 0 := by
      change wallForm Q t x x = 0
      rw [wallForm_self htO, hxu, hQu]
    rw [hdot] at h1
    have h2 : (∑ i, c i) ^ 2 = 0 := by
      rw [sum_pow_char]
      simp only [pow_two]
      exact h1
    exact pow_eq_zero_iff two_ne_zero |>.mp h2
  have hx0 : (⟨x, hxX⟩ : X) ≠ 0 := by
    intro h
    apply hu0
    have hx : x = 0 := congrArg Subtype.val h
    rw [← hxu, hx, map_zero, sub_zero]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    apply hx0
    have hc0 : c = 0 := Finsupp.ext h
    exact b.repr.injective (by rw [← hc, hc0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ c i := by
    by_contra! h
    have hs : ∑ k, c k = (finrank K X : K) * c i := by
      rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hfin : (finrank K X : K) = 1 := by
      rw [finrank_compl_eq hX']
      obtain ⟨m, hm⟩ := hodd
      rw [hm]
      push_cast
      rw [CharTwo.two_eq_zero, zero_mul, zero_add]
    rw [hsum, hfin, one_mul] at hs
    exact hi hs.symm
  have hij : i ≠ j := fun h => hj (h ▸ rfl)
  refine ⟨(b i : V) + (b j : V), ?_, ?_⟩
  · rw [← wallForm_self htO]
    change B (b i + b j) (b i + b j) = 0
    have e1 : B (b i) (b i) = 1 := by simp [hentry]
    have e2 : B (b j) (b j) = 1 := by simp [hentry]
    have e3 : B (b i) (b j) = 0 := by simp [hentry, hij]
    have e4 : B (b j) (b i) = 0 := by simp [hentry, Ne.symm hij]
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, e1, e2, e3, e4, add_zero,
      zero_add, CharTwo.add_self_eq_zero]
  · rw [← hxu, polar_sub_eq_polar_sub htO htt, ← wallForm_apply]
    change B ⟨x, hxX⟩ (b i + b j) ≠ 0
    rw [map_add, hcoord, hcoord]
    intro h
    apply hj
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h.symm

theorem apply_eq_of_mem_commSpace [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) (hodd : Odd (finrank K (commSpace t))) {F : Subgroup (V ≃ₗ[K] V)}
    (hFO : F ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hF2 : IsPGroup 2 F)
    (hFt : ∀ f ∈ F, f * t = t * f)
    (hN : ∀ w, Q (t w - w) = 0 → ∀ f ∈ F,
      (eichler Q (t w - w) w)⁻¹ * f * eichler Q (t w - w) w ∈ F)
    {f : V ≃ₗ[K] V} (hf : f ∈ F) {z : V} (hz : z ∈ commSpace t) : f z = z := by
  have hFZ : ∀ f ∈ F, ∀ z ∈ commSpace t, f z ∈ commSpace t := by
    intro f hf z hz
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hz
    rw [map_sub, ← LinearEquiv.mul_apply, hFt f hf, LinearEquiv.mul_apply]
    exact sub_mem_commSpace t (f v)
  have hstep : ∀ u ∈ commSpace t, (∀ f ∈ F, f u = u) → ∀ w, Q (t w - w) = 0 →
      polar Q u w ≠ 0 → ∀ f ∈ F, f (t w - w) = t w - w := by
    intro u hu hfu w hw hpol f hf
    have hgu := eichler_apply_commSpace htO htt hw hu
    have h1 : f (eichler Q (t w - w) w u) = eichler Q (t w - w) w u := by
      have h2 := hfu _ (hN w hw f hf)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h2
      have h3 := congrArg (eichler Q (t w - w) w) h2
      rwa [LinearEquiv.apply_inv_apply'] at h3
    rw [hgu, map_sub, map_smul, hfu f hf] at h1
    exact smul_right_injective V hpol (sub_right_injective h1)
  let Z0 : Submodule K V :=
    { carrier := {z | z ∈ commSpace t ∧ Q z = 0}
      add_mem' := fun {a b} ha hb => ⟨(commSpace t).add_mem ha.1 hb.1, by
        rw [map_add_eq, ha.2, hb.2, polar_commSpace_eq_zero htO htt ha.1 hb.1, add_zero,
          add_zero]⟩
      zero_mem' := ⟨(commSpace t).zero_mem, QuadraticMap.map_zero Q⟩
      smul_mem' := fun c a ha => ⟨(commSpace t).smul_mem c ha.1, by
        rw [QuadraticMap.map_smul, ha.2, smul_zero]⟩ }
  have hZ0fix : ∀ z ∈ commSpace t, Q z = 0 → ∀ f ∈ F, f z = z := by
    by_cases hbot : Z0 = ⊥
    · intro z hz hQz f _
      have hmem : z ∈ Z0 := ⟨hz, hQz⟩
      rw [hbot, Submodule.mem_bot] at hmem
      rw [hmem, map_zero]
    · obtain ⟨u, hu, hu0, hfu⟩ := exists_fixed_ne_zero hF2 (U := Z0)
        (fun f hf z hz => ⟨hFZ f hf z hz.1, by rw [map_of_mem (hFO hf), hz.2]⟩) hbot
      intro z hz hQz f hf
      obtain ⟨w, hwz⟩ := mem_commSpace.mp hz
      obtain ⟨w₁, hw₁, hpol₁⟩ := exists_polar_ne_zero_of_odd hQ htO htt hodd hu.1 hu.2 hu0
      have hfix₁ := hstep u hu.1 hfu w₁ hw₁ hpol₁
      by_cases hp : polar Q u w = 0
      · have hsplit : t (w + w₁) - (w + w₁) = (t w - w) + (t w₁ - w₁) := by
          rw [map_add]
          abel
        have hQ' : Q (t (w + w₁) - (w + w₁)) = 0 := by
          rw [hsplit, map_add_eq, hwz, hQz, hw₁,
            polar_commSpace_eq_zero htO htt hz (sub_mem_commSpace t w₁), add_zero, add_zero]
        have hp' : polar Q u (w + w₁) ≠ 0 := by
          rw [polar_add_right, hp, zero_add]
          exact hpol₁
        have h := hstep u hu.1 hfu (w + w₁) hQ' hp' f hf
        rw [hsplit, map_add, hfix₁ f hf, hwz] at h
        exact add_right_cancel h
      · rw [← hwz]
        exact hstep u hu.1 hfu w (by rw [hwz, hQz]) hp f hf
  have hfinv : f⁻¹ ∈ F := F.inv_mem hf
  by_contra hne
  have hd0 : f z - z ≠ 0 := sub_ne_zero.mpr hne
  have hdZ : f z - z ∈ commSpace t := sub_mem (hFZ f hf z hz) hz
  have hQd : Q (f z - z) = 0 := by
    rw [sub_eq_add_vec K, map_add_eq, map_of_mem (hFO hf),
      polar_commSpace_eq_zero htO htt (hFZ f hf z hz) hz, add_zero, CharTwo.add_self_eq_zero]
  obtain ⟨w, hw, hpol⟩ := exists_polar_ne_zero_of_odd hQ htO htt hodd hdZ hQd hd0
  apply hpol
  have h1 : f⁻¹ (t w - w) = t w - w := hZ0fix _ (sub_mem_commSpace t w) hw _ hfinv
  have htf : t (f⁻¹ w) = f⁻¹ (t w) := by
    calc t (f⁻¹ w) = (t * f⁻¹) w := (LinearEquiv.mul_apply _ _ _).symm
      _ = (f⁻¹ * t) w := by rw [hFt _ hfinv]
      _ = f⁻¹ (t w) := LinearEquiv.mul_apply _ _ _
  have h2 : f⁻¹ w - w ∈ fixSpace t := by
    rw [mem_fixSpace, map_sub, htf, ← sub_eq_zero]
    rw [show f⁻¹ (t w) - t w - (f⁻¹ w - w) = f⁻¹ (t w - w) - (t w - w) by rw [map_sub]; abel,
      h1, sub_self]
  have h3 : polar Q z (f⁻¹ w - w) = 0 := by
    have h4 := (fixSpace_eq_orthogonal_commSpace hQ htO htt).le h2
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at h4
    have h5 : Q.polarBilin z (f⁻¹ w - w) = 0 := h4 z hz
    rwa [polarBilin_apply_apply] at h5
  have h5 : polar Q (f z) w = polar Q z (f⁻¹ w) :=
    (polar_map_of_mem (hFO hfinv) (f z) w).symm.trans (by rw [LinearEquiv.inv_apply_apply'])
  rw [polar_sub_left, h5, ← polar_sub_right, h3]

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal
