module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteSplitTorusCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.GorensteinWalter Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def weylGL (K : Type) [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def weylPGL (K : Type) [Field K] : PGL2 K :=
  Matrix.ProjGenLinGroup.mk (weylGL K)

theorem weylGL_mul_self : weylGL K * weylGL K =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Kˣ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weylGL, Matrix.GeneralLinearGroup.scalar]

theorem weylPGL_mul_self : weylPGL K * weylPGL K = 1 := by
  rw [weylPGL, ← map_mul, weylGL_mul_self, Matrix.ProjGenLinGroup.mk_scalar]

theorem weylPGL_inv : (weylPGL K)⁻¹ = weylPGL K :=
  (eq_inv_of_mul_eq_one_right weylPGL_mul_self).symm

theorem weylPGL_conj_torus (a : Kˣ) :
    weylPGL K * pGammaL2FullSplitTorus K a * (weylPGL K)⁻¹ =
      (pGammaL2FullSplitTorus K a)⁻¹ := by
  rw [weylPGL_inv, ← map_inv]
  change Matrix.ProjGenLinGroup.mk (weylGL K) *
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K a) *
        Matrix.ProjGenLinGroup.mk (weylGL K) =
    Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K a⁻¹)
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨-a⁻¹, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weylGL, pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem pgl2FieldAut_weylPGL (σ : K ≃+* K) : pgl2FieldAut K σ (weylPGL K) = weylPGL K := by
  change pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (weylGL K)) =
    QuotientGroup.mk' (Subgroup.center _) (weylGL K)
  rw [pgl2RingEquiv_mk]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [weylGL, Matrix.GeneralLinearGroup.map]

theorem weylPGL_mem_range :
    weylPGL K ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  let g : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨QuotientGroup.mk' _ g, ?_⟩
  rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem weylPGL_not_mem_torus : weylPGL K ∉ (pGammaL2FullSplitTorus K).range := by
  rintro ⟨a, ha⟩
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K a) =
    Matrix.ProjGenLinGroup.mk (weylGL K) at ha
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp ha
  have h01 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
  simp [weylGL, pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar] at h01

theorem weylPGL_commute_s0 :
    weylPGL K * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * weylPGL K := by
  have h := weylPGL_conj_torus (K := K) (-1)
  rw [← map_inv, inv_neg_one] at h
  calc weylPGL K * pGammaL2FullSplitTorus K (-1)
      = (weylPGL K * pGammaL2FullSplitTorus K (-1) * (weylPGL K)⁻¹) * weylPGL K := by group
    _ = pGammaL2FullSplitTorus K (-1) * weylPGL K := by rw [h]

variable [Finite K]

theorem mem_torus_or_mul_weyl (hK : IsOddPrimePower (Nat.card K)) {x : PGL2 K}
    (hx : x * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * x) :
    x ∈ (pGammaL2FullSplitTorus K).range ∨
      x * weylPGL K ∈ (pGammaL2FullSplitTorus K).range := by
  have : Finite (PGL2 K) := Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨w, -, -, -, -, -, -, -, hC, hcardC, -⟩ := pgl2_fullSplitTorus_centralizer_data K hK
  set U := (pGammaL2FullSplitTorus K).range with hU
  set C := Subgroup.centralizer ({pGammaL2FullSplitTorus K (-1)} : Set (PGL2 K)) with hCdef
  have hUC : U ≤ C := hC ▸ le_sup_left
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hx
  have hnC : weylPGL K ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr weylPGL_commute_s0
  have hidx : (U.subgroupOf C).index = 2 := by
    have h1 := (U.subgroupOf C).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv] at h1
    have h2 : Nat.card C = 2 * Nat.card U := by rw [hC]; exact hcardC
    rw [h2] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · right
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hxC⟩)
      (b := ⟨weylPGL K, hnC⟩)).mpr ⟨fun h => absurd h hxU, fun h => absurd h weylPGL_not_mem_torus⟩
    exact h

theorem mul_fieldAut_mem_torus (hK : IsOddPrimePower (Nat.card K)) (σ : K ≃+* K) {h : PGL2 K}
    (hh : h * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * h) :
    h * pgl2FieldAut K σ h ∈ (pGammaL2FullSplitTorus K).range := by
  rcases mem_torus_or_mul_weyl hK hh with ⟨a, rfl⟩ | ⟨a, ha⟩
  · exact ⟨a * Units.map σ.toRingHom a, by rw [map_mul, pGammaL2FullSplitTorus_map_field]⟩
  · have hh' : h = pGammaL2FullSplitTorus K a * weylPGL K := by
      rw [ha, mul_assoc, weylPGL_mul_self, mul_one]
    refine ⟨a * (Units.map σ.toRingHom a)⁻¹, ?_⟩
    have e1 : pgl2FieldAut K σ (pGammaL2FullSplitTorus K a * weylPGL K) =
        pGammaL2FullSplitTorus K (Units.map σ.toRingHom a) * weylPGL K := by
      rw [map_mul, pgl2FieldAut_weylPGL, pGammaL2FullSplitTorus_map_field]
    rw [hh', e1, map_mul, map_inv]
    symm
    calc pGammaL2FullSplitTorus K a * weylPGL K *
          (pGammaL2FullSplitTorus K (Units.map σ.toRingHom a) * weylPGL K)
        = pGammaL2FullSplitTorus K a * (weylPGL K *
            pGammaL2FullSplitTorus K (Units.map σ.toRingHom a) * (weylPGL K)⁻¹) := by
          rw [weylPGL_inv]; group
      _ = pGammaL2FullSplitTorus K a *
          (pGammaL2FullSplitTorus K (Units.map σ.toRingHom a))⁻¹ := by
          rw [weylPGL_conj_torus]

omit [Finite K] in
theorem pgl2FieldAut_s0 (σ : K ≃+* K) :
    pgl2FieldAut K σ (pGammaL2FullSplitTorus K (-1)) = pGammaL2FullSplitTorus K (-1) := by
  rw [pGammaL2FullSplitTorus_map_field]
  congr 1
  ext
  simp

theorem sq_eq_of_commute_s0 (hK : IsOddPrimePower (Nat.card K))
    (h4 : ∀ σ : K ≃+* K, σ ^ 4 = 1 → σ ^ 2 = 1) {g : PGammaL2 K}
    (hg : g * SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) * g) (hg4 : g ^ 4 = 1) :
    g ^ 2 = 1 ∨ g ^ 2 = SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) := by
  have hl : g.left * pGammaL2FullSplitTorus K (-1) = pGammaL2FullSplitTorus K (-1) * g.left := by
    have h := congrArg SemidirectProduct.left hg
    simpa [SemidirectProduct.mul_left, pgl2FieldAut_s0] using h
  have hr4 : g.right ^ 4 = 1 := by
    have h := congrArg SemidirectProduct.rightHom hg4
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  have hr2 := h4 _ hr4
  obtain ⟨a, ha⟩ := mul_fieldAut_mem_torus hK g.right hl
  have hg2 : g ^ 2 = SemidirectProduct.inl (pGammaL2FullSplitTorus K a) := by
    apply SemidirectProduct.ext
    · rw [sq, SemidirectProduct.mul_left, SemidirectProduct.left_inl, ha]
    · rw [SemidirectProduct.right_inl, sq, SemidirectProduct.mul_right, ← sq, hr2]
  have ha2 : a * a = 1 := by
    have h : (g ^ 2) * (g ^ 2) = 1 := by rw [← pow_add, hg4]
    rw [hg2, ← map_mul, ← map_mul] at h
    have h' : pGammaL2FullSplitTorus K (a * a) = pGammaL2FullSplitTorus K 1 := by
      have h2 := congrArg SemidirectProduct.left h
      rw [map_one]
      simpa using h2
    exact pGammaL2FullSplitTorus_injective K h'
  rcases mul_self_eq_one_iff.mp (congrArg Units.val ha2 |>.trans Units.val_one) with h | h
  · left
    rw [hg2, show a = 1 from Units.ext h, map_one, map_one]
  · right
    rw [hg2, show a = -1 from Units.ext (by simpa using h)]

end CFSG.ClassicalInvolution.Q3.TL4.MF164
