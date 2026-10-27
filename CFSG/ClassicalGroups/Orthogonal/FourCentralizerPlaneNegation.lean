module

public import CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow
public import CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

public noncomputable section

open Module QuadraticMap

namespace CFSG.ClassicalGroups.Orthogonal.FourCentralizerPlaneNegation

variable {K : Type} [Field K] [Finite K]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {Q : QuadraticForm K W}

private theorem centralizer_eq_operator
    (A : TauCeti.QuadraticMap.orthogonalGroup Q) :
    Subgroup.centralizer ({A} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) =
      CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.orthogonalOperatorCentralizer
        Q ((A : W ≃ₗ[K] W).toLinearMap) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change x * A = A * x ↔ ∀ v : W, (x : W ≃ₗ[K] W) (((A : W ≃ₗ[K] W).toLinearMap) v) =
    ((A : W ≃ₗ[K] W).toLinearMap) ((x : W ≃ₗ[K] W) v)
  constructor
  · intro h v
    have h' := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
      (g : W ≃ₗ[K] W)) h
    have hv := congrArg (fun g : W ≃ₗ[K] W => g v) h'
    simpa [LinearEquiv.mul_apply] using hv
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := h v
    simpa [LinearEquiv.mul_apply] using hv

private theorem eigenspace_cases
    (hodd : Odd (Nat.card K)) (hQ : Q.polarBilin.Nondegenerate)
    (A : TauCeti.QuadraticMap.orthogonalGroup Q) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) (hAneg : ((A : W ≃ₗ[K] W) : W →ₗ[K] W) ≠ -1)
    (e : Basis (Fin 4) K W) (he : ∀ i, Q (e i) = 1) :
    Module.finrank K (Module.End.eigenspace (((A : W ≃ₗ[K] W).toLinearMap)) (-1)) = 1 ∨
    Module.finrank K (Module.End.eigenspace (((A : W ≃ₗ[K] W).toLinearMap)) (-1)) = 2 ∨
    Module.finrank K (Module.End.eigenspace (((A : W ≃ₗ[K] W).toLinearMap)) (-1)) = 3 := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let T : Module.End K W := ((A : W ≃ₗ[K] W)).toLinearMap
  have hA2v : ∀ v : W, T (T v) = v := by
    intro v
    have hmul : (A : W ≃ₗ[K] W) * (A : W ≃ₗ[K] W) = 1 := by
      have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (g : W ≃ₗ[K] W)) hA2
      simpa using h
    have h := congrArg (fun g : W ≃ₗ[K] W => g v) hmul
    simpa [LinearEquiv.mul_apply, T] using h
  have hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W) := by
    ext v
    change T (T v) = (1 : K) ^ 2 • v
    rw [one_pow, one_smul, hA2v v]
  have hcompl := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl
    T 1 one_ne_zero h2 hT2
  have hdimsum := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspace_finrank
    T 1 one_ne_zero h2 hT2
  have hdimW : Module.finrank K W = 4 := by
    rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hneg : T.eigenspace (-1) ≠ ⊥ := by
    intro hbot
    have htop : T.eigenspace 1 = ⊤ := by
      have := hcompl.sup_eq_top
      rw [hbot, sup_bot_eq] at this
      exact this
    have hscalar := (CFSG.ComponentClassification.CatalogueBProjectiveInvolution.eigenspace_eq_top_iff_scalar
      T 1).mp htop
    apply hA1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun f : Module.End K W => f v) hscalar
    simpa [T, LinearEquiv.mul_apply] using hv
  have hpos : T.eigenspace 1 ≠ ⊥ := by
    intro hbot
    have htop : T.eigenspace (-1) = ⊤ := by
      have := hcompl.sup_eq_top
      rw [hbot, bot_sup_eq] at this
      exact this
    have hscalar := (CFSG.ComponentClassification.CatalogueBProjectiveInvolution.eigenspace_eq_top_iff_scalar
      T (-1)).mp htop
    apply hAneg
    have hv := hscalar
    simpa [T] using hv
  have hnegpos : 0 < Module.finrank K (T.eigenspace (-1)) := by
    by_contra h
    exact hneg (Submodule.finrank_eq_zero.mp (by omega))
  have hpospos : 0 < Module.finrank K (T.eigenspace 1) := by
    by_contra h
    exact hpos (Submodule.finrank_eq_zero.mp (by omega))
  change Module.finrank K (T.eigenspace (-1)) = 1 ∨
    Module.finrank K (T.eigenspace (-1)) = 2 ∨
    Module.finrank K (T.eigenspace (-1)) = 3
  omega

private theorem discr_eq_zero_of_unit_basis
    [Invertible (2 : K)]
    (hQ : Q.polarBilin.Nondegenerate)
    (e : Basis (Fin 4) K W) (he : ∀ i, Q (e i) = 1)
    (horth : ∀ i j : Fin 4, i ≠ j → Q.polarBilin (e i) (e j) = 0) :
    TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) = 0 := by
  classical
  have hO : LinearMap.IsOrthoᵢ (QuadraticMap.associated Q) ⇑e := by
    intro i j hij
    change (QuadraticMap.associated Q) (e i) (e j) = 0
    rw [QuadraticMap.associated_apply (S := K), QuadraticMap.map_add Q (e i) (e j),
      ← QuadraticMap.polarBilin_apply_apply, horth i j hij]
    simp
  have hrepr : Q.basisRepr e =
      QuadraticMap.weightedSumSquares K (fun i => Q (e i)) :=
    QuadraticMap.basisRepr_eq_of_iIsOrtho Q e hO
  let p : TauCeti.RegularFormPresentation K := ⟨4, fun _ => 1⟩
  have hp : QuadraticMap.weightedSumSquares K (fun i => Q (e i)) =
      TauCeti.presentedForm p := by
    ext x
    rw [TauCeti.presentedForm_apply]
    simp [p, QuadraticMap.weightedSumSquares, he]
  have hE : Q.Equivalent (TauCeti.presentedForm p) := by
    have e0 := QuadraticMap.isometryEquivBasisRepr Q e
    rw [hrepr] at e0
    exact ⟨hp ▸ e0⟩
  have hd := TauCeti.discr_formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ) p hE
  rw [hd]
  have hprod : (∏ i : Fin 4, p.snd i) = 1 := by
    simp [p]
  rw [hprod]
  exact (TauCeti.squareClass_eq_zero_iff (1 : Kˣ)).mpr ⟨1, by simp⟩

private noncomputable def eigenspace_prod_isometry
    [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) (T : Module.End K W)
    (hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W))
    (hself : ∀ x y : W, Q.polarBilin (T x) y = Q.polarBilin x (T y)) :
    Q.IsometryEquiv
      ((Q.comp (T.eigenspace 1).subtype).prod (Q.comp (T.eigenspace (-1)).subtype)) := by
  let e := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
    T 1 one_ne_zero h2 hT2
  have he : ∀ (x : T.eigenspace 1) (y : T.eigenspace (-1)), e (x, y) = x.val + y.val := by
    intro x y
    simp [e, CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv,
      Submodule.coe_prodEquivOfIsCompl, LinearMap.coprod_apply]
  refine { toLinearEquiv := e.symm, map_app' := ?_ }
  intro v
  obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
  change ((Q.comp (T.eigenspace 1).subtype).prod
    (Q.comp (T.eigenspace (-1)).subtype)) (e.symm (e (x, y))) = Q (e (x, y))
  rw [LinearEquiv.symm_apply_apply, he, QuadraticMap.prod_apply]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positive_eigenspace_sum
    Q T 1 one_ne_zero h2 hself x y).symm

private theorem discr_eigenspaces_sum
    [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) (hQ : Q.polarBilin.Nondegenerate)
    (T : Module.End K W)
    (hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W))
    (hself : ∀ x y : W, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) = 0) :
    let hnde :=
      CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positive_adjoint_eigenspaces_nondegenerate
        Q.polarBilin hQ
        (LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q))
        T 1 one_ne_zero h2 hT2 hself
    TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace 1).subtype)
          (QuadraticMap.nondegenerate_polar_iff.mp hnde.1)) +
      TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace (-1)).subtype)
          (QuadraticMap.nondegenerate_polar_iff.mp hnde.2)) = 0 := by
  dsimp only
  let hnde :=
    CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positive_adjoint_eigenspaces_nondegenerate
      Q.polarBilin hQ
      (LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q))
      T 1 one_ne_zero h2 hT2 hself
  let hplus : (Q.comp (T.eigenspace 1).subtype).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp hnde.1
  let hminus : (Q.comp (T.eigenspace (-1)).subtype).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp hnde.2
  let hprod : ((Q.comp (T.eigenspace 1).subtype).prod
      (Q.comp (T.eigenspace (-1)).subtype)).Nondegenerate :=
    Nondegenerate.prod hplus hminus
  have hclass : TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ) =
      TauCeti.formClass ((Q.comp (T.eigenspace 1).subtype).prod
        (Q.comp (T.eigenspace (-1)).subtype)) hprod :=
    (TauCeti.formClass_eq_iff Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)
      ((Q.comp (T.eigenspace 1).subtype).prod
        (Q.comp (T.eigenspace (-1)).subtype)) hprod).mpr
      ⟨eigenspace_prod_isometry h2 T hT2 hself⟩
  have hsplit : TauCeti.RegularFormClass.discr
      (TauCeti.formClass ((Q.comp (T.eigenspace 1).subtype).prod
        (Q.comp (T.eigenspace (-1)).subtype)) hprod) =
      TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace 1).subtype) hplus) +
      TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace (-1)).subtype) hminus) := by
    rw [TauCeti.formClass_prod (Q.comp (T.eigenspace 1).subtype) hplus
      (Q.comp (T.eigenspace (-1)).subtype) hminus,
      TauCeti.RegularFormClass.discr_add]
  calc TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace 1).subtype) hplus) +
      TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace (-1)).subtype) hminus)
      = TauCeti.RegularFormClass.discr
          (TauCeti.formClass ((Q.comp (T.eigenspace 1).subtype).prod
            (Q.comp (T.eigenspace (-1)).subtype)) hprod) := hsplit.symm
    _ = TauCeti.RegularFormClass.discr
          (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) := by
        rw [hclass]
    _ = 0 := hdisc

private theorem coord_plane_signchange_unit
    [Invertible (2 : K)]
    (Q : QuadraticForm K (Fin 2 → K)) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate)
    (c : Basis (Fin 2) K (Fin 2 → K))
    (hc : ∀ i j : Fin 2, i ≠ j → Q.IsOrtho (c i) (c j))
    (hc0 : Q (c 0) = 1)
    (hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) ≠ 0)
    (SV : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ∃ b : TauCeti.QuadraticMap.orthogonalGroup Q,
      b ∈ (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      (∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
        x ∈ (SV : Subgroup _) → x * b = b * x) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      ∃ u : Fin 2 → K, Q u = 1 ∧ (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) u = -u ∧
        (∀ x : Fin 2 → K, Q.polarBilin u x = 0 →
          (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) x = x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hQn : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨hSle, hScard, S0, hS0⟩ :=
    CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.isSylow_signChangeSubgroup_of_discr_ne_zero
      (K := K) (V := Fin 2 → K) (Q := Q) (hQ := hQn) (c := c) (hc := hc) (hdisc := hdisc)
  haveI : (S0 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  haveI : Finite (Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    Sylow.finite_of_finiteIndex S0
  obtain ⟨g, hg⟩ := (Sylow.isPretransitive_of_finite (p := 2)
    (G := TauCeti.QuadraticMap.orthogonalGroup Q)).exists_smul_eq S0 SV
  let s : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0},
      hSle (CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv_mem_signChangeSubgroup c {0})⟩
  have hsS0 : s ∈ (S0 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [hS0, Subgroup.mem_subgroupOf]
    exact CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv_mem_signChangeSubgroup c {0}
  let b : TauCeti.QuadraticMap.orthogonalGroup Q := g * s * g⁻¹
  have hbSV : b ∈ (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map.mpr ⟨s, hsS0, rfl⟩
  have hcentral : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
      x ∈ (SV : Subgroup _) → x * b = b * x := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hx
    obtain ⟨t, htS0, htx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 2),
        (t : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
          CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c T := by
      rw [hS0, Subgroup.mem_subgroupOf] at htS0
      exact htS0
    have hsval : (s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
        CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0} := rfl
    have hst : t * s = s * t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hT, hsval,
        CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv_comm]
    have htx' : (MulAut.conj g) t = x := htx
    calc x * b = (MulAut.conj g) t * ((MulAut.conj g) s) := by rw [htx']; rfl
      _ = (MulAut.conj g) (t * s) := by rw [map_mul]
      _ = (MulAut.conj g) (s * t) := by rw [hst]
      _ = (MulAut.conj g) s * (MulAut.conj g) t := by rw [map_mul]
      _ = b * x := by rw [htx']; rfl
  refine ⟨b, hbSV, hcentral, ?_, ?_, ?_⟩
  · have hs2 : s * s = 1 := by
      apply Subtype.ext
      exact CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signChangeSubgroup_mul_self
        (CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv_mem_signChangeSubgroup c {0})
    calc b * b = g * s * g⁻¹ * (g * s * g⁻¹) := rfl
      _ = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  · intro hb1
    have hs1 : s = 1 := by
      have h : g⁻¹ * b * g = s := by
        calc g⁻¹ * b * g = g⁻¹ * (g * s * g⁻¹) * g := rfl
          _ = s := by group
      rw [hb1] at h
      simpa using h.symm
    have hsval : (s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
        CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0} := rfl
    have hsign1 : CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0} =
        (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := by
      have : (s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) = 1 := by rw [hs1]; rfl
      rwa [hsval] at this
    have hsc0 : (CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0}) (c 0) = - c 0 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.signEquiv_apply_basis]
      simp
    have hc0eval : (c 0 : Fin 2 → K) = - c 0 := by
      have h := hsc0
      rw [hsign1] at h
      simpa using h
    have hsum : (c 0 : Fin 2 → K) + c 0 = 0 := by
      have := congrArg (fun y : Fin 2 → K => y + c 0) hc0eval
      simpa using this
    have hsmul : (2 : K) • c 0 = 0 := by
      rw [two_smul]
      exact hsum
    rcases smul_eq_zero.mp hsmul with hzero | h0
    · exact h2 hzero
    · exact (c.ne_zero 0) h0
  · refine ⟨(g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0), ?_, ?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem g.property, hc0]
    · have hsc0 : (CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.signEquiv c {0}) (c 0) = - c 0 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.signEquiv_apply_basis]
        simp
      calc (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0))
          = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0)))) := by rfl
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0)) := by rw [LinearEquiv.symm_apply_apply]
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (-(c 0)) := by
          have hs0 : (s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0) = -c 0 := hsc0
          rw [hs0]
        _ = - ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0)) := by rw [map_neg]
    · intro x hx
      set a0 : K := c.repr ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) 0 with ha0
      set a1 : K := c.repr ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) 1 with ha1
      have hxcoord : (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x = a0 • c 0 + a1 • c 1 := by
        rw [show (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x =
          (c.repr ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) 0) • c 0 +
            (c.repr ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) 1) • c 1 from by
          simpa only [Fin.sum_univ_two] using
            (c.sum_repr ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x)).symm]
      have hxorth : Q.polarBilin (c 0) ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) = 0 := by
        have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.property (c 0)
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x)
        rw [LinearEquiv.apply_symm_apply] at h
        have hx' : Q.polarBilin ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (c 0)) x = 0 := by
          rw [QuadraticMap.polarBilin_apply_apply]
          exact hx
        rw [← QuadraticMap.polarBilin_apply_apply] at h
        rw [hx'] at h
        exact h.symm
      have hcoef : a0 = 0 := by
        have hp : Q.polarBilin (c 0) ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) =
            a0 * Q.polarBilin (c 0) (c 0) := by
          rw [hxcoord, map_add, map_smul, map_smul,
            (QuadraticMap.isOrtho_polarBilin).mpr (hc 0 1 (by decide)), smul_zero, add_zero]
          rw [smul_eq_mul]
        rw [hp] at hxorth
        have hdiag : Q.polarBilin (c 0) (c 0) = 2 := by
          rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hc0]
          norm_num
        rw [hdiag] at hxorth
        exact (mul_eq_zero.mp hxorth).resolve_right h2
      have hx1 : (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x = a1 • c 1 := by
        rw [hxcoord, hcoef, zero_smul, zero_add]
      calc (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) x
          = ((g * s * g⁻¹ : TauCeti.QuadraticMap.orthogonalGroup Q) :
              (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) x := rfl
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
              ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x)) := rfl
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((s : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
              (a1 • c 1)) := by rw [hx1]
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (a1 • c 1) := by
          congr 1
          rw [map_smul]
          congr 1
          dsimp only [s]
          rw [CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.signEquiv_apply_basis]
          simp
        _ = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).symm x) := by
          rw [hx1]
        _ = x := LinearEquiv.apply_symm_apply (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) x


private theorem plane_signchange_unit_of_nonsquare
    [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 2)
    (hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) ≠ 0)
    (SV : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ∃ b : TauCeti.QuadraticMap.orthogonalGroup Q,
      b ∈ (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      (∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
        x ∈ (SV : Subgroup _) → x * b = b * x) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      ∃ u : V, Q u = 1 ∧ (b : V ≃ₗ[K] V) u = -u ∧
        (∀ x : V, Q.polarBilin u x = 0 → (b : V ≃ₗ[K] V) x = x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hQn : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨c, hcorth, hcnorm, hc1ne⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hodd
      (V := V) hdim (by norm_num) Q hQ (a := 1) one_ne_zero
  have hc0 : Q (c 0) = 1 := hcnorm 0 (by norm_num)
  let Q2 : QuadraticForm K (Fin 2 → K) := Q.basisRepr c
  let e : Q.IsometryEquiv Q2 := QuadraticMap.isometryEquivBasisRepr Q c
  let eG : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      TauCeti.QuadraticMap.orthogonalGroup Q2 :=
    TauCeti.QuadraticMap.orthogonalGroupCongr e
  have hQ2n : Q2.Nondegenerate := e.nondegenerate_iff.mp hQn
  have hQ2 : Q2.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ2n
  have hclass : TauCeti.formClass Q hQn =
      TauCeti.formClass Q2 hQ2n :=
    (TauCeti.formClass_eq_iff Q hQn Q2 hQ2n).mpr ⟨e⟩
  have hdisc2 : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q2 hQ2n) ≠ 0 := by
    intro h
    apply hdisc
    rw [hclass]
    exact h
  let c2 : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  have he_ci : ∀ i : Fin 2, e (c i) = c2 i := by
    intro i
    rw [show c2 i = Pi.single i (1 : K) from Pi.basisFun_apply K (Fin 2) i]
    change c.equivFun (c i) = Pi.single i 1
    ext j
    rw [Basis.equivFun_self]
    by_cases h : j = i
    · simp [h]
    · simp [Pi.single_eq_of_ne h, (Ne.symm h)]
  have hc2_0 : Q2 (c2 0) = 1 := by
    rw [← he_ci 0]
    exact (e.map_app (c 0)).trans hc0
  have hc2 : ∀ i j : Fin 2, i ≠ j → Q2.IsOrtho (c2 i) (c2 j) := by
    intro i j hij
    rw [← QuadraticMap.isOrtho_polarBilin]
    rw [QuadraticMap.polarBilin_apply_apply]
    calc polar Q2 (c2 i) (c2 j)
        = polar Q2 (e (c i)) (e (c j)) := by rw [he_ci i, he_ci j]
      _ = polar Q (c i) (c j) := e.polar_apply (c i) (c j)
      _ = 0 := hcorth i j hij
  let S2 : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q2) :=
    Sylow.mapSurjective (f := eG.toMonoidHom) eG.surjective SV
  obtain ⟨b2, hb2S, hb2cent, hb2sq, hb2ne, u2, hu2, hb2u2, hb2fix⟩ :=
    coord_plane_signchange_unit Q2 hodd hQ2 c2 hc2 hc2_0 hdisc2 S2
  let b : TauCeti.QuadraticMap.orthogonalGroup Q := eG.symm b2
  have heGb : eG b = b2 := eG.apply_symm_apply b2
  have hbSV : b ∈ (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    have hb2map : b2 ∈ Subgroup.map eG.toMonoidHom
        (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      rw [← Sylow.coe_mapSurjective (f := eG.toMonoidHom) eG.surjective SV]
      exact hb2S
    obtain ⟨b', hb'SV, hb'eq⟩ := Subgroup.mem_map.mp hb2map
    have hb'eq' : eG b' = b2 := hb'eq
    have hb' : b' = b := by
      apply eG.injective
      rw [hb'eq', heGb]
    rwa [hb'] at hb'SV
  have hcentral : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
      x ∈ (SV : Subgroup _) → x * b = b * x := by
    intro x hx
    apply eG.injective
    have hx2 : eG x ∈ (S2 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q2)) := by
      rw [show (S2 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q2)) =
        Subgroup.map eG.toMonoidHom
          (SV : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) from
        Sylow.coe_mapSurjective (f := eG.toMonoidHom) eG.surjective SV]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h := hb2cent (eG x) hx2
    simpa only [map_mul, heGb] using h
  refine ⟨b, hbSV, hcentral, ?_, ?_, e.symm u2, ?_, ?_, ?_⟩
  · apply eG.injective
    simpa only [map_mul, heGb, hb2sq, map_one, b] using hb2sq
  · intro hb1
    apply hb2ne
    rw [← heGb, hb1, map_one]
  ·
    have h := e.map_app (e.symm u2)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans hu2
  ·
    apply e.injective
    have hcongr := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e b (e (e.symm u2))
    rw [e.apply_symm_apply, heGb] at hcongr
    calc e.toLinearEquiv ((b : V ≃ₗ[K] V) (e.symm u2))
        = (b2 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) u2 := hcongr.symm
      _ = -u2 := hb2u2
      _ = e.toLinearEquiv (-e.symm u2) := by
        rw [map_neg]
        exact (congrArg Neg.neg (e.apply_symm_apply u2)).symm
  ·
    intro x hx
    apply e.injective
    have hx' : Q2.polarBilin u2 (e x) = 0 := by
      have h := e.polar_apply (e.symm u2) x
      rw [e.apply_symm_apply] at h
      rw [QuadraticMap.polarBilin_apply_apply]
      rw [h]
      rw [← QuadraticMap.polarBilin_apply_apply]
      exact hx
    have hfix := hb2fix (e x) hx'
    have hcongr : (b2 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (e x) =
        e.toLinearEquiv ((b : V ≃ₗ[K] V) x) := by
      have h := TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e b (e x)
      rw [heGb] at h
      simpa [LinearEquiv.symm_apply_apply] using h
    rw [← hcongr, hfix]
    rfl


private theorem plane_unit_basis_of_square
    [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 2)
    (hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) = 0) :
    ∃ u v : V, Q u = 1 ∧ Q v = 1 ∧ Q.polarBilin u v = 0 ∧
      (∀ x : V, Q.polarBilin u x = 0 → Q.polarBilin v x = 0 → x = 0) := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hQn : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨c, hcorth, hcnorm, hc1ne⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hodd
      (V := V) hdim (by norm_num) Q hQ (a := 1) one_ne_zero
  have hc0 : Q (c 0) = 1 := hcnorm 0 (by norm_num)
  have hc1ne' : Q (c (1 : Fin 2)) ≠ 0 := by
    simpa using hc1ne
  have hc01 : Q.polarBilin (c 0) (c 1) = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hcorth 0 1 (by decide)
  have hc10 : Q.polarBilin (c 1) (c 0) = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hcorth 1 0 (by decide)
  let Q2 : QuadraticForm K (Fin 2 → K) := Q.basisRepr c
  let e : Q.IsometryEquiv Q2 := QuadraticMap.isometryEquivBasisRepr Q c
  have hQ2n : Q2.Nondegenerate := e.nondegenerate_iff.mp hQn
  have hQ2 : Q2.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ2n
  have hclass : TauCeti.formClass Q hQn = TauCeti.formClass Q2 hQ2n :=
    (TauCeti.formClass_eq_iff Q hQn Q2 hQ2n).mpr ⟨e⟩
  have hdisc2 : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q2 hQ2n) = 0 := by
    rw [← hclass]
    exact hdisc
  let c2 : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  have he_ci : ∀ i : Fin 2, e (c i) = c2 i := by
    intro i
    rw [show c2 i = Pi.single i (1 : K) from Pi.basisFun_apply K (Fin 2) i]
    change c.equivFun (c i) = Pi.single i 1
    ext j
    rw [Basis.equivFun_self]
    by_cases h : j = i
    · simp [h]
    · simp [Pi.single_eq_of_ne h, (Ne.symm h)]
  have hc2 : ∀ i j : Fin 2, i ≠ j → Q2.IsOrtho (c2 i) (c2 j) := by
    intro i j hij
    rw [← QuadraticMap.isOrtho_polarBilin]
    rw [QuadraticMap.polarBilin_apply_apply]
    calc polar Q2 (c2 i) (c2 j)
        = polar Q2 (e (c i)) (e (c j)) := by rw [he_ci i, he_ci j]
      _ = polar Q (c i) (c j) := e.polar_apply (c i) (c j)
      _ = 0 := hcorth i j hij
  have hc2_0 : Q2 (c2 0) = 1 := by
    rw [← he_ci 0]
    exact (e.map_app (c 0)).trans hc0
  have hc2_1 : Q2 (c2 1) = Q (c 1) := by
    rw [← he_ci 1]
    exact e.map_app (c 1)
  have hc2ne : ∀ i : Fin 2, Q2 (c2 i) ≠ 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hc2_0]; exact one_ne_zero
    · have hi1 : i = 1 := by
        apply Fin.ext
        have := i.isLt
        omega
      rw [hi1, hc2_1]
      exact hc1ne'
  have hprod :=
    CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.discr_formClass_eq_squareClass_prod
      (K := K) (V := Fin 2 → K) Q2 hQ2n c2 hc2 hc2ne
  have hsqclass : TauCeti.squareClass
      (Units.mk0 (Q2 (c2 0)) (hc2ne 0) * Units.mk0 (Q2 (c2 1)) (hc2ne 1)) = 0 := by
    rw [← hprod]
    exact hdisc2
  obtain ⟨s, hs⟩ := (TauCeti.squareClass_eq_zero_iff _).mp hsqclass
  have hsval : (s : K) * (s : K) = Q (c 1) := by
    have h := congrArg Units.val hs
    simp only [Units.val_mul, Units.val_mk0] at h
    rw [hc2_0, hc2_1, one_mul] at h
    exact h.symm
  have hsne : (s : K) ≠ 0 := by
    intro h
    apply hc1ne'
    rw [← hsval, h]
    simp
  refine ⟨c 0, (s : K)⁻¹ • c 1, hc0, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_smul, ← hsval, smul_eq_mul]
    field_simp [hsne]
  · rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_right,
      hcorth 0 1 (by decide), smul_zero]
  ·
    intro x hx0 hx1
    set a0 : K := c.repr x 0 with ha0
    set a1 : K := c.repr x 1 with ha1
    have hxcoord : x = a0 • c 0 + a1 • c 1 := by
      rw [show x = (c.repr x 0) • c 0 + (c.repr x 1) • c 1 from by
        simpa only [Fin.sum_univ_two] using (c.sum_repr x).symm]
    have hcoef0 : a0 = 0 := by
      have hp : Q.polarBilin (c 0) x = a0 * Q.polarBilin (c 0) (c 0) := by
        rw [hxcoord, map_add, map_smul, map_smul, hc01, smul_zero, add_zero]
        rw [smul_eq_mul]
      rw [hp] at hx0
      have hdiag : Q.polarBilin (c 0) (c 0) = 2 := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hc0]
        norm_num
      rw [hdiag] at hx0
      exact (mul_eq_zero.mp hx0).resolve_right h2
    have hcoef1 : a1 = 0 := by
      have hp : Q.polarBilin ((s : K)⁻¹ • c 1) x =
          a1 * ((s : K)⁻¹ * Q.polarBilin (c 1) (c 1)) := by
        rw [hxcoord]
        simp only [map_add, map_smul, LinearMap.smul_apply, hc10, smul_zero, zero_add,
          smul_eq_mul]
        ring
      rw [hp] at hx1
      have hdiag : Q.polarBilin (c 1) (c 1) = 2 * Q (c 1) := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
        norm_num
      rw [hdiag] at hx1
      have hsne' : (s : K)⁻¹ ≠ 0 := inv_ne_zero hsne
      have hc1ne'' : Q (c 1) ≠ 0 := hc1ne'
      have hfactor : ((s : K)⁻¹ * (2 * Q (c 1))) ≠ 0 :=
        mul_ne_zero hsne' (mul_ne_zero h2 hc1ne'')
      exact (mul_eq_zero.mp hx1).resolve_right hfactor
    rw [hxcoord, hcoef0, hcoef1, zero_smul, zero_smul, add_zero]


private theorem squareScalar_eigenspaceEquiv_apply
    (h2 : (2 : K) ≠ 0) (T : Module.End K W)
    (hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W))
    (x : T.eigenspace 1) (y : T.eigenspace (-1)) :
    CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
      T 1 one_ne_zero h2 hT2 (x, y) = x.val + y.val := by
  simp [CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv,
    Submodule.coe_prodEquivOfIsCompl, LinearMap.coprod_apply]

private theorem positiveCentralizer_symm_apply
    (h2 : (2 : K) ≠ 0) (T : Module.End K W)
    (hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W))
    (hself : ∀ x y : W, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace 1).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-1)).subtype))
    (x : T.eigenspace 1) (y : T.eigenspace (-1)) :
    ((CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positiveOrthogonalCentralizerEquiv
        Q T 1 one_ne_zero h2 hT2 hself).symm g).val.val (x.val + y.val) =
      ((g.1 : T.eigenspace 1 ≃ₗ[K] T.eigenspace 1) x).val +
        ((g.2 : T.eigenspace (-1) ≃ₗ[K] T.eigenspace (-1)) y).val := by
  have h := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positiveOrthogonalExtension_apply
    Q T 1 one_ne_zero h2 hT2 hself g (x, y)
  rwa [squareScalar_eigenspaceEquiv_apply] at h

private theorem nonsquare_action_data
    (Q : QuadraticForm K W) (h2 : (2 : K) ≠ 0) (T : Module.End K W)
    (hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W))
    (hself : ∀ x y : W, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    {b1 : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace 1).subtype)}
    {b2 : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-1)).subtype)}
    {u1 : T.eigenspace 1} {u2 : T.eigenspace (-1)}
    (hu1 : (Q.comp (T.eigenspace 1).subtype) u1 = 1)
    (hu2 : (Q.comp (T.eigenspace (-1)).subtype) u2 = 1)
    (huv : Q.polarBilin (u1 : W) (u2 : W) = 0)
    (hb1u1 : (b1 : T.eigenspace 1 ≃ₗ[K] T.eigenspace 1) u1 = -u1)
    (hb2u2 : (b2 : T.eigenspace (-1) ≃ₗ[K] T.eigenspace (-1)) u2 = -u2)
    (hfix1 : ∀ x : T.eigenspace 1,
      (Q.comp (T.eigenspace 1).subtype).polarBilin u1 x = 0 →
        (b1 : T.eigenspace 1 ≃ₗ[K] T.eigenspace 1) x = x)
    (hfix2 : ∀ x : T.eigenspace (-1),
      (Q.comp (T.eigenspace (-1)).subtype).polarBilin u2 x = 0 →
        (b2 : T.eigenspace (-1) ≃ₗ[K] T.eigenspace (-1)) x = x) :
    let g : CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.orthogonalOperatorCentralizer Q T :=
      (CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positiveOrthogonalCentralizerEquiv
        Q T 1 one_ne_zero h2 hT2 hself).symm (b1, b2)
    Q (u1 : W) = 1 ∧ Q (u2 : W) = 1 ∧ Q.polarBilin (u1 : W) (u2 : W) = 0 ∧
      (g : W ≃ₗ[K] W) (u1 : W) = -(u1 : W) ∧
      (g : W ≃ₗ[K] W) (u2 : W) = -(u2 : W) ∧
      (∀ x : W, Q.polarBilin (u1 : W) x = 0 → Q.polarBilin (u2 : W) x = 0 →
        (g : W ≃ₗ[K] W) x = x) := by
  dsimp only
  refine ⟨hu1, hu2, huv, ?_, ?_, ?_⟩
  · have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself (b1, b2) u1 0
    simpa [hb1u1] using hact
  · have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself (b1, b2) 0 u2
    simpa [hb2u2] using hact
  · intro x hx0 hx1
    obtain ⟨⟨xp, xm⟩, hx⟩ :=
      (CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
        T 1 one_ne_zero h2 hT2).surjective x
    have hxsum : x = (xp : W) + (xm : W) := by
      rw [← hx, squareScalar_eigenspaceEquiv_apply]
    have hxp0 : (Q.comp (T.eigenspace 1).subtype).polarBilin u1 xp = 0 := by
      have h := hx0
      rw [hxsum, map_add] at h
      have hxm : Q.polarBilin (u1 : W) (xm : W) = 0 :=
        CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
          Q.polarBilin T 1 one_ne_zero h2 hself u1.val xm.val u1.property xm.property
      rw [hxm, add_zero] at h
      exact h
    have hxm1 : (Q.comp (T.eigenspace (-1)).subtype).polarBilin u2 xm = 0 := by
      have h := hx1
      rw [hxsum, map_add] at h
      have hxp : Q.polarBilin (u2 : W) (xp : W) = 0 := by
        have ho := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
          Q.polarBilin T 1 one_ne_zero h2 hself xp.val u2.val xp.property u2.property
        rw [QuadraticMap.polarBilin_apply_apply] at ho ⊢
        rw [QuadraticMap.polar_comm]
        exact ho
      rw [hxp, zero_add] at h
      exact h
    have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself (b1, b2) xp xm
    have hfix1' := hfix1 xp hxp0
    have hfix2' := hfix2 xm hxm1
    rw [hxsum, hact, hfix1', hfix2']

theorem exists_central_plane_negation_of_sylow
    (Q : QuadraticForm K W) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate)
    (e : Basis (Fin 4) K W) (he : ∀ i, Q (e i) = 1)
    (horth : ∀ i j : Fin 4, i ≠ j → Q.polarBilin (e i) (e j) = 0)
    (A : TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA2 : A * A = 1) (hA1 : A ≠ 1)
    (hAneg : ((A : W ≃ₗ[K] W) : W →ₗ[K] W) ≠ -1)
    (R : Sylow 2 (Subgroup.centralizer
      ({A} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)))) :
    ∃ b : TauCeti.QuadraticMap.orthogonalGroup Q,
      b ∈ (Subgroup.center R).map
        ((Subgroup.centralizer ({A} : Set
          (TauCeti.QuadraticMap.orthogonalGroup Q))).subtype.comp
          (R : Subgroup (Subgroup.centralizer
            ({A} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)))).subtype) ∧
      b * b = 1 ∧ b ≠ 1 ∧
      ∃ u v : W, Q u = 1 ∧ Q v = 1 ∧ Q.polarBilin u v = 0 ∧
        (b : W ≃ₗ[K] W) u = -u ∧ (b : W ≃ₗ[K] W) v = -v ∧
        (∀ x : W, Q.polarBilin u x = 0 → Q.polarBilin v x = 0 →
          (b : W ≃ₗ[K] W) x = x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  let T : Module.End K W := ((A : W ≃ₗ[K] W)).toLinearMap
  have hT2 : T * T = (1 : K) ^ 2 • (1 : Module.End K W) := by
    ext v
    have hmul : (A : W ≃ₗ[K] W) * (A : W ≃ₗ[K] W) = 1 := by
      have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (g : W ≃ₗ[K] W)) hA2
      simpa using h
    have h := congrArg (fun g : W ≃ₗ[K] W => g v) hmul
    have hv : (A : W ≃ₗ[K] W) ((A : W ≃ₗ[K] W) v) = v := by
      simpa [LinearEquiv.mul_apply] using h
    change (A : W ≃ₗ[K] W) ((A : W ≃ₗ[K] W) v) = (1 : K) ^ 2 • v
    rw [one_pow, one_smul, hv]
  have hself : ∀ x y : W, Q.polarBilin (T x) y = Q.polarBilin x (T y) := by
    intro x y
    have hA2' : (A : W ≃ₗ[K] W) * (A : W ≃ₗ[K] W) = 1 := by
      have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (g : W ≃ₗ[K] W)) hA2
      simpa using h
    have h := CFSG.RankThree.OrthogonalInvolutions.polar_apply_eq_polar_apply
      (Q := Q) (t := (A : W ≃ₗ[K] W)) A.property hA2' x y
    simpa [T, QuadraticMap.polarBilin_apply_apply] using h
  have hdisc0 : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q (QuadraticMap.nondegenerate_polar_iff.mp hQ)) = 0 :=
    discr_eq_zero_of_unit_basis hQ e he horth
  have hnde :=
    CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positive_adjoint_eigenspaces_nondegenerate
      Q.polarBilin hQ
      (LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q))
      T 1 one_ne_zero h2 hT2 hself
  have hplusnde : (Q.comp (T.eigenspace 1).subtype).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp hnde.1
  have hminusnde : (Q.comp (T.eigenspace (-1)).subtype).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp hnde.2
  have hdiscsum : TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace 1).subtype) hplusnde) +
      TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.comp (T.eigenspace (-1)).subtype) hminusnde) = 0 :=
    discr_eigenspaces_sum h2 hQ T hT2 hself hdisc0
  have hcases := eigenspace_cases hodd hQ A hA2 hA1 hAneg e he
  have hdimW : Module.finrank K W = 4 := by
    rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hdimsum : Module.finrank K (T.eigenspace 1) + Module.finrank K (T.eigenspace (-1)) = 4 := by
    rw [← hdimW]
    exact CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspace_finrank
      T 1 one_ne_zero h2 hT2
  let O : Type _ := TauCeti.QuadraticMap.orthogonalGroup Q
  let C : Subgroup O := Subgroup.centralizer ({A} : Set O)
  let C' : Subgroup O :=
    CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.orthogonalOperatorCentralizer Q T
  have hCeq : C = C' := centralizer_eq_operator A
  let φ : C ≃* C' := MulEquiv.subgroupCongr hCeq
  let R' : Sylow 2 C' := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective R
  let X : Type _ := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace 1).subtype)
  let Y : Type _ := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-1)).subtype)
  let e : C' ≃* (X × Y) :=
    CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positiveOrthogonalCentralizerEquiv
      Q T 1 one_ne_zero h2 hT2 hself
  let S : Sylow 2 (X × Y) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R'
  let S1 : Sylow 2 X := Sylow.mapSurjective (f := MonoidHom.fst X Y)
    (fun x => ⟨(x, 1), rfl⟩) S
  let S2 : Sylow 2 Y := Sylow.mapSurjective (f := MonoidHom.snd X Y)
    (fun y => ⟨(1, y), rfl⟩) S
  have hSprod : (S : Subgroup (X × Y)) = (S1 : Subgroup X).prod (S2 : Subgroup Y) := by
    refine (S.is_maximal' (Q := (S1 : Subgroup X).prod (S2 : Subgroup Y)) ?_ ?_).symm
    · have hpg : IsPGroup 2 (↥S1 × ↥S2) := IsPGroup.prod S1.isPGroup' S2.isPGroup'
      exact hpg.of_equiv (Subgroup.prodEquiv (S1 : Subgroup X) (S2 : Subgroup Y)).symm
    · intro x hx
      rw [Subgroup.mem_prod]
      exact ⟨Subgroup.mem_map_of_mem (f := MonoidHom.fst X Y) hx,
        Subgroup.mem_map_of_mem (f := MonoidHom.snd X Y) hx⟩
  have fromPair : ∀ (bp : X × Y), bp ∈ (S : Subgroup (X × Y)) →
      (∀ y : X × Y, y ∈ (S : Subgroup (X × Y)) → y * bp = bp * y) →
      ∃ c' : C', c' ∈ (R' : Subgroup C') ∧ e c' = bp ∧
        (∀ r : C', r ∈ (R' : Subgroup C') → r * c' = c' * r) ∧
        (((φ.symm c' : C) : O) ∈ (Subgroup.center R).map
            (C.subtype.comp (R : Subgroup C).subtype)) := by
    intro bp hbp hbpcent
    have hbpmap : bp ∈ Subgroup.map e.toMonoidHom (R' : Subgroup C') := by
      rw [← Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R']
      exact hbp
    obtain ⟨c', hc'R, hc'eqm⟩ := Subgroup.mem_map.mp hbpmap
    have hc'eq : e c' = bp := hc'eqm
    have hc'cent : ∀ r : C', r ∈ (R' : Subgroup C') → r * c' = c' * r := by
      intro r hr
      apply e.injective
      have hrS : e r ∈ (S : Subgroup (X × Y)) := by
        rw [show (S : Subgroup (X × Y)) =
          Subgroup.map e.toMonoidHom (R' : Subgroup C') from
          Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R']
        exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
      have h := hbpcent (e r) hrS
      calc e (r * c') = e r * e c' := map_mul e r c'
        _ = e r * bp := by rw [hc'eq]
        _ = bp * e r := h
        _ = e c' * e r := by rw [hc'eq]
        _ = e (c' * r) := (map_mul e c' r).symm
    have hcR : (φ.symm c' : C) ∈ (R : Subgroup C) := by
      have hmap : c' ∈ Subgroup.map φ.toMonoidHom (R : Subgroup C) := by
        rw [← Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective R]
        exact hc'R
      obtain ⟨c, hcR, hceq⟩ := Subgroup.mem_map.mp hmap
      have hceq' : φ c = c' := hceq
      have hc : c = φ.symm c' := by
        apply φ.injective
        rw [hceq', φ.apply_symm_apply]
      rwa [hc] at hcR
    have hcenter : (⟨(φ.symm c' : C), hcR⟩ : R) ∈ Subgroup.center R := by
      refine Subgroup.mem_center_iff.mpr ?_
      intro r
      apply Subtype.ext
      apply φ.injective
      have hr' : φ (r : C) ∈ (R' : Subgroup C') := by
        rw [show (R' : Subgroup C') = Subgroup.map φ.toMonoidHom (R : Subgroup C) from
          Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective R]
        exact Subgroup.mem_map.mpr ⟨(r : C), r.2, rfl⟩
      have h := hc'cent (φ (r : C)) hr'
      calc φ ((r : C) * (φ.symm c' : C))
          = φ (r : C) * φ (φ.symm c') := map_mul φ (r : C) (φ.symm c')
        _ = φ (r : C) * c' := by rw [φ.apply_symm_apply]
        _ = c' * φ (r : C) := h
        _ = φ (φ.symm c') * φ (r : C) := by rw [φ.apply_symm_apply]
        _ = φ ((φ.symm c' : C) * (r : C)) := (map_mul φ (φ.symm c') (r : C)).symm
        _ = φ (((⟨(φ.symm c' : C), hcR⟩ : R) * r : R) : C) := by rfl
    refine ⟨c', hc'R, hc'eq, hc'cent, ?_⟩
    exact Subgroup.mem_map.mpr ⟨⟨(φ.symm c' : C), hcR⟩, hcenter, rfl⟩
  rcases hcases with hd1 | hd2 | hd3
  ·
    have hd1' : Module.finrank K (T.eigenspace (-1)) = 1 := hd1
    have hplusdim : Module.finrank K (T.eigenspace 1) = 3 := by omega
    obtain ⟨b1, hb1S1, hb1cent, hb1sq, hb1ne, u1, v1, hu1, hv1, huv1, hb1u1, hb1v1, hfix1⟩ :=
      CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow.exists_central_plane_negation_of_sylow
        (Q := Q.comp (T.eigenspace 1).subtype) hodd
        (QuadraticMap.nondegenerate_polar_iff.mpr hplusnde) hplusdim S1
    let bp : X × Y := (b1, 1)
    have hbpS : bp ∈ (S : Subgroup (X × Y)) := by
      rw [hSprod, Subgroup.mem_prod]
      exact ⟨hb1S1, (S2 : Subgroup Y).one_mem⟩
    have hbpcent : ∀ y : X × Y, y ∈ (S : Subgroup (X × Y)) → y * bp = bp * y := by
      intro y hy
      rw [hSprod, Subgroup.mem_prod] at hy
      change (y.1 * b1, y.2 * (1 : Y)) = (b1 * y.1, (1 : Y) * y.2)
      rw [mul_one, one_mul, hb1cent y.1 hy.1]
    obtain ⟨c', hc'R, hc'eq, hc'cent, hbImage⟩ := fromPair bp hbpS hbpcent
    refine ⟨((φ.symm c' : C) : O), hbImage, ?_, ?_, (u1 : W), (v1 : W), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hbp_sq : bp * bp = 1 := by
        ext <;> simp [bp, hb1sq]
      have hc'sq : c' * c' = 1 := by
        apply e.injective
        rw [map_mul, hc'eq, hbp_sq, map_one]
      have h := congrArg (fun x : C' => (x : O)) hc'sq
      have hcoe : ((φ.symm c' : C) : O) = (c' : O) := rfl
      rw [hcoe]
      exact h
    · intro hb1'
      apply hb1ne
      have hb1'' : (φ.symm c' : C) = 1 := Subtype.ext hb1'
      have hc'1 : c' = 1 := by
        have h := congrArg φ hb1''
        simpa using h
      have hbp1 : bp = 1 := by rw [← hc'eq, hc'1, map_one]
      simpa [bp] using congrArg Prod.fst hbp1
    · exact hu1
    · exact hv1
    · exact huv1
    ·
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp u1 0
      change (((φ.symm c' : C) : O) : W ≃ₗ[K] W) (u1 : W) = -(u1 : W)
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      have h : (e.symm bp : C').val.val (u1 : W) = - (u1 : W) := by
        have := hact
        simpa [bp, hb1u1] using this
      exact h
    ·
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp v1 0
      change (((φ.symm c' : C) : O) : W ≃ₗ[K] W) (v1 : W) = -(v1 : W)
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      have h : (e.symm bp : C').val.val (v1 : W) = - (v1 : W) := by
        have := hact
        simpa [bp, hb1v1] using this
      exact h
    ·
      intro x hx0 hx1
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      let ee := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
        T 1 one_ne_zero h2 hT2
      obtain ⟨⟨xp, xm⟩, hx⟩ := ee.surjective x
      have hxsum : x = (xp : W) + (xm : W) := by
        rw [← hx, squareScalar_eigenspaceEquiv_apply]
      have hxp0 : (Q.comp (T.eigenspace 1).subtype).polarBilin u1 xp = 0 := by
        have h := hx0
        rw [hxsum, map_add] at h
        have hxm : Q.polarBilin (u1 : W) (xm : W) = 0 :=
          CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
            Q.polarBilin T 1 one_ne_zero h2 hself u1.val xm.val u1.property xm.property
        rw [hxm, add_zero] at h
        exact h
      have hxp1 : (Q.comp (T.eigenspace 1).subtype).polarBilin v1 xp = 0 := by
        have h := hx1
        rw [hxsum, map_add] at h
        have hxm : Q.polarBilin (v1 : W) (xm : W) = 0 :=
          CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
            Q.polarBilin T 1 one_ne_zero h2 hself v1.val xm.val v1.property xm.property
        rw [hxm, add_zero] at h
        exact h
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp xp xm
      have hfix := hfix1 xp hxp0 hxp1
      rw [← hx]
      rw [show (e.symm bp : C').val.val (ee (xp, xm)) = _ from hact]
      rw [squareScalar_eigenspaceEquiv_apply]
      simp [bp, hfix]
  ·
    have hd2' : Module.finrank K (T.eigenspace (-1)) = 2 := hd2
    have hplusdim2 : Module.finrank K (T.eigenspace 1) = 2 := by omega
    let Qp : QuadraticForm K (T.eigenspace 1) := Q.comp (T.eigenspace 1).subtype
    let Qm : QuadraticForm K (T.eigenspace (-1)) := Q.comp (T.eigenspace (-1)).subtype
    have hpluspol : Qp.polarBilin.Nondegenerate :=
      QuadraticMap.nondegenerate_polar_iff.mpr hplusnde
    have hminuspol : Qm.polarBilin.Nondegenerate :=
      QuadraticMap.nondegenerate_polar_iff.mpr hminusnde
    have hdiscsum' : TauCeti.RegularFormClass.discr (TauCeti.formClass Qp hplusnde) +
        TauCeti.RegularFormClass.discr (TauCeti.formClass Qm hminusnde) = 0 := hdiscsum
    by_cases hsq : TauCeti.RegularFormClass.discr (TauCeti.formClass Qm hminusnde) = 0
    ·
      obtain ⟨u3, v3, hu3, hv3, huv3, hspan⟩ :=
        plane_unit_basis_of_square (Q := Qm) hodd hminuspol hd2' hsq
      let aC : C := ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have haC2 : aC * aC = 1 := by
        apply Subtype.ext
        simpa [aC] using hA2
      have haC1 : aC ≠ 1 := by
        intro h
        have hAO : (aC : O) = 1 := by
          simpa using congrArg Subtype.val h
        exact hA1 (by simpa [aC] using hAO)
      have horder : orderOf aC = 2 := by
        apply orderOf_eq_prime (p := 2)
        · rw [pow_two]; exact haC2
        · exact haC1
      have hP : IsPGroup 2 (Subgroup.zpowers aC) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder]; norm_num)
      have hmemcenter : aC ∈ Subgroup.center C := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        simpa [aC] using (Subgroup.mem_centralizer_singleton_iff.mp x.2)
      have hN : (Subgroup.zpowers aC).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hmemcenter)
      have hle : Subgroup.zpowers aC ≤ (R : Subgroup C) :=
        IsPGroup.le_sylow_of_normal hP R
      have haCR : aC ∈ (R : Subgroup C) := hle (Subgroup.mem_zpowers aC)
      have hcenterR : (⟨aC, haCR⟩ : R) ∈ Subgroup.center R := by
        refine Subgroup.mem_center_iff.mpr ?_
        intro r
        apply Subtype.ext
        apply Subtype.ext
        have hr : ((r.1 : C) : O) ∈ Subgroup.centralizer ({A} : Set O) := (r.1).2
        simpa [aC] using (Subgroup.mem_centralizer_singleton_iff.mp hr)
      have hbImage : (aC : O) ∈ (Subgroup.center R).map
          (C.subtype.comp (R : Subgroup C).subtype) :=
        Subgroup.mem_map.mpr ⟨⟨aC, haCR⟩, hcenterR, rfl⟩
      have hactu : ((aC : O) : W ≃ₗ[K] W) (u3 : W) = -(u3 : W) := by
        have h := Module.End.mem_eigenspace_iff.mp u3.property
        simpa [aC, T] using h
      have hactv : ((aC : O) : W ≃ₗ[K] W) (v3 : W) = -(v3 : W) := by
        have h := Module.End.mem_eigenspace_iff.mp v3.property
        simpa [aC, T] using h
      refine ⟨(aC : O), hbImage, ?_, ?_, (u3 : W), (v3 : W), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [aC] using hA2
      · intro h
        have hAO : (aC : O) = 1 := by
          simpa using congrArg Subtype.val h
        exact hA1 (by simpa [aC] using hAO)
      · exact hu3
      · exact hv3
      · exact huv3
      · exact hactu
      · exact hactv
      · intro x hx0 hx1
        let ee := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
          T 1 one_ne_zero h2 hT2
        obtain ⟨⟨xp, xm⟩, hx⟩ := ee.surjective x
        have hxsum : x = (xp : W) + (xm : W) := by
          rw [← hx, squareScalar_eigenspaceEquiv_apply]
        have hxm0 : Qm.polarBilin u3 xm = 0 := by
          have h := hx0
          rw [hxsum, map_add] at h
          have hxp : Q.polarBilin (u3 : W) (xp : W) = 0 := by
            have ho := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
              Q.polarBilin T 1 one_ne_zero h2 hself xp.val u3.val xp.property u3.property
            rw [QuadraticMap.polarBilin_apply_apply] at ho ⊢
            rw [QuadraticMap.polar_comm]
            exact ho
          rw [hxp, zero_add] at h
          exact h
        have hxm1 : Qm.polarBilin v3 xm = 0 := by
          have h := hx1
          rw [hxsum, map_add] at h
          have hxp : Q.polarBilin (v3 : W) (xp : W) = 0 := by
            have ho := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
              Q.polarBilin T 1 one_ne_zero h2 hself xp.val v3.val xp.property v3.property
            rw [QuadraticMap.polarBilin_apply_apply] at ho ⊢
            rw [QuadraticMap.polar_comm]
            exact ho
          rw [hxp, zero_add] at h
          exact h
        have hxmzero : xm = 0 := hspan xm hxm0 hxm1
        have hfixp : ((aC : O) : W ≃ₗ[K] W) (xp : W) = (xp : W) := by
          have h := Module.End.mem_eigenspace_iff.mp xp.property
          simpa [aC, T] using h
        rw [hxsum, map_add, hxmzero, hfixp]
        simp
    ·
      have hdiscplus : TauCeti.RegularFormClass.discr (TauCeti.formClass Qp hplusnde) ≠ 0 := by
        intro h
        apply hsq
        have hs := hdiscsum'
        rw [h, zero_add] at hs
        exact hs
      obtain ⟨b1, hb1S1, hb1cent, hb1sq, hb1ne, u1, hu1, hb1u1, hfix1⟩ :=
        plane_signchange_unit_of_nonsquare (Q := Qp) hodd hpluspol hplusdim2 hdiscplus S1
      obtain ⟨b2, hb2S2, hb2cent, hb2sq, hb2ne, u2, hu2, hb2u2, hfix2⟩ :=
        plane_signchange_unit_of_nonsquare (Q := Qm) hodd hminuspol hd2' hsq S2
      have huv : Q.polarBilin (u1 : W) (u2 : W) = 0 :=
        CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
          Q.polarBilin T 1 one_ne_zero h2 hself u1.val u2.val u1.property u2.property
      let bp : X × Y := (b1, b2)
      have hbpS : bp ∈ (S : Subgroup (X × Y)) := by
        rw [hSprod, Subgroup.mem_prod]
        exact ⟨hb1S1, hb2S2⟩
      have hbpcent : ∀ y : X × Y, y ∈ (S : Subgroup (X × Y)) → y * bp = bp * y := by
        intro y hy
        rw [hSprod, Subgroup.mem_prod] at hy
        change (y.1 * b1, y.2 * b2) = (b1 * y.1, b2 * y.2)
        rw [hb1cent y.1 hy.1, hb2cent y.2 hy.2]
      obtain ⟨c', hc'R, hc'eq, hc'cent, hbImage⟩ := fromPair bp hbpS hbpcent
      have hdata := nonsquare_action_data (Q := Q) h2 T hT2 hself
        (b1 := b1) (b2 := b2) (u1 := u1) (u2 := u2) hu1 hu2 huv hb1u1 hb2u2 hfix1 hfix2
      obtain ⟨hQ1, hQ2, hQpol, hgu, hgv, hgfix⟩ := hdata
      have hb_eq_g : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) =
          (((CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.positiveOrthogonalCentralizerEquiv
            Q T 1 one_ne_zero h2 hT2 hself).symm bp : C') : W ≃ₗ[K] W) := by
        have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
        rw [show ((φ.symm c' : C) : O) = (c' : O) from rfl, hc']
      refine ⟨((φ.symm c' : C) : O), hbImage, ?_, ?_, (u1 : W), (u2 : W),
        hQ1, hQ2, hQpol, ?_, ?_, ?_⟩
      · have hbp_sq : bp * bp = 1 := by
          ext <;> simp [bp, hb1sq, hb2sq]
        have hc'sq : c' * c' = 1 := by
          apply e.injective
          rw [map_mul, hc'eq, hbp_sq, map_one]
        have h := congrArg (fun x : C' => (x : O)) hc'sq
        have hcoe : ((φ.symm c' : C) : O) = (c' : O) := rfl
        rw [hcoe]
        exact h
      · intro hb1'
        apply hb1ne
        have hb1'' : (φ.symm c' : C) = 1 := Subtype.ext hb1'
        have hc'1 : c' = 1 := by
          have h := congrArg φ hb1''
          simpa using h
        have hbp1 : bp = 1 := by rw [← hc'eq, hc'1, map_one]
        simpa [bp] using congrArg Prod.fst hbp1
      · rw [hb_eq_g]; exact hgu
      · rw [hb_eq_g]; exact hgv
      · rw [hb_eq_g]; exact hgfix
  ·
    have hminusdim : Module.finrank K (T.eigenspace (-1)) = 3 := hd3
    obtain ⟨b3, hb3S2, hb3cent, hb3sq, hb3ne, u3, v3, hu3, hv3, huv3, hb3u3, hb3v3, hfix3⟩ :=
      CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow.exists_central_plane_negation_of_sylow
        (Q := Q.comp (T.eigenspace (-1)).subtype) hodd
        (QuadraticMap.nondegenerate_polar_iff.mpr hminusnde) hminusdim S2
    let bp : X × Y := (1, b3)
    have hbpS : bp ∈ (S : Subgroup (X × Y)) := by
      rw [hSprod, Subgroup.mem_prod]
      exact ⟨(S1 : Subgroup X).one_mem, hb3S2⟩
    have hbpcent : ∀ y : X × Y, y ∈ (S : Subgroup (X × Y)) → y * bp = bp * y := by
      intro y hy
      rw [hSprod, Subgroup.mem_prod] at hy
      change (y.1 * (1 : X), y.2 * b3) = ((1 : X) * y.1, b3 * y.2)
      rw [mul_one, one_mul, hb3cent y.2 hy.2]
    obtain ⟨c', hc'R, hc'eq, hc'cent, hbImage⟩ := fromPair bp hbpS hbpcent
    refine ⟨((φ.symm c' : C) : O), hbImage, ?_, ?_, (u3 : W), (v3 : W), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hbp_sq : bp * bp = 1 := by
        ext <;> simp [bp, hb3sq]
      have hc'sq : c' * c' = 1 := by
        apply e.injective
        rw [map_mul, hc'eq, hbp_sq, map_one]
      have h := congrArg (fun x : C' => (x : O)) hc'sq
      have hcoe : ((φ.symm c' : C) : O) = (c' : O) := rfl
      rw [hcoe]
      exact h
    · intro hb1
      apply hb3ne
      have hb1' : (φ.symm c' : C) = 1 := Subtype.ext hb1
      have hc'1 : c' = 1 := by
        have h := congrArg φ hb1'
        simpa using h
      have hbp1 : bp = 1 := by rw [← hc'eq, hc'1, map_one]
      simpa [bp] using congrArg Prod.snd hbp1
    · exact hu3
    · exact hv3
    · exact huv3
    ·
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp 0 u3
      change (((φ.symm c' : C) : O) : W ≃ₗ[K] W) (u3 : W) = -(u3 : W)
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      have h : (e.symm bp : C').val.val (u3 : W) = - (u3 : W) := by
        have := hact
        simpa [bp, hb3u3] using this
      exact h
    ·
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp 0 v3
      change (((φ.symm c' : C) : O) : W ≃ₗ[K] W) (v3 : W) = -(v3 : W)
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      have h : (e.symm bp : C').val.val (v3 : W) = - (v3 : W) := by
        have := hact
        simpa [bp, hb3v3] using this
      exact h
    ·
      intro x hx0 hx1
      have hc' : c' = e.symm bp := e.injective (by rw [hc'eq, e.apply_symm_apply])
      have hval : (((φ.symm c' : C) : O) : W ≃ₗ[K] W) = (c' : W ≃ₗ[K] W) := rfl
      rw [hval, hc']
      let ee := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaceEquiv
        T 1 one_ne_zero h2 hT2
      obtain ⟨⟨xp, xm⟩, hx⟩ := ee.surjective x
      have hxsum : x = (xp : W) + (xm : W) := by
        rw [← hx, squareScalar_eigenspaceEquiv_apply]
      have hxm0 : (Q.comp (T.eigenspace (-1)).subtype).polarBilin u3 xm = 0 := by
        have h := hx0
        rw [hxsum, map_add] at h
        have hxp : Q.polarBilin (u3 : W) (xp : W) = 0 := by
          have ho := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
            Q.polarBilin T 1 one_ne_zero h2 hself xp.val u3.val xp.property u3.property
          rw [QuadraticMap.polarBilin_apply_apply] at ho ⊢
          rw [QuadraticMap.polar_comm]
          exact ho
        rw [hxp, zero_add] at h
        exact h
      have hxm1 : (Q.comp (T.eigenspace (-1)).subtype).polarBilin v3 xm = 0 := by
        have h := hx1
        rw [hxsum, map_add] at h
        have hxp : Q.polarBilin (v3 : W) (xp : W) = 0 := by
          have ho := CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
            Q.polarBilin T 1 one_ne_zero h2 hself xp.val v3.val xp.property v3.property
          rw [QuadraticMap.polarBilin_apply_apply] at ho ⊢
          rw [QuadraticMap.polar_comm]
          exact ho
        rw [hxp, zero_add] at h
        exact h
      have hact := positiveCentralizer_symm_apply (Q := Q) h2 T hT2 hself bp xp xm
      have hfix := hfix3 xm hxm0 hxm1
      rw [← hx]
      rw [show (e.symm bp : C').val.val (ee (xp, xm)) = _ from hact]
      rw [squareScalar_eigenspaceEquiv_apply]
      simp [bp, hfix]

end CFSG.ClassicalGroups.Orthogonal.FourCentralizerPlaneNegation
