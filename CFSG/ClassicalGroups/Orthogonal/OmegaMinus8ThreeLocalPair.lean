module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalModel
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType
import CFSG.LinearAlgebra.ChebyshevPow
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K] {b c : K}

private def emul (a z : K × K) : K × K :=
  (a.1 * z.1 - a.2 * z.2, a.1 * z.2 + a.2 * z.1 - a.2 * z.2)

private def econj (a : K × K) : K × K := (a.1 - a.2, -a.2)

private theorem emul_add (a z w : K × K) : emul a (z + w) = emul a z + emul a w := by
  ext <;> simp [emul] <;> ring

private theorem emul_smul (a z : K × K) (r : K) : emul a (r • z) = r • emul a z := by
  ext <;> simp [emul] <;> ring

private def emulLin (a : K × K) : (K × K) →ₗ[K] (K × K) where
  toFun := emul a
  map_add' := emul_add a
  map_smul' r z := emul_smul a z r

private theorem emul_rotLE (a z : K × K) : emul a (rotLE K z) = rotLE K (emul a z) := by
  ext <;> simp [emul, rotLE] <;> ring

private theorem emul_rotPow (a : K × K) (k : ZMod 3) (z : K × K) :
    emul a (rotPow K k z) = rotPow K k (emul a z) := by
  have h : ∀ n : ℕ, emul a ((rotLE K ^ n) z) = (rotLE K ^ n) (emul a z) := by
    intro n
    induction n generalizing z with
    | zero => simp
    | succ n ih =>
      change emul a ((rotLE K ^ n) (rotLE K z)) = (rotLE K ^ (n + 1)) (emul a z)
      rw [pow_succ, LinearEquiv.mul_apply, ih (z := rotLE K z), emul_rotLE]
  unfold rotPow
  exact h k.val

private theorem rotForm_pair (α β z₁ z₂ : K × K) :
    rotForm K (emul α z₁ + emul β z₂) + rotForm K (emul (-econj β) z₁ + emul (econj α) z₂)
      = (rotForm K α + rotForm K β) * (rotForm K z₁ + rotForm K z₂) := by
  simp [rotForm_apply, emul, econj]
  ring

private theorem rotForm_pairMap (τ : K) (β z₁ z₂ : K × K)
    (hβ : rotForm K β = 1 - τ ^ 2) :
    rotForm K (emul (0, -τ) z₁ + emul β z₂)
      + rotForm K (emul (-econj β) z₁ + emul (econj ((0 : K), -τ)) z₂)
      = rotForm K z₁ + rotForm K z₂ := by
  rw [rotForm_pair]
  have hα : rotForm K ((0 : K), -τ) = τ ^ 2 := by
    rw [rotForm_apply]; ring
  rw [hα, hβ]
  ring

private def pairMap (α β : K × K) :
    ((K × K) × (K × K)) →ₗ[K] ((K × K) × (K × K)) :=
  LinearMap.prod
    ((emulLin α).comp (LinearMap.fst K (K × K) (K × K)) +
      (emulLin β).comp (LinearMap.snd K (K × K) (K × K)))
    ((emulLin (-econj β)).comp (LinearMap.fst K (K × K) (K × K)) +
      (emulLin (econj α)).comp (LinearMap.snd K (K × K) (K × K)))

private theorem pairMap_apply (α β : K × K) (z : (K × K) × (K × K)) :
    pairMap α β z =
      (emul α z.1 + emul β z.2, emul (-econj β) z.1 + emul (econj α) z.2) := by
  simp [pairMap, emulLin]

private theorem pairMap_general (α β : K × K) (z : (K × K) × (K × K)) :
    pairMap α β (pairMap α β z) - (2 * α.1 - α.2) • pairMap α β z
      + (rotForm K α + rotForm K β) • z = 0 := by
  simp only [pairMap_apply]
  ext <;> simp [emul, econj, rotForm_apply] <;> ring

private theorem pairMap_pairMap (τ : K) (β : K × K) (hβ : rotForm K β = 1 - τ ^ 2)
    (z : (K × K) × (K × K)) :
    pairMap (0, -τ) β (pairMap (0, -τ) β z) = τ • pairMap (0, -τ) β z - z := by
  have h := pairMap_general ((0 : K), -τ) β z
  have hTr : 2 * ((0 : K), -τ).1 - ((0 : K), -τ).2 = τ := by simp
  have hN : rotForm K ((0 : K), -τ) = τ ^ 2 := by
    rw [rotForm_apply]; ring
  rw [hTr, hN, hβ, show τ ^ 2 + (1 - τ ^ 2) = (1 : K) by ring, one_smul] at h
  linear_combination h

private noncomputable def pairEquiv (τ : K) (β : K × K) (hβ : rotForm K β = 1 - τ ^ 2) :
    ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)) :=
  LinearEquiv.ofLinear (pairMap (0, -τ) β) (τ • 1 - pairMap (0, -τ) β)
    (by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Module.End.one_apply, map_sub, map_smul]
      rw [pairMap_pairMap τ β hβ]
      module)
    (by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Module.End.one_apply]
      rw [pairMap_pairMap τ β hβ]
      module)

private theorem pairEquiv_apply (τ : K) (β : K × K) (hβ : rotForm K β = 1 - τ ^ 2)
    (z : (K × K) × (K × K)) :
    pairEquiv τ β hβ z = pairMap (0, -τ) β z :=
  rfl

private theorem pairEquiv_sq (τ : K) (β : K × K) (hβ : rotForm K β = 1 - τ ^ 2) :
    (pairEquiv τ β hβ : Module.End K ((K × K) × (K × K))) ^ 2
      = τ • (pairEquiv τ β hβ : Module.End K ((K × K) × (K × K))) - 1 := by
  refine LinearMap.ext fun z => ?_
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, pairEquiv_apply]
  exact pairMap_pairMap τ β hβ z

private theorem det_eq_one_of_odd_orderOf
    {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c))
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgp : orderOf g = p) :
    LinearEquiv.det g = 1 := by
  have hsq : (QuadraticMap.orthogonalDet (wForm b c)) ⟨g, hg⟩ ^ 2 = 1 :=
    TauCeti.QuadraticMap.orthogonalDet_sq
      (nondegenerate_polarBilin_wForm hbc).1 _
  rw [QuadraticMap.orthogonalDet_apply] at hsq
  have hgp' : g ^ p = 1 := by rw [← hgp]; exact pow_orderOf_eq_one g
  have hpow : LinearEquiv.det g ^ p = 1 := by
    rw [← map_pow, hgp', map_one]
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hxp : LinearEquiv.det g ^ p = LinearEquiv.det g := by
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [← hxp, hpow]

private theorem exists_trace_sq_eq {g : (K × K) ≃ₗ[K] (K × K)}
    (hgdet : LinearEquiv.det g = 1) :
    ∃ τ : K, (g : Module.End K (K × K)) ^ 2 = τ • (g : Module.End K (K × K)) - 1 := by
  let B : Basis (Fin 2) K (K × K) := Basis.finTwoProd K
  let A : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix B B (g : K × K →ₗ[K] K × K)
  refine ⟨A.trace, ?_⟩
  have hA : A ^ 2 = A.trace • A - A.det • 1 :=
    Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two A
  have hdetA : A.det = 1 := by
    rw [LinearMap.det_toMatrix B (g : K × K →ₗ[K] K × K), ← LinearEquiv.coe_det, hgdet,
      Units.val_one]
  have hA' : A ^ 2 = A.trace • A - 1 := by
    rw [hdetA, one_smul] at hA
    exact hA
  have h := congrArg (LinearMap.toMatrixAlgEquiv B).symm hA'
  have hAe : (LinearMap.toMatrixAlgEquiv B).symm A = (g : K × K →ₗ[K] K × K) := by
    rw [show A = LinearMap.toMatrixAlgEquiv B (g : K × K →ₗ[K] K × K) from rfl,
      AlgEquiv.symm_apply_apply]
  simp only [map_pow, map_smul, map_sub, map_one] at h
  rw [hAe] at h
  exact h

private noncomputable def pairExtendFun
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    ModelSpace K :=
  (fun i : Fin 3 =>
      if i = 0 then (h (x.1 0, x.1 1)).1
      else if i = 1 then (h (x.1 0, x.1 1)).2
      else x.1 i, x.2)

private theorem pairExtendFun_fst_zero
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtendFun h x).1 0 = (h (x.1 0, x.1 1)).1 := by
  simp [pairExtendFun]

private theorem pairExtendFun_fst_one
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtendFun h x).1 1 = (h (x.1 0, x.1 1)).2 := by
  simp [pairExtendFun]

private theorem pairExtendFun_fst_two
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtendFun h x).1 2 = x.1 2 := by
  simp [pairExtendFun]

private noncomputable def pairExtend
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) :
    ModelSpace K ≃ₗ[K] ModelSpace K where
  toFun := pairExtendFun h
  invFun := pairExtendFun h.symm
  left_inv x := by
    refine Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp [pairExtendFun]
  right_inv x := by
    refine Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp [pairExtendFun]
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp only [pairExtendFun]
    · change (h ((x.1 0, x.1 1) + (y.1 0, y.1 1))).1
        = (h (x.1 0, x.1 1)).1 + (h (y.1 0, y.1 1)).1
      rw [h.map_add]; rfl
    · change (h ((x.1 0, x.1 1) + (y.1 0, y.1 1))).2
        = (h (x.1 0, x.1 1)).2 + (h (y.1 0, y.1 1)).2
      rw [h.map_add]; rfl
    · rfl
  map_smul' r x := by
    refine Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp only [pairExtendFun]
    · change (h (r • (x.1 0, x.1 1))).1 = r • (h (x.1 0, x.1 1)).1
      rw [h.map_smul]; rfl
    · change (h (r • (x.1 0, x.1 1))).2 = r • (h (x.1 0, x.1 1)).2
      rw [h.map_smul]; rfl
    · rfl

private theorem pairExtend_fst_zero
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtend h x).1 0 = (h (x.1 0, x.1 1)).1 :=
  pairExtendFun_fst_zero h x

private theorem pairExtend_fst_one
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtend h x).1 1 = (h (x.1 0, x.1 1)).2 :=
  pairExtendFun_fst_one h x

private theorem pairExtend_fst_two
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtend h x).1 2 = x.1 2 :=
  pairExtendFun_fst_two h x

private theorem pairExtend_snd
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (x : ModelSpace K) :
    (pairExtend h x).2 = x.2 :=
  rfl

private noncomputable def pairExtendHom :
    (((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) →*
      (ModelSpace K ≃ₗ[K] ModelSpace K) where
  toFun := pairExtend
  map_one' := by
    refine LinearEquiv.ext fun x => Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp [pairExtend, pairExtendFun]
  map_mul' h h' := by
    refine LinearEquiv.ext fun x => Prod.ext (funext fun i => ?_) rfl
    fin_cases i <;> simp [pairExtend, pairExtendFun, LinearEquiv.mul_apply]

private theorem pairExtend_injective : Function.Injective (pairExtend (K := K)) := by
  intro h h' hh
  refine LinearEquiv.ext fun z => ?_
  obtain ⟨z₁, z₂⟩ := z
  let x : ModelSpace K := (Pi.single (0 : Fin 3) z₁ + Pi.single (1 : Fin 3) z₂, 0)
  have h0 : (h (z₁, z₂)).1 = (h' (z₁, z₂)).1 := by
    have := congrArg (fun e : ModelSpace K ≃ₗ[K] ModelSpace K => (e x).1 0) hh
    simpa [pairExtend_fst_zero, x] using this
  have h1 : (h (z₁, z₂)).2 = (h' (z₁, z₂)).2 := by
    have := congrArg (fun e : ModelSpace K ≃ₗ[K] ModelSpace K => (e x).1 1) hh
    simpa [pairExtend_fst_one, x] using this
  exact Prod.ext h0 h1

private theorem pairExtend_mem_modelO
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)))
    (hpres : ∀ z : (K × K) × (K × K),
      rotForm K (h z).1 + rotForm K (h z).2 = rotForm K z.1 + rotForm K z.2) :
    pairExtend h ∈ modelO b c := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [modelForm_apply, modelForm_apply, pairExtend_snd, Fin.sum_univ_three, Fin.sum_univ_three,
    pairExtend_fst_zero, pairExtend_fst_one, pairExtend_fst_two, hpres (x.1 0, x.1 1)]

private theorem pairExtend_commute_cmEquiv
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)))
    (hrot : ∀ (k : ZMod 3) (z : (K × K) × (K × K)),
      h (rotPow K k z.1, rotPow K k z.2)
        = (rotPow K k (h z).1, rotPow K k (h z).2))
    {v : Fin 3 → ZMod 3} (hv : v 0 = v 1) :
    Commute (pairExtend h) (cmEquiv K v) := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, cmEquiv_apply, cmEquiv_apply]
  refine Prod.ext (funext fun i => ?_) rfl
  fin_cases i
  · change (h (rotPow K (v 0) (x.1 0), rotPow K (v 1) (x.1 1))).1
      = rotPow K (v 0) ((h (x.1 0, x.1 1)).1)
    rw [show rotPow K (v 1) (x.1 1) = rotPow K (v 0) (x.1 1) from by rw [hv],
      hrot (v 0) (x.1 0, x.1 1)]
  · change (h (rotPow K (v 0) (x.1 0), rotPow K (v 1) (x.1 1))).2
      = rotPow K (v 1) ((h (x.1 0, x.1 1)).2)
    rw [show rotPow K (v 0) (x.1 0) = rotPow K (v 1) (x.1 0) from by rw [hv],
      hrot (v 1) (x.1 0, x.1 1)]
  · change (fun i => rotPow K (v i) (x.1 i)) 2 = rotPow K (v 2) (x.1 2)
    rfl

private theorem pairExtend_commute_wExtend
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)))
    (g' : (K × K) ≃ₗ[K] (K × K)) :
    Commute (pairExtend h) (wExtend K g') := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rfl

private theorem pairExtend_apply_wVec
    (h : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K))) (q : K × K) :
    pairExtend h (wVec q) = wVec q := by
  refine Prod.ext (funext fun i => ?_) rfl
  fin_cases i
  · change (h ((0 : K × K), (0 : K × K))).1 = (0 : K × K)
    rw [show (((0 : K × K), (0 : K × K)) : (K × K) × (K × K)) = 0 from rfl, h.map_zero]
    rfl
  · change (h ((0 : K × K), (0 : K × K))).2 = (0 : K × K)
    rw [show (((0 : K × K), (0 : K × K)) : (K × K) × (K × K)) = 0 from rfl, h.map_zero]
    rfl
  · rfl

private theorem wForm_one_zero : wForm b c ((1 : K), 0) = 1 := by
  by_cases h : IsSplit K
  · rw [wForm_of_isSplit h, binForm_apply]; ring
  · rw [wForm_of_not_isSplit h, binForm_apply]; ring

private theorem wForm_smul_one_zero (lam : K) :
    wForm b c (lam • ((1 : K), 0) : K × K) = lam ^ 2 := by
  have h : (lam • ((1 : K), 0) : K × K) = (lam, 0) := by ext <;> simp
  rw [h]
  by_cases hs : IsSplit K
  · rw [wForm_of_isSplit hs, binForm_apply]; ring
  · rw [wForm_of_not_isSplit hs, binForm_apply]; ring

private theorem not_scalar_of_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c))
    (hgp : orderOf g = p) :
    ¬ ∃ lam : K, (g : Module.End K (K × K)) = lam • 1 := by
  rintro ⟨lam, hlam⟩
  have h1 : wForm b c ((lam, 0) : K × K) = 1 := by
    have h := CFSG.ClassicalGroups.Orthogonal.map_of_mem hg ((1 : K), 0)
    rw [wForm_one_zero] at h
    have hglam : g ((1 : K), 0) = (lam, 0) := by
      have h2 := congrArg (fun f : Module.End K (K × K) => f ((1 : K), 0)) hlam
      simpa [Module.End.one_apply] using h2
    rwa [hglam] at h
  have harg : (lam • ((1 : K), 0) : K × K) = (lam, 0) := by ext <;> simp
  have hsq : lam ^ 2 = 1 := by
    have h := wForm_smul_one_zero (b := b) (c := c) lam
    rw [harg, h1] at h
    exact h.symm
  have hgp' : (g : Module.End K (K × K)) ^ p = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := K) (M := K × K)) g p
    rw [show g ^ p = 1 from by rw [← hgp]; exact pow_orderOf_eq_one g, map_one,
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] at h
    exact h.symm
  have hlampow : lam ^ p = 1 := by
    have hpowsmul : (lam • (1 : Module.End K (K × K))) ^ p = lam ^ p • 1 := by
      rw [smul_pow, one_pow]
    have h := hgp'
    rw [hlam, hpowsmul] at h
    have h2 := congrArg (fun f : Module.End K (K × K) => f ((1 : K), 0)) h
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
    have h3 := congrArg Prod.fst h2
    simpa using h3
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hlameq : lam ^ p = lam := by
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [hlameq] at hlampow
  have hg1 : g = 1 := by
    apply LinearEquiv.toLinearMap_injective
    rw [hlam, hlampow, one_smul]
    rfl
  rw [hg1, orderOf_one] at hgp
  exact hp.ne_one hgp.symm

private theorem coeffs_eq_of_not_scalar {g : Module.End K (K × K)} {a a' : K}
    (h : 1 = a • g - a' • 1) (hns : ¬ ∃ lam : K, g = lam • 1) : a = 0 ∧ a' = -1 := by
  have ha : a = 0 := by
    by_contra ha
    refine hns ⟨a⁻¹ * (1 + a'), ?_⟩
    have h1 : a • g = (1 + a') • 1 := by
      rw [add_smul, one_smul]
      exact sub_eq_iff_eq_add.mp h.symm
    calc g = a⁻¹ • (a • g) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = (a⁻¹ * (1 + a')) • 1 := by rw [h1, smul_smul]
  refine ⟨ha, ?_⟩
  rw [ha, zero_smul, zero_sub] at h
  have h1 := congrArg (fun f : Module.End K (K × K) => (f ((1 : K), 0)).1) h
  simp only [Module.End.one_apply, LinearMap.neg_apply, LinearMap.smul_apply, Prod.fst_neg,
    Prod.smul_fst, smul_eq_mul, mul_one] at h1
  linear_combination h1

private theorem pairEquiv_ne_one (τ : K) (β : K × K)
    (hβ : rotForm K β = 1 - τ ^ 2) :
    pairEquiv τ β hβ ≠ 1 := by
  intro h
  have := congrArg (fun e : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)) =>
    (e (((1 : K), 0), ((0 : K), 0))).1.1) h
  simp [pairEquiv_apply, pairMap_apply, emul] at this

private theorem pairMap_rotPow (α β : K × K) (k : ZMod 3) (z : (K × K) × (K × K)) :
    pairMap α β (rotPow K k z.1, rotPow K k z.2)
      = (rotPow K k (pairMap α β z).1, rotPow K k (pairMap α β z).2) := by
  rw [pairMap_apply, pairMap_apply]
  simp only [emul_rotPow, map_add]

theorem exists_pairIsometry [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgp : orderOf g = p) :
    ∃ m ∈ modelO b c, orderOf m = p ∧
      (∀ w : Fin 3 → ZMod 3, w 0 = w 1 → Commute m (cmEquiv K w)) ∧
      (∀ g' : (K × K) ≃ₗ[K] (K × K), Commute m (wExtend K g')) ∧
      ∀ q : K × K, m (wVec q) = wVec q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdet := det_eq_one_of_odd_orderOf hg hbc hp hp2 hgp
  obtain ⟨τ, hτ⟩ := exists_trace_sq_eq hdet
  obtain ⟨β, hβ⟩ := exists_rotForm_eq h3 (1 - τ ^ 2)
  let M0 : ((K × K) × (K × K)) ≃ₗ[K] ((K × K) × (K × K)) := pairEquiv τ β hβ
  have hM0rel : (M0 : Module.End K ((K × K) × (K × K))) ^ 2
      = τ • (M0 : Module.End K ((K × K) × (K × K))) - 1 := pairEquiv_sq τ β hβ
  have hns : ¬ ∃ lam : K, (g : Module.End K (K × K)) = lam • 1 :=
    not_scalar_of_orderOf hp hp2 hg hgp
  have hgpow : (g : Module.End K (K × K)) ^ p = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := K) (M := K × K)) g p
    rw [show g ^ p = 1 from by rw [← hgp]; exact pow_orderOf_eq_one g, map_one,
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] at h
    exact h.symm
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  have hgS := CFSG.LinearAlgebra.pow_succ_eq_chebyshevS hτ (p - 1)
  rw [hp1, hgpow] at hgS
  obtain ⟨ha, ha'⟩ := coeffs_eq_of_not_scalar hgS hns
  have hM0powEnd : (M0 : Module.End K ((K × K) × (K × K))) ^ p = 1 := by
    have h := CFSG.LinearAlgebra.pow_succ_eq_chebyshevS hM0rel (p - 1)
    rwa [hp1, ha, ha', zero_smul, zero_sub, neg_smul, one_smul, neg_neg] at h
  have hM0pow : M0 ^ p = 1 := by
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.pow_apply]
    have h := congrArg (fun f : Module.End K ((K × K) × (K × K)) => f x) hM0powEnd
    rw [Module.End.pow_apply] at h
    simpa [LinearEquiv.coe_one] using h
  have hM0ne : M0 ≠ 1 := pairEquiv_ne_one τ β hβ
  have hM0ord : orderOf M0 = p := orderOf_eq_prime hM0pow hM0ne
  refine ⟨pairExtend M0, pairExtend_mem_modelO M0 ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [show M0 z = pairMap (0, -τ) β z from rfl, pairMap_apply]
    exact rotForm_pairMap τ β z.1 z.2 hβ
  · have h := orderOf_injective pairExtendHom pairExtend_injective M0
    rw [hM0ord] at h
    exact h
  · intro w hw
    refine pairExtend_commute_cmEquiv M0 ?_ hw
    intro k z
    exact pairMap_rotPow (0, -τ) β k z
  · intro g'
    exact pairExtend_commute_wExtend M0 g'
  · intro q
    exact pairExtend_apply_wVec M0 q

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
