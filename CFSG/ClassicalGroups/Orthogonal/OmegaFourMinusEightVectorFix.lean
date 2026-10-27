module

public import CFSG.ClassicalGroups.Orthogonal.MinusLeviBlocks
public import CFSG.LieType.Universal.SpinCenterMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Fixed
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix QuadraticMap CFSG.Open CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

abbrev omegaMinusFourIndex : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem plane_binary {K : Type} [Field K] (b c : K) (x : Fin 2 → K) :
    binaryForm K b c x = planeNorm b c x := by
  rw [CFSG.LieType.Universal.Spin.binaryForm_apply, planeNorm]

private def planeVec {K : Type} [Field K] (t : K) : omegaMinusFourIndex → K
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => t
  | Sum.inr (Sum.inr _) => 0

private theorem quad_planeVec {K : Type} [Field K] (b c t : K) :
    quadMinus 2 K b c (planeVec t) = t := by
  rw [quadMinus_apply]
  simp [planeVec]

private theorem planeVec_ne_zero {K : Type} [Field K] {t : K} : planeVec t ≠ 0 := by
  intro h
  have h1 := congrFun h (Sum.inl (0 : Fin (2 - 1)))
  simp [planeVec] at h1

private theorem planeBlockHom_planeVec {K : Type} [Field K] {t : K}
    (Y : GL (Fin 2) K) :
    ((planeBlockHom (m := 1) Y : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ
        planeVec t = planeVec t := by
  rw [planeBlockHom_mulVec]
  funext i
  rcases i with i | i | i
  · simp [planeVec]
  · simp [planeVec]
  · simp [planeVec]
    fin_cases i <;> rfl

theorem exists_planeOrder_three_of_card_eight {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ Y : GL (Fin 2) K, orderOf Y = 3 ∧
      ∀ z : Fin 2 → K, planeNorm b c (Y *ᵥ z) = planeNorm b c z := by
  classical
  have hfin_lin : Finite ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    Finite.of_injective
      (fun e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) => (e : (Fin 2 → K) → (Fin 2 → K)))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  let Q : QuadraticForm K (Fin 2 → K) := binaryForm K b c
  have hfin_orth : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    @Finite.of_injective _ ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) hfin_lin
      (fun x : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
        (x.1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)))
      (fun x y h => Subtype.ext h)
  have hani : ∀ x : Fin 2 → K, x ≠ 0 → Q x ≠ 0 := by
    intro x hx
    rw [show Q x = planeNorm b c x by
      rw [CFSG.LieType.Universal.Spin.binaryForm_apply, planeNorm]]
    exact planeNorm_ne_zero hirr hx
  have hcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * (Nat.card K + 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
      (A := Fin 2 → K) (Q := Q) (by simp) hani
  have h3 : 3 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [hcard, hK]
    norm_num
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card'
    ↥(TauCeti.QuadraticMap.orthogonalGroup Q) _ hfin_orth 3 hfact h3
  let Y : GL (Fin 2) K := (toLinEquiv (Fin 2) K).symm
    (x : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
  have hYlin : (toLinEquiv (Fin 2) K) Y =
      (x : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    MulEquiv.apply_symm_apply _ _
  have hYord : orderOf Y = 3 := by
    rw [← MulEquiv.orderOf_eq (toLinEquiv (Fin 2) K) Y, hYlin, Subgroup.orderOf_coe, hx]
  have hY : ∀ z : Fin 2 → K, planeNorm b c (Y *ᵥ z) = planeNorm b c z := by
    intro z
    have hxO : (x : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := x.2
    have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxO) z
    have hYz : Y *ᵥ z = (x : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) z := by
      rw [← toLinEquiv_apply, hYlin]
    calc planeNorm b c (Y *ᵥ z) = Q (Y *ᵥ z) := (plane_binary b c (Y *ᵥ z)).symm
      _ = Q ((x : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) z) := by rw [hYz]
      _ = Q z := h
      _ = planeNorm b c z := plane_binary b c z
  exact ⟨Y, hYord, hY⟩

theorem exists_orderOf_three_fix_statedOmega_quadMinus_two
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : omegaMinusFourIndex → K) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 2 K b c), orderOf g = 3 ∧
      ((g : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ v = v) := by
  classical
  have hQnd : (QuadraticMap.polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨Y, hYord, hYplane⟩ := exists_planeOrder_three_of_card_eight hK hirr
  let g : GL omegaMinusFourIndex K := planeBlockHom (m := 1) Y
  have hgord : orderOf g = 3 := by
    dsimp [g]
    rw [orderOf_planeBlockHom, hYord]
  have hg3 : g ^ 3 = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one g
  have hgQ : ∀ x : omegaMinusFourIndex → K,
      StatedQuadMinus 2 K b c ((g : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x) =
        StatedQuadMinus 2 K b c x :=
    fun x => planeBlockHom_isometry (n := 2) Y hYplane x
  have hgmem : g ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
    rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)]
    refine CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_mem_orthDerived_of_pow_prime
      (quadMinus 2 K b c) hQnd (by
        show 3 ≤ Module.finrank K (omegaMinusFourIndex → K)
        simp) (by rw [hK]; norm_num) Nat.prime_three (by norm_num) ?_ ?_
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro x
      have h := hgQ x
      rw [← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
          (((g : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x)),
        ← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) x] at h
      rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply]
    · rw [← map_pow, hg3, map_one]
  by_cases hv : v = 0
  · exact ⟨g, hgmem, hgord, by rw [hv, Matrix.mulVec_zero]⟩
  · let t : K := quadMinus 2 K b c v
    let u : omegaMinusFourIndex → K := planeVec t
    have hu : u ≠ 0 := planeVec_ne_zero
    have hQu : quadMinus 2 K b c u = quadMinus 2 K b c v := by
      dsimp [u, t]
      rw [quad_planeVec]
    obtain ⟨tlin, htO, htuv⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.exists_mem_orthogonalGroup_apply_eq_of_map_eq
        hQnd hv hu hQu
    let T : GL omegaMinusFourIndex K := (toLinEquiv omegaMinusFourIndex K).symm tlin
    have hTlin : (toLinEquiv omegaMinusFourIndex K) T = tlin := MulEquiv.apply_symm_apply _ _
    have hTv : (T : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ v = u := by
      rw [← toLinEquiv_apply, hTlin]
      exact htuv
    have hTQ : ∀ x : omegaMinusFourIndex → K,
        quadMinus 2 K b c ((T : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x) =
          quadMinus 2 K b c x := by
      intro x
      have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp htO) x
      have hx : tlin x = (T : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x := by
        rw [← hTlin, toLinEquiv_apply]
      rwa [hx] at h
    have hTQ' : ∀ x : omegaMinusFourIndex → K,
        StatedQuadMinus 2 K b c ((T : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x) =
          StatedQuadMinus 2 K b c x := by
      intro x
      rw [← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
          ((T : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x),
        ← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) x]
      exact hTQ x
    have hTinv_mem : (toLinEquiv omegaMinusFourIndex K) T⁻¹ ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c) := by
      rw [map_inv, hTlin]
      exact (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)).inv_mem htO
    have hTinvQ : ∀ x : omegaMinusFourIndex → K,
        StatedQuadMinus 2 K b c
          (((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x) =
            StatedQuadMinus 2 K b c x := by
      intro x
      have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hTinv_mem) x
      rw [toLinEquiv_apply] at h
      rw [← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
          (((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) *ᵥ x),
        ← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) x]
      exact h
    let h : GL omegaMinusFourIndex K := T⁻¹ * g * T
    have hfix : Matrix.mulVec (h : Matrix omegaMinusFourIndex omegaMinusFourIndex K) v = v := by
      have h1 : Matrix.mulVec (h : Matrix omegaMinusFourIndex omegaMinusFourIndex K) v =
          Matrix.mulVec ((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K)
            (Matrix.mulVec ((g : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K)
              (Matrix.mulVec ((T : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) v)) := by
        dsimp [h]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [h1, hTv, planeBlockHom_planeVec Y]
      calc Matrix.mulVec ((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) u
          = Matrix.mulVec ((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K)
              (Matrix.mulVec ((T : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) v) := by
              rw [hTv]
        _ = Matrix.mulVec (((T⁻¹ * T : GL omegaMinusFourIndex K)) :
              Matrix omegaMinusFourIndex omegaMinusFourIndex K) v := by
              rw [Matrix.mulVec_mulVec]
              rfl
        _ = v := by rw [inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hQ : ∀ x : omegaMinusFourIndex → K,
        StatedQuadMinus 2 K b c (Matrix.mulVec (h : Matrix omegaMinusFourIndex omegaMinusFourIndex K) x) =
          StatedQuadMinus 2 K b c x := by
      intro x
      have h1 : Matrix.mulVec (h : Matrix omegaMinusFourIndex omegaMinusFourIndex K) x =
          Matrix.mulVec ((T⁻¹ : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K)
            (Matrix.mulVec ((g : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K)
              (Matrix.mulVec ((T : GL omegaMinusFourIndex K) : Matrix omegaMinusFourIndex omegaMinusFourIndex K) x)) := by
        dsimp [h]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [h1, hTinvQ, hgQ, hTQ']
    have h3 : h ^ 3 = 1 := by
      have hconj : h = (MulAut.conj T⁻¹) g := by
        dsimp [h]
        simp
      rw [hconj, ← map_pow, hg3, map_one]
    have hord : orderOf h = 3 := by
      have hconj : h = (MulAut.conj T⁻¹) g := by
        dsimp [h]
        simp
      rw [hconj, MulEquiv.orderOf_eq, hgord]
    have hmem : h ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
      rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)]
      refine CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_mem_orthDerived_of_pow_prime
        (quadMinus 2 K b c) hQnd (by
          show 3 ≤ Module.finrank K (omegaMinusFourIndex → K)
          simp) (by rw [hK]; norm_num) Nat.prime_three (by norm_num) ?_ ?_
      · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro x
        have hh := hQ x
        rw [← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
            (Matrix.mulVec (h : Matrix omegaMinusFourIndex omegaMinusFourIndex K) x),
          ← congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) x] at hh
        rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply]
      · rw [← map_pow, h3, map_one]
    exact ⟨h, hmem, hord, hfix⟩

theorem exists_orderOf_three_fix_mod_of_realizes
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hR : (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).Realizes
      H U Z) :
    ∀ u ∈ U, ∃ x ∈ H, orderOf x = 3 ∧ (x : MulAut W) u * u⁻¹ ∈ Z := by
  classical
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.FFC.exists_natMap hπ
  have hπinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on
      (CFSG.Quasithin.FFModel.nat_faithful
        (StatedOmega (StatedQuadMinus 2 K b c))) hπ
  intro u hu
  let z : omegaMinusFourIndex → K := Multiplicative.toAdd (f ⟨u, hu⟩)
  obtain ⟨γ, hγmem, hγord, hγz⟩ :=
    exists_orderOf_three_fix_statedOmega_quadMinus_two hK hirr z
  let γ' : (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).Gam :=
    ⟨γ, hγmem⟩
  have hγ'ord : orderOf γ' = 3 := by
    change orderOf (⟨γ, hγmem⟩ : ↥(StatedOmega (StatedQuadMinus 2 K b c))) = 3
    exact (Subgroup.orderOf_mk γ hγmem).trans hγord
  have hπu : ((π γ' : ↥H) : MulAut W) u ∈ U := hπ.2.2.2.1 (π γ') u hu
  have hact : CFSG.Quasithin.natAct (StatedOmega (StatedQuadMinus 2 K b c)) γ'
      (f ⟨u, hu⟩) = f ⟨u, hu⟩ := by
    apply Multiplicative.ext
    rw [CFSG.Quasithin.natAct, show Multiplicative.toAdd (f ⟨u, hu⟩) = z from rfl, hγz,
      ofAdd_toAdd]
  have hf_eq : f ⟨((π γ' : ↥H) : MulAut W) u, hπu⟩ = f ⟨u, hu⟩ := by
    calc f ⟨((π γ' : ↥H) : MulAut W) u, hπu⟩
        = CFSG.Quasithin.natAct (StatedOmega (StatedQuadMinus 2 K b c)) γ'
            (f ⟨u, hu⟩) := by
            exact hfe γ' ⟨u, hu⟩ hπu
      _ = f ⟨u, hu⟩ := hact
  have hker : f (⟨((π γ' : ↥H) : MulAut W) u, hπu⟩ * ⟨u, hu⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hf_eq, mul_inv_cancel]
  have hmem : ((⟨((π γ' : ↥H) : MulAut W) u, hπu⟩ * ⟨u, hu⟩⁻¹ : ↥U) : W) ∈ Z :=
    (hfk _).mp hker
  refine ⟨π γ', (π γ').2, ?_, ?_⟩
  · have hcoe : orderOf ((π γ' : ↥H) : MulAut W) = orderOf (π γ') := Subgroup.orderOf_coe _
    rw [hcoe, orderOf_injective π hπinj γ', hγ'ord]
  · simpa using hmem

end CFSG.ClassicalGroups.Orthogonal

end
