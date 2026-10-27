module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Par
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Model
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U
import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec4.E27
open scoped commutatorElement MatrixGroups
open CFSG.RankThree.PartTwo.Sec21.Item219LieProof (d4_threeA_model d4_threeA_model_unitary)

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

section Layer


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem classX_layer_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x) :
    x ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ∧
    ∀ z ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆,
      z ^ 3 = 1 →
      (∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆,
        z * d = d * z) →
      z ∈ Subgroup.zpowers x := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  rcases P.mod_three with hq1 | hq1
  · obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, -, ⟨e⟩⟩ :=
      d4_threeA_model P.prime P.one_le P.ne_three hq1 P.card P.frob hg hy3 hy1
    have hL : TorusLayerAux.LayerProp (c * (g * x * g⁻¹) * c⁻¹) :=
      TorusLayerAux.layer_of_SL _ R hq.1 hcR hRc hcomm
        (TorusLayerAux.conj_pow_eq_one (g := c) hy3)
        (TorusLayerAux.conj_ne_one (c := c) hy1) e
    exact TorusLayerAux.layerProp_of_conj g x (TorusLayerAux.layerProp_of_conj c _ hL)
  · obtain ⟨c, R, hcR, hRc, hcomm, hq, U, hU, e, hcen⟩ :=
      d4_threeA_model_unitary P.prime P.one_le P.ne_three hq1 (by have := P.five_le; omega)
        P.card P.frob hg hy3 hy1
    have hL : TorusLayerAux.LayerProp (c * (g * x * g⁻¹) * c⁻¹) :=
      TorusLayerAux.layer_of_SU _ R hq.1 hcR hRc hcomm
        (TorusLayerAux.conj_pow_eq_one (g := c) hy3)
        (TorusLayerAux.conj_ne_one (c := c) hy1) U e hcen
    exact TorusLayerAux.layerProp_of_conj g x (TorusLayerAux.layerProp_of_conj c _ hL)

theorem layer_facts_linear_odd (P : D4ParOdd ℓ f X σ) (hq1 : ℓ ^ f % 3 = 1) {x : C0 σ}
    (hx : IsClassX σ x) : HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, hFcard, ⟨e⟩⟩ :=
    d4_threeA_model P.prime P.one_le P.ne_three hq1 P.card P.frob hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulEquiv.subgroupCongr hD).trans e
  have h3F : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3F
  have hω3 : (ω : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rw [hω] at this
    exact congrArg Units.val this
  have hω1 : (ω : F) ≠ 1 := by
    intro h1
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    omega
  have hH : HeisIn (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) :=
    heisIn_of_mulEquiv _ e' (heisPair_SL3 hω3 hω1)
  have hC : CubeCenter (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) := by
    intro t ht htc
    have hmem : e' ⟨t, ht⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨s', rfl⟩ := e'.surjective s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (htc _ s'.2).symm
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
    have h3 : (e' ⟨t, ht⟩) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.SpecialLinearGroup.coe_one,
        ← map_pow]
      rw [Fintype.card_fin] at hr3
      rw [hr3, map_one]
    have : (⟨t, ht⟩ : layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) ^ 3 = 1 := by
      apply e'.injective
      rw [map_pow, h3, map_one]
    exact congrArg Subtype.val this
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  rw [hwh] at hH hC
  exact ⟨heisIn_of_conj _ _ hH, cubeCenter_of_conj _ _ hC⟩

theorem layer_facts_unitary_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) : HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have h5 : 5 ≤ ℓ ^ f := P.five_le
  obtain ⟨c, R, hcR, hRc, hcomm, hq, U, hU, e, hcen⟩ :=
    d4_threeA_model_unitary P.prime P.one_le P.ne_three hq2 (by omega) P.card P.frob hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* U := (MulEquiv.subgroupCongr hD).trans e
  have hcharX : CharP X ℓ := P.charP
  have hcharL : CharP (AlgebraicClosure X) ℓ :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective ℓ
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) ℓ] at h'
    exact P.ne_three ((Nat.prime_dvd_prime_iff_eq P.prime Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three
    (AlgebraicClosure X) h3L
  have hζ3 : (ζ : AlgebraicClosure X) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this
  have hζ1 : (ζ : AlgebraicClosure X) ≠ 1 := by
    intro h1
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζ
    omega
  have hζq : (ζ : AlgebraicClosure X) ^ (ℓ ^ f + 1) = 1 := by
    have h3dvd : 3 ∣ ℓ ^ f + 1 := by omega
    obtain ⟨k, hk⟩ := h3dvd
    rw [hk, pow_mul, hζ3, one_pow]
  have hH : HeisIn (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) :=
    heisIn_of_mulEquiv _ e' (heisPair_unitary (q := ℓ ^ f) (by omega) hζ3 hζ1 hζq U hU)
  have hC : CubeCenter (layerSub σ (c * (g * x * g⁻¹) * c⁻¹)) := by
    intro t ht htc
    have htR : t ∈ R := hD ▸ ht
    set t' : R := ⟨t, htR⟩ with ht'
    have hcent : t' ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro d
      exact Subtype.ext (htc (d : C0 σ) (hD ▸ d.2)).symm
    obtain ⟨μ, hμ⟩ := (hcen t').1 hcent
    have hmem : ((e t' : U) : GL (Fin 3) (AlgebraicClosure X)) ∈
        CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3 := by
      rw [← hU]
      exact (e t').2
    have hdet : (((e t' : U) : GL (Fin 3) (AlgebraicClosure X)) :
        Matrix (Fin 3) (Fin 3) (AlgebraicClosure X)).det = 1 := hmem.2.1
    have hμ3 : μ ^ 3 = 1 := by
      rw [hμ, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdet
      exact hdet
    have h3 : (e t') ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hμ, ← map_pow, hμ3, map_one]
      rfl
    have : t' ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h3, map_one]
    exact congrArg Subtype.val this
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  rw [hwh] at hH hC
  exact ⟨heisIn_of_conj _ _ hH, cubeCenter_of_conj _ _ hC⟩

theorem layer_facts_odd' (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x) :
    HeisIn (layerSub σ x) ∧ CubeCenter (layerSub σ x) := by
  rcases P.mod_three with hq1 | hq2
  · exact layer_facts_linear_odd P hq1 hx
  · exact layer_facts_unitary_odd P hq2 hx

theorem layer_card_linear_odd (P : D4ParOdd ℓ f X σ) (hq1 : ℓ ^ f % 3 = 1) {x : C0 σ}
    (hx : IsClassX σ x) :
    Nat.card (layerSub σ x) = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 - 1)) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, hFcard, ⟨e⟩⟩ :=
    d4_threeA_model P.prime P.one_le P.ne_three hq1 P.card P.frob hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  let e' : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulEquiv.subgroupCongr hD).trans e
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  have h1 : Nat.card (layerSub σ ((c * g) * x * (c * g)⁻¹)) = Nat.card (layerSub σ x) :=
    card_layer_conj (c * g) x
  rw [hwh] at e'
  rw [← h1, Nat.card_congr e'.toEquiv, CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', hFcard]

theorem layer_model_unitary_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) :
    ∃ (h : C0 σ) (U : Subgroup (GL (Fin 3) (AlgebraicClosure X))),
      (U : Set (GL (Fin 3) (AlgebraicClosure X))) =
        CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3 ∧
      Nonempty (layerSub σ (h * x * h⁻¹) ≃* U) := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have h5 : 5 ≤ ℓ ^ f := P.five_le
  obtain ⟨c, R, hcR, hRc, hcomm, hq, U, hU, e, -⟩ :=
    d4_threeA_model_unitary P.prime P.one_le P.ne_three hq2 (by omega) P.card P.frob hg hy3 hy1
  have hD : layerSub σ (c * (g * x * g⁻¹) * c⁻¹) = R :=
    TorusLayerAux.commutator_centralizer_eq _ R hq.1 hRc hcomm
  have hwh : c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ := by group
  refine ⟨c * g, U, hU, ⟨?_⟩⟩
  rw [← hwh]
  exact (MulEquiv.subgroupCongr hD).trans e

theorem layer_card_unitary_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) :
    Nat.card (layerSub σ x) = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  obtain ⟨h, U, hU, ⟨e⟩⟩ := layer_model_unitary_odd P hq2 hx
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  haveI : CharP X ℓ := P.charP
  haveI : CharP (AlgebraicClosure X) ℓ :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective ℓ
  rw [← card_layer_conj h x, Nat.card_congr e.toEquiv]
  exact card_subgroup_unitarySet (ℓ := ℓ) (f := f) P.one_le U hU

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
