module

public import CFSG.LocalAnalysis.SteinbergSFOddHigherLinearFixedRootSelector
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.SteinbergSFOddOrthogonalScalarQuotientSL2

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace OddClassicalRankOne

@[expose] def FixedRootTwoConfig {P : Type*} [Group P] (β : MulAut P) (K : Type*) [Field K] :
    Prop :=
  ∃ S : Subgroup (fixedSubgroup β), S.Normal ∧ IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
    ∀ W : Subgroup P, W ≤ fixedSubgroup β ⊓
      centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) : Set P) →
      IsPGroup 2 W → Nat.card W ≤ 2

theorem FixedRootTwoConfig.of_mulEquiv {P P' : Type*} [Group P] [Group P'] {K : Type*}
    [Field K] (e : P ≃* P') {β : MulAut P} {β' : MulAut P'} (hint : ∀ x, e (β x) = β' (e x))
    (h : FixedRootTwoConfig β K) : FixedRootTwoConfig β' K := by
  obtain ⟨S, hSn, hSs, ⟨a, b, hab⟩, ⟨φ⟩, hr⟩ := h
  have hfix := OddClassSelector.map_fixedSubgroup_of_comm e β β' hint
  let eF : fixedSubgroup β ≃* fixedSubgroup β' :=
    ((fixedSubgroup β).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let eS : S ≃* S.map eF.toMonoidHom := S.equivMapOfInjective eF.toMonoidHom eF.injective
  have hmapS : (S.map eF.toMonoidHom).map (fixedSubgroup β').subtype =
      (S.map (fixedSubgroup β).subtype).map e.toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hinf : fixedSubgroup β' ⊓ centralizer (((S.map eF.toMonoidHom).map
      (fixedSubgroup β').subtype : Subgroup P') : Set P') =
      (fixedSubgroup β ⊓ centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) :
        Set P)).map e.toMonoidHom := by
    rw [hmapS, ← SymplecticFourStandard.map_centralizer_mulEquiv, ← hfix,
      ← map_inf_eq _ _ _ e.injective]
  refine ⟨S.map eF.toMonoidHom, hSn.map _ eF.surjective, eS.symm.isSimpleGroup,
    ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩,
    ⟨eS.symm.trans φ⟩, fun W hW hWp => ?_⟩
  have hW' : W.map e.symm.toMonoidHom ≤ fixedSubgroup β ⊓
      centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) : Set P) := by
    have h1 := Subgroup.map_mono (f := e.symm.toMonoidHom) (hW.trans hinf.le)
    rwa [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id P by
      ext x; exact e.symm_apply_apply x, map_id] at h1
  have h2 := hr _ hW' (hWp.map _)
  rwa [card_map_of_injective e.symm.injective] at h2

theorem false_of_four_dvd {G : Type*} [Group G] {p : G → Prop}
    (hp : ∀ W : Subgroup G, (∀ w ∈ W, p w) → IsPGroup 2 W → Nat.card W ≤ 2) {W : Subgroup G}
    [Finite W] (hW : ∀ w ∈ W, p w) (h4 : 4 ∣ Nat.card W) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 2 (n := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact h4)
  have hcard : Nat.card (Q.map W.subtype) = 2 ^ 2 := by
    rw [card_map_of_injective W.subtype_injective, hQ]
  have h1 := hp (Q.map W.subtype) (fun w hw => hW w (map_subtype_le Q hw)) (IsPGroup.of_card hcard)
  rw [hcard] at h1
  omega

theorem card_map_mk'_eq_index {U : Type*} [Group U] (Z : Subgroup U) [Z.Normal] (T : Subgroup U) :
    Nat.card (T.map (QuotientGroup.mk' Z)) = (Z.subgroupOf T).index := by
  have hker : ((QuotientGroup.mk' Z).comp T.subtype).ker = Z.subgroupOf T := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  rw [← hker, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]

theorem isSimpleGroup_SL2_of_card {K : Type*} [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = 2 ^ n) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := n) Nat.prime_two (by omega) (by rw [Nat.card_eq_fintype_card, hK])
  have hle : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr ⟨s, hs⟩)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem exists_mul_ne_SL2 (K : Type*) [Field K] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  let a : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨a, b, fun h => ?_⟩
  have h00 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change ((a : Matrix (Fin 2) (Fin 2) K) * (b : Matrix (Fin 2) (Fin 2) K)) 0 0 =
    ((b : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K)) 0 0 at h00
  simp [a, b, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem subgroupOf_fixedRoot_data {D : Type*} [Group D] {n : ℕ} (hn : 2 ≤ n) {K : Type*}
    [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) {α : MulAut D} {S : Subgroup D}
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) ∧
      (∃ a b : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), a * b ≠ b * a) ∧
      Nonempty (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K) ∧
      (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).map
        (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype = S := by
  obtain ⟨φ⟩ := hSK
  let e := (Subgroup.subgroupOfEquivOfLe hSα).trans φ
  have := isSimpleGroup_SL2_of_card hn hK
  obtain ⟨a, b, hab⟩ := exists_mul_ne_SL2 K
  refine ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by
    rw [map_mul, map_mul, h]))⟩, ⟨e⟩, ?_⟩
  rw [subgroupOf_map_subtype, inf_of_le_left hSα]

theorem two_bound_of_fixedRootRankOne {D : Type*} [Group D] {α : MulAut D} {S : Subgroup D}
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D)) (hr : FixedRootRankOne α S) :
    ∀ W : Subgroup D, W ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer (((S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).map
        (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) : Set D) →
      IsPGroup 2 W → Nat.card W ≤ 2 := by
  intro W hW hWp
  rw [subgroupOf_map_subtype, inf_of_le_left hSα] at hW
  exact (hr W hW hWp).1

theorem statedClassicalModel_of_lieModel {D : Type} [Group D] {t : StatedLieTag} {m p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel D t m p f) : StatedClassicalModel D t m p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

end OddClassicalRankOne

open OddClassicalRankOne

namespace OddLinearRankOne

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.LocalAnalysis.SymplecticFourStandard.OddLinearRoot

variable {F : Type} [Field F] [Finite F] {d : ℕ}

theorem symmetric_case_two {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {B : GL (Fin d) F}
    (hB : (B : Matrix (Fin d) (Fin d) F)ᵀ = B) (hZ : center (projectiveSL d F) = ⊥)
    {X : Subgroup (MulAut (projectiveSL d F))}
    (hX : CFSG.Assembly.IsComponentOf X
      (inner (projectiveSL d F) ⊓ centralizer {conjAut d F B * dualAut d F}))
    (hsmall : ∀ W : Subgroup (projectiveSL d F), W ≤ fixedSubgroup (conjAut d F B * dualAut d F) →
      (∀ w ∈ W, ∀ x ∈ X, MulAut.conj w * x = x * MulAut.conj w) → IsPGroup 2 W →
        Nat.card W ≤ 2)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : n = 2 ∧ Nat.card F = 5 ∧ d = 3 := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hk2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hd B hX
  set Xh := ⁅X.comap (conjAut d F), X.comap (conjAut d F)⁆
  set R : GL (Fin d) F := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup d F R
  have hR : (R : Matrix (Fin d) (Fin d) F)ᵀ = R := by
    set Rm : Matrix (Fin d) (Fin d) F := (R : Matrix (Fin d) (Fin d) F) with hRm
    set Bm : Matrix (Fin d) (Fin d) F := (B : Matrix (Fin d) (Fin d) F) with hBm
    have hBR : Bm * Rm = 1 := by
      rw [hBm, hRm, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Rmᵀ = Rmᵀ * (Bm * Rm) := by rw [hBR, Matrix.mul_one]
      _ = (Bm * Rm)ᵀ * Rm := by rw [transpose_mul, hB, Matrix.mul_assoc]
      _ = Rm := by rw [hBR, transpose_one, Matrix.one_mul]
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  set eO := matrixOrthogonalEquiv hk2 R hR
  have heO : ∀ y : TauCeti.QuadraticMap.orthogonalGroup Q, ((eO y : O) : GL (Fin d) F) =
      CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun F (Fin d))
        (y : (Fin d → F) ≃ₗ[F] (Fin d → F)) := fun y => rfl
  set Y := (Xh.subgroupOf O).map eO.symm.toMonoidHom
  have hY : CFSG.IsComponent Y := isComponent_map_of_isComponent eO.symm
    ((isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh)
  set ψ : Y →* MulAut (projectiveSL d F) :=
    (conjAut d F).comp (O.subtype.comp (eO.toMonoidHom.comp Y.subtype))
  have hψr : ψ.range = X := by
    rw [← hmap]
    ext y
    constructor
    · rintro ⟨⟨g, x, hx, rfl⟩, rfl⟩
      refine ⟨(x : GL (Fin d) F), hx, ?_⟩
      change conjAut d F (x : GL (Fin d) F) =
        conjAut d F ((eO (eO.symm x) : O) : GL (Fin d) F)
      rw [MulEquiv.apply_symm_apply]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨eO.symm ⟨x, hXh.1 hx⟩, ⟨x, hXh.1 hx⟩, hx, rfl⟩, ?_⟩
      change conjAut d F ((eO (eO.symm ⟨x, hXh.1 hx⟩) : O) : GL (Fin d) F) = conjAut d F x
      rw [MulEquiv.apply_symm_apply]
  have hA : ∀ a ∈ ψ.ker, ∃ c : F, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup Q) : (Fin d → F) ≃ₗ[F] (Fin d → F)) v =
        c • v := by
    intro a ha
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hd _).mp ha
    exact ⟨c, apply_eq_smul_of_basisMatrixEquiv_eq ((heO a).symm.trans hc.symm)⟩
  obtain ⟨φ⟩ := nonempty_quotient_ker ψ hψr eX
  obtain ⟨hn2, h5, h3 | h4⟩ :=
    odd_orthogonal_component_scalar_quotients_even_SL2_small_exceptions hodd Q hQ hY ψ.ker hA hn
      K hK ⟨φ⟩
  · refine ⟨hn2, h5, ?_⟩
    have h := h3.1
    rwa [Module.finrank_fin_fun] at h
  ·
    exfalso
    obtain ⟨-, -, -, -, -, T, hTcomm, -, hTc, hT60, -⟩ := h4
    have : Finite ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
      Finite.of_injective (fun g : (Fin d → F) ≃ₗ[F] (Fin d → F) => (g : (Fin d → F) → Fin d → F))
        DFunLike.coe_injective
    set φT : T →* MulAut (projectiveSL d F) :=
      (conjAut d F).comp (O.subtype.comp (eO.toMonoidHom.comp T.subtype))
    have hdet : ∀ t : T, (((eO t : O) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
      intro t
      have h1 := congrArg Units.val (OddOrthogonalQuotient.det_eq_one_of_mem_commutator (hTc t.2))
      rw [LinearEquiv.coe_det, Units.val_one] at h1
      rw [heO, CatalogueBAlternatingIsometry.basisMatrixEquiv_val, LinearMap.det_toMatrix]
      exact h1
    have hinn : φT.range ≤ (MulAut.conj : projectiveSL d F →* MulAut (projectiveSL d F)).range := by
      rintro _ ⟨t, rfl⟩
      set g : Matrix.SpecialLinearGroup (Fin d) F :=
        ⟨(((eO t : O) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F), hdet t⟩
      refine ⟨proj d F g, ?_⟩
      rw [← conjAut_toGL]
      change conjAut d F (SpecialLinearGroup.toGL g) = conjAut d F ((eO t : O) : GL (Fin d) F)
      exact congrArg _ (Units.ext rfl)
    have hconj := OddClassSelector.conj_injective hZ
    set W := φT.range.comap (MulAut.conj : projectiveSL d F →* MulAut (projectiveSL d F))
    have hWcard : Nat.card W = Nat.card φT.range := by
      rw [← Subgroup.card_map_of_injective hconj, Subgroup.map_comap_eq_self hinn]
    have hWfix : W ≤ fixedSubgroup (conjAut d F B * dualAut d F) := by
      intro w hw
      obtain ⟨t, ht⟩ := hw
      refine apply_eq_of_conj_commute hZ _ ?_
      rw [← ht]
      exact mem_centralizer_singleton_iff.mp (isometryGroup_le_comap_centralizer B (eO t).2)
    have hWX : ∀ w ∈ W, ∀ x ∈ X, MulAut.conj w * x = x * MulAut.conj w := by
      intro w hw x hx
      obtain ⟨t, ht⟩ := hw
      rw [← ht]
      rw [← hmap] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      have hgO : g ∈ O := hXh.1 hg
      have hyY : eO.symm ⟨g, hgO⟩ ∈ Y := ⟨⟨g, hgO⟩, hg, rfl⟩
      have h1 := congrArg (fun y => ((eO y : O) : GL (Fin d) F)) (hTcomm _ hyY _ t.2)
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
      change conjAut d F ((eO t : O) : GL (Fin d) F) * conjAut d F g =
        conjAut d F g * conjAut d F ((eO t : O) : GL (Fin d) F)
      rw [← map_mul, ← map_mul, h1]
    have hker : φT.ker ≤ (OddOrthogonalQuotient.scalarIsometries Q).subgroupOf T := by
      intro t ht
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hd _).mp ht
      exact ⟨c, apply_eq_smul_of_basisMatrixEquiv_eq ((heO t).symm.trans hc.symm)⟩
    have h60 : 60 ∣ Nat.card φT.range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φT).toEquiv]
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hker
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φT.ker
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((OddOrthogonalQuotient.scalarIsometries Q).subgroupOf T)
      rw [hT60, hk] at h2
      have h4 : 0 < Nat.card φT.ker := Nat.card_pos
      refine ⟨k, Nat.eq_of_mul_eq_mul_right h4 ?_⟩
      rw [← h1, h2]
      ring
    exact false_of_four_dvd
      (p := fun w => w ∈ fixedSubgroup (conjAut d F B * dualAut d F) ∧
        ∀ x ∈ X, MulAut.conj w * x = x * MulAut.conj w)
      (fun V hV hVp => hsmall V (fun v hv => (hV v hv).1) (fun v hv => (hV v hv).2) hVp)
      (W := W) (fun w hw => ⟨hWfix hw, hWX w hw⟩)
      (by rw [hWcard]; exact dvd_trans (by norm_num) h60)

theorem projective_selector_two {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {β : MulAut (projectiveSL d F)} (hβ : orderOf β = 2)
    (h : FixedRootTwoConfig β K) :
    n = 2 ∧ Nat.card F = 5 ∧ d = 3 ∧ ∃ A : GL (Fin d) F, (A : Matrix (Fin d) (Fin d) F)ᵀ = A ∧
      β = conjAut d F A * dualAut d F := by
  classical
  obtain ⟨S, hSn, hSs, hSnab, ⟨φS⟩, hcard⟩ := h
  have hβ2 : β ^ 2 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hβ
    omega
  have : IsSimpleGroup (projectiveSL d F) := isSimpleGroup_projectiveSL hd
  have hnabP : ∃ x y : projectiveSL d F, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hSnab
    exact ⟨((x : fixedSubgroup β) : projectiveSL d F), ((y : fixedSubgroup β) : projectiveSL d F),
      fun h => hxy (Subtype.ext (Subtype.ext h))⟩
  have hZ : center (projectiveSL d F) = ⊥ := ComponentInitial.center_eq_bot_of_isSimpleGroup hnabP
  have hconj := OddClassSelector.conj_injective hZ
  set ι := (MulAut.conj : projectiveSL d F →* MulAut (projectiveSL d F)).comp
    (fixedSubgroup β).subtype
  have hιi : Function.Injective ι := hconj.comp (Subgroup.subtype_injective _)
  set X := S.map ι
  have hX : CFSG.Assembly.IsComponentOf X (inner (projectiveSL d F) ⊓ centralizer {β}) := by
    have h1 := SymmetricLocal.isComponentOf_map_of_injective _ hconj
      (isComponentOf_map_subtype S hSn hSs hSnab)
    rwa [Subgroup.map_map, OddClassSelector.map_conj_fixedSubgroup hconj β] at h1
  have eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (S.equivMapOfInjective ι hιi).symm.trans φS
  have hsmall : ∀ W : Subgroup (projectiveSL d F), W ≤ fixedSubgroup β →
      (∀ w ∈ W, ∀ x ∈ X, MulAut.conj w * x = x * MulAut.conj w) → IsPGroup 2 W →
        Nat.card W ≤ 2 := by
    intro W hWβ hWX hW2
    have hle : W ≤ fixedSubgroup β ⊓
        centralizer ((S.map (fixedSubgroup β).subtype : Subgroup (projectiveSL d F)) :
          Set (projectiveSL d F)) := by
      intro w hw
      refine ⟨hWβ hw, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      apply hconj
      rw [map_mul, map_mul]
      exact (hWX w hw (ι s) ⟨s, hs, rfl⟩).symm
    exact hcard W hle hW2
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) hd
  obtain ⟨B, σ, ε, hε, hβB⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hβB
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hβB
      exact (inner_false hℓ hℓ2 he hF hd hβB hβ1 hβ2 hX hn hK eX).elim
    · exact (field_false hℓ hℓ2 he hF hd hσ hβB hβ2 hX hn hK eX).elim
  · rw [pow_one] at hβB
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hβB
      subst hβB
      rcases transpose_eq_or_eq_neg_of_pureGraph hd B hβ2 with hB | hB
      · obtain ⟨hn2, h5, hd3⟩ := symmetric_case_two hℓ hℓ2 he hF hd hB hZ hX hsmall hn hK eX
        exact ⟨hn2, h5, hd3, B, hB, rfl⟩
      · exact (alternating_false hℓ hℓ2 he hF hd hB hX hn hK eX).elim
    · exact (graph_field_false hℓ hℓ2 he hF hd hσ hβB hβ2 hX hn hK eX).elim

end OddLinearRankOne

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem odd_higher_linear_fixed_root_rankOne_selector
    (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id D))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (h2 : ∀ W : Subgroup D, W ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ((S.map (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) :
        Set D) → IsPGroup 2 W → Nat.card W ≤ 2)
    (d p f : ℕ) (hp : p ≠ 2) (hd : 3 ≤ d) (hM : StatedClassicalModel D .PSL d p f) :
    n = 2 ∧ p = 5 ∧ f = 1 ∧ d = 3 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      ∀ (F : Type) [Field F], Nat.card F = p ^ f → ∀ η : D ≃* projectiveSL d F,
        ∃ A : GL (Fin d) F, (A : Matrix (Fin d) (Fin d) F)ᵀ = A ∧
          ∀ x, η (α x) = conjAut d F A (dualAut d F (η x)) := by
  obtain ⟨⟨hprime, hf, -, -, -⟩, F₀, _, _, hF₀, ⟨θ₀⟩⟩ := hM
  have h0 : FixedRootTwoConfig α K := ⟨S, hSn, hSs, hSnab, hSK, h2⟩
  have hall : ∀ (F : Type) [Field F], Nat.card F = p ^ f → ∀ η : D ≃* projectiveSL d F,
      n = 2 ∧ Nat.card F = 5 ∧ d = 3 ∧
        ∃ A : GL (Fin d) F, (A : Matrix (Fin d) (Fin d) F)ᵀ = A ∧
          ∀ x, η (α x) = conjAut d F A (dualAut d F (η x)) := by
    intro F _ hF η
    have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hprime.ne_zero)
    obtain ⟨hn2, h5, hd3, A, hA, hαA⟩ := OddLinearRankOne.projective_selector_two hprime hp hf hF
      hd hn hK (β := MulAut.congr η α) (by rw [MulEquiv.orderOf_eq]; exact hα)
      (h0.of_mulEquiv η fun x => by
        change η (α x) = η (α (η.symm (η x)))
        rw [MulEquiv.symm_apply_apply])
    refine ⟨hn2, h5, hd3, A, hA, fun x => ?_⟩
    have h1 : MulAut.congr η α (η x) = η (α x) := by
      change η (α (η.symm (η x))) = η (α x)
      rw [MulEquiv.symm_apply_apply]
    rw [← h1, hαA, MulAut.mul_apply]
  set η₀ := θ₀.trans (CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL d F₀)
  obtain ⟨hn2, h5, hd3, A, -, hαA⟩ := hall F₀ hF₀ η₀
  have hpf : p ^ f = 5 := by rw [← hF₀, h5]
  obtain ⟨hp5, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_five).mp hpf
  refine ⟨hn2, hp5, hf1, hd3, ?_, fun F _ hF η => (hall F hF η).2.2.2⟩
  rintro ⟨y, hy⟩
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F₀) hd
  obtain ⟨g, hg⟩ := proj_surjective d F₀ (η₀ y)
  have h1 : conjAut d F₀ A * dualAut d F₀ = conjAut d F₀ (SpecialLinearGroup.toGL g) := by
    ext z
    obtain ⟨x, rfl⟩ := η₀.surjective z
    rw [MulAut.mul_apply, ← hαA x, ← hy, conjAut_toGL, hg, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv]
  have h2 : dualAut d F₀ = (conjAut d F₀ A)⁻¹ * conjAut d F₀ (SpecialLinearGroup.toGL g) := by
    rw [← h1, inv_mul_cancel_left]
  rw [h2]
  exact mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A)))
    (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))

theorem fixedRootSelector_oddHigherLinear :
    FixedRootSelector fun D _ =>
      ∃ d p f : ℕ, p ≠ 2 ∧ 3 ≤ d ∧ StatedClassicalModel D .PSL d p f := by
  intro D _ _ _ ⟨d, p, f, hp, hd, hM⟩ n hn K _ _ hK α hα S hSα hSn hSK hr
  obtain ⟨hSs, hSnab, hSK', -⟩ := subgroupOf_fixedRoot_data hn hK hSα hSK
  obtain ⟨hn2, rfl, rfl, rfl, -⟩ := odd_higher_linear_fixed_root_rankOne_selector K hn
    (by rw [Nat.card_eq_fintype_card, hK]) α hα _ hSn hSs hSnab hSK'
    (two_bound_of_fixedRootRankOne hSα hr) d p f hp hd hM
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (Or.inl ⟨by decide, hM⟩)))))⟩)))

theorem fixedRootSelector_oddHigherLinear_lieModel :
    FixedRootSelector fun D _ => ∃ d p f : ℕ, p ≠ 2 ∧ 3 ≤ d ∧ LieModel D .PSL d p f :=
  fixedRootSelector_oddHigherLinear.mono fun _ _ _ _ ⟨d, p, f, hp, hd, h⟩ =>
    ⟨d, p, f, hp, hd, statedClassicalModel_of_lieModel (by decide) h⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
