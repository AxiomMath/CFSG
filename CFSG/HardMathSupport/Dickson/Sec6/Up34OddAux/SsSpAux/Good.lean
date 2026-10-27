module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsSp

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open scoped commutatorElement

@[expose] def LayerGood (H : Type) [Group H] : Prop :=
  (CFSG.IsQuasisimple ↥(commutator H) ∧
      ¬ IsLThreeFour (↥(commutator H) ⧸ Subgroup.center ↥(commutator H))) ∨ Group.IsSolvable H

theorem LayerGood.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : LayerGood H) :
    LayerGood G := by
  rcases h with ⟨hq, hno⟩ | hs
  · left
    have hmap : (commutator G).map e.toMonoidHom = commutator H := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
    let e' : ↥(commutator G) ≃* ↥(commutator H) :=
      ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hq, fun hL => hno ?_⟩
    exact IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ e' (Subgroup.map_center_eq e')) hL
  · right
    haveI := hs
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem layerGood_of_commutator_eq {H : Type} [Group H] (N : Subgroup H) (hN : commutator H = N)
    (hq : CFSG.IsQuasisimple ↥N) (hno : ¬ IsLThreeFour (↥N ⧸ Subgroup.center ↥N)) :
    LayerGood H := by
  subst hN
  exact Or.inl ⟨hq, hno⟩

theorem commutator_eq_ker_of_perfect {G A : Type*} [Group G] [CommGroup A] (D : G →* A)
    (hperf : Group.IsPerfect ↥D.ker) : commutator G = D.ker := by
  have hle : commutator G ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator G := by
    have h1 := Subgroup.isPerfect_iff.mp hperf
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (_root_.commutator_def G).symm
  exact le_antisymm hle hge

theorem layerGood_of_isQuasisimple {H : Type} [Group H] (hq : CFSG.IsQuasisimple H)
    (hno : ¬ IsLThreeFour (H ⧸ Subgroup.center H)) : LayerGood H := by
  have hcomm : commutator H = ⊤ := Group.isPerfect_def.mp hq.1
  let e : ↥(⊤ : Subgroup H) ≃* H := Subgroup.topEquiv
  refine layerGood_of_commutator_eq _ hcomm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq) fun hL => hno ?_
  exact IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL

theorem lieModel_psl_of_equiv {G : Type} [Group G] {E : Type} [Field E] {n ℓ g : ℕ}
    (hℓ : ℓ.Prime) (hg : 1 ≤ g) (hE : Nat.card E = ℓ ^ g) (hn : 2 ≤ n) (hq : 4 ≤ ℓ ^ g)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin n) E) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .PSL n ℓ g := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; positivity)
  refine (lieModel_classical_iff (by decide)).mpr ⟨⟨hℓ, hg, hn, fun hc => ?_, fun hc => ?_⟩, E,
    inferInstance, inferInstance, hE, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (projectiveSpecialLinearGroupEquivStatedProj n E)⟩⟩
  · have := (Prod.mk.inj hc).2
    omega
  · have := (Prod.mk.inj hc).2
    omega

theorem not_isLThreeFour_of_equiv_sl (hO : LieOrderFormulasInput) {G : Type} [Group G]
    {E : Type} [Field E] {n ℓ g : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hg : 1 ≤ g)
    (hE : Nat.card E = ℓ ^ g) (hn : 2 ≤ n) (e : G ≃* Matrix.SpecialLinearGroup (Fin n) E) :
    ¬ IsLThreeFour (G ⧸ Subgroup.center G) :=
  not_isLThreeFour_of_lieModel_odd hO (by omega)
    (lieModel_psl_of_equiv hℓ hg hE hn
      (le_trans (by omega) (Nat.le_self_pow (by omega : g ≠ 0) ℓ)) e)

theorem not_isLThreeFour_statedSp (hO : LieOrderFormulasInput) {ℓ f s : ℕ} (hℓ : ℓ.Prime)
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (hs : 1 ≤ s) : ¬ IsLThreeFour (↥(StatedSp s K) ⧸ Subgroup.center ↥(StatedSp s K)) := by
  have hq : 4 ≤ ℓ ^ f := le_trans (by omega) (Nat.le_self_pow (by omega : f ≠ 0) ℓ)
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · obtain rfl : s = 1 := by omega
    exact not_isLThreeFour_of_equiv_sl hO hℓ hℓ5 hf hK le_rfl
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm
  · have hadm : StatedLieAdmissible .PSp s ℓ f :=
      ⟨hℓ, hf, hs2, fun hc => by have := (Prod.mk.inj hc).2; omega⟩
    exact not_isLThreeFour_of_lieModel_odd hO (by omega)
      ((lieModel_classical_iff (by decide)).mpr
        (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient s K hadm hK))

theorem layerGood_statedSp (hO : LieOrderFormulasInput) {ℓ f s : ℕ} (hℓ : ℓ.Prime)
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (hs : 1 ≤ s) : LayerGood (StatedSp s K) := by
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact le_trans (by omega) (Nat.le_self_pow (by omega : f ≠ 0) ℓ)
  exact layerGood_of_isQuasisimple
    (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs (Or.inl (Or.inr hq4)))
    (not_isLThreeFour_statedSp hO hℓ hℓ5 hf hK hs)

theorem layerGood_matrixGL (hO : LieOrderFormulasInput) {ℓ g : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (hg : 1 ≤ g) {E : Type} [Field E] (hE : Nat.card E = ℓ ^ g) (m : ℕ) :
    LayerGood (Matrix.GeneralLinearGroup (Fin m) E) := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; positivity)
  have hq : 4 ≤ ℓ ^ g := le_trans (by omega) (Nat.le_self_pow (by omega : g ≠ 0) ℓ)
  by_cases hm : 2 ≤ m
  · have h4 : ∃ s : Finset E, s.card = 4 :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card (by rw [hE]; exact hq)
    have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) E) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm (Or.inr h4)
    let eK : Matrix.SpecialLinearGroup (Fin m) E ≃* ↥(Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker := Matrix.SpecialLinearGroup.toGLKerEquiv
    have hkq : CFSG.IsQuasisimple ↥(Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hSL
    refine layerGood_of_commutator_eq _ (commutator_eq_ker_of_perfect _ hkq.1) hkq fun hL => ?_
    exact not_isLThreeFour_of_equiv_sl hO hℓ hℓ5 hg hE hm eK.symm hL
  · right
    have hsub : Subsingleton (Fin m) := by
      have : m ≤ 1 := by omega
      interval_cases m <;> infer_instance
    refine Group.isSolvable_of_comm fun a b => Units.ext (Matrix.ext fun i j => ?_)
    have hj : j = i := Subsingleton.elim _ _
    subst hj
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Fintype.sum_subsingleton _ j, Fintype.sum_subsingleton _ j, mul_comm]

theorem lieModel_of_sesqSU_odd {ℓ g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ g E)
    {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 2 ≤ Module.finrank E W) (hq : 4 ≤ ℓ ^ g) {G : Type} [Group G]
    (e : G ≃* sesqSpecialUnitaryGroup Hf) :
    ∃ (t' : StatedLieTag) (n' : ℕ), CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t' n' ℓ g := by
  have hfin := hE.finite
  have : Fact ℓ.Prime := ⟨hE.prime⟩
  have hg1 : 1 ≤ g := hE.one_le
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with h2 | h3
  · have hV : Module.finrank E W = 2 := by omega
    obtain ⟨φ⟩ :=
      CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
    exact ⟨.PSL, 2, lieModel_psl_of_equiv hE.prime hg1 hE.card_fixedField le_rfl hq (e.trans φ)⟩
  · have hF : Nat.card E = (ℓ ^ g) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
    have hnq : (Module.finrank E W, ℓ ^ g) ≠ (3, 2) := by
      intro hc
      have := (Prod.mk.inj hc).2
      omega
    obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    let e3 : G ≃* StatedSU (Module.finrank E W) (ℓ ^ g) E :=
      (e.trans φ).trans
        (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hE _).symm)
    obtain ⟨-, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF h3 hnq
    refine ⟨.PSU, Module.finrank E W, (lieModel_classical_iff (by decide)).mpr
      ⟨⟨hE.prime, hg1, h3, hnq⟩, E, inferInstance, inferInstance, hF, ⟨?_⟩⟩⟩
    exact (QuotientGroup.congr _ _ e3 (Subgroup.map_center_eq e3)).trans
      (QuotientGroup.quotientMulEquivOfEq hZc)

theorem layerGood_sesqUnitaryGroup (hO : LieOrderFormulasInput) {ℓ g : ℕ} (hℓ5 : 5 ≤ ℓ)
    {E : Type} [Field E] (hE : UnitaryFieldData ℓ g E) {W : Type} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) : LayerGood ↥(sesqUnitaryGroup Hf) := by
  have hg1 : 1 ≤ g := hE.one_le
  have hq : 4 ≤ ℓ ^ g := le_trans (by omega) (Nat.le_self_pow (by omega : g ≠ 0) ℓ)
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨-, -, -, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
    let eN : ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) ≃*
        ↥(sesqSpecialUnitaryGroup Hf) :=
      Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)
    have hQ : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup Hf) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl
        hm ⟨fun _ => hq, fun _ => by omega⟩
    have hNq : CFSG.IsQuasisimple
        ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hQ
    have hcomm : commutator ↥(sesqUnitaryGroup Hf) =
        (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
      rw [← hker]
      exact commutator_eq_ker_of_perfect (CFSG.LinearGroups.unitaryDet Hf)
        (by rw [hker]; exact hNq.1)
    refine layerGood_of_commutator_eq _ hcomm hNq fun hL => ?_
    obtain ⟨t, n, hmod⟩ := lieModel_of_sesqSU_odd hE hHf hHfl hm hq eN
    exact not_isLThreeFour_of_lieModel_odd hO (by omega) hmod hL
  · right
    refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

end CFSG.HardMathSupport.Dickson.Sec6.SsSp
