module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightUni
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
import CFSG.RankThree.CentralLift.DefiningUnitary
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {G : Type*} [Group G]

theorem lieSEightSp_commutator_le_self (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem lieSEightSp_map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

theorem lieSEightSp_range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

theorem lieSEightSp_range_comp_eq_commutator {A : Subgroup G} {B X : Type*} [Group B] [Group X]
    (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact lieSEightSp_map_commutator_mulEquiv φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

theorem lieSEightSp_not_isSolvable_of_isQuasisimple_commutator {H : Subgroup G}
    (hQ : CFSG.IsQuasisimple ↥⁅H, H⁆) : ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hle : ⁅H, H⁆ ≤ H := lieSEightSp_commutator_le_self H
  haveI : Group.IsSolvable ↥⁅H, H⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅H, H⁆ := hQ.1
  haveI : Nontrivial ↥⁅H, H⁆ := by
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  exact Group.IsPerfect.not_isSolvable ↥⁅H, H⁆ inferInstance

theorem lieSEightSp_exists_cover_of_range {G T : Type*} [Group G] [Group T] (π : G →* T)
    (hker : π.ker ≤ Subgroup.center G) {X : Type*} [Group X] (ψ : X →* G)
    (hψ : Function.Injective ψ) {H : Subgroup G} (hH : ψ.range = H) :
    ∃ f : X →* ↥(H.map π), Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  subst hH
  refine ⟨(π.subgroupMap ψ.range).comp ψ.rangeRestrict,
    (MonoidHom.subgroupMap_surjective _ _).comp ψ.rangeRestrict_surjective, fun x hx => ?_⟩
  have h1 : π (ψ x) = 1 := congrArg Subtype.val hx
  have h2 : ψ x ∈ Subgroup.center G := hker h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply hψ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 h2 (ψ y)

theorem lieSEightSp_isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

end Generic

section Factors

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem lieSEightSp_ker_proj_le_center :
    (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
  rw [SymplecticHigher.ker_proj]
  exact SymplecticHigher.spScalars_le_center

theorem lieSEightSp_gl_card_ne (hLO : LieOrderBridge) {E : Type} [Field E] [Fintype E] {g m : ℕ}
    (hg : 3 ≤ g) (hEc : Fintype.card E = 2 ^ g) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    Nat.card (↥((⁅A, A⁆).map (SymplecticFlag.proj r K)) ⧸
      Subgroup.center ↥((⁅A, A⁆).map (SymplecticFlag.proj r K))) ≠ 1056706560 := by
  classical
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := lieSEightSp_isSolvable_gl_of_le_one (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact lieSEightSp_not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have h8 : 8 ≤ 2 ^ g := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hX := slFactorFacts_holds E m hm (fun _ => by rw [hEc]; omega)
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine lieSEightSp_range_eq_commutator_of_perfect θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  obtain ⟨f, hf, hker⟩ := lieSEightSp_exists_cover_of_range (SymplecticFlag.proj r K)
    lieSEightSp_ker_proj_le_center (A.subtype.comp (φ.symm.toMonoidHom.comp θ))
    (Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective))
    (lieSEightSp_range_comp_eq_commutator φ θ hθ)
  exact lieSEight_slQuot_card_ne hLO hm hg hEc f hf hker

theorem lieSEightSp_isSolvable_sesqUnitaryGroup_of_le_one {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hm : Module.finrank E W ≤ 1) :
    Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
  have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
    hm ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
    ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
  simpa [Subgroup.coe_mul, Units.val_mul] using this

theorem lieSEightSp_exists_range_of_special_equiv {ℓ g : ℕ} {G : Type*} [Group G] {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ g E) {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm1 : 1 ≤ Module.finrank E V) {A : Subgroup G}
    (φ : A ≃* sesqUnitaryGroup Hf) {X : Type} [Group X] (hXp : commutator X = ⊤)
    (e : ↥(sesqSpecialUnitaryGroup Hf) ≃* X) :
    ∃ ψ : X →* G, Function.Injective ψ ∧ ψ.range = ⁅A, A⁆ := by
  obtain ⟨-, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hm1
  let θ : X →* ↥(sesqUnitaryGroup Hf) :=
    (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.toMonoidHom
  have hθi : Function.Injective θ :=
    (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.injective
  have hθ : θ.range = commutator ↥(sesqUnitaryGroup Hf) := by
    refine lieSEightSp_range_eq_commutator_of_perfect θ hXp
      (CFSG.LinearGroups.unitaryDet Hf) fun u hu => ?_
    rw [hker] at hu
    exact ⟨e ⟨u, hu⟩, Subtype.ext (by simp [θ])⟩
  exact ⟨A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp hθi),
    lieSEightSp_range_comp_eq_commutator φ θ hθ⟩

open CFSG.RankThree.CentralLift CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag in
theorem lieSEightSp_gu_card_ne (hLO : LieOrderBridge) {g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 g E) (hg : 3 ≤ g) {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {m : ℕ} (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* sesqUnitaryGroup Hf) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    Nat.card (↥((⁅A, A⁆).map (SymplecticFlag.proj r K)) ⧸
      Subgroup.center ↥((⁅A, A⁆).map (SymplecticFlag.proj r K))) ≠ 1056706560 := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := lieSEightSp_isSolvable_sesqUnitaryGroup_of_le_one hE
      (hfin ▸ (by omega : m ≤ 1) : Module.finrank E V ≤ 1) (Hf := Hf)
    exact lieSEightSp_not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have h8 : 8 ≤ 2 ^ g := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨hE.prime⟩
  haveI : CharP E 2 := hE.charP
  have hEcard : Fintype.card E = (2 ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  haveI : Finite ↥hE.fixedField := inferInstance
  haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
  have hFcard : Fintype.card ↥hE.fixedField = 2 ^ g := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_fixedField
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
    have hX := slFactorFacts_holds ↥hE.fixedField 2 le_rfl (fun _ => by rw [hFcard]; omega)
    obtain ⟨ψ, hψi, hψ⟩ := lieSEightSp_exists_range_of_special_equiv hE hHf hHfl (by omega) φ
      hX.perfect e
    obtain ⟨f, hf, hker⟩ := lieSEightSp_exists_cover_of_range (SymplecticFlag.proj r K)
      lieSEightSp_ker_proj_le_center ψ hψi hψ
    exact lieSEight_slQuot_card_ne hLO le_rfl hg hFcard f hf hker
  ·
    have hnq : (m, 2 ^ g) ≠ (3, 2) := by
      intro h
      have h2 := congrArg Prod.snd h
      simp only at h2
      omega
    have hX := suFactorFacts_holds E m (2 ^ g) hEcard hm3 hnq
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (2 ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (2 ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    obtain ⟨ψ, hψi, hψ⟩ := lieSEightSp_exists_range_of_special_equiv hE hHf hHfl (by omega) φ
      hX.perfect e'
    obtain ⟨f, hf, hker⟩ := lieSEightSp_exists_cover_of_range (SymplecticFlag.proj r K)
      lieSEightSp_ker_proj_le_center ψ hψi hψ
    exact lieSEight_suQuot_card_ne hLO (Q := 2 ^ g) (g := g) rfl hm3 (by omega) hEcard hnq f hf
      hker

end Factors

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
