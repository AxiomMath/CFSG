module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Outer
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Descent
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.SEITZ2.SUnCore
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K card_ringAut_K)

@[expose] def fixSub {X : Type*} [Group X] (α : MulAut X) : Subgroup X where
  carrier := {x | α x = x}
  mul_mem' {a b} ha hb := by
    change α (a * b) = a * b
    rw [map_mul, show α a = a from ha, show α b = b from hb]
  one_mem' := map_one α
  inv_mem' {a} ha := by
    change α a⁻¹ = a⁻¹
    rw [map_inv, show α a = a from ha]

theorem mem_fixSub {X : Type*} [Group X] {α : MulAut X} {x : X} : x ∈ fixSub α ↔ α x = x :=
  Iff.rfl

@[expose] def fixSubEquivOfConj {X : Type*} [Group X] {α β : MulAut X} (h : X)
    (hαβ : ∀ x, α (h * x * h⁻¹) = h * β x * h⁻¹) : fixSub β ≃* fixSub α where
  toFun x := ⟨h * x * h⁻¹, by
    have hx : β x = x := x.2
    change α (h * x * h⁻¹) = h * x * h⁻¹
    rw [hαβ, hx]⟩
  invFun y := ⟨h⁻¹ * y * h, by
    have hy : α y = y := y.2
    have h1 := hαβ (h⁻¹ * y * h)
    rw [show h * (h⁻¹ * y * h) * h⁻¹ = y by group, hy] at h1
    change β (h⁻¹ * y * h) = h⁻¹ * y * h
    have h2 : h * β (h⁻¹ * y * h) * h⁻¹ = y := h1.symm
    calc β (h⁻¹ * y * h) = h⁻¹ * (h * β (h⁻¹ * y * h) * h⁻¹) * h := by group
      _ = h⁻¹ * y * h := by rw [h2]⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem exists_fixField {φ : K ≃+* K} (hφ : orderOf φ = 3) :
    ∃ S : Subfield K, (∀ a, a ∈ S ↔ φ a = a) ∧ Nat.card S = 4 := by
  obtain ⟨-, -, -, -, -, hA⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := K) Nat.prime_two (n := 6) (by norm_num) (by rw [card_K]; norm_num)
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers φ)
  refine ⟨S, fun a => ?_, ?_⟩
  · have hmem : a ∈ S ↔ ∀ τ ∈ Subgroup.zpowers φ, τ a = a := by
      have := Set.ext_iff.mp hS a
      simpa using this
    rw [hmem]
    refine ⟨fun h => h φ (Subgroup.mem_zpowers φ), fun ha τ hτ => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    clear hτ
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [_root_.zpow_add_one]
      change (φ ^ (n : ℤ)) (φ a) = a
      rw [ha]; exact ih
    | pred n ih =>
      rw [_root_.zpow_sub_one]
      change (φ ^ (-(n : ℤ))) (φ.symm a) = a
      have : φ.symm a = a := by rw [RingEquiv.symm_apply_eq]; exact ha.symm
      rw [this]; exact ih
  · rw [hcard, Nat.card_zpowers, hφ]
    norm_num

theorem exists_conj_fieldSU4 {α : MulAut SU4} (hα3 : α ^ 3 = 1) (hα1 : fieldFactor4 α ≠ 1) :
    ∃ h : SU4, ∀ x : SU4, α (h * x * h⁻¹) = h * fieldSU4 (fieldFactor4 α) x * h⁻¹ := by
  set φ : K ≃+* K := fieldFactor4 α with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hα3, map_one]
  obtain ⟨g₀, hg₀⟩ := exists_conj_field4 α
  have hα : ∀ x, α x = g₀ * fieldSU4 φ x * g₀⁻¹ := fun x => Subtype.ext (by rw [hg₀ x]; rfl)
  have hN : g₀ * fieldSU4 φ g₀ * fieldSU4 φ (fieldSU4 φ g₀) = 1 :=
    mul_apply_apply_eq_one center_SU4 g₀ hα (by rw [fieldSU4_pow, hφ3, fieldSU4_one]) hα3
  have hN' : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
      (((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ).map φ = 1 := by
    have := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hN
    simpa [coe_fieldSU4, coe_glAut] using this
  obtain ⟨H, hH, hgH, -⟩ := exists_fixed_orthonormal_eigenbasis
    (unitary_of_mem_SU4 g₀) hφ3 hα1 hN' (p := 1) (by simp) (by simp) (by simp)
  let Hu : GL (Fin 4) K := ⟨H, (H.map hK.bar)ᵀ, mul_eq_one_comm.mp hH, hH⟩
  have hHu : Hu ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary]
    simpa using hH
  obtain ⟨h₀, hh₀⟩ := exists_SU4_conj_eq hHu
  refine ⟨h₀, fun x => ?_⟩
  apply Subtype.ext
  have e3 : (g₀ : GL (Fin 4) K) * glAut φ Hu = Hu := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    exact hgH
  have e1 : ((h₀ * x * h₀⁻¹ : SU4) : GL (Fin 4) K) = Hu * (x : GL (Fin 4) K) * Hu⁻¹ :=
    (hh₀ (x : GL (Fin 4) K)).symm
  have e1' : ((h₀ * fieldSU4 φ x * h₀⁻¹ : SU4) : GL (Fin 4) K) =
      Hu * glAut φ (x : GL (Fin 4) K) * Hu⁻¹ :=
    (hh₀ (glAut φ (x : GL (Fin 4) K))).symm
  rw [e1', hg₀ (h₀ * x * h₀⁻¹), e1, ← hφdef, map_mul, map_mul, map_inv]
  calc (g₀ : GL (Fin 4) K) * (glAut φ Hu * glAut φ (x : GL (Fin 4) K) * (glAut φ Hu)⁻¹) *
        (g₀ : GL (Fin 4) K)⁻¹
      = ((g₀ : GL (Fin 4) K) * glAut φ Hu) * glAut φ (x : GL (Fin 4) K) *
          ((g₀ : GL (Fin 4) K) * glAut φ Hu)⁻¹ := by group
    _ = Hu * glAut φ (x : GL (Fin 4) K) * Hu⁻¹ := by rw [e3]

@[expose] def fixField (φ : K ≃+* K) : Subfield K where
  carrier := {a | φ a = a}
  mul_mem' {a b} ha hb := by
    change φ (a * b) = a * b
    rw [map_mul, show φ a = a from ha, show φ b = b from hb]
  one_mem' := map_one φ
  add_mem' {a b} ha hb := by
    change φ (a + b) = a + b
    rw [map_add, show φ a = a from ha, show φ b = b from hb]
  zero_mem' := map_zero φ
  neg_mem' {a} ha := by
    change φ (-a) = -a
    rw [map_neg, show φ a = a from ha]
  inv_mem' {a} ha := by
    change φ a⁻¹ = a⁻¹
    rw [map_inv₀, show φ a = a from ha]

theorem mem_fixField {φ : K ≃+* K} {a : K} : a ∈ fixField φ ↔ φ a = a := Iff.rfl

theorem card_fixField {φ : K ≃+* K} (hφ : orderOf φ = 3) : Nat.card (fixField φ) = 4 := by
  obtain ⟨S, hS, hc⟩ := exists_fixField hφ
  have : fixField φ = S := SetLike.ext fun a => (mem_fixField.trans (hS a).symm)
  rw [this]; exact hc

instance charP_subfield (S : Subfield K) : CharP S 2 :=
  (RingHom.charP_iff S.subtype S.subtype_injective 2).mpr inferInstance

instance finite_subfield (S : Subfield K) : Finite S := inferInstance

theorem unitaryFieldData_fixField {φ : K ≃+* K} (hφ : orderOf φ = 3) :
    UnitaryFieldData 2 1 (fixField φ) :=
  ⟨Nat.prime_two, le_rfl, by rw [card_fixField hφ]; norm_num⟩

noncomputable section Embed

variable (S : Subfield K)

@[expose] def emb : GL (Fin 4) S →* GL (Fin 4) K := Matrix.GeneralLinearGroup.map S.subtype

theorem coe_emb (g : GL (Fin 4) S) :
    ((emb S g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) S).map S.subtype := rfl

theorem emb_injective : Function.Injective (emb S) := by
  intro g h hgh
  apply Units.ext
  have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hgh
  simp only [coe_emb] at this
  exact Matrix.map_injective S.subtype_injective this

variable {S}

theorem sigma4_subtype (hS : Nat.card S = 4) (c : S) :
    unitaryInvolution K 2 3 (c : K) = ((unitaryInvolution S 2 1 c : S) : K) := by
  haveI : Fintype S := Fintype.ofFinite S
  have h4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hS] at this
  have h4' : (c : K) ^ 4 = c := by
    have := congrArg (fun x : S => (x : K)) h4
    simpa using this
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have : (c : K) ^ 2 ^ 3 = (c : K) ^ 2 := by
    calc (c : K) ^ 2 ^ 3 = ((c : K) ^ 4) ^ 2 := by rw [← pow_mul]; norm_num
      _ = (c : K) ^ 2 := by rw [h4']
  rw [this]
  simp

theorem conjTr_emb (hS : Nat.card S = 4) (g : GL (Fin 4) S) :
    conjTr (unitaryInvolution K 2 3) ((emb S g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (conjTr (unitaryInvolution S 2 1) (g : Matrix (Fin 4) (Fin 4) S)).map S.subtype := by
  ext i j
  simp only [conjTr, coe_emb, Matrix.transpose_apply, Matrix.map_apply]
  exact sigma4_subtype hS _

theorem emb_mem_iff (hS : Nat.card S = 4) (g : GL (Fin 4) S) :
    emb S g ∈ SUid (unitaryInvolution K 2 3) 4 ↔ g ∈ SUid (unitaryInvolution S 2 1) 4 := by
  rw [mem_SUid, mem_SUid, conjTr_emb hS, coe_emb]
  have hdet : ((g : Matrix (Fin 4) (Fin 4) S).map S.subtype).det =
      S.subtype (g : Matrix (Fin 4) (Fin 4) S).det := by
    rw [RingHom.map_det]; rfl
  rw [hdet]
  have h1 : ∀ x : Matrix (Fin 4) (Fin 4) S, x.map S.subtype = 1 ↔ x = 1 := by
    intro x
    constructor
    · intro h
      have h2 : x.map S.subtype = (1 : Matrix (Fin 4) (Fin 4) S).map S.subtype := by
        rw [h]; exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
      exact Matrix.map_injective S.subtype_injective h2
    · rintro rfl
      exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [← Matrix.map_mul, h1]
  constructor
  · rintro ⟨hd, hm⟩
    exact ⟨S.subtype_injective (by rw [hd, map_one]), hm⟩
  · rintro ⟨hd, hm⟩
    exact ⟨by rw [hd, map_one], hm⟩

end Embed

noncomputable section Fixed

variable {S : Subfield K}

@[expose] def toSU (hS : Nat.card S = 4) : ↥(SUid (unitaryInvolution S 2 1) 4) →* SU4 :=
  ((emb S).comp (SUid (unitaryInvolution S 2 1) 4).subtype).codRestrict
    (SUid (unitaryInvolution K 2 3) 4) fun g => (emb_mem_iff hS _).mpr g.2

theorem coe_toSU (hS : Nat.card S = 4) (g : ↥(SUid (unitaryInvolution S 2 1) 4)) :
    ((toSU hS g : SU4) : GL (Fin 4) K) = emb S (g : GL (Fin 4) S) := rfl

theorem toSU_injective (hS : Nat.card S = 4) : Function.Injective (toSU hS) := by
  intro a b h
  apply Subtype.ext
  apply emb_injective S
  exact congrArg (fun x : SU4 => (x : GL (Fin 4) K)) h

theorem entry_fixed_of_mem_fixSub {φ : K ≃+* K} {y : SU4} (hy : y ∈ fixSub (fieldSU4 φ))
    (i j : Fin 4) : φ (((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j) =
      ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j := by
  have h := congrArg (fun z : SU4 => ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j) hy
  simpa [coe_fieldSU4, coe_glAut] using h

theorem toSU_range {φ : K ≃+* K} (hφ : orderOf φ = 3) :
    (toSU (S := fixField φ) (card_fixField hφ)).range = fixSub (fieldSU4 φ) := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    show fieldSU4 φ (toSU (card_fixField hφ) g) = toSU (card_fixField hφ) g
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSU4, coe_glAut, coe_toSU, coe_emb]
    ext i j
    simp only [Matrix.map_apply]
    exact (g : GL (Fin 4) (fixField φ)) i j |>.2
  · intro hy
    have hy' : y⁻¹ ∈ fixSub (fieldSU4 φ) := (fixSub (fieldSU4 φ)).inv_mem hy
    let M : Matrix (Fin 4) (Fin 4) (fixField φ) :=
      Matrix.of fun i j => ⟨((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j,
        mem_fixField.mpr (entry_fixed_of_mem_fixSub hy i j)⟩
    let M' : Matrix (Fin 4) (Fin 4) (fixField φ) :=
      Matrix.of fun i j => ⟨(((y⁻¹ : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j,
        mem_fixField.mpr (entry_fixed_of_mem_fixSub hy' i j)⟩
    have hM : M.map (fixField φ).subtype = ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := rfl
    have hM' : M'.map (fixField φ).subtype =
        (((y⁻¹ : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := rfl
    have h1 : M * M' = 1 := by
      apply Matrix.map_injective (fixField φ).subtype_injective
      beta_reduce
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      rw [← Units.val_mul]
      have : ((y : GL (Fin 4) K) * ((y⁻¹ : SU4) : GL (Fin 4) K)) = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
      rw [this]; rfl
    have h2 : M' * M = 1 := by
      apply Matrix.map_injective (fixField φ).subtype_injective
      beta_reduce
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      rw [← Units.val_mul]
      have : (((y⁻¹ : SU4) : GL (Fin 4) K) * (y : GL (Fin 4) K)) = 1 := by
        rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]; rfl
    let x : GL (Fin 4) (fixField φ) := ⟨M, M', h1, h2⟩
    have hx : emb (fixField φ) x = (y : GL (Fin 4) K) := Units.ext hM
    have hxmem : x ∈ SUid (unitaryInvolution (fixField φ) 2 1) 4 :=
      (emb_mem_iff (card_fixField hφ) x).mp (by rw [hx]; exact y.2)
    exact ⟨⟨x, hxmem⟩, Subtype.ext hx⟩

@[expose] def fixSubEquiv {φ : K ≃+* K} (hφ : orderOf φ = 3) :
    ↥(SUid (unitaryInvolution (fixField φ) 2 1) 4) ≃* ↥(fixSub (fieldSU4 φ)) :=
  (MonoidHom.ofInjective (toSU_injective (card_fixField hφ))).trans
    (MulEquiv.subgroupCongr (toSU_range hφ))

end Fixed

noncomputable section Catalog

@[expose] def suEquivStatedProj {S : Subfield K} (hS : Nat.card S = 4) :
    ↥(SUid (unitaryInvolution S 2 1) 4) ≃* StatedProj (StatedSU 4 (2 ^ 1) S) :=
  ((MulEquiv.subgroupCongr (SUid_eq_statedSU (F := S) (p := 2) (f := 1) (by rw [hS]; norm_num)
    4)).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
        (K := S) (2 ^ 1))).trans QuotientGroup.quotientBot).symm)

theorem catalogIs_fixSub {α : MulAut SU4} (hα3 : α ^ 3 = 1) (hα1 : fieldFactor4 α ≠ 1) :
    catalogIs ↥(fixSub α) S9.isU4two ∧ Nat.card ↥(fixSub α) = 25920 := by
  obtain ⟨h, hh⟩ := exists_conj_fieldSU4 hα3 hα1
  have hφ3 : fieldFactor4 α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hφ : orderOf (fieldFactor4 α) = 3 := orderOf_eq_prime hφ3 hα1
  let e : ↥(fixSub α) ≃* ↥(SUid (unitaryInvolution (fixField (fieldFactor4 α)) 2 1) 4) :=
    (fixSubEquivOfConj h hh).symm.trans (fixSubEquiv hφ).symm
  have hcat : catalogIs ↥(fixSub α) S9.isU4two :=
    catalogIs_u4two_of_statedProj (card_fixField hφ) (e.trans (suEquivStatedProj (card_fixField hφ)))
  refine ⟨hcat, ?_⟩
  obtain ⟨g⟩ := bridge_u4two hcat
  rw [Nat.card_congr g.toEquiv]
  exact CFSG.LieType.Multipliers.U42.card_PSp43

end Catalog

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
