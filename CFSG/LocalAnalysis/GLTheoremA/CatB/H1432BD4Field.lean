module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432BD4Rank
public import CFSG.HardMathSupport.Timmesfeld.DFour.Tower
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Stab
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.LieType.Chevalley.CoordinateFieldFixedStructure
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
  (mem_zpowers_of_forall_fixedFieldImage)

private def resHom {G : Type*} [Group G] (J : Subgroup G) (B : Subgroup (MulAut G))
    (hJ : ∀ φ ∈ B, ∀ x ∈ J, φ x ∈ J) : ↥B →* MulAut ↥J where
  toFun φ :=
    { toFun := fun x => ⟨φ.1 x, hJ _ φ.2 _ x.2⟩
      invFun := fun x => ⟨φ.1⁻¹ x, hJ _ (inv_mem φ.2) _ x.2⟩
      left_inv := fun x => Subtype.ext (φ.1.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (φ.1.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul φ.1 x.1 y.1) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

private theorem resHom_apply {G : Type*} [Group G] (J : Subgroup G) (B : Subgroup (MulAut G))
    (hJ : ∀ φ ∈ B, ∀ x ∈ J, φ x ∈ J) (φ : ↥B) (x : ↥J) :
    ((resHom J B hJ φ x : ↥J) : G) = (φ : MulAut G) x :=
  rfl


@[expose] def BD4FieldNormalForm : Prop :=
  ∀ (K : Type) [Field K], Nat.card K = 27 →
    ∀ α : MulAut ↥(adjointGroup Tag.D4 K), α ^ 3 = 1 → α ∉ inner ↥(adjointGroup Tag.D4 K) →
      ∀ A : Subgroup ↥(adjointGroup Tag.D4 K), GLAPComponent 3 (fixSubgroup α) A →
        Nat.card (PSimple 3 A) = 4952179814400 →
        ∃ (T : K ≃+* K) (ψ : MulAut ↥(adjointGroup Tag.D4 K)), (∀ c, T c = c ^ 3) ∧
          (ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T ∨
            ψ * α ^ 2 * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T)


set_option linter.unusedSectionVars false

theorem card_le_pow_nine_of_frobenius {F : Type} [Field F] [Finite F] (hF : Nat.card F = 27)
    (T : F ≃+* F) (hT : ∀ c, T c = c ^ 3) {B : Subgroup (MulAut ↥(adjointGroup Tag.D4 F))}
    (hB : IsElemAbelian 3 B) (hβB : entrywiseAdjointAut Tag.D4 T ∈ B) : Nat.card B ≤ 3 ^ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := Tag.D4) (K := F)
  have hF3 : Nat.card F = 3 ^ 3 := hF.trans (by norm_num)
  haveI : CharP F 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by norm_num) hF3
  have hM : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three (by norm_num) hF3
  have hTo : orderOf T = 3 := by
    rw [show T = fr from RingEquiv.ext fun c => by rw [hT, hfr], hord]
  have hT3 : T ^ 3 = 1 := by
    rw [← hTo]
    exact pow_orderOf_eq_one T
  obtain ⟨-, hk⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_three (by norm_num) hF3 T
  rw [hTo] at hk
  have hk3 : Nat.card ↥(fixSubfield T) = 3 := hk.trans (by norm_num)
  set β := entrywiseAdjointAut Tag.D4 T with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← entrywiseAdjointAut_pow, hT3, entrywiseAdjointAut_one]
  obtain ⟨-, -, -, hJΓ, -, -, -, hder⟩ := Chevalley_coordinate_field_fixed_structure Tag.D4 F hM T
  have hJA : fixedFieldImage Tag.D4 T ≤ adjointGroup Tag.D4 F := hJΓ.trans inf_le_left
  set J : Subgroup ↥(adjointGroup Tag.D4 F) :=
    (fixedFieldImage Tag.D4 T).subgroupOf (adjointGroup Tag.D4 F) with hJ
  set Fβ : Subgroup ↥(adjointGroup Tag.D4 F) := fixSubgroup β with hFβdef
  have hΓ : entrywiseFixedGroup Tag.D4 T = Fβ.map (adjointGroup Tag.D4 F).subtype := by
    ext g
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨hg, hfix⟩
      exact ⟨⟨g, hg⟩, mem_fixSubgroup.2 (Subtype.ext
        ((coe_entrywiseAdjointAut Tag.D4 T ⟨g, hg⟩).trans hfix)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (coe_entrywiseAdjointAut Tag.D4 T x).symm.trans
        (congrArg Subtype.val (mem_fixSubgroup.1 hx))⟩
  have hJeq : J = ⁅Fβ, Fβ⁆ := by
    ext x
    rw [hJ, Subgroup.mem_subgroupOf, ← hder, hΓ, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)
  have hFβ : ∀ φ ∈ B, Fβ.map φ.toMonoidHom ≤ Fβ := by
    rintro φ hφ _ ⟨x, hx, rfl⟩
    have hc : φ * β = β * φ := d3f_commute hB hφ hβB
    have hx' : β x = x := mem_fixSubgroup.1 hx
    refine mem_fixSubgroup.2 ?_
    change β (φ x) = φ x
    rw [← MulAut.mul_apply, ← hc, MulAut.mul_apply, hx']
  have hJB : ∀ φ ∈ B, ∀ x ∈ J, φ x ∈ J := by
    intro φ hφ x hx
    have h1 : ⁅Fβ, Fβ⁆.map φ.toMonoidHom ≤ ⁅Fβ, Fβ⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (hFβ φ hφ) (hFβ φ hφ)
    rw [hJeq] at hx ⊢
    exact h1 (Subgroup.mem_map_of_mem _ hx)
  set ρ : ↥B →* MulAut ↥J := resHom J B hJB with hρ
  have hker : ∀ φ : ↥B, ρ φ = 1 → (φ : MulAut ↥(adjointGroup Tag.D4 F)) ∈ Subgroup.zpowers β := by
    intro φ h
    refine mem_zpowers_of_forall_fixedFieldImage T fun j hj => ?_
    have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨j, hj⟩ : ↥J) : ↥(adjointGroup Tag.D4 F))) h
    simpa only [hρ, resHom_apply, MulAut.one_apply] using h1
  have hkle : Nat.card ρ.ker ≤ 3 := by
    have h1 : Nat.card ρ.ker ≤ Nat.card (Subgroup.zpowers β) :=
      Nat.card_le_card_of_injective (fun φ => ⟨φ.1.1, hker φ.1 (MonoidHom.mem_ker.1 φ.2)⟩)
        fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h')
    rw [Nat.card_zpowers] at h1
    exact h1.trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hβ3))
  have hcommB : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (d3f_commute hB a.2 b.2)
  have hpowB : ∀ a : ↥B, a ^ 3 = 1 := fun a => Subtype.ext (hB.2 a.1 a.2)
  have hRE : IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : MulAut ↥J) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hcommB]
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hz
      rw [← map_pow, hpowB, map_one]
  let eJ : ↥J ≃* adjointGroup Tag.D4 (fixSubfield T) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv T).symm
  obtain ⟨Φ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
      (fixSubfield T)
  have hmodelJ : StatedClassicalModel ↥J .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, ↥(fixSubfield T), inferInstance, inferInstance,
      by rw [hk3, pow_one], ⟨eJ.trans Φ.symm⟩⟩
  have hcen : Subgroup.center ↥J = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [Nat.card_congr (Subgroup.centerCongr eJ).toEquiv, center_adjointGroup_eq_bot_field,
      Subgroup.card_bot]
  have hR : Nat.card ρ.range ≤ 3 ^ 8 := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hRE]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : ρ.range ≤ ⊤)
    have h2 := CFSG.HardMathSupport.Timmesfeld.DFour.pRank_mulAut_le_of_not_dvd hmodelJ hcen
      (by norm_num)
    have h3 := pRank_top_le_seven hk3 eJ
    omega
  rw [← Subgroup.card_ker_mul_card_range ρ]
  calc Nat.card ρ.ker * Nat.card ρ.range ≤ 3 * 3 ^ 8 := Nat.mul_le_mul hkle hR
    _ = 3 ^ 9 := by norm_num

theorem card_le_pow_nine_of_fieldNormalForm (hN : BD4FieldNormalForm) {F : Type} [Field F]
    (hF : Nat.card F = 27) (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα3 : α ^ 3 = 1)
    (hout : α ∉ inner ↥(adjointGroup Tag.D4 F)) {A : Subgroup ↥(adjointGroup Tag.D4 F)}
    (hA : GLAPComponent 3 (fixSubgroup α) A) (hcard : Nat.card (PSimple 3 A) = 4952179814400)
    {B : Subgroup (MulAut ↥(adjointGroup Tag.D4 F))} (hB : IsElemAbelian 3 B) (hαB : α ∈ B) :
    Nat.card B ≤ 3 ^ 9 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨T, ψ, hT, hψ⟩ := hN F hF α hα3 hout A hA hcard
  set c : MulAut (MulAut ↥(adjointGroup Tag.D4 F)) := MulAut.conj ψ with hc
  have hβB : entrywiseAdjointAut Tag.D4 T ∈ B.map c.toMonoidHom := by
    rcases hψ with h | h
    · exact ⟨α, hαB, h⟩
    · exact ⟨α ^ 2, pow_mem hαB 2, h⟩
  have hcard' : Nat.card (B.map c.toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective c.injective
  rw [← hcard']
  exact card_le_pow_nine_of_frobenius hF T hT (CFSG.SectionRank.isElemAbelian_map hB c.toMonoidHom)
    hβB

end CFSG.LocalAnalysis.GLTheoremA.H1420.BD4

end
