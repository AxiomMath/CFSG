module

public import CFSG.GH74.Generic.BProg.B2.PuL4Inner
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412
public import CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
public import CFSG.GH74.GLS.Stage2.Final.ModelClsFam
public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen
public import CFSG.GH74.GLS.Stage2.Final.ModelE
public import CFSG.GH74.GLS.Stage2.Final.ModelIVK410
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Mat
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final

namespace PuL4InnerSD

theorem dihedral_q8_relation {k : ℕ} (x y : DihedralGroup k) (hxy : x * y = (x * x) * (y * x))
    (hsq : x * x = y * y) : x * x = 1 := by
  rcases x with a | a <;> rcases y with b | b
  · rw [DihedralGroup.one_def]
    simp only [DihedralGroup.r_mul_r, DihedralGroup.r.injEq] at hxy ⊢
    linear_combination (-1 : ZMod k) * hxy
  · rw [hsq]; exact DihedralGroup.sr_mul_self b
  · exact DihedralGroup.sr_mul_self a
  · exact DihedralGroup.sr_mul_self a

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {D₁ D₂ : Subgroup G}
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) {g : G} (hg : g ∈ D₁ ⊔ D₂) :
    ∃ a ∈ D₁, ∃ b ∈ D₂, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ D₁, ∃ b ∈ D₂, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', D₁.mul_mem ha ha', b * b', D₂.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, D₁.one_mem, 1, D₂.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, D₁.inv_mem ha, b⁻¹, D₂.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have := hcomm a⁻¹ (D₁.inv_mem ha) b⁻¹ (D₂.inv_mem hb)
            exact this.symm }
  have : D₁ ⊔ D₂ ≤ S := sup_le
    (fun a ha => ⟨a, ha, 1, D₂.one_mem, by simp⟩) (fun b hb => ⟨1, D₁.one_mem, b, hb, by simp⟩)
  exact this hg

theorem eq_of_mul_eq_mul {G : Type*} [Group G] {D₁ D₂ : Subgroup G} (hbot : D₁ ⊓ D₂ = ⊥)
    {a a' b b' : G} (ha : a ∈ D₁) (ha' : a' ∈ D₁) (hb : b ∈ D₂) (hb' : b' ∈ D₂)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hm : a'⁻¹ * a ∈ D₁ ⊓ D₂ :=
    ⟨D₁.mul_mem (D₁.inv_mem ha') ha, h1 ▸ D₂.mul_mem hb' (D₂.inv_mem hb)⟩
  rw [hbot, Subgroup.mem_bot] at hm
  refine ⟨?_, ?_⟩
  · exact (inv_mul_eq_one.mp hm).symm
  · rw [hm] at h1
    exact (mul_inv_eq_one.mp h1.symm).symm


theorem no_q8_of_dihedral_pair {G : Type*} [Group G] {D₁ D₂ : Subgroup G}
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) (hbot : D₁ ⊓ D₂ = ⊥) {k₁ k₂ : ℕ}
    (e₁ : ↥D₁ ≃* DihedralGroup k₁) (e₂ : ↥D₂ ≃* DihedralGroup k₂) (ψ : QuaternionGroup 2 →* G)
    (hψ : Function.Injective ψ) (hle : ∀ x, ψ x ∈ D₁ ⊔ D₂) : False := by
  have hii : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 = QuaternionGroup.a 2 := by decide
  have hjj : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by decide
  have hij : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by decide
  have hz : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  obtain ⟨a₁, ha₁, a₂, ha₂, hI⟩ := exists_mul_of_mem_sup hcomm (hle (QuaternionGroup.a 1))
  obtain ⟨b₁, hb₁, b₂, hb₂, hJ⟩ := exists_mul_of_mem_sup hcomm (hle (QuaternionGroup.xa 0))
  have hsq : ∀ (x y : G), x ∈ D₁ → y ∈ D₂ → (x * y) * (x * y) = (x * x) * (y * y) := by
    intro x y hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcomm x hx y hy]
      _ = (x * x) * (y * y) := by group
  have hzz : ψ (QuaternionGroup.a 2) = (a₁ * a₁) * (a₂ * a₂) := by
    rw [← hii, map_mul, hI, hsq _ _ ha₁ ha₂]
  have hzz' : ψ (QuaternionGroup.a 2) = (b₁ * b₁) * (b₂ * b₂) := by
    rw [← hjj, map_mul, hJ, hsq _ _ hb₁ hb₂]
  have hsq1 := eq_of_mul_eq_mul hbot (D₁.mul_mem ha₁ ha₁) (D₁.mul_mem hb₁ hb₁)
    (D₂.mul_mem ha₂ ha₂) (D₂.mul_mem hb₂ hb₂) (hzz.symm.trans hzz')
  have hrel : ψ (QuaternionGroup.a 1) * ψ (QuaternionGroup.xa 0) =
      ψ (QuaternionGroup.a 2) * (ψ (QuaternionGroup.xa 0) * ψ (QuaternionGroup.a 1)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← hij]
  have hcc : ∀ (x y x' y' : G), x ∈ D₁ → y ∈ D₂ → x' ∈ D₁ → y' ∈ D₂ →
      (x * y) * (x' * y') = (x * x') * (y * y') := by
    intro x y x' y' hx hy hx' hy'
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [← hcomm x' hx' y hy]
      _ = (x * x') * (y * y') := by group
  have hrel' : ((a₁ * b₁) * (a₂ * b₂)) =
      (((a₁ * a₁) * (b₁ * a₁)) * ((a₂ * a₂) * (b₂ * a₂))) := by
    rw [← hcc _ _ _ _ ha₁ ha₂ hb₁ hb₂]
    rw [hI, hJ] at hrel
    rw [hrel, hzz, hcc _ _ _ _ hb₁ hb₂ ha₁ ha₂,
      hcc _ _ _ _ (D₁.mul_mem ha₁ ha₁) (D₂.mul_mem ha₂ ha₂) (D₁.mul_mem hb₁ ha₁) (D₂.mul_mem hb₂ ha₂)]
  have hu := eq_of_mul_eq_mul hbot (D₁.mul_mem ha₁ hb₁)
    (D₁.mul_mem (D₁.mul_mem ha₁ ha₁) (D₁.mul_mem hb₁ ha₁)) (D₂.mul_mem ha₂ hb₂)
    (D₂.mul_mem (D₂.mul_mem ha₂ ha₂) (D₂.mul_mem hb₂ ha₂)) hrel'
  have h1 : a₁ * a₁ = 1 := by
    have := dihedral_q8_relation (e₁ ⟨a₁, ha₁⟩) (e₁ ⟨b₁, hb₁⟩)
      (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]; exact congrArg e₁ (Subtype.ext hu.1))
      (by rw [← map_mul, ← map_mul]; exact congrArg e₁ (Subtype.ext hsq1.1))
    rw [← map_mul] at this
    exact congrArg Subtype.val (e₁.injective (this.trans (map_one e₁).symm))
  have h2 : a₂ * a₂ = 1 := by
    have := dihedral_q8_relation (e₂ ⟨a₂, ha₂⟩) (e₂ ⟨b₂, hb₂⟩)
      (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]; exact congrArg e₂ (Subtype.ext hu.2))
      (by rw [← map_mul, ← map_mul]; exact congrArg e₂ (Subtype.ext hsq1.2))
    rw [← map_mul] at this
    exact congrArg Subtype.val (e₂.injective (this.trans (map_one e₂).symm))
  apply hz
  apply hψ
  rw [hzz, h1, h2, mul_one, map_one]

theorem false_of_noncentral_shape3 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (htH : t ∈ H) {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IVK.IsLnEps 4 ↥H 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 ↥H (-1) q))
    (hnc : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H))
    (h3 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShape3 (↥L ⧸ Z)) : False := by
  obtain ⟨Z, -, hZo, hZn, h3'⟩ := h3
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLC hZn hZo (exists_q8_of_shape13 (Or.inr h3'))
  set u : ↥H := ⟨t, htH⟩ with hu
  have hu2 : orderOf u = 2 := by rw [← Subgroup.orderOf_coe]; exact hs.inv
  have hcomm : ∀ y : ↥(H ⊓ centralizer ({t} : Set N)),
      Subgroup.inclusion inf_le_left y ∈ centralizer ({u} : Set ↥H) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    exact this
  let ψK : QuaternionGroup 2 →* ↥(centralizer ({u} : Set ↥H)) :=
    ((Subgroup.inclusion inf_le_left).comp ψ).codRestrict _ (fun x => hcomm (ψ x))
  have hψK : Function.Injective ψK := by
    intro a b hab
    apply hψ
    have h1 : Subgroup.inclusion (inf_le_left : H ⊓ centralizer ({t} : Set N) ≤ H) (ψ a) =
        Subgroup.inclusion (inf_le_left : H ⊓ centralizer ({t} : Set N) ≤ H) (ψ b) :=
      congrArg Subtype.val hab
    exact Subgroup.inclusion_injective _ h1
  have hP : IsPGroup 2 ψK.range :=
    IsPGroup.of_surjective isPGroup_q8 ψK.rangeRestrict ψK.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨D₁, D₂, n, -, hSD, hcm, hbot, ⟨-, k₁, -, -, ⟨e₁⟩⟩, ⟨-, k₂, -, -, ⟨e₂⟩⟩, -⟩ :=
    ivk_4_12_nc hq h5 hK hu2 hnc S
  refine no_q8_of_dihedral_pair hcm hbot e₁ e₂
    ((centralizer ({u} : Set ↥H)).subtype.comp ψK) ?_ ?_
  · exact (centralizer ({u} : Set ↥H)).subtype_injective.comp hψK
  · intro x
    rw [← hSD]
    exact Subgroup.mem_map.2 ⟨ψK x, hS ⟨x, rfl⟩, rfl⟩


section Certified3


theorem false_of_inner_shape3_SD {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hSD : T4.PuL4SD ↥H) (htH : t ∈ H)
    (h3 : T4.ShapeS3 L) : False := by
  obtain ⟨p, f, hp, hp2, hf, hq3, ⟨h4, hL⟩ | ⟨h4, hU⟩⟩ := hSD
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have e' : ↥H ≃* PG (ModelData.lin F) := e
    have h5 : 5 ≤ Nat.card F := by rw [hF]; omega
    have h4' : Nat.card F % 4 = 3 := by rw [hF]; exact h4
    have hG : GoodModel (ModelData.lin F) := goodModel_lin h2 h5
    have hZ : ZsTwo (ModelData.lin F) := zsTwo_lin h4'
    have hC : ClsFacts (ModelData.lin F) := clsFacts_lin h2 h5 h4'
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    rcases all_inv_classes hG hZ hC hx with hc | hc
    · exact PuL4Inner.false_of_inner_shape_model hG hs htH e' hc
    · have hSq : HasSqLift (ModelData.lin F) (e' ⟨t, htH⟩) (ModelData.lin F).xK :=
        HasSqLift.conj (ModelData.xK_mem_center _) (hasSqLift_wy _) hc
      have hnc := not_isCentralInvolution_of_sqLift hG hZ hSq
      have hnc' : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H) := fun hcen =>
        hnc (ModelBlock.isCentralInvolution_map e' hcen)
      exact false_of_noncentral_shape3 hs htH (q := p ^ f) (Nat.odd_iff.mpr (by omega))
        (by omega) (Or.inl ⟨h4, Or.inl ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩⟩) hnc' h3
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    have e' : ↥H ≃* PG (ModelData.uni hF) := e
    have h5 : 5 ≤ p ^ f := by omega
    have hG : GoodModel (ModelData.uni hF) := goodModel_uni hF hp2 h5
    have hZ : ZsTwo (ModelData.uni hF) := zsTwo_uni hF h4
    have hC : ClsFacts (ModelData.uni hF) := clsFacts_uni hF hp2 h5 h4
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    rcases all_inv_classes hG hZ hC hx with hc | hc
    · exact PuL4Inner.false_of_inner_shape_model hG hs htH e' hc
    · have hSq : HasSqLift (ModelData.uni hF) (e' ⟨t, htH⟩) (ModelData.uni hF).xK :=
        HasSqLift.conj (ModelData.xK_mem_center _) (hasSqLift_wy _) hc
      have hnc := not_isCentralInvolution_of_sqLift hG hZ hSq
      have hnc' : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H) := fun hcen =>
        hnc (ModelBlock.isCentralInvolution_map e' hcen)
      exact false_of_noncentral_shape3 hs htH (q := p ^ f) (Nat.odd_iff.mpr (by omega))
        (by omega) (Or.inr ⟨h4, Or.inr ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩⟩) hnc' h3

end Certified3

end PuL4InnerSD

end CFSG.GH74.Generic.BProg.B2
