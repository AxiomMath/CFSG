module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcReeShape
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Arith
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open scoped commutatorElement

@[expose] def G28CompType (Q : Type) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (IsSmallTwistedIdx d.1 ∨ IsL2EightIndex d.1) ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isoInvariant_g28CompType : IsoInvariant G28CompType := by
  rintro Q Q' _ _ e ⟨d, hd, ⟨a⟩⟩
  exact ⟨d, hd, ⟨e.symm.trans a⟩⟩

theorem isBalSmall_of_g28CompType {X : Type} [Group X] {J : Subgroup X}
    (h : G28CompType (↥J ⧸ Subgroup.center ↥J)) : IsBalSmall J := by
  obtain ⟨d, hd | hd, e⟩ := h
  · exact Or.inr (Or.inl ⟨d, hd, e⟩)
  · exact Or.inr (Or.inr ⟨d, hd, e⟩)

theorem g28CompType_psl2 {E : Type} [Field E] [Finite E] (hE : Nat.card E = 8) :
    G28CompType (Matrix.SpecialLinearGroup (Fin 2) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField E 2 3 (by norm_num)
    (by rw [hE]; norm_num)
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact ⟨⟨.A 1 q, hv⟩, Or.inr ⟨rfl, rfl, rfl⟩, ⟨eP.trans eC.symm⟩⟩

theorem g28CompType_psu38 {E : Type} [Field E] [Finite E] (hE : Nat.card E = (2 ^ 3) ^ 2) :
    G28CompType (↥(StatedSU 3 (2 ^ 3) E) ⧸ Subgroup.center ↥(StatedSU 3 (2 ^ 3) E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (n := 3) hE
    le_rfl (by decide)
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨le_rfl, fun _ => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 2 ^ 3
    norm_num
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hE]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK 3 (2 ^ 3)
  let eC := QuotientGroup.quotientMulEquivOfEq hQ.2
  exact ⟨⟨.twistedA 2 q, hv⟩, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, ⟨(eC.trans eP).trans e₀.symm⟩⟩

theorem g28CompType_of_lieModel_u33 {Y : Type} [Group Y] (h : LieModel Y .PSU 3 3 1) :
    G28CompType Y := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.statedClassicalModel_of_lieModel_psu (by norm_num) h
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨le_rfl, fun _ => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 3 ^ 1
    norm_num
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype F := Fintype.ofFinite F
  have hKK : Fintype.card F = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hF]
  let eK : F ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK 3 (3 ^ 1)
  exact ⟨⟨.twistedA 2 q, hv⟩, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, ⟨(e.trans eP).trans e₀.symm⟩⟩

section Shape


variable {K : Type} [Field K] [Finite K]

theorem g28_compShape_threeA
    (hK : Nat.card K = 8) {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    CompShape G28CompType (MulAut.conj z) := by
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  set C := Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) with hCdef
  have hC : fixSubgroup (MulAut.conj z) = C := b3Lie_fixSubgroup_conj z
  have h3 : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  have hK8 : Nat.card K = 2 ^ 3 := hK.trans (by norm_num)
  have hq : CFSG.Open.IsQuasisimple ↥C :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 (by norm_num [hK]) hzS hz3 hz1)
  haveI : CharP K 2 :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.charP_two_of_even_natCard K
      (by rw [hK]; decide)
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU (p := 2) (f := 3)
    hK8 h3 hdeg hzS hz3 hz1
  have hT : G28CompType (↥C ⧸ Subgroup.center ↥C) :=
    isoInvariant_g28CompType _ _ (centerQuotientCongr e).symm
      (g28CompType_psu38 (by rw [natCard_quadratic hdeg, hK8]))
  refine excRee_compShape_of_comm_mem (MulAut.conj z) hC.ge (fun c₁ hc₁ c₂ hc₂ => ?_) hq hT
  rw [hC] at hc₁ hc₂
  rw [commutatorElement_def]
  exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)

theorem g28_compShape_threeB (hK : Nat.card K = 8) {z : adjointGroup .G2 K}
    (hzM : z ∈ g2LongSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CompShape G28CompType (MulAut.conj z) := by
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  have hC : fixSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) :=
    b3Lie_fixSubgroup_conj z
  have hK4 : 4 ≤ Nat.card K := by norm_num [hK]
  obtain ⟨hB1, -⟩ := g2ThreeBCentMinus_holds K (by norm_num [hK]) hK4 z hzM hz3 hz1
  have hSC : g2ShortSL2 K ≤ fixSubgroup (MulAut.conj z) := fun s hs => by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.2 (g2Short_commute_g2Long hs hzM)
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  have hT : G28CompType (↥(g2ShortSL2 K) ⧸ Subgroup.center ↥(g2ShortSL2 K)) :=
    isoInvariant_g28CompType _ _ (centerQuotientCongr e) (g28CompType_psl2 hK)
  refine excRee_compShape_of_comm_mem (MulAut.conj z) hSC (fun c₁ hc₁ c₂ hc₂ => ?_)
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (isQuasisimple_g2ShortSL2 hK4)) hT
  rw [hC] at hc₁ hc₂
  rw [commutatorElement_def]
  exact hB1 c₁ hc₁ c₂ hc₂

theorem g28_compShape_field (hK : Nat.card K = 2 ^ 3)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    CompShape G28CompType (entrywiseAdjointAut Tag.G2 σ) := by
  classical
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, hk, hJC, hfixeq, -, -, -, -, -, -, -, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders (by norm_num : 2 ≤ 3) hK σ
  rw [hσ] at hk
  have hk2 : Nat.card (fixSubfield σ) = 2 := hk.trans (by norm_num)
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hmemφ : ∀ a : adjointGroup Tag.G2 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) ∈
        adjointGroup Tag.G2 K := fun a => hJC ⟨a, a.2, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : adjointGroup Tag.G2 (fixSubfield σ) →* adjointGroup Tag.G2 K,
      ∀ a, (φ a : ModGL Tag.G2 K) =
        baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) :=
    ⟨((baseChangeGL (fixSubfield σ).subtype).comp
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype).codRestrict _ hmemφ, fun _ => rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective _ (by rw [← hφdef, ← hφdef, h]))
  have hC : fixSubgroup (entrywiseAdjointAut Tag.G2 σ) = φ.range := by
    ext g
    rw [mem_fixSubgroup]
    have h1 : g ∈ φ.range ↔ (g : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 σ := by
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    rw [h1, ← hfixeq]
    constructor
    · intro h
      exact ⟨g, h, rfl⟩
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      subst this
      exact hg'
  obtain ⟨hq, -, hZT, -, -⟩ := derived_range_adjointG2_two (fixSubfield σ) hk2 φ hφ
  have hT0 : ⁅φ.range, φ.range⁆ = (commutator (adjointGroup Tag.G2 (fixSubfield σ))).map φ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  let eT : ↥⁅φ.range, φ.range⁆ ≃*
      ↥⁅adjointGroup Tag.G2 (fixSubfield σ), adjointGroup Tag.G2 (fixSubfield σ)⁆ :=
    ((MulEquiv.subgroupCongr hT0).trans
      ((commutator (adjointGroup Tag.G2 (fixSubfield σ))).equivMapOfInjective φ hφ).symm).trans
      (((commutator (adjointGroup Tag.G2 (fixSubfield σ))).equivMapOfInjective
        (adjointGroup Tag.G2 (fixSubfield σ)).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _)))
  have hTN : G28CompType ↥⁅φ.range, φ.range⁆ :=
    isoInvariant_g28CompType _ _ eT.symm (g28CompType_of_lieModel_u33
      (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds _ hk2))
  have hT : G28CompType (↥⁅φ.range, φ.range⁆ ⧸ Subgroup.center ↥⁅φ.range, φ.range⁆) :=
    isoInvariant_g28CompType _ _
      ((QuotientGroup.quotientMulEquivOfEq hZT).trans QuotientGroup.quotientBot).symm hTN
  refine excRee_compShape_of_comm_mem _ (N := ⁅φ.range, φ.range⁆) ?_ (fun c₁ hc₁ c₂ hc₂ => ?_)
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq) hT
  · rw [hC]
    exact (commutator_self_le_and_normalized φ.range).1
  · rw [hC] at hc₁ hc₂
    exact Subgroup.commutator_mem_commutator hc₁ hc₂

theorem g28_compShape
    (hK : Nat.card K = 8)
    {β : MulAut ↥(adjointGroup Tag.G2 K)} (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    CompShape G28CompType β := by
  classical
  have hK8 : Nat.card K = 2 ^ 3 := hK.trans (by norm_num)
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  by_cases hin : β ∈ (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut _).range
  · obtain ⟨s, rfl, hs3, hs1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ hin hβ hβ1
    have hK3 : ringChar K ≠ 3 :=
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.ringChar_ne_three_of_dvd_add_one K
        (by norm_num [hK])
    obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 (by norm_num [hK]) s hs3 hs1
    have hz3 : (g * s * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hs3]; group
    have hz1 : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    refine CompShape.of_congr isoInvariant_g28CompType
      ((MulAut.conj g : MulAut ↥(adjointGroup Tag.G2 K)) : ↥(adjointGroup Tag.G2 K) ≃* _) ?_
    rw [excRee_congr_self, ← map_inv MulAut.conj, ← map_mul MulAut.conj,
      ← map_mul MulAut.conj]
    rcases hg with h | h
    · exact g28_compShape_threeA hK h hz3 hz1
    · exact g28_compShape_threeB hK h hz3 hz1
  · have hNF := conj_normalForm_of_pointwise
      (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        (by norm_num : 2 ≤ 3) K hK8).1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF β
    have hαp : orderOf (⟨β, Subgroup.mem_top β⟩ :
        (⊤ : Subgroup (MulAut ↥(adjointGroup Tag.G2 K)))) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hβ hβ1
    obtain ⟨hσp, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial
      (by norm_num : 2 ≤ 3) hK8 Nat.prime_three ⊤ le_top ⟨β, Subgroup.mem_top β⟩ hin hαp y σ hyσ
    have hh' : MulAut.conj h * β * (MulAut.conj h)⁻¹ = entrywiseAdjointAut Tag.G2 σ := hh
    refine CompShape.of_congr isoInvariant_g28CompType
      ((MulAut.conj h : MulAut ↥(adjointGroup Tag.G2 K)) : ↥(adjointGroup Tag.G2 K) ≃* _) ?_
    rw [excRee_congr_self, hh']
    exact g28_compShape_field hK8 hσp

end Shape

end CFSG.HardMathSupport.Dickson.Bal207

end
