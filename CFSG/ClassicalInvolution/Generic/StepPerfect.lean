module

public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.PerfectCase
public import CFSG.ClassicalInvolution.SubnormalClosure.Reduction
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open scoped MatrixGroups

theorem five_le_pow_of_nonsolvable_witness {K : Type*} [Group K] [Finite K] {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (φ : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p n))
    (hns : ¬ Group.IsSolvable K) : 5 ≤ p ^ n := by
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have h3 : 3 ≤ p ^ n := hp3.trans (Nat.le_self_pow hn.ne' p)
  have hodd : Odd (p ^ n) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  by_contra hlt
  have h3' : p ^ n = 3 := by
    have hlt' : p ^ n < 5 := not_le.mp hlt
    obtain ⟨k, hk⟩ := hodd
    omega
  apply hns
  have h24 : Nat.card SL(2, GaloisField p n) = 24 := by
    have := Fintype.ofFinite (GaloisField p n)
    rw [Matrix.card_SL_field 2, ← Nat.card_eq_fintype_card, hcard, h3', Fin.prod_univ_two]
    norm_num
  have hsolv : Group.IsSolvable SL(2, GaloisField p n) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
  have h1 : Group.IsSolvable (K ⧸ classicalInvolutionOddCore K) :=
    Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have h2 : Group.IsSolvable (classicalInvolutionOddCore K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card K)
  exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore K)

section Member

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Group F] [Finite F]

theorem exists_classicalMember_of_witness {z : F} (hz : orderOf z = 2) {K : Subgroup F}
    (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer ({z} : Set F)))
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (hf : 0 < f)
    (hp2 : p ≠ 2) (hns : ¬ Group.IsSolvable K) :
    ∃ L : Subgroup F, IsClassicalMember p f L z := by
  set X : Subgroup F := Subgroup.centralizer ({z} : Set F) with hX
  have hKX : K ≤ X := isSubnormal_le hK
  have hzX : z ∈ X := hKX hzK
  have hKsub : IsSubnormal (K.subgroupOf X) ⊤ := by
    have := isSubnormal_subgroupOf hK X
    rwa [Subgroup.subgroupOf_self] at this
  have hw : classicalInvolutionWitness K := Or.inl ⟨p, f, inferInstance, hp2, hf, ⟨e⟩⟩
  have eKX : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have hwX : classicalInvolutionWitness (K.subgroupOf X) :=
    classicalInvolutionWitness_of_mulEquiv eKX.symm hw
  have hnsX : ¬ Group.IsSolvable (K.subgroupOf X) := fun h =>
    hns (Group.isSolvable_of_surjective (f := eKX.toMonoidHom) eKX.surjective)
  have hq := isQuasisimple_oddCoreQuotient_of_witness hwX hnsX
  obtain ⟨L, hLle, hL2, hmap⟩ := exists_isTwoComponent_le (K.subgroupOf X) hKsub hq
  have hLsub : IsSubnormal L ⊤ := hL2.1
  have hz'L : (⟨z, hzX⟩ : X) ∈ L :=
    mem_of_orderOf_eq_two_of_map_eq hLle hLsub hKsub hmap (Subgroup.mem_subgroupOf.mpr hzK)
      (by rw [Subgroup.orderOf_mk]; exact hz)
  obtain ⟨e2⟩ := nonempty_oddCoreQuotientEquiv_of_map_eq hLsub hKsub hmap
  have hOK : (classicalInvolutionOddCore (K.subgroupOf X)).map eKX.toMonoidHom =
      classicalInvolutionOddCore K := OddCore.equiv_invariant eKX
  let eLK : L ⧸ classicalInvolutionOddCore L ≃* SL(2, GaloisField p f) :=
    e2.trans ((QuotientGroup.congr _ _ eKX hOK).trans e)
  let eLX : L ≃* L.map X.subtype := L.equivMapOfInjective X.subtype X.subtype_injective
  have hOLX : (classicalInvolutionOddCore L).map eLX.toMonoidHom =
      classicalInvolutionOddCore (L.map X.subtype) := OddCore.equiv_invariant eLX
  refine ⟨L.map X.subtype, ?_, ⟨⟨z, hzX⟩, hz'L, rfl⟩, ?_, ?_, ?_⟩
  · exact hz
  · have : Group.IsPerfect L := ⟨TwoComponents.perfect hL2⟩
    exact Group.IsPerfect.map X.subtype
  · have h1 := Components.chain_map X.subtype hLsub
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h1
  · exact ⟨(QuotientGroup.congr _ _ eLX hOLX).symm.trans eLK⟩

end Member

section OddLieType

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem oddLieType_of_classicalMember (hI : CITInductiveU p f) (h0 : ModelClauseZero)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hnab : ∃ a b : F, a * b ≠ b * a) {L : Subgroup F} {z : F}
    (h : IsClassicalMember p f L z) : CFSG.Blueprint.OddLieType F := by
  have hmod := hI hp2 hq F _ (inClass_conjugates h)
  have hO : classicalInvolutionOddCore F = ⊥ := oddCore_eq_bot_of_simple h.orderOf_eq_two
  obtain ⟨D⟩ := lieSystem_of_lieSystemMod_corefree hO hmod
  obtain ⟨t, n, e, hp, ψ, hsurj, hker, hFT, hadm, -⟩ := D.exists_model_of_simple hnab
  obtain ⟨-, hmodel⟩ := h0 t n p e hp hFT hadm
  let eF : (modelUniv t n p e hp).K ⧸ Subgroup.center (modelUniv t n p e hp).K ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  exact ⟨t, n, p, e, hp, hp2, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eF hmodel⟩

end OddLieType

@[expose] def CITSimplePerfectSL2 : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) →
    (∃ (p n : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 0 < n ∧
      Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p n))) →
    ¬ Group.IsSolvable K →
    CFSG.Blueprint.OddLieType F

@[expose] def CIT2A7Case : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) →
    (CFSG.Open.IsQuasisimple (K ⧸ classicalInvolutionOddCore K) ∧
      Nat.card (Subgroup.center (K ⧸ classicalInvolutionOddCore K)) = 2 ∧
      Nonempty ((K ⧸ classicalInvolutionOddCore K) ⧸
        Subgroup.center (K ⧸ classicalInvolutionOddCore K) ≃* alternatingGroup (Fin 7))) →
    ¬ Group.IsSolvable K →
    CFSG.Blueprint.OddLieType F ∨ CFSG.Blueprint.NativeSporadic.IsSporadic F .M11

theorem citSimplePerfect_of_cases (h1 : CITSimplePerfectSL2) (h2 : CIT2A7Case) :
    CITSimplePerfect := by
  intro F _ _ _ hnab z hz K hzK hK hw hns
  rcases hw with ⟨p, n, hp, hp2, hn, he⟩ | hw2
  · exact Or.inl (h1 F hnab z hz K hzK hK ⟨p, n, hp, hp2, hn, he⟩ hns)
  · exact h2 F hnab z hz K hzK hK hw2 hns

theorem citSimplePerfectSL2_of_citInductiveU
    (hI : ∀ (p f : ℕ) [Fact p.Prime], CITInductiveU p f) (h0 : ModelClauseZero) :
    CITSimplePerfectSL2 := by
  intro F _ _ _ hnab z hz K hzK hK ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ hns
  have hq5 : 5 ≤ p ^ n := five_le_pow_of_nonsolvable_witness hp2 hn e hns
  obtain ⟨L, hL⟩ := exists_classicalMember_of_witness hz hzK hK e hn hp2 hns
  exact oddLieType_of_classicalMember (hI p n) h0 hp2 hq5 hnab hL

theorem citSimplePerfect_of_coreStep
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreStep p f)
    (hfund : ∀ (p f : ℕ) [Fact p.Prime], ClassicalIsFundamental p f)
    (hlift : ∀ (p : ℕ) [Fact p.Prime], CentralLift p) (h0 : ModelClauseZero)
    (h2 : CIT2A7Case) : CITSimplePerfect :=
  citSimplePerfect_of_cases
    (citSimplePerfectSL2_of_citInductiveU
      (fun p f _ => citInductiveU_of_coreStep (hcore p f) (hfund p f) (hlift p)) h0) h2

end CFSG.ClassicalInvolution.Generic
