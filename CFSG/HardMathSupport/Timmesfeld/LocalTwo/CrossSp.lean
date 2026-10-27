module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFamily
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticB
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)

theorem isLocallyBalancedAbs_two_psp {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hpℓ : p ≠ ℓ) :
    IsLocallyBalancedAbs p 2 (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hp2 : p ≠ 2 := by omega
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective hℓ hf hK hr hrq
  have O := CFSG.RankThree.PartOne.KCSpComm.spOuter hℓ hf hr hK
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : NeZero r := ⟨by omega⟩
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_ ?_
  · intro E hEin hE hEc H hH
    exact localDeltaIn_eq_bot_psp hℓ hf hK hp (by omega) hpℓ hr hrq E hEin hE hEc hH
  · intro D hD hDc hDin
    have hEel : CFSG.IsElementaryAbelian p D :=
      { toIsMulCommutative := hD.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hD.2 x x.2) }
    have hcap := CFSG.RankThree.PartOne.KCSpComm.card_inf_inner_eq_prime O hr hp hp2 hcyc
      (A := D) hDc hDin
    obtain ⟨y, hyD, hy1⟩ : ∃ y ∈ D ⊓ innerAut (StatedProj (StatedSp r K)), y ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : D ⊓ innerAut (StatedProj (StatedSp r K)) = ⊥ :=
        eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
      have hcap' : Nat.card ↥(D ⊓ innerAut (StatedProj (StatedSp r K))) = p := hcap
      rw [hbot, Subgroup.card_bot] at hcap'
      exact hp.one_lt.ne hcap'
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    obtain ⟨hpf, σ, hσ, h, -, hxh⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.noninner_element_data O hp hp2 (A := D) hxD hxin
    have hcomm : y * x = x * y := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨y, hyD.1⟩ ⟨x, hxD⟩)
    have hyp : y ^ p = 1 := hD.2 y hyD.1
    have hfull := CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      (K := K) hℓ hp (by omega) hpℓ hf hr hK σ hσ
    obtain ⟨-, -, hTs, -, -, hJfix, -, hJs, -, hfixing, hzp, hzcard, -, hexc⟩ := hfull
    have hδp : orderOf (fieldAut r K σ) = p := by
      rw [← Nat.card_zpowers, hzcard]
    obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyD.2 hy1 hyp hcomm
    have hnexc : ¬ (r = 2 ∧ ℓ ^ (f / p) = 2) := by
      rintro hex
      obtain ⟨-, hp5', -⟩ := hexc hex ⟨k, (hJfix k).2 hkδ, hkord⟩
      omega
    obtain ⟨hJsimple, hJnc⟩ := hJs hnexc
    have hJq : CFSG.IsQuasisimple (CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup K r σ) :=
      isQuasisimple_of_simple_nonabelian (fun hc => by
        obtain ⟨a, b, hab⟩ := hJnc
        exact hab (hc a b))
    refine ⟨x, hxD, hxin, ?_⟩
    refine fieldCoreAt_of_canonical_conj hp hinj hδp hJq hJfix ?_ hxh hyD.2 hy1 hyp hcomm
    intro β hβ
    have hβmem : β ∈ fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        ((CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup K r σ : Subgroup
          (StatedProj (StatedSp r K))) : Set (StatedProj (StatedSp r K))) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hβ u hu
    rw [hfixing, hzp] at hβmem
    exact hβmem

open CFSG.HardMathSupport.Timmesfeld.DefChar

theorem crossCharTwoFamCat_C : CrossCharTwoFamCat .C := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ p hp hp5 hc _
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := hrange.1
  have hq2 : q.p ≠ 2 := hrange.2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hodd : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := by omega
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
    (isLocallyBalancedAbs_two_psp q.prime_p q.exponent_pos hK (by omega) hodd hp hp5 hpq)

@[expose] def regimeBSpTwo (idx : TauCeti.ValidLieTypeIndex) (_p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ (r = 2 ∨ q.p = 2)

theorem crossCharTwoFamAt_B_symplectic : CrossCharTwoFamAt .B regimeBSpTwo := by
  rintro ⟨d, hv⟩ _ p hp hp5 hc ⟨r, q, hd, hsp⟩ _
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  by_cases hr2 : r = 2
  · subst hr2
    have hrq : ¬ (2 = 2 ∧ q.p ^ q.exponent = 2) := by rw [← hcard]; exact hrange.2
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (isLocallyBalancedAbs_two_psp q.prime_p q.exponent_pos hK le_rfl hrq hp hp5 hpq)
  · have hq2 : q.p = 2 := hsp.resolve_left hr2
    have hr3 : 3 ≤ r := by have := hrange.1; omega
    have hrq : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := fun h => hr2 h.1
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      (isLocallyBalancedAbs_two_psp q.prime_p q.exponent_pos hK (by omega) hrq hp hp5 hpq)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
