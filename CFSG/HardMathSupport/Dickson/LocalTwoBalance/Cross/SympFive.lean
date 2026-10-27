module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.SympFiveAux.Exc
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)

theorem isLocallyBalancedAbs_two_psp_five_aux {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    (hpℓ : 5 ≠ ℓ) (hex : ¬ (r = 2 ∧ ℓ ^ f = 32)) :
    IsLocallyBalancedAbs 5 2 (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective hℓ hf hK hr hrq
  have O := CFSG.RankThree.PartOne.KCSpComm.spOuter hℓ hf hr hK
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : NeZero r := ⟨by omega⟩
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_ ?_
  · intro E hEin hE hEc H hH
    exact localDeltaIn_eq_bot_psp hℓ hf hK hp (by norm_num) hpℓ hr hrq E hEin hE hEc hH
  · intro D hD hDc hDin
    have hEel : CFSG.IsElementaryAbelian 5 D :=
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
      have hcap' : Nat.card ↥(D ⊓ innerAut (StatedProj (StatedSp r K))) = 5 := hcap
      rw [hbot, Subgroup.card_bot] at hcap'
      exact hp.one_lt.ne hcap'
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    obtain ⟨-, σ, hσ, h, -, hxh⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.noninner_element_data O hp hp2 (A := D) hxD hxin
    have hcomm : y * x = x * y := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨y, hyD.1⟩ ⟨x, hxD⟩)
    have hyp : y ^ 5 = 1 := hD.2 y hyD.1
    have hfull := CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      (K := K) hℓ hp (by norm_num) hpℓ hf hr hK σ hσ
    obtain ⟨-, -, hTs, -, -, hJfix, -, hJs, -, hfixing, hzp, hzcard, -, hexc⟩ := hfull
    have hδp : orderOf (fieldAut r K σ) = 5 := by
      rw [← Nat.card_zpowers, hzcard]
    obtain ⟨k, hkδ, hkord⟩ :=
      exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyD.2 hy1 hyp hcomm
    have hnexc : ¬ (r = 2 ∧ ℓ ^ (f / 5) = 2) := by
      rintro hex2
      obtain ⟨-, -, -, h32⟩ := hexc hex2 ⟨k, (hJfix k).2 hkδ, hkord⟩
      exact hex ⟨hex2.1, h32⟩
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

theorem isLocallyBalancedAbs_two_psp_five {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    (hpℓ : 5 ≠ ℓ) (hex : ¬ (r = 2 ∧ ℓ ^ (f / 5) = 2)) :
    IsLocallyBalancedAbs 5 2 (StatedProj (StatedSp r K)) := by
  refine isLocallyBalancedAbs_two_psp_five_aux hℓ hf hK hr hrq hpℓ ?_
  rintro ⟨hr2, h32⟩
  apply hex
  refine ⟨hr2, ?_⟩
  have hℓ2 : ℓ = 2 := by
    have hdvd : ℓ ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← h32]
      exact dvd_pow_self ℓ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow hdvd)
  subst hℓ2
  have hf5 : f = 5 := by
    have h2 : (2 : ℕ) ^ f = 2 ^ 5 := by rw [h32]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hf5
  norm_num

theorem localTwoCrossFamCat_five_C : LocalTwoCrossFamCat 5 .C := by
  rintro ⟨d, hv⟩ ⟨r, q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := hrange.1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hodd : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := fun h => absurd h.1 (by omega)
  have hex : ¬ (r = 2 ∧ q.p ^ (q.exponent / 5) = 2) := fun h => absurd h.1 (by omega)
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
    (isLocallyBalancedAbs_two_psp_five q.prime_p q.exponent_pos hK (by omega) hodd hpq hex)

theorem localTwoCrossFamAt_B_two_exc (p : ℕ) (hp : p = 3 ∨ p = 5) :
    LocalTwoCrossFamAt p .B fun idx =>
      ∃ q : TauCeti.PrimePower, idx.1 = .B 2 q ∧ ((p = 3 ∧ q.card = 8) ∨ (p = 5 ∧ q.card = 32)) := by
  rintro ⟨d, hv⟩ _ ⟨q, hd, hq⟩ _ _
  change d = _ at hd
  subst hd
  have hcard : q.card = 2 ^ p := by
    rcases hq with ⟨hp3, h8⟩ | ⟨hp5, h32⟩
    · subst hp3
      rw [h8]
      norm_num
    · subst hp5
      rw [h32]
      norm_num
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 2 ^ p := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    have hq : TauCeti.ValidLieTypeIndex.fieldOrder (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) =
        q.p ^ q.exponent := by
      simp [TauCeti.ValidLieTypeIndex.fieldOrder]
    rw [hq, ← TauCeti.PrimePower.card_def]
    exact hcard
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
    (isLocallyBalancedAbs_two_sp_two_exc hp hK)

theorem localTwoCrossFamAt_five_B_symplectic :
    LocalTwoCrossFamAt 5 .B fun idx => regimeBSpTwo idx 5 := by
  rintro ⟨d, hv⟩ hk ⟨r, q, hd, hsp⟩ hc hnexc
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
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  by_cases hr2 : r = 2
  · subst hr2
    by_cases h32 : q.card = 32
    · exact localTwoCrossFamAt_B_two_exc 5 (Or.inr rfl) (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)
        hk ⟨q, rfl, Or.inr ⟨rfl, h32⟩⟩ hc hnexc
    · have hrq : ¬ (2 = 2 ∧ q.p ^ q.exponent = 2) := by
        rw [← hcard]
        exact hrange.2
      have hex : ¬ (2 = 2 ∧ q.p ^ q.exponent = 32) := by
        rw [← hcard]
        exact fun h => h32 h.2
      exact IsLocallyBalancedAbs.of_mulEquiv
        (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
        (isLocallyBalancedAbs_two_psp_five_aux q.prime_p q.exponent_pos hK le_rfl hrq hpq hex)
  · have hq2 : q.p = 2 := hsp.resolve_left hr2
    have hr3 : 3 ≤ r := by
      have := hrange.1
      omega
    have hrq : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := fun h => hr2 h.1
    have hex : ¬ (r = 2 ∧ q.p ^ q.exponent = 32) := fun h => hr2 h.1
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      (isLocallyBalancedAbs_two_psp_five_aux q.prime_p q.exponent_pos hK (by omega) hrq hpq hex)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
