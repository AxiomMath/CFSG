module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedSymplectic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms

theorem catalogueOver_of_spFactorOver {ℓ q : ℕ} {K : Type} [Field K] [Finite K] {X : Type}
    [Group X] (hX : SpFactorOver ℓ q K X) : ∃ j : ℕ, 1 ≤ j ∧ CatalogueOver ℓ (q ^ j) X := by
  haveI : Fintype K := Fintype.ofFinite K
  unfold SpFactorOver at hX
  rcases hX with ⟨m, j, E, hE, hEf, hm, hj, hch, hcard, h4, ⟨e⟩⟩
    | ⟨m, j, q', E, hE, hEf, hm, hj, hch, hq', hcard, hne, ⟨e⟩⟩
    | ⟨hq, hch, s, hs, hne, ⟨e⟩⟩
    | ⟨hq, hch, hK2, ⟨e⟩⟩
  · have h := CatalogueOver.of_mulEquiv (catalogueOver_sl E m hm h4) e.symm
    rw [hch, hcard] at h
    exact ⟨j, hj, h⟩
  · have h := CatalogueOver.of_mulEquiv (catalogueOver_su E m q' hcard hm hne) e.symm
    rw [hch, hq'] at h
    exact ⟨j, hj, h⟩
  · have hne' : (s, Fintype.card K) ≠ (2, 2) := by
      simpa only [Nat.card_eq_fintype_card] using hne
    have h := CatalogueOver.of_mulEquiv (catalogueOver_sp K s hs hne') e.symm
    have h' : CatalogueOver ℓ (Nat.card K) X := by
      rw [Nat.card_eq_fintype_card, ← hch]
      exact h
    refine ⟨1, le_rfl, ?_⟩
    rw [hq, pow_one]
    exact h'
  · have hK2' : Fintype.card K = 2 := by simpa only [Nat.card_eq_fintype_card] using hK2
    have hℓ2 : ringChar K = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hK2']; norm_num)
      exact ringChar.eq K 2
    have h := CatalogueOver.of_mulEquiv (catalogueOver_sp_four_two K hK2') e.symm
    refine ⟨1, le_rfl, ?_⟩
    rw [hq, hK2, pow_one, ← hch, hℓ2]
    exact h

theorem mem_inner_of_mem_innAutDerived_statedSp {p r ℓ f : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hne : ¬ (r = 2 ∧ ℓ ^ f = 2)) {β : MulAut (StatedProj (StatedSp r K))}
    (hβ : β ∈ innAutDerived (StatedProj (StatedSp r K))) (hβp : β ^ p = 1) :
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := by
  haveI : NeZero r := ⟨by omega⟩
  have hD : β ∈ spLinearAutGroup r K :=
    innAutDerived_statedSp_le_spLinearAutGroup (K := K) hr
      (fun hr2 => by
        have h2 : Nat.card K ≠ 2 := by
          rw [hK]
          exact fun h => hne ⟨hr2, h⟩
        have h1 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
        omega) hβ
  have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
    (SymplecticHigher.relIndex_inner_spLinearAutGroup_dvd (r := r) hℓ hf hK).trans
      (Nat.gcd_dvd_left 2 _)
  exact CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hβp

theorem compIdxAt_statedProj {p r ℓ f : ℕ} {K : Type} [Field K] [Finite K]
    {d : TauCeti.LieTypeIndex} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ ℓ ^ f = 2))
    (hpℓ : p ≠ ℓ) (hchar : d.characteristic = ℓ) (hfs : fieldSize d = ℓ ^ f) :
    CompIdxAt p d (StatedProj (StatedSp r K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero r := ⟨by omega⟩
  intro β hβmem hβp hβ1 K' hK'
  have hinn : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K)) :=
    mem_inner_of_mem_innAutDerived_statedSp hp hp2 hℓ hf hK hr hne hβmem hβp
  obtain ⟨t, ht⟩ := hinn
  have ht_p : t ^ p = 1 := by
    obtain ⟨hsimple, hperf⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr (by rwa [hK])
    haveI := hsimple
    have hnc : ∃ u v : StatedProj (StatedSp r K), u * v ≠ v * u := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative _
        ⟨⟨fun u v => h u v⟩⟩
    exact CFSG.mulAutConj_injective_of_center_eq_bot (b3Lie_center_eq_bot hnc)
      (by rw [map_pow, ht, hβp, map_one])
  obtain ⟨x, hx, hxp⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (r := r) (K := K)
    (by omega) hp hp2 ht_p
  have hβeq : β = MulAut.conj (SymplecticFlag.proj r K x) := by rw [← ht, ← hx]
  have hK'' : IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) := by
    rw [← hβeq]
    exact hK'
  obtain ⟨X, inst, hfin, ⟨hX, -⟩, hfac, g, hg, hk⟩ :=
    (lieCompsCore_conj_sp_card (a6 := False) slFactorFacts_holds suFactorFacts_holds
      spFactorFacts_holds spFourTwoFacts_holds False.elim False.elim False.elim
      hp hp2 hℓ hf hK (by omega) hpℓ False.elim x hxp).2 K' hK''
  obtain ⟨j, hj, hcat⟩ := catalogueOver_of_spFactorOver (q := Nat.card K) hfac
  have hcatK' : CatalogueOver ℓ (fieldSize d ^ j) ↥K' := by
    have h := hcat.of_surjective hX.perfect g hg hk
    rw [hK] at h
    rwa [hfs]
  obtain ⟨i, ⟨φ⟩, hidx⟩ := hcatK'
  rw [← hchar] at hidx
  exact ⟨i, ⟨φ⟩, compRelC_of_idxOver (d := d) (i := i) (j := j) hj hidx⟩

@[expose] def isSymplecticIdx : TauCeti.LieTypeIndex → Prop
  | .B r q => r = 2 ∨ q.p = 2
  | .C _ _ => True
  | _ => False

theorem exists_mulEquiv_statedProj_of_isSymplecticIdx {d : TauCeti.ValidLieTypeIndex}
    (hd : isSymplecticIdx d.1) :
    ∃ r, 2 ≤ r ∧ ¬ (r = 2 ∧ fieldSize d.1 = 2) ∧ Nat.card d.fixedField = fieldSize d.1 ∧
      Nonempty (StatedProj (StatedSp r d.fixedField) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨idx, hv⟩ := d
  simp only [isSymplecticIdx] at hd
  cases idx with
  | B r q =>
      by_cases hr2 : r = 2
      · subst hr2
        let dd : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
        let K := ↥dd.fixedField
        haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField dd
        have hK : Nat.card K = dd.characteristic ^ dd.fieldExponent := by
          rw [TauCeti.ValidLieTypeIndex.card_fixedField,
            TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
        have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hq2 : q.card ≠ 2 := fun h => hstd.2 ⟨rfl, h⟩
        have hfs : fieldSize (TauCeti.LieTypeIndex.B 2 q) =
            (TauCeti.LieTypeIndex.B 2 q).characteristic ^
              (TauCeti.LieTypeIndex.B 2 q).fieldExponent := by
          rw [TauCeti.LieTypeIndex.characteristic_B, TauCeti.LieTypeIndex.fieldExponent_B]
          show q.card = q.p ^ q.exponent
          exact TauCeti.PrimePower.card_def q
        have hqcard : q.card = dd.characteristic ^ dd.fieldExponent := hfs
        have hcard : Nat.card K = fieldSize (TauCeti.LieTypeIndex.B 2 q) := hK.trans hfs.symm
        refine ⟨2, le_rfl, ?_, hcard, ?_⟩
        · rintro ⟨-, h2⟩
          rw [hfs] at h2
          exact hq2 (hqcard.trans h2)
        · obtain ⟨e⟩ :=
            CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj hv
              (k := K) (by
                rw [hK, TauCeti.ValidLieTypeIndex.characteristic,
                  TauCeti.ValidLieTypeIndex.fieldExponent,
                  TauCeti.LieTypeIndex.characteristic_B,
                  TauCeti.LieTypeIndex.fieldExponent_B]
                exact (TauCeti.PrimePower.card_def q).symm)
          exact ⟨e⟩
      · have hq2 : q.p = 2 := by
          rcases hd with h | h
          · omega
          · exact h
        have hr3 : 3 ≤ r := by
          have := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
          omega
        let dd : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.B r q, hv⟩
        let K := ↥dd.fixedField
        haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField dd
        have hK : Nat.card K = dd.characteristic ^ dd.fieldExponent := by
          rw [TauCeti.ValidLieTypeIndex.card_fixedField,
            TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
        have hfs : fieldSize (TauCeti.LieTypeIndex.B r q) =
            (TauCeti.LieTypeIndex.B r q).characteristic ^
              (TauCeti.LieTypeIndex.B r q).fieldExponent := by
          rw [TauCeti.LieTypeIndex.characteristic_B, TauCeti.LieTypeIndex.fieldExponent_B]
          show q.card = q.p ^ q.exponent
          exact TauCeti.PrimePower.card_def q
        have hcard : Nat.card K = fieldSize (TauCeti.LieTypeIndex.B r q) := hK.trans hfs.symm
        refine ⟨r, by omega, ?_, hcard, ?_⟩
        · rintro ⟨h1, -⟩
          omega
        · obtain ⟨e⟩ :=
            CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj hv hq2 hr3
              (k := K) (by
                rw [hK, TauCeti.ValidLieTypeIndex.characteristic,
                  TauCeti.ValidLieTypeIndex.fieldExponent,
                  TauCeti.LieTypeIndex.characteristic_B,
                  TauCeti.LieTypeIndex.fieldExponent_B]
                exact (TauCeti.PrimePower.card_def q).symm)
          exact ⟨e⟩
  | C r q =>
      let dd : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.C r q, hv⟩
      let K := ↥dd.fixedField
      haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField dd
      have hK : Nat.card K = dd.characteristic ^ dd.fieldExponent := by
        rw [TauCeti.ValidLieTypeIndex.card_fixedField,
          TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
      have hr3 : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      have hfs : fieldSize (TauCeti.LieTypeIndex.C r q) =
          (TauCeti.LieTypeIndex.C r q).characteristic ^
            (TauCeti.LieTypeIndex.C r q).fieldExponent := by
        rw [TauCeti.LieTypeIndex.characteristic_C, TauCeti.LieTypeIndex.fieldExponent_C]
        show q.card = q.p ^ q.exponent
        exact TauCeti.PrimePower.card_def q
      have hcard : Nat.card K = fieldSize (TauCeti.LieTypeIndex.C r q) := hK.trans hfs.symm
      refine ⟨r, by omega, ?_, hcard, ?_⟩
      · rintro ⟨h1, -⟩
        omega
      · obtain ⟨e⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj hv
            (k := K) (by
              rw [hK, TauCeti.ValidLieTypeIndex.characteristic,
                TauCeti.ValidLieTypeIndex.fieldExponent,
                TauCeti.LieTypeIndex.characteristic_C,
                TauCeti.LieTypeIndex.fieldExponent_C]
              exact (TauCeti.PrimePower.card_def q).symm)
        exact ⟨e⟩
  | _ => exact absurd hd (by simp [isSymplecticIdx])

theorem compIdxAt_psp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : isSymplecticIdx d.1) (hpc : p ≠ d.1.characteristic) :
    CompIdxAt p d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨r, hr, hne, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hℓ : d.characteristic.Prime := d.characteristic_prime
  have hf : 1 ≤ d.fieldExponent := d.fieldExponent_pos
  have hK : Nat.card ↥d.fixedField = d.characteristic ^ d.fieldExponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have hfs : fieldSize d.1 = d.characteristic ^ d.fieldExponent := hcard.symm.trans hK
  have hne' : ¬ (r = 2 ∧ d.characteristic ^ d.fieldExponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [hfs]; exact h2⟩
  have hmodel := compIdxAt_statedProj (p := p) (r := r) (ℓ := d.characteristic)
    (f := d.fieldExponent) (K := ↥d.fixedField) (d := d.1) hp hp2 hℓ hf hK hr hne'
    hpc rfl hfs
  exact compIdxAt_of_mulEquiv e hmodel

@[expose] def SymplecticCompAlgEight : Prop :=
  ∀ (r : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ r → ¬(r = 2 ∧ Nat.card K = 2) →
    Nat.card K = 8 → CompAlgAt (StatedProj (StatedSp r K))

theorem compAlgAt_psp (h : SymplecticCompAlgEight) {d : TauCeti.ValidLieTypeIndex}
    (hd : isSymplecticIdx d.1) (hfield : fieldSize d.1 = 8) :
    CompAlgAt (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨r, hr, hne, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hK8 : Nat.card ↥d.fixedField = 8 := hcard.trans hfield
  have hne' : ¬ (r = 2 ∧ Nat.card ↥d.fixedField = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [← hcard]; exact h2⟩
  exact compAlgAt_of_mulEquiv e (h r ↥d.fixedField hr hne' hK8)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
