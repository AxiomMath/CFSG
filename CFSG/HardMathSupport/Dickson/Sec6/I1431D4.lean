module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.Reduction
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4C3
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Normal

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamOK FamD4)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)

section Main


theorem exists_equiv_of_model {Y : Type} [Group Y] {ℓ f : ℕ}
    (hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 ℓ f) :
    ∃ (_ : Fact ℓ.Prime) (K : Type) (_ : Field K) (_ : Finite K),
      1 ≤ f ∧ Nat.card K = ℓ ^ f ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* adjointGroup Tag.D4 K) := by
  obtain ⟨⟨hℓ, hf, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  obtain ⟨e'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  exact ⟨⟨hℓ⟩, K, hKf, hKfin, hf, hK, ⟨e.trans e'⟩⟩

theorem IsD4Type.exists_equiv {Y : Type} [Group Y] (hD : IsD4Type Y) :
    ∃ (ℓ f : ℕ) (_ : Fact ℓ.Prime) (K : Type) (_ : Field K) (_ : Finite K),
      1 ≤ f ∧ Nat.card K = ℓ ^ f ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* adjointGroup Tag.D4 K) := by
  obtain ⟨ℓ, f, hm⟩ := hD
  obtain ⟨hℓ, K, hKf, hKfin, hf, hK, he⟩ := exists_equiv_of_model hm
  exact ⟨ℓ, f, hℓ, K, hKf, hKfin, hf, hK, he⟩

theorem ringChar_ne_three_of_card {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (h3 : ℓ ≠ 3) : ringChar K ≠ 3 := by
  intro h
  haveI : CharP K 3 := by
    have := ringChar.charP K
    rwa [h] at this
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have h1 : ℓ ∣ 3 ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self ℓ (by omega)
  exact h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow h1))

theorem Y1431Cfg.isInnerAut_of_d4 {V : InndiagVocab} {Y : Type}
    [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hD : IsD4Type Y) : IsInnerAut ξ := by
  obtain ⟨q0, hq0, hqq⟩ := cfg_cube CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds c
  obtain ⟨ℓ, f, hℓ, K, _, _, hf, hK, ⟨E⟩⟩ := hD.exists_equiv
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.finite_adjointD4 K
  have hP : FamOK (adjointGroup Tag.D4 K) := fun ψ hψ3 hninn =>
    ⟨1, ψ, by simp, CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.noL2Layer_adjointD4_outer
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      CFSG.HardMathSupport.Dickson.Sec6.I923.triD4A2NoL2_holds
      CFSG.HardMathSupport.Dickson.Sec6.I923.triD4C3NoL2_holds hf K hK ψ hψ3 hninn⟩
  have hinn := c.inner_of_famOK hq0 hqq E hP
  haveI : Group.IsPerfect Y := ⟨c.quasisimple.1⟩
  exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr E _).1 hinn)

theorem Y1431Cfg.false_of_d4 (hNo : D4NoCfg) {V : InndiagVocab} {Y : Type} [Group Y] [Finite Y]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hV : ∀ a ∈ Â, a ∈ innAutDerived Y) (hD : IsD4Type Y)
    (hξ : IsInnerAut ξ) : False := by
  obtain ⟨q0, hq0, hqq⟩ := cfg_cube CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds c
  obtain ⟨ℓ, f, hm⟩ := hD
  by_cases h3 : ℓ = 3
  · subst h3
    exact c.false_of_char3 hm hξ
  obtain ⟨hℓ, K, _, _, hf, hK, ⟨E⟩⟩ := exists_equiv_of_model hm
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.finite_adjointD4 K
  refine hNo K (ringChar_ne_three_of_card hℓ.out hf hK h3) (Â.map (descendHom E))
    (descendHom E ξ) (J.map (descendProj E)) q
    (c.descend E) ⟨q0, hq0, hqq⟩ (isInnerAut_congr_centerDescend E hξ) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_innAutDerived_congr E).2 (centerDescend_mem_innAutDerived (hV a ha))

theorem i1431D4Rest_of_noCfg (hNo : D4NoCfg) : I1431D4Rest := by
  intro Y _ _ Â ξ J q c hD e he
  exact (c.false_of_d4 hNo (fun a ha => c.inn a ha) hD (c.isInnerAut_of_d4 hD)).elim

theorem y1431_D4_of_noCfg (hNo : D4NoCfg) : Y1431_D4 := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨rfl, rfl⟩ := hF
  have hD : IsD4Type Y := ⟨p, f, (lieModel_classical_iff (by decide)).mp hm⟩
  have hξ : ξ ∈ innerAut Y := by
    have h := c.inn ξ c.mem
    simp only [d4Vocab, if_pos hD] at h
    exact h
  exact c.false_of_d4 hNo (fun a ha => c.mem_innAutDerived ha) hD hξ

theorem i1431D4Rest_of_rootSL2 (hR : D4RootSL2) : I1431D4Rest :=
  i1431D4Rest_of_noCfg (d4NoCfg_of_rootSL2 hR)

theorem y1431_D4_of_rootSL2 (hR : D4RootSL2) : Y1431_D4 :=
  y1431_D4_of_noCfg (d4NoCfg_of_rootSL2 hR)

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
