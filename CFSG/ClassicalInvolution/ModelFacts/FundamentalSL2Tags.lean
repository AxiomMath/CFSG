module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectExc
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal
open scoped MatrixGroups

section Partner

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundamentalSL2_PSL (hadm : StatedLieAdmissible .PSL n p e) (hn : 3 ≤ n) :
    FundamentalSL2 p .PSL n e :=
  fundamentalSL2_of_partner .PSL n p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_PSL n p e hadm hn hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_POmegaPlus (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    FundamentalSL2 p .POmegaPlus n e :=
  fundamentalSL2_of_partner .POmegaPlus n p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaPlus p e n hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_POmegaOdd (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    FundamentalSL2 p .POmegaOdd n e :=
  fundamentalSL2_of_partner .POmegaOdd n p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaOdd p e n hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_POmegaMinus (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : FundamentalSL2 p .POmegaMinus n e :=
  fundamentalSL2_of_partner .POmegaMinus n p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaMinus n p e hp2 hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_E6 (hadm : StatedLieAdmissible .E6 0 p e) : FundamentalSL2 p .E6 0 e :=
  fundamentalSL2_of_partner .E6 0 p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E6 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_E7 (hadm : StatedLieAdmissible .E7 0 p e) : FundamentalSL2 p .E7 0 e :=
  fundamentalSL2_of_partner .E7 0 p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E7 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_E8 (hadm : StatedLieAdmissible .E8 0 p e) : FundamentalSL2 p .E8 0 e :=
  fundamentalSL2_of_partner .E8 0 p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E8 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundamentalSL2_F4 (hadm : StatedLieAdmissible .F4 0 p e) : FundamentalSL2 p .F4 0 e :=
  fundamentalSL2_of_partner .F4 0 p e fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_F4 p e hadm hγ
    exact ⟨δ, W, hW⟩

end Partner

section Classical

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundamentalSL2_PSL_two (hadm : StatedLieAdmissible .PSL 2 p e) :
    FundamentalSL2 p .PSL 2 e := by
  intro g γ hγ
  have hR := fundamentalSubgroups_eq_top_PSL_two p e hp.out hadm _ ⟨g, γ, Or.inl hγ, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hR).trans Subgroup.topEquiv⟩

theorem fundamentalSL2_PSp (hadm : StatedLieAdmissible .PSp n p e) : FundamentalSL2 p .PSp n e := by
  have hn : 2 ≤ n := hadm.2.2.1
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : IsLongestRoot (modelUniv .PSp n p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .PSp n p e hp.out trivial hadm k (show (n - 1) + 1 = n by omega)
  refine fundamentalSL2_of_longest_root .PSp n p e trivial hadm (γ₀ := Pi.single k 1) hk ?_
  have h := Models.SymplecticPairs.range_longBlock_eq_rankOne (K := GaloisField p e) (n := n)
    (k := k) (show ¬ k.val + 1 < n by show ¬ n - 1 + 1 < n; omega)
  have h' : (modelUniv .PSp n p e hp.out).D.rootGroup (Pi.single k 1) ⊔
      (modelUniv .PSp n p e hp.out).D.rootGroup (-Pi.single k 1) =
        (Models.SymplecticPairs.longBlock (GaloisField p e) n k).range := h.symm
  have hSL : Nonempty ((Models.SymplecticPairs.longBlock (GaloisField p e) n k).range ≃*
      SL(2, GaloisField p e)) :=
    ⟨(MonoidHom.ofInjective (Models.SymplecticPairs.longBlock_injective k)).symm⟩
  rw [← h'] at hSL
  exact hSL

theorem fundamentalSL2_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    FundamentalSL2 p .twistedE6 0 e := by
  have hf : 1 ≤ e := hadm.2.1
  let k : Fin (modelUniv .twistedE6 0 p e hp.out).D.rank :=
    CFSG.LieType.Steinberg.TwistedE6.nf 0
  have hk : IsLongestRoot (modelUniv .twistedE6 0 p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .twistedE6 0 p e hp.out trivial hadm k (by show 0 < 2; decide)
  refine fundamentalSL2_of_longest_root .twistedE6 0 p e trivial hadm (γ₀ := Pi.single k 1) hk ?_
  obtain ⟨W, hW⟩ := linearBlockStandardPair_twistedE6_long
    (CFSG.LieType.Steinberg.Exceptional.frobQ p e)
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨eF⟩ := nonempty_ringEquiv_fixedField_frobQ p e hf hF
  obtain ⟨⟨eU⟩, -⟩ := linearBlockStandardPair_equiv
    (LinearBlockStandardPair.of_ringEquiv eF.symm hW)
  exact ⟨eU⟩

end Classical

section Unitary

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem nonempty_ringEquiv_of_natCard_eq {F F' : Type} [Field F] [Field F'] [Finite F]
    [Finite F'] (h : Nat.card F = Nat.card F') : Nonempty (F ≃+* F') := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite F'
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h])⟩

theorem fundamentalSL2_PSU (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p e) :
    FundamentalSL2 p .PSU n e := by
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv hp2 hadm
  intro g γ hγ
  obtain ⟨i, hi⟩ := (hφ _).mp ⟨g, γ, Or.inl hγ, rfl⟩
  obtain ⟨eL⟩ := (hi.isClassicalSL2 hK hp2).nonempty_mulEquiv
  obtain ⟨eF⟩ := nonempty_ringEquiv_of_natCard_eq (F := CFSG.LieType.Steinberg.fixedSubfield
    (GaloisField p (2 * e)) p e) (F' := GaloisField p e) (by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hK, GaloisField.card p e (by omega)])
  exact ⟨(Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (eL.trans (slMapEquiv eF))⟩

end Unitary

section G2

open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType

theorem g2_rankOne_equiv {K : Type} [Field K] (l : Fin (Tag.rank .G2)) :
    Nonempty (rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l ≃* SL(2, K)) := by
  obtain ⟨φ, hinj, hup, hlow⟩ := Adjoint.g2_exists_sl2_hom (K := K) l
  have hup' : ∀ c, φ (sl2Upper c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (Pi.single l 1) c := fun c => by
    rw [hup, Adjoint.xPar_simple]
  have hlow' : ∀ c, φ (sl2Lower c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (-Pi.single l 1) c := fun c => by
    rw [hlow, Adjoint.xPar_neg_simple]
  have hle : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Upper c, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_neg_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Lower c, hlow c⟩
  have heq : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l = φ.range :=
    rankOne_eq_range_of_sl2 (D := Adjoint.g2Datum K) (i := l) φ
      (fun c => by rw [hup']; exact Adjoint.xPar_mem (isRoot_single .G2 l) c)
      (fun c => by rw [hlow']; exact Adjoint.xPar_mem (isRoot_neg_single .G2 l) c) hle
  rw [heq]
  exact ⟨(MonoidHom.ofInjective hinj).symm⟩

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundamentalSL2_G2 (hadm : StatedLieAdmissible .G2 n p e) : FundamentalSL2 p .G2 n e := by
  let l : Fin (Tag.rank .G2) := ⟨0, by decide⟩
  have hk : IsLongestRoot (modelUniv .G2 n p e hp.out).D (Pi.single l 1) :=
    isLongestRoot_single .G2 n p e hp.out trivial hadm l rfl
  refine fundamentalSL2_of_longest_root .G2 n p e trivial hadm (γ₀ := Pi.single l 1) hk ?_
  obtain ⟨φ⟩ := g2_rankOne_equiv (K := GaloisField p e) l
  exact ⟨φ⟩

end G2

section D4

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits

theorem card_fixedField_iterateFrobenius {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
      (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e := by
  refine le_antisymm ?_ (le_card_fixedField_iterateFrobenius he)
  classical
  have := Fintype.ofFinite (GaloisField p (3 * e))
  set σ := iterateFrobenius (GaloisField p (3 * e)) p e with hσ
  let Z : Finset (GaloisField p (3 * e)) :=
    Finset.univ.filter fun x => x ∈ CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ
  have hq : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hne := FiniteField.X_pow_card_sub_X_ne_zero (GaloisField p (3 * e)) hq
  have hZ : Z.val ⊆ (Polynomial.X ^ (p ^ e) - Polynomial.X :
      Polynomial (GaloisField p (3 * e))).roots := by
    intro x hx
    have hx' : x ∈ CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ :=
      (Finset.mem_filter.mp hx).2
    have hxσ : σ x = x := hx'
    rw [hσ, iterateFrobenius_def] at hxσ
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hxσ]
  have h := Polynomial.card_le_degree_of_subset_roots hZ
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq] at h
  have hc : Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ) = Z.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  exact h

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundamentalSL2_trialityD4 (hadm : StatedLieAdmissible .trialityD4 n p e) :
    FundamentalSL2 p .trialityD4 n e := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  let k : Fin (modelUniv .trialityD4 n p e hp.out).D.rank := ng 0
  have hk : IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .trialityD4 n p e hp.out trivial hadm k rfl
  refine fundamentalSL2_of_longest_root .trialityD4 n p e trivial hadm (γ₀ := Pi.single k 1) hk ?_
  have h := rankOne_long_eq_range hσ
  have h' : (modelUniv .trialityD4 n p e hp.out).D.rootGroup (Pi.single k 1) ⊔
      (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-Pi.single k 1) =
        (slLong (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range := h
  obtain ⟨eF⟩ := nonempty_ringEquiv_of_natCard_eq
    (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
      (iterateFrobenius (GaloisField p (3 * e)) p e)) (F' := GaloisField p e) (by
      rw [card_fixedField_iterateFrobenius he, GaloisField.card p e (by omega)])
  have hSL : Nonempty ((slLong (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range ≃*
      SL(2, GaloisField p e)) :=
    ⟨((MonoidHom.ofInjective (slLong_injective hσ)).symm).trans (slMapEquiv eF)⟩
  rw [← h'] at hSL
  exact hSL

end D4

end CFSG.ClassicalInvolution.ModelFacts
