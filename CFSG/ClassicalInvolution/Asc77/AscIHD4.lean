module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Tags
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem
open scoped MatrixGroups

@[expose] def D4OrdersDiffer (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), t = .trialityD4 → StatedLieAdmissible t n p e →
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∀ S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      (¬ ∃ g, S = R.map (MulAut.conj g).toMonoidHom) → Nat.card R ≠ Nat.card S

theorem exists_conj_rankOne_node_of_trialityD4 (n p e : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible .trialityD4 n p e)
    {R : Subgroup (modelUniv .trialityD4 n p e hp.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D) :
    ∃ (i : Fin (modelUniv .trialityD4 n p e hp.out).D.rank)
      (g : (modelUniv .trialityD4 n p e hp.out).K),
      R = (rankOne (modelUniv .trialityD4 n p e hp.out).D.rootGroup i).map
        (MulAut.conj g).toMonoidHom := by
  have hfund : ModelFacts.IsFundTag .trialityD4 := trivial
  obtain ⟨_, _, hct, -⟩ := ModelFacts.hasBruhatDatum .trialityD4 n p e hp.out hfund hadm
  obtain ⟨g, γ, hγ, hRγ⟩ : ∃ (g : (modelUniv .trialityD4 n p e hp.out).K)
      (γ : Fin (modelUniv .trialityD4 n p e hp.out).D.rank → ℤ),
      γ ∈ (modelUniv .trialityD4 n p e hp.out).D.roots ∧
        R = ((modelUniv .trialityD4 n p e hp.out).D.rootGroup γ ⊔
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-γ)).map
            (MulAut.conj g).toMonoidHom :=
    ModelFacts.mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨w, i, rfl⟩ : ∃ (w : (coxeterMatrix
        (modelUniv .trialityD4 n p e hp.out).D.isFiniteType).Group)
      (i : Fin (modelUniv .trialityD4 n p e hp.out).D.rank),
      γ = weylAction (modelUniv .trialityD4 n p e hp.out).D.isFiniteType w (Pi.single i 1) := by
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · exact ⟨w, i, rfl⟩
    · exact absurd hi (Set.notMem_empty i)
  obtain ⟨g', hg'⟩ : ∃ g' : (modelUniv .trialityD4 n p e hp.out).K,
      ∀ γ ∈ (modelUniv .trialityD4 n p e hp.out).D.roots,
        ((modelUniv .trialityD4 n p e hp.out).D.rootGroup γ ⊔
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-γ)).map
            (MulAut.conj g').toMonoidHom =
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (weylAction
            (modelUniv .trialityD4 n p e hp.out).D.isFiniteType w γ) ⊔
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-weylAction
            (modelUniv .trialityD4 n p e hp.out).D.isFiniteType w γ) :=
    ModelFacts.exists_map_conj_rankOne hct w
  have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
  refine ⟨i, g * g', ?_⟩
  rw [hRγ, ← h1, CFSG.LieType.CurtisTits.rankOne, Subgroup.map_map]
  congr 1

private theorem natCard_map_conj {X : Type*} [Group X] (L : Subgroup X) (g : X) :
    Nat.card (L.map (MulAut.conj g).toMonoidHom) = Nat.card L :=
  (Nat.card_congr (L.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

private theorem map_conj_map_conj' {X : Type*} [Group X] (L : Subgroup X) (g h : X) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      L.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem sl2_card_lt (q : ℕ) (hq : 2 ≤ q) : q * (q ^ 2 - 1) < q ^ 3 * ((q ^ 3) ^ 2 - 1) := by
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have hq3 : q ^ 3 = q ^ 2 * q := by ring
  have h2 : q ≤ q ^ 3 := by nlinarith
  have h3 : q ^ 2 < (q ^ 3) ^ 2 := Nat.pow_lt_pow_left (by nlinarith) (by norm_num)
  have h4 : q ^ 2 - 1 < (q ^ 3) ^ 2 - 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  calc q * (q ^ 2 - 1) < q ^ 3 * (q ^ 2 - 1) + q ^ 3 := by nlinarith [Nat.zero_le (q ^ 2 - 1)]
    _ ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := by
      have h5 : q ^ 2 - 1 + 1 ≤ (q ^ 3) ^ 2 - 1 := h4
      nlinarith [Nat.zero_le (q ^ 2 - 1)]

section Cards

variable (n p e : ℕ) [hp : Fact p.Prime]

private theorem card_galoisField_three_mul (he : 1 ≤ e) :
    Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
  rw [GaloisField.card p (3 * e) (by omega), pow_mul']

theorem natCard_rankOne_long (hadm : StatedLieAdmissible .trialityD4 n p e) :
    Nat.card (rankOne (modelUniv .trialityD4 n p e hp.out).D.rootGroup
      (ng 0 : Fin (modelUniv .trialityD4 n p e hp.out).D.rank)) =
      p ^ e * ((p ^ e) ^ 2 - 1) := by
  have he : 1 ≤ e := hadm.2.1
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    (card_galoisField_three_mul p e he) (fun c => iterateFrobenius_def p e c)
  show Nat.card (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    (ng 0)) = _
  rw [ModelFacts.rankOne_long_eq_range hσ,
    ← Nat.card_congr (MonoidHom.ofInjective (slLong_injective hσ)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    show Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e from
      ModelFacts.card_fixedField_iterateFrobenius he]

theorem natCard_rankOne_short (hadm : StatedLieAdmissible .trialityD4 n p e) :
    Nat.card (rankOne (modelUniv .trialityD4 n p e hp.out).D.rootGroup
      (ng 1 : Fin (modelUniv .trialityD4 n p e hp.out).D.rank)) =
      (p ^ e) ^ 3 * (((p ^ e) ^ 3) ^ 2 - 1) := by
  have he : 1 ≤ e := hadm.2.1
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    (card_galoisField_three_mul p e he) (fun c => iterateFrobenius_def p e c)
  show Nat.card (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    (ng 1)) = _
  rw [ModelFacts.rankOne_short_eq_range hσ,
    ← Nat.card_congr (MonoidHom.ofInjective (slShort_injective hσ)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    card_galoisField_three_mul p e he]

end Cards

theorem d4OrdersDiffer (p : ℕ) [Fact p.Prime] : D4OrdersDiffer p := by
  intro t n e ht hadm R hR S hS hnc
  subst ht
  obtain ⟨i, g, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 n p e hadm hR
  obtain ⟨j, h, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 n p e hadm hS
  intro hcard
  rw [natCard_map_conj, natCard_map_conj] at hcard
  by_cases hij : i = j
  · subst hij
    apply hnc
    refine ⟨h * g⁻¹, ?_⟩
    rw [map_conj_map_conj', inv_mul_cancel_right]
  · have hq : 2 ≤ p ^ e := by
      have he : 1 ≤ e := hadm.2.1
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
        _ ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hlt := sl2_card_lt (p ^ e) hq
    have hi : (i : ℕ) < 2 := i.2
    have hj : (j : ℕ) < 2 := j.2
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases (by omega : (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 0) with
      ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hi' : i = (ng 0 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h0
      have hj' : j = (ng 1 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h1
      subst hi' hj'
      rw [natCard_rankOne_long n p e hadm, natCard_rankOne_short n p e hadm] at hcard
      omega
    · have hi' : i = (ng 1 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h1
      have hj' : j = (ng 0 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h0
      subst hi' hj'
      rw [natCard_rankOne_long n p e hadm, natCard_rankOne_short n p e hadm] at hcard
      omega

end CFSG.ClassicalInvolution.Asc77
