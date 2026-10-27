module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectL

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem nonempty_equiv_sl2_fund_g2 {e : ℕ}
    {R : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e))) :
    Nonempty (R ≃* SL(2, GaloisField p e)) := by
  open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
    CFSG.LieType.CurtisTits in
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hct := g2_isCTGroupDatum (GaloisField p e)
  have hroot : IsRoot .G2 γ := by
    have h : γ ∈ (g2Datum (GaloisField p e)).roots := by
      rcases hγ with h | ⟨-, h⟩ | ⟨h', -⟩
      · exact h.1
      · exact h
      · exact absurd h' (by decide)
    exact mem_adjDatum_roots.mp h
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hroot
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne hct w
  have hb : (Pi.single j 1 : Fin (Tag.rank .G2) → ℤ) ∈ (g2Datum (GaloisField p e)).roots :=
    mem_adjDatum_roots.mpr (isRoot_single .G2 j)
  have h2 : (g2Datum (GaloisField p e)).rootGroup (w • Pi.single j 1) ⊔
      (g2Datum (GaloisField p e)).rootGroup (-(w • Pi.single j 1)) =
      (rankOne (rootGroup (rootOperatorFamily .G2) (GaloisField p e)) j).map
        (MulAut.conj h).toMonoidHom := (hh _ hb).symm
  obtain ⟨φ⟩ := ModelFacts.g2_rankOne_equiv (K := GaloisField p e) j
  subst hw
  unfold conjSub
  rw [h2]
  exact ⟨((Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm).trans φ⟩

theorem exists_equiv_sl2_fund_d4 {n e : ℕ} (hadm : StatedLieAdmissible .trialityD4 n p e)
    {R : Subgroup (modelUniv .trialityD4 n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e Fact.out).D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      (Nat.card F = p ^ e ∨ Nat.card F = p ^ (3 * e)) ∧ Nonempty (R ≃* SL(2, F)) := by
  open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits in
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨i, g, rfl⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 n p e hadm hR
  suffices h : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      (Nat.card F = p ^ e ∨ Nat.card F = p ^ (3 * e)) ∧
      Nonempty (rankOne (modelUniv .trialityD4 n p e Fact.out).D.rootGroup i ≃* SL(2, F)) by
    obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := h
    exact ⟨F, hF, hFin, hcard,
      ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans φ⟩⟩
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e)
    (q := p ^ e) hK (fun c => iterateFrobenius_def p e c)
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = (ng 0 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h0
    subst hi'
    refine ⟨Models.TwistedPairs.fixedField (iterateFrobenius (GaloisField p (3 * e)) p e),
      inferInstance, inferInstance, Or.inl (ModelFacts.card_fixedField_iterateFrobenius he), ?_⟩
    show Nonempty (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
      (ng 0) ≃* _)
    rw [ModelFacts.rankOne_long_eq_range hσ]
    exact ⟨(MonoidHom.ofInjective (slLong_injective hσ)).symm⟩
  · have hi' : i = (ng 1 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h1
    subst hi'
    refine ⟨GaloisField p (3 * e), inferInstance, inferInstance,
      Or.inr (GaloisField.card p (3 * e) (by omega)), ?_⟩
    show Nonempty (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
      (ng 1) ≃* _)
    rw [ModelFacts.rankOne_short_eq_range hσ]
    exact ⟨(MonoidHom.ofInjective (slShort_injective hσ)).symm⟩

theorem exists_equiv_sl2_of_mem_g2d4 {f : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {t : StatedLieTag} {k e : ℕ} (M : Asc77.Ih8Model p f Ω t k e) (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .trialityD4) {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (L ≃* SL(2, F)) := by
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      (Nat.card F = p ^ e ∨ Nat.card F = p ^ (3 * e)) ∧ Nonempty (R ≃* SL(2, F)) := by
    rcases ht with rfl | rfl
    · obtain ⟨hk, -⟩ := M.admissible.2.2
      subst hk
      exact ⟨GaloisField p e, inferInstance, inferInstance,
        Or.inl (GaloisField.card p e (by have := M.admissible.2.1; omega)),
        nonempty_equiv_sl2_fund_g2 (M.cls_sub hR)⟩
    · exact exists_equiv_sl2_fund_d4 M.admissible (M.cls_sub hR)
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine ⟨F, hF, hFin, by rcases hcard with h | h <;> rw [h] <;> exact hpo.pow, ?_⟩
  have hinj := (M.bijective_of_g2d4 hp2 ht).1
  exact ⟨(Subgroup.equivMapOfInjective R M.ψ hinj).symm.trans φ⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
