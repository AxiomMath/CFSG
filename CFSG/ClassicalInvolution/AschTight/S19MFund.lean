module

public import CFSG.ClassicalInvolution.AschTight.S1911P3d
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem exists_isUniqueInvolution_of_equiv_sl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {G : Type} [Group G] {R : Subgroup G} (e : R ≃* SL(2, F)) :
    ∃ c, IsUniqueInvolution R c := by
  have hinj : Function.Injective (R.subtype.comp e.symm.toMonoidHom) :=
    R.subtype_injective.comp e.symm.injective
  have hrange : (R.subtype.comp e.symm.toMonoidHom).range = R := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (e.symm s).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  have h := G2D4Models.isUniqueInvolution_range_sl2 hodd hinj
  rw [hrange] at h
  exact ⟨_, h⟩

theorem odd_natCard_galoisField (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    Odd (Nat.card (GaloisField p e)) := by
  rw [GaloisField.card p e (by omega)]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow

theorem exists_isUniqueInvolution_fund_g2 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e))) :
    ∃ c, IsUniqueInvolution R c := by
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
  obtain ⟨c, hc⟩ := exists_isUniqueInvolution_of_equiv_sl2 (odd_natCard_galoisField hp2 he) φ
  refine ⟨g * (h * c * h⁻¹) * g⁻¹, ?_⟩
  subst hw
  have hc' := (hc.conj h).conj g
  unfold conjSub at hc' ⊢
  rw [h2]
  exact hc'

theorem exists_isUniqueInvolution_fund_d4 (hp2 : p ≠ 2) {n e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n p e)
    {R : Subgroup (modelUniv .trialityD4 n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e Fact.out).D) :
    ∃ c, IsUniqueInvolution R c := by
  open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits in
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨i, g, rfl⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 n p e hadm hR
  suffices h : ∃ c, IsUniqueInvolution
      (rankOne (modelUniv .trialityD4 n p e Fact.out).D.rootGroup i) c by
    obtain ⟨c, hc⟩ := h
    exact ⟨g * c * g⁻¹, hc.conj g⟩
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e)
    (q := p ^ e) hK (fun c => iterateFrobenius_def p e c)
  have hodd : Odd (p ^ e) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = (ng 0 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h0
    subst hi'
    have hodd1 : Odd (Nat.card (Models.TwistedPairs.fixedField
        (iterateFrobenius (GaloisField p (3 * e)) p e))) := by
      rw [ModelFacts.card_fixedField_iterateFrobenius he]
      exact hodd
    show ∃ c, IsUniqueInvolution
      (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) (ng 0)) c
    rw [ModelFacts.rankOne_long_eq_range hσ]
    exact ⟨_, G2D4Models.isUniqueInvolution_range_sl2 hodd1 (slLong_injective hσ)⟩
  · have hi' : i = (ng 1 : Fin (modelUniv .trialityD4 n p e Fact.out).D.rank) := Fin.ext h1
    subst hi'
    have hodd3 : Odd (Nat.card (GaloisField p (3 * e))) := by
      rw [hK]
      exact hodd.pow
    show ∃ c, IsUniqueInvolution
      (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) (ng 1)) c
    rw [ModelFacts.rankOne_short_eq_range hσ]
    exact ⟨_, G2D4Models.isUniqueInvolution_range_sl2 hodd3 (slShort_injective hσ)⟩

theorem exists_isUniqueInvolution_fund_classical (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    ∃ c, IsUniqueInvolution R c := by
  obtain ⟨φ⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2
    hD4 hR
  exact exists_isUniqueInvolution_of_equiv_sl2 (odd_natCard_galoisField hp2 hadm.2.1) φ

theorem exists_isUniqueInvolution_of_mem_fund (hp2 : p ≠ 2) {t : StatedLieTag} {k e : ℕ}
    (ht : S1911.IsT6Tag t k) (hadm : StatedLieAdmissible t k p e)
    {R : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D) :
    ∃ c, IsUniqueInvolution R c := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_isUniqueInvolution_fund_classical (t := .PSL) hp2 trivial hadm (by decide)
      (by decide) hR
  · exact exists_isUniqueInvolution_fund_classical (t := .PSU) hp2 trivial hadm (by decide)
      (by decide) hR
  · exact exists_isUniqueInvolution_fund_g2 hp2 hadm.2.1 hR
  · exact exists_isUniqueInvolution_fund_d4 hp2 hadm hR

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
