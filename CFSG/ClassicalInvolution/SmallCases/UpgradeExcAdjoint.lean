module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcToral
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsOrthogonal
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalCentral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem card_eq_of_isClassicalMember_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {L : Subgroup ↥(adjointGroup τ K)} {z : ↥(adjointGroup τ K)}
    (h : IsClassicalMember p f L z) : Nat.card K = p ^ f := by
  obtain ⟨hodd, -⟩ := ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  obtain ⟨g, b, hb, hgz⟩ := ModelFacts.exists_conj_eq_rootDiagUnit_of_involution hτ hK z hz2
  have hL' := ModelFacts.isClassicalMember_map_conj hodd h g
  exact card_eq_of_isClassicalMember_toral hp2 hq hK b hb hgz hL'

theorem eq_of_card_galoisField_eq {r e : ℕ} [Fact r.Prime] (hq : 5 ≤ p ^ f) (he : 1 ≤ e)
    (h : Nat.card (GaloisField r e) = p ^ f) : r = p ∧ e = f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card r e (by omega)] at h
  exact Nat.Prime.pow_inj' Fact.out Fact.out (by omega) hf h

theorem classicalMemberParametersAt_g2 : ClassicalMemberParametersAt p f .G2 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  have hodd := odd_card_galoisField (r := r) hr2 he
  have hM : Generic.modelUniv .G2 n r e hr = ⟨↥(adjointGroup .G2 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField r e)⟩ := rfl
  suffices h : ∀ M : LieUniversal, M = ⟨↥(adjointGroup .G2 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField r e)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.G2 = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  have hcard := card_eq_of_isClassicalMember_adjoint (τ := .G2) (Or.inl rfl) hp2 hq hodd hL
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
  exact ⟨rfl, Or.inl rfl⟩

theorem classicalMemberParametersAt_f4 : ClassicalMemberParametersAt p f .F4 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  have hodd := odd_card_galoisField (r := r) hr2 he
  have hM : Generic.modelUniv .F4 n r e hr = ⟨↥(adjointGroup .F4 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField r e)⟩ := rfl
  suffices h : ∀ M : LieUniversal, M = ⟨↥(adjointGroup .F4 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField r e)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.F4 = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  have hcard := card_eq_of_isClassicalMember_adjoint (τ := .F4) (Or.inr (Or.inl rfl)) hp2 hq
    hodd hL
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
  exact ⟨rfl, Or.inl rfl⟩

theorem classicalMemberParametersAt_e8 : ClassicalMemberParametersAt p f .E8 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  have hodd := odd_card_galoisField (r := r) hr2 he
  have hM : Generic.modelUniv .E8 n r e hr = ⟨↥(adjointGroup .E8 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField r e)⟩ := rfl
  suffices h : ∀ M : LieUniversal, M = ⟨↥(adjointGroup .E8 (GaloisField r e)),
      CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField r e)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.E8 = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  have hcard := card_eq_of_isClassicalMember_adjoint (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
    hp2 hq hodd hL
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
  exact ⟨rfl, Or.inl rfl⟩

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits in
theorem card_eq_of_isClassicalMember_e6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    [Finite ↥(e6Data_valid.minGroup K)] {L : Subgroup ↥(e6Data_valid.minGroup K)}
    {z : ↥(e6Data_valid.minGroup K)} (h : IsClassicalMember p f L z) : Nat.card K = p ^ f := by
  obtain ⟨hodd, -⟩ := ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  have hqs := isQuasisimple_e6 K
  have hθ := e6Isogeny_surjective K
  have hker : (e6Isogeny K).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one K)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_card hK)
  have hz : e6Isogeny K z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := ModelFacts.exists_two_involutions_minGroup e6Data_valid K h2
      (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) (by simp)
    by_cases h' : y₁ = z
    · exact ModelFacts.false_of_isClassicalMember_of_central (ModelFacts.open_isQuasisimple hqs)
        hodd h hzc hy₂ (fun h'' => hne (h'.trans h''.symm))
    · exact ModelFacts.false_of_isClassicalMember_of_central (ModelFacts.open_isQuasisimple hqs)
        hodd h hzc hy₁ h'
  have hL' := ModelFacts.isClassicalMember_map_central (e6Isogeny K) hθ hker hodd h hz
  exact card_eq_of_isClassicalMember_adjoint (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hp2 hq hK
    hL'

theorem classicalMemberParametersAt_e6 : ClassicalMemberParametersAt p f .E6 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  have hodd := odd_card_galoisField (r := r) hr2 he
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .E6 0 r e hr).K :=
    ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField r e)) :=
    hfin
  have hcard := card_eq_of_isClassicalMember_e6 hp2 hq hodd (L := L) (z := z) hL
  obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
  exact ⟨rfl, Or.inl rfl⟩

end CFSG.ClassicalInvolution.Upgrade
