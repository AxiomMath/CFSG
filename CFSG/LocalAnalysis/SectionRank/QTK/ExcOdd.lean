module

public import CFSG.RankThree.Chevalley.SteinbergCFOddFourCommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.PartTwo.Census.Exceptional.TrialityD4

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups

theorem ringChar_ne_two_of_card {K : Type} [Field K] [Fintype K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Fintype.card K = p ^ f) : ringChar K ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow hK
  rwa [ringChar.eq K p]


theorem four_mul_le_localRank_of_untwistedModel_odd {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UntwistedChevalleyModel S τ (p ^ f)) : 4 * f ≤ localRank p S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  let e' : S ≃* adjointGroup τ K := e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv τ K)
  have : Finite (adjointGroup τ K) := Finite.of_equiv S e'.toEquiv
  obtain ⟨ι, hι, hcomm⟩ :=
    CFSG.RankThree.Chevalley.higher_ordinary_exceptional_four_commuting_faithful_SL2 K
      (ringChar_ne_two_of_card hp hp2 hcard) τ hτ
  have h := sum_le_localRank_of_commuting_SL2 hp hp2 (0 : Fin 4) (K := fun _ => K)
    (fun _ => f) (fun _ => hcard) ι hι hcomm
  rw [Fin.sum_const, smul_eq_mul] at h
  rw [localRank_eq_of_mulEquiv e' hp]
  exact h

theorem two_mul_le_localRank_of_G2Model_odd {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : UntwistedChevalleyModel S .G2 (p ^ f)) :
    2 * f ≤ localRank p S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  let e' : S ≃* adjointGroup .G2 K :=
    e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 K)
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv S e'.toEquiv
  obtain ⟨ι₁, ι₂, h₁, h₂, hcomm⟩ :=
    CFSG.RankThree.Chevalley.G2_two_commuting_faithful_SL2 K (ringChar_ne_two_of_card hp hp2 hcard)
  have h := add_le_localRank_of_two_commuting_SL2 hp hp2 (K₁ := K) (K₂ := K) hcard hcard ι₁ ι₂ h₁
    h₂ hcomm
  rw [localRank_eq_of_mulEquiv e' hp]
  omega

theorem four_mul_le_localRank_of_twistedE6Model_odd {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : TwistedChevalleyModel S .E6 (p ^ f)) :
    4 * f ≤ localRank p S := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨e₀⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv .E6 hp hf K hK σ hσ
  let e' : S ≃* graphFixedRootGroup .E6 K σ := e.trans e₀
  have : Finite (graphFixedRootGroup .E6 K σ) := Finite.of_equiv S e'.toEquiv
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hK
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK2]; exact (pow_pos (pow_pos hp.pos f) 2).ne')
  have : Fintype K := Fintype.ofFinite K
  have hKp : Fintype.card K = p ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hK2, ← pow_mul, mul_comm]
  set F := RingHom.eqLocusField σ (RingHom.id K)
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = p ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hp hf hK2 hσ
  obtain ⟨ι, hι, hcomm⟩ := CFSG.RankThree.Chevalley.twisted_E6_four_commuting_faithful_fixed_SL2 K
    (ringChar_ne_two_of_card hp hp2 hKp) σ
  have h := sum_le_localRank_of_commuting_SL2 hp hp2 (0 : Fin 4) (K := fun _ => F)
    (fun _ => f) (fun _ => hF) ι hι hcomm
  rw [Fin.sum_const, smul_eq_mul] at h
  rw [localRank_eq_of_mulEquiv e' hp]
  exact h

theorem four_le_localRank_of_trialityModel_odd {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : TwistedChevalleyModel S .D4 (p ^ f)) :
    4 ≤ localRank p S := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨σ', hσ', -, -, -, k, hk, hkcard, -⟩ := finite_graph_field_parameter_fields .D4 hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  subst hσσ'
  have hK' : Nat.card K = (p ^ f) ^ 3 := hK
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK']; exact (pow_pos (pow_pos hp.pos f) 3).ne')
  have h3 : σ' ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ' (σ' (σ' c)) = c
    have : Fintype K := Fintype.ofFinite K
    rw [hσ', hσ', hσ', ← pow_mul, ← pow_mul,
      show p ^ f * (p ^ f * p ^ f) = (p ^ f) ^ 3 by ring, ← hK', Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hfix : fixSubfield σ' = k := SetLike.ext' (by
    rw [hk]
    ext c
    change σ' c = c ↔ c ^ (p ^ f) = c
    rw [hσ'])
  have hkcard' : Nat.card (fixSubfield σ') = p ^ f := by rw [hfix, hkcard]
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK', ← pow_mul, mul_comm]
  have : Finite (DerivedCentralQuotient (twistedFixedGroup .D4 K σ'.toRingHom)) :=
    Finite.of_equiv S e.toEquiv
  rw [localRank_eq_of_mulEquiv e hp]
  exact four_le_localRank_derivedCentralQuotient_D4 σ' hp hp2 hf h3 hK3 hkcard'

end CFSG.SectionRank.QTK
