module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem seven_le_card_of_valid_A_one {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) : 7 ≤ q.card := by
  have h := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have h1 := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 h.1
  have h2 := h.2
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at h2
  have h4 : 4 ≤ q.card := h1.2 rfl
  by_contra hlt
  have h6 : q.card = 6 := by
    have : q.card ≠ 4 := fun h => h2 (Or.inl ⟨rfl, Or.inl h⟩)
    have : q.card ≠ 5 := fun h => h2 (Or.inl ⟨rfl, Or.inr (Or.inl h)⟩)
    omega
  have hp := q.prime_p
  rw [TauCeti.PrimePower.card_def] at h6
  have hdvd : q.p ∣ 2 * 3 := by
    have h := dvd_pow_self q.p q.exponent_pos.ne'
    rw [h6] at h
    exact h
  have hpe : q.exponent ≤ 6 := by
    have h2 : 2 ^ q.exponent ≤ q.p ^ q.exponent := Nat.pow_le_pow_left hp.two_le q.exponent
    rw [h6] at h2
    by_contra hex
    have h3 : 2 ^ 7 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    rw [h2] at h6
    interval_cases q.exponent <;> omega
  · have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    rw [h3] at h6
    interval_cases q.exponent <;> omega

theorem crossSylowAbelianAt_linearOne {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) : CrossSylowAbelianAt ⟨.A 1 q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdp' : q.p ≠ p := by simpa using hdp
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne']
  have h7 : 7 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hK, ← TauCeti.PrimePower.card_def]
    exact seven_le_card_of_valid_A_one hv
  have hcop : Nat.Coprime p (Nat.card (GaloisField q.p q.exponent)) := by
    rw [hK]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp q.prime_p).2 (Ne.symm hdp'))
  let eL : L ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hcyc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
    (GaloisField q.p q.exponent) hK h7 p (by omega) hcop
  exact isMulCommutative_sylow_of_mulEquiv_isCyclic eL hcyc P

theorem crossAt_linearOne {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    CrossAt ⟨.A 1 q, hv⟩ :=
  crossAt_of_sylowAbelian (crossSylowAbelianAt_linearOne hv)

end CFSG.LocalAnalysis.RankFourTheoremC
