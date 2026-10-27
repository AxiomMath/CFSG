module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Lower
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Block
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Upper
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

theorem two_pow_mod_three_cases (f : ℕ) : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
  have h : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  omega

theorem agl418_psl {X : Type} [Group X] [Finite X] {r f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL (r + 1) 2 f) (hr0 : 1 ≤ r) (hr1 : r = 1 → 3 ≤ f)
    (hrank : Open.pRank 3 (⊤ : Subgroup X) = 2) :
    (r = 2 ∧ 2 ^ f % 3 = 1) ∨ (r = 3 ∧ 2 ^ f % 3 = 2) ∨ (r = 4 ∧ 2 ^ f % 3 = 2) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e'] at hrank
  have hmod := two_pow_mod_three_cases f
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | rfl | hr5
  · have h1 := pRank_three_psl_two_le_one hK (hr1 rfl)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    omega
  · rcases hmod with h1 | h2
    · exact Or.inl ⟨rfl, h1⟩
    · have h1 := pRank_three_psl_three_le_one hK h2
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
      omega
  · rcases hmod with h1 | h2
    · have h3 := psl_three_le_pRank_of_dvd (K := K) (n := 4) (by rw [hK]; omega) (by norm_num)
      omega
    · exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · rcases hmod with h1 | h2
    · have h3 := psl_three_le_pRank_of_dvd (K := K) (n := 5) (by rw [hK]; omega) (by norm_num)
      omega
    · exact Or.inr (Or.inr ⟨rfl, h2⟩)
  · have h3 := psl_three_le_pRank_three (K := K) (n := r + 1) (by omega)
    omega

theorem agl418_psu {X : Type} [Group X] [Finite X] {r f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU (r + 1) 2 f) (hr : 2 ≤ r)
    (hrank : Open.pRank 3 (⊤ : Subgroup X) = 2) :
    (r = 2 ∧ 2 ^ f % 3 = 2) ∨ (r = 3 ∧ 2 ^ f % 3 = 1) ∨ (r = 4 ∧ 2 ^ f % 3 = 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := f * 2)
    (by rw [hK, pow_mul])
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e'] at hrank
  have hmod := two_pow_mod_three_cases f
  have hq : 2 ^ f ≠ 0 := by positivity
  have htorus : 2 ^ f % 3 = 2 → 4 ≤ r + 1 → False := fun h2 hn => by
    have h3 := psu_three_le_pRank_of_dvd (K := K) (n := r + 1) hq hK (by omega) hn
    omega
  rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | hr5
  · rcases hmod with h1 | h2
    · have h3 := pRank_three_psu_three_le_one hK h1
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h3
      omega
    · exact Or.inl ⟨rfl, h2⟩
  · rcases hmod with h1 | h2
    · exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · exact (htorus h2 (by norm_num)).elim
  · rcases hmod with h1 | h2
    · exact Or.inr (Or.inr ⟨rfl, h1⟩)
    · exact (htorus h2 (by norm_num)).elim
  · rcases hmod with h1 | h2
    · have h3 := psu_three_le_pRank_of_one_mod_three (K := K) (n := r + 1) hK (by omega) (by omega)
      omega
    · exact (htorus h2 (by omega)).elim

theorem agl418_proved : Agl418 := by
  intro d _ hcl hrank
  obtain ⟨d1, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  cases d1 with
  | A r q =>
    simp only [IsClassicalOrG2Index] at hcl
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    rw [hcl] at h
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hcl]
    have hr1 : r = 1 → 3 ≤ q.exponent := fun hr => by
      subst hr
      have h4 := hrange.2 rfl
      have h4' : ¬ q.card = 4 := fun h => hdup (Or.inl ⟨rfl, Or.inl h⟩)
      rw [hcard] at h4 h4'
      by_contra hlt
      have : q.exponent = 0 ∨ q.exponent = 1 ∨ q.exponent = 2 := by omega
      rcases this with h0 | h0 | h0 <;> rw [h0] at h4 h4' <;> omega
    rcases agl418_psl h hrange.1 hr1 hrank with ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hcard]; exact h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hcard]; exact h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hcard]; exact h2⟩))))))
  | twistedA r q =>
    simp only [IsClassicalOrG2Index] at hcl
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    rw [hcl] at h
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hcl]
    rcases agl418_psu h hrange.1 hrank with ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hcard]; exact h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hcard]; exact h2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl, by rw [hcard]; exact h2⟩))))))
  | B r q =>
    simp only [IsClassicalOrG2Index] at hcl
    rcases (show r = 2 ∨ 3 ≤ r by have := hrange.1; omega) with rfl | hr3
    · exact Or.inr (Or.inl ⟨q, rfl⟩)
    · exfalso
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hcl hr3
        (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group)
      obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
      have : CharP K 2 := by
        have := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := q.p) (K := K) hK
        rwa [hcl] at this
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e'] at hrank
      have h3 := psp_three_le_pRank_three (K := K) (n := r) hr3
      omega
  | D r q =>
    simp only [IsClassicalOrG2Index] at hcl
    exfalso
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hcl
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group)
    obtain ⟨⟨_, _, hm⟩, K, _, _, hK, ⟨e'⟩⟩ := h
    have : CharP K 2 := by
      have := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := q.p) (K := K) hK
      rwa [hcl] at this
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e'] at hrank
    have h3 := omegaPlus_three_le_pRank_three (K := K) hm
    omega
  | twistedD r q =>
    simp only [IsClassicalOrG2Index] at hcl
    exfalso
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hcl
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group)
    obtain ⟨⟨_, _, hm⟩, K, _, _, hK, b, c, -, ⟨e'⟩⟩ := h
    have : CharP K 2 := by
      have := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := q.p) (K := K) hK
      rwa [hcl] at this
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e'] at hrank
    have h3 := omegaMinus_three_le_pRank_three (K := K) hm b c
    omega
  | G2 q => exact Or.inl ⟨q, rfl⟩
  | _ => exact hcl.elim

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
