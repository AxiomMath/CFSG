module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.LieOrderGrid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416L

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LieGrid

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator.I1420
  CFSG.LocalAnalysis.GLTheoremA

abbrev Chev2GridAt (ps : List ℕ) (N : ℕ) : Prop :=
  (∀ n ≤ 10, ∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderA n c = N →
      n = 0 ∨ (n = 1 ∧ (c = 2 ∨ c = 4 ∨ c = 8)) ∨ (n = 2 ∧ (c = 2 ∨ c = 4)) ∨ (n = 3 ∧ c = 2)) ∧
    (∀ n ≤ 10, ∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderTwistedA n c = N →
      n ≤ 1 ∨ (n = 2 ∧ c = 2) ∨ (n = 3 ∧ c = 2)) ∧
    (∀ n ≤ 7, ∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderBC n c = N → n ≤ 1 ∨ (n = 2 ∧ c = 2)) ∧
    (∀ n ≤ 8, ∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderD n c = N → n ≤ 3) ∧
    (∀ n ≤ 8, ∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderTwistedD n c = N → n ≤ 3) ∧
    (∀ c ∈ ppDivs ps N, c ∣ 2 ^ 60 → orderE6 c ≠ N ∧ orderTwistedE6 c ≠ N ∧ orderF4 c ≠ N ∧
      (orderG2 c = N → c = 2) ∧ orderTrialityD4 c ≠ N) ∧
    (∀ m ≤ 14, orderSuzuki (2 ^ (2 * m + 1)) = N → m = 0) ∧
    (∀ m ≤ 1, orderTwistedF4 (2 ^ (2 * m + 1)) = N → m = 0) ∧ orderTits ≠ N

set_option synthInstance.maxSize 4096 in
instance instDecidableChev2GridAt (ps : List ℕ) (N : ℕ) : Decidable (Chev2GridAt ps N) := by
  unfold Chev2GridAt
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_))))))) <;> infer_instance

theorem dvd_of_mem_ppDivs {ps : List ℕ} {N c : ℕ} (h : c ∈ ppDivs ps N) : c ∣ N := by
  unfold ppDivs at h
  rw [List.mem_filter] at h
  simpa using h.2

theorem dvd_two_pow_of_char {ps : List ℕ} {N : ℕ} (hN0 : 0 < N) (hNlt : N < 2 ^ 60)
    {q : TauCeti.PrimePower} (hp : q.p = 2) (hq : q.card ∈ ppDivs ps N) : q.card ∣ 2 ^ 60 := by
  have hc := TauCeti.PrimePower.card_def q
  rw [hp] at hc
  have hle : q.card ≤ N := Nat.le_of_dvd hN0 (dvd_of_mem_ppDivs hq)
  have he : q.exponent ≤ 60 := by
    by_contra h
    push Not at h
    have : 2 ^ 60 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hc]
  exact pow_dvd_pow 2 he

theorem chev2Spor_of_lie {ps : List ℕ} {N : ℕ} (hps : ∀ p, p.Prime → p ∣ N → p ∈ ps)
    (hN0 : 0 < N) (hNlt : N < 2 ^ 60) (hG : Chev2GridAt ps N) (d : TauCeti.ValidLieTypeIndex)
    (h2 : d.1.characteristic = 2) (h : lieOrderFormula d.1 = N) :
    chev2Spor (TauCeti.CFSGIndex.lie d) := by
  obtain ⟨d, hd⟩ := d
  obtain ⟨hs, hdup⟩ := (TauCeti.LieTypeIndex.valid_iff d).1 hd
  have hg := lieGridOK_of_order hps hN0 hNlt hs h
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  obtain ⟨hGA, hG2A, hGBC, hGD, hG2D, hGE, hGSz, hGRF, hGT⟩ := hG
  cases d with
  | A n q =>
    rw [TauCeti.LieTypeIndex.characteristic_A] at h2
    obtain ⟨hc, hn, ho⟩ := hg
    rcases hGA n hn _ hc (dvd_two_pow_of_char hN0 hNlt h2 hc) ho with
      h0 | ⟨rfl, h12 | h4 | h8⟩ | ⟨rfl, h22 | h24⟩ | ⟨rfl, h32⟩
    · exact absurd hs.1 (by omega)
    · exact absurd (hs.2 rfl) (by omega)
    · exact (hdup (Or.inl ⟨rfl, Or.inl h4⟩)).elim
    · exact Or.inl (Or.inr h8)
    · exact (hdup (Or.inr (Or.inl ⟨rfl, h22⟩))).elim
    · exact Or.inr h24
    · exact (hdup (Or.inr (Or.inr ⟨rfl, h32⟩))).elim
  | twistedA n q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedA] at h2
    obtain ⟨hc, hn, ho⟩ := hg
    rcases hG2A n hn _ hc (dvd_two_pow_of_char hN0 hNlt h2 hc) ho with h1 | ⟨rfl, h22⟩ | ⟨rfl, h32⟩
    · exact absurd hs.1 (by omega)
    · exact absurd (hs.2 rfl) (by omega)
    · exact Or.inl h32
  | B n q =>
    rw [TauCeti.LieTypeIndex.characteristic_B] at h2
    obtain ⟨hc, hn, ho⟩ := hg
    rcases hGBC n hn _ hc (dvd_two_pow_of_char hN0 hNlt h2 hc) ho with h1 | ⟨rfl, h22⟩
    · exact absurd hs.1 (by omega)
    · exact (hs.2 ⟨rfl, h22⟩).elim
  | C n q =>
    rw [TauCeti.LieTypeIndex.characteristic_C] at h2
    exact (hs.2 h2).elim
  | D n q =>
    rw [TauCeti.LieTypeIndex.characteristic_D] at h2
    obtain ⟨hc, hn, ho⟩ := hg
    have := hGD n hn _ hc (dvd_two_pow_of_char hN0 hNlt h2 hc) ho
    exact absurd hs (by omega)
  | twistedD n q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedD] at h2
    obtain ⟨hc, hn, ho⟩ := hg
    have := hG2D n hn _ hc (dvd_two_pow_of_char hN0 hNlt h2 hc) ho
    exact absurd hs (by omega)
  | E6 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E6] at h2
    exact ((hGE _ hg.1 (dvd_two_pow_of_char hN0 hNlt h2 hg.1)).1 hg.2).elim
  | E7 q => exact hg.elim
  | E8 q => exact hg.elim
  | F4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_F4] at h2
    exact ((hGE _ hg.1 (dvd_two_pow_of_char hN0 hNlt h2 hg.1)).2.2.1 hg.2).elim
  | G2 q =>
    rw [TauCeti.LieTypeIndex.characteristic_G2] at h2
    have := (hGE _ hg.1 (dvd_two_pow_of_char hN0 hNlt h2 hg.1)).2.2.2.1 hg.2
    exact absurd hs (by omega)
  | twistedE6 q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at h2
    exact ((hGE _ hg.1 (dvd_two_pow_of_char hN0 hNlt h2 hg.1)).2.1 hg.2).elim
  | trialityD4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at h2
    exact ((hGE _ hg.1 (dvd_two_pow_of_char hN0 hNlt h2 hg.1)).2.2.2.2 hg.2).elim
  | suzuki m =>
    have := hGSz m hg.1 hg.2
    exact absurd hs (by omega)
  | reeG2 m =>
    rw [TauCeti.LieTypeIndex.characteristic_reeG2] at h2
    exact absurd h2 (by norm_num)
  | reeF4 m =>
    have := hGRF m hg.1 hg.2
    exact absurd hs (by omega)
  | tits => exact (hGT hg).elim

theorem chev2Small_of_ambiguous {i : TauCeti.CFSGIndex} (h : ambiguousChev 2 i) :
    chev2Small i := by
  cases i with
  | alternating n hn =>
    simp only [ambiguousChev] at h
    simp only [chev2Small]
    omega
  | lie d =>
    obtain ⟨d, hd⟩ := d
    cases d with
    | A n q =>
      rcases n with _ | _ | n
      · simp [ambiguousChev] at h
      · simp only [ambiguousChev] at h
        simp only [chev2Small]
        omega
      · simp [ambiguousChev] at h
    | twistedA n q =>
      rcases n with _ | _ | _ | _ | n
      · simp [ambiguousChev] at h
      · simp [ambiguousChev] at h
      · simp only [ambiguousChev] at h
        simp only [chev2Small]
        exact h.1
      · simp only [ambiguousChev] at h
        omega
      · simp [ambiguousChev] at h
    | _ => simp [ambiguousChev] at h
  | _ => simp [ambiguousChev] at h

end CFSG.LocalAnalysis.GLTheoremA.LieGrid
