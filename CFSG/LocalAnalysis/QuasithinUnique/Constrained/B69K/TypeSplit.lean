module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Assembly
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.Quasithin.B69K

open CFSG.Open

@[expose] def Survivor (K : Type) [Group K] : Prop :=
  (∃ f : ℕ, StatedClassicalModel K .PSL 2 2 f) ∨ (∃ f : ℕ, StatedClassicalModel K .PSL 3 2 f) ∨
    (∃ f : ℕ, StatedClassicalModel K .PSU 3 2 f) ∨ (∃ f : ℕ, StatedClassicalModel K .PSp 2 2 f) ∨
    CFSG.Quasithin.IsAlt 5 K ∨ CFSG.Quasithin.IsAlt 6 K

@[expose] def HighRankModel (K : Type) [Group K] : Prop :=
  (∃ n f : ℕ, 4 ≤ n ∧ StatedClassicalModel K .PSL n 2 f) ∨
    (∃ n f : ℕ, 4 ≤ n ∧ StatedClassicalModel K .PSU n 2 f) ∨
    (∃ r f : ℕ, 3 ≤ r ∧ StatedClassicalModel K .PSp r 2 f) ∨
    (∃ n f : ℕ, 4 ≤ n ∧ StatedClassicalModel K .POmegaPlus n 2 f) ∨
    (∃ n f : ℕ, 4 ≤ n ∧ StatedClassicalModel K .POmegaMinus n 2 f)

@[expose] def ExcludedType (K : Type) [Group K] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ CFSG.Quasithin.IsG2 2 f K) ∨ CFSG.Quasithin.IsAlt 7 K ∨
    CFSG.Quasithin.IsAlt 8 K ∨ CFSG.Quasithin.IsPSU 3 3 1 K

theorem survivor_psl2 {K : Type} [Group K] {f : ℕ} (h : StatedClassicalModel K .PSL 2 2 f) :
    Survivor K :=
  Or.inl ⟨f, h⟩

theorem survivor_psl3 {K : Type} [Group K] {f : ℕ} (h : StatedClassicalModel K .PSL 3 2 f) :
    Survivor K :=
  Or.inr (Or.inl ⟨f, h⟩)

theorem survivor_psu32 {K : Type} [Group K] {f : ℕ} (h : StatedClassicalModel K .PSU 3 2 f) :
    Survivor K :=
  Or.inr (Or.inr (Or.inl ⟨f, h⟩))

theorem survivor_psp2 {K : Type} [Group K] {f : ℕ} (h : StatedClassicalModel K .PSp 2 2 f) :
    Survivor K :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩)))

theorem survivor_alt5 {K : Type} [Group K] (h : CFSG.Quasithin.IsAlt 5 K) : Survivor K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem survivor_alt6 {K : Type} [Group K] (h : CFSG.Quasithin.IsAlt 6 K) : Survivor K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem highRank_psl {K : Type} [Group K] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel K .PSL n 2 f) : HighRankModel K :=
  Or.inl ⟨n, f, hn, h⟩

theorem highRank_psu {K : Type} [Group K] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel K .PSU n 2 f) : HighRankModel K :=
  Or.inr (Or.inl ⟨n, f, hn, h⟩)

theorem highRank_psp {K : Type} [Group K] {r f : ℕ} (hr : 3 ≤ r)
    (h : StatedClassicalModel K .PSp r 2 f) : HighRankModel K :=
  Or.inr (Or.inr (Or.inl ⟨r, f, hr, h⟩))

theorem highRank_omegaPlus {K : Type} [Group K] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel K .POmegaPlus n 2 f) : HighRankModel K :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, f, hn, h⟩)))

theorem highRank_omegaMinus {K : Type} [Group K] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel K .POmegaMinus n 2 f) : HighRankModel K :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨n, f, hn, h⟩)))

theorem excluded_g2 {K : Type} [Group K] (h : ∃ f : ℕ, 2 ≤ f ∧ CFSG.Quasithin.IsG2 2 f K) :
    ExcludedType K :=
  Or.inl h

theorem excluded_alt7 {K : Type} [Group K] (h : CFSG.Quasithin.IsAlt 7 K) : ExcludedType K :=
  Or.inr (Or.inl h)

theorem excluded_alt8 {K : Type} [Group K] (h : CFSG.Quasithin.IsAlt 8 K) : ExcludedType K :=
  Or.inr (Or.inr (Or.inl h))

theorem excluded_psu331 {K : Type} [Group K] (h : CFSG.Quasithin.IsPSU 3 3 1 K) :
    ExcludedType K :=
  Or.inr (Or.inr (Or.inr h))

theorem g2_index_isG2
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hdq : d.1 = .G2 q) (hp : q.p = 2) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ f : ℕ, 2 ≤ f ∧ CFSG.Quasithin.IsG2 2 f Y := by
  obtain ⟨d, hv⟩ := d
  have hdq' : d = .G2 q := hdq
  subst hdq'
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
  have hf2 : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    rw [h1, pow_one] at hcard
    omega
  have hK : Nat.card (GaloisField 2 q.exponent) = q.card := by
    rw [hcard, GaloisField.card 2 q.exponent (by omega)]
  obtain ⟨b⟩ :=
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp (GaloisField 2 q.exponent) hK
  refine ⟨q.exponent, hf2, ?_⟩
  exact ⟨⟨Nat.prime_two, by omega, rfl, by rw [← hcard]; exact hq3⟩,
    GaloisField 2 q.exponent, inferInstance, inferInstance, hK.trans hcard, ⟨e.trans b.symm⟩⟩

theorem g2_hyp_of_certificates :
    ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d.1 = .G2 q → q.p = 2 →
      ∀ (Y : Type) [Group Y], Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ f : ℕ, 2 ≤ f ∧ CFSG.Quasithin.IsG2 2 f Y := by
  intro d q hdq hp Y _ he
  obtain ⟨e⟩ := he
  exact g2_index_isG2 hdq hp e

theorem typeSplit {K : Type} [Group K] [Finite K]
    (hG2 : ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d.1 = .G2 q → q.p = 2 →
      ∀ (Y : Type) [Group Y], Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ f : ℕ, 2 ≤ f ∧ CFSG.Quasithin.IsG2 2 f Y)
    (h : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion K) :
    Survivor K ∨ HighRankModel K ∨ ExcludedType K ∨ ∃ m : ℕ, 9 ≤ m ∧ CFSG.Quasithin.IsAlt m K := by
  rcases h with hc | ⟨m, hm5, ⟨e⟩⟩
  · rcases CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isClassicalTwoOrG2_cases hc with
      hpsl | hrest | h6 | hpsu | hg2 | hb
    ·
      obtain ⟨n, f, hm⟩ := hpsl
      have hn : 2 ≤ n := by
        obtain ⟨-, -, h2, -, -⟩ := hm.1
        exact h2
      rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
      · exact Or.inl (survivor_psl2 hm)
      · exact Or.inl (survivor_psl3 hm)
      · exact Or.inr (Or.inl (highRank_psl h4 hm))
    ·
      obtain ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩ := hrest
      cases idx with
      | twistedA r q =>
        change q.p = 2 at hd
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
        rw [hd] at hm
        have h3 : 3 ≤ r + 1 := by
          obtain ⟨-, -, h3, -⟩ := hm.1
          exact h3
        rcases (show r + 1 = 3 ∨ 4 ≤ r + 1 by omega) with h | h
        · obtain rfl : r = 2 := by omega
          exact Or.inl (survivor_psu32 hm)
        · exact Or.inr (Or.inl (highRank_psu h hm))
      | D r q =>
        change q.p = 2 at hd
        have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
        rw [hd] at hm
        have h4 : 4 ≤ r := by
          obtain ⟨-, -, h4⟩ := hm.1
          exact h4
        exact Or.inr (Or.inl (highRank_omegaPlus h4 hm))
      | twistedD r q =>
        change q.p = 2 at hd
        have hm :=
          CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
        rw [hd] at hm
        have h4 : 4 ≤ r := by
          obtain ⟨-, -, h4⟩ := hm.1
          exact h4
        exact Or.inr (Or.inl (highRank_omegaMinus h4 hm))
      | _ => exact hd.elim
    · exact Or.inl (survivor_alt6 h6)
    · exact Or.inr (Or.inr (Or.inl (excluded_psu331 hpsu)))
    · obtain ⟨d, q, hdq, hp, ⟨e⟩⟩ := hg2
      exact Or.inr (Or.inr (Or.inl (excluded_g2 (hG2 d q hdq hp K ⟨e⟩))))
    ·
      obtain ⟨⟨idx, hv⟩, r, q, hdr, hq2, ⟨e⟩⟩ := hb
      have hdr' : idx = .B r q := hdr
      subst hdr'
      have hr2 : 2 ≤ r :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      rcases Nat.lt_or_ge r 3 with hlt | hge
      · obtain rfl : r = 2 := by omega
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hq2] at hm
        exact Or.inl (survivor_psp2 hm)
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hge e
        rw [hq2] at hm
        exact Or.inr (Or.inl (highRank_psp hge hm))
  · rcases (show m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ 9 ≤ m by omega) with rfl | rfl | rfl | rfl | h9
    · exact Or.inl (survivor_alt5 ⟨e⟩)
    · exact Or.inl (survivor_alt6 ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl (excluded_alt7 ⟨e⟩)))
    · exact Or.inr (Or.inr (Or.inl (excluded_alt8 ⟨e⟩)))
    · exact Or.inr (Or.inr (Or.inr ⟨m, h9, ⟨e⟩⟩))

theorem typeSplit_cert
    {K : Type} [Group K] [Finite K]
    (h : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion K) :
    Survivor K ∨ HighRankModel K ∨ ExcludedType K ∨ ∃ m : ℕ, 9 ≤ m ∧ CFSG.Quasithin.IsAlt m K :=
  typeSplit g2_hyp_of_certificates h

end CFSG.Quasithin.B69K
