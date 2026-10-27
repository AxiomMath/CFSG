module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree

theorem not_catalogIs_isLnA_one (S : Type) [Group S] (q : ℕ) : ¬ catalogIs S (isLnA 1 q) := by
  rintro ⟨i, hi, -⟩
  rcases hi with h1 | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating n hn => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r qq =>
        have h1' : r + 1 = 1 ∧ qq.card = q := h1
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        omega
      | _ => simp [onLie, isLnEps] at h1
  · omega
  · omega
  · omega
  · omega

theorem cases_isLnA_two_four {S : Type} [Group S] (h : catalogIs S (isLnA 2 4)) :
    (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid),
        q.card = 4 ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group)) ∨
    Nonempty (S ≃* (TauCeti.CFSGIndex.alternating 5 (by norm_num)).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨h4, -, hi⟩ | ⟨-, h9, -⟩ | ⟨h3, -, -⟩ | ⟨h4', -, -⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating n hn => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r qq =>
        have h1' : r + 1 = 2 ∧ qq.card = 4 := h1
        obtain ⟨hr, hq⟩ := h1'
        have hr1 : r = 1 := by omega
        subst hr1
        exact Or.inl ⟨qq, hv, hq, ⟨e⟩⟩
      | _ => simp [onLie, isLnEps] at h1
  · cases i with
    | cyclic p hp => simp [isAltN] at hi
    | alternating n hn =>
      have hn5 : n = 5 := hi
      subst hn5
      exact Or.inr ⟨e⟩
    | sporadic s => simp [isAltN] at hi
    | lie idx => simp [isAltN] at hi
  · omega
  · omega
  · omega

theorem card_of_isLnA_two_four (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (isLnA 2 4)) : Nat.card S = 60 := by
  rcases cases_isLnA_two_four h with ⟨q, hv, hq, he⟩ | he
  · obtain ⟨e⟩ := he
    have hc := hb ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩ S ⟨e⟩
    rw [hc]
    show orderA 1 q.card = 60
    rw [hq]
    decide
  · obtain ⟨e⟩ := he
    rw [CFSG.LocalAnalysis.GLTheoremA.S172.card_of_equiv_alt (by norm_num) e]
    decide

theorem factorization_three_sixty : (60 : ℕ).factorization 3 = 1 := by
  have h60 : (60 : ℕ) = 3 ^ 1 * 20 := by norm_num
  rw [h60, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem autThreePowInner_of_isLnA_two_four {S : Type} [Group S] [Finite S]
    (h : catalogIs S (isLnA 2 4)) (h3 : (Nat.card S).factorization 3 = 1) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner S := by
  rcases cases_isLnA_two_four h with ⟨q, hv, hq, he⟩ | he
  · obtain ⟨e⟩ := he
    have hM : CFSG.Open.StatedClassicalModel S CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
      statedClassicalModel_psl_of_typeA 1 q hv e
    have hp2 : q.p = 2 := by
      have hd : q.p ∣ 4 := by
        rw [← hq, TauCeti.PrimePower.card_def]
        exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      have h2 : q.p ∣ 2 := by
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4] at hd
        exact q.prime_p.dvd_of_dvd_pow hd
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2
    exact autThreePowInner_of_psl_two hM (by rw [hp2]; norm_num) h3
  · obtain ⟨e⟩ := he
    exact autThreePowInner_of_alt_five e

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
