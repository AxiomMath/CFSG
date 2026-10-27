module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityWrap
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Decode
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (projectiveSpecialLinearEquivProjectiveSL)

theorem parityCoreAt_of_catalogIs_isLnA (ha : ParityCoreLinA) {J : Type} [Group J] {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hJ : catalogIs J (isLnA n 2)) : ParityCoreAt 3 J := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hJ
  rcases hi with hi | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨m, F, _, _, rfl, hF, ⟨e'⟩⟩ := exists_psl_of_isLnEps (S := J) ⟨i, hi, ⟨e⟩⟩
    exact parityCoreAt_of_mulEquiv (e'.trans (projectiveSpecialLinearEquivProjectiveSL _ F))
      (ha _ F hn h5 hF)
  all_goals omega

theorem parityCoreAt_of_catalogIs_isOmMA (hb : ParityCoreOmMinus) {J : Type} [Group J] {n : ℕ}
    (hn : Even n) (h6 : 6 ≤ n) (hJ : catalogIs J (isOmMA n 2)) : ParityCoreAt 3 J := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hJ
  rcases hi with hi | ⟨h, -⟩
  · cases i with
    | cyclic _ _ => simp [isOmM, onLie] at hi
    | alternating _ _ => simp [isOmM, onLie] at hi
    | sporadic _ => simp [isOmM, onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedD r qq =>
        obtain ⟨hr, hq⟩ : r = n ∧ qq.card = 2 := hi
        have hr' : Even r := by rw [hr]; exact hn
        rcases (CFSG.Models.lieModel_twistedD r qq hv e).2 with
          ⟨-, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ | ⟨h0, -⟩
        · exact parityCoreAt_of_mulEquiv e' (hb r K b c hr' (by omega)
            (by rw [hK, ← TauCeti.PrimePower.card_def, hq]) hirr)
        · omega
      | _ => simp [isOmM, onLie] at hi
  · omega

theorem parityCoreAt_of_catalogIs_isOmPA (hl : ParityCoreL4) (hc : ParityCoreOmPlus) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Type} [Group J] {n k : ℕ} (hn : Odd n)
    (hk1 : k = 1 → 5 ≤ n) (hk : 1 ≤ k) (hdvd : p ∣ 2 ^ k + 1)
    (hJ : catalogIs J (isOmPA n (2 ^ k))) : ParityCoreAt p J := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hJ
  rcases hi with hi | ⟨hn3, hi⟩
  · cases i with
    | cyclic _ _ => simp [isOmP, onLie] at hi
    | alternating _ _ => simp [isOmP, onLie] at hi
    | sporadic _ => simp [isOmP, onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | D r qq =>
        obtain ⟨hr, hq⟩ : r = n ∧ qq.card = 2 ^ k := hi
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        have hr' : Odd r := by rw [hr]; exact hn
        have h5 : 5 ≤ r := by
          obtain ⟨j, hj⟩ := hr'
          omega
        rcases (CFSG.Models.lieModel_D r qq hv e).2 with ⟨-, K, _, _, hK, ⟨e'⟩⟩ | ⟨h0, -⟩
        · exact parityCoreAt_of_mulEquiv e'
            (hc p r k K hp hp2 hr' h5 hk hdvd (by rw [hK, ← TauCeti.PrimePower.card_def, hq]))
        · omega
      | _ => simp [isOmP, onLie] at hi
  ·
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have := hk1 (by omega)
      omega
    rcases hi with hi | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · obtain ⟨m, F, _, _, hm, hF, ⟨e'⟩⟩ := exists_psl_of_isLnEps (S := J) ⟨i, hi, ⟨e⟩⟩
      obtain rfl : m = 3 := by omega
      exact parityCoreAt_of_mulEquiv (e'.trans (projectiveSpecialLinearEquivProjectiveSL _ F))
        (hl p k F hp hp2 hk2 hdvd hF)
    · omega
    · omega
    · omega
    · have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      rw [h] at h4
      omega

theorem aut167JCore_of_families (ha : ParityCoreLinA) (hl : ParityCoreL4)
    (hb : ParityCoreOmMinus) (hc : ParityCoreOmPlus) : Aut167JCore := by
  intro p J _ _ hp hp2 hJ
  rcases hJ with ⟨rfl, n, hn, h5, hJ⟩ | ⟨rfl, n, hn, h6, hJ⟩ | ⟨n, k, hn, -, hk1, hk, hdvd, hJ⟩
  · exact parityCoreAt_of_catalogIs_isLnA ha hn h5 hJ
  · exact parityCoreAt_of_catalogIs_isOmMA hb hn h6 hJ
  · exact parityCoreAt_of_catalogIs_isOmPA hl hc hp hp2 hn hk1 hk hdvd hJ

theorem parityFact_of_families (ha : ParityCoreLinA) (hl : ParityCoreL4)
    (hb : ParityCoreOmMinus) (hc : ParityCoreOmPlus) : ParityFact :=
  parityFact_of_core (aut167JCore_of_families ha hl hb hc)

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
