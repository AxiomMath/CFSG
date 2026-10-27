module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem rk2_evenRank_le {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2KRank)
    (hL : Rk2IsLabel K lab) {B : ℕ}
    (hB : ∀ m, 1 ≤ m → (lab.n = 1 → 2 ≤ m) → rk2Mult lab m ≤ B) : evenRank K ≤ B := by
  show sSup {k | ∃ (q : ℕ) (H : Subgroup K), q.Prime ∧ q ≠ 2 ∧ IsTwoLocal H ∧
    CFSG.Open.pRank q H = k} ≤ B
  refine csSup_le' ?_
  rintro k ⟨q, H, hq, hq2, -, rfl⟩
  have h1 := CFSG.SectionRank.pRank_mono hq.one_lt (le_top : H ≤ ⊤)
  have h2 := hK K lab q hL hq hq2
  have hpos := rk2Ord_pos hq hq2 lab.n
  refine h1.trans (h2.trans (hB _ hpos fun hn1 => ?_))
  have h3 := rk2Ord_one_ne_one (p := q) hq
  have h4 := rk2Ord_pos hq hq2 1
  rw [hn1]
  omega

private theorem cnt_le_length (fs : List (ℕ × Bool)) (m : ℕ) : rk2Cnt fs m ≤ fs.length := by
  unfold rk2Cnt
  exact List.countP_le_length

private theorem bd_le {lab : GLALabel} (ht : lab.tag = .B ∨ lab.tag = .D) {m : ℕ} (hm : 1 ≤ m) :
    rk2Mult lab m ≤ lab.rank := by
  have h1 : lab.rank / m ≤ lab.rank := Nat.div_le_self _ _
  have h2 : m % 2 = 0 → 2 * lab.rank / m ≤ lab.rank := fun h => by
    have hm2 : 2 ≤ m := by omega
    calc 2 * lab.rank / m ≤ 2 * lab.rank / 2 := Nat.div_le_div_left hm2 (by norm_num)
      _ = lab.rank := by omega
  rcases ht with ht | ht
  · simp only [rk2Mult, ht]
    split_ifs with h
    · exact h2 h
    · exact h1
  · simp only [rk2Mult, ht]
    split_ifs with h h'
    · have := h2 h; omega
    · exact h2 h
    · exact h1

theorem rk2_eUpAt_of_tables (hK : Rk2KRank) (hU : Rk2Upper) {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hL : Rk2IsLabel K lab) :
    Rk2EUpAt lab (Subgroup.center K = ⊥) (evenRank K) := by
  have h1 := hU.1 K lab hL
  refine ⟨?_, ?_, ?_, ?_, h1.1, h1.2.1, ?_, ?_, h1.2.2.1, h1.2.2.2⟩
  · intro ht hn
    exact rk2_evenRank_le hK hL fun m hm _ => bd_le ht hm
  · intro ht hn
    refine rk2_evenRank_le hK hL (B := 4) fun m hm _ => ?_
    simp only [rk2Mult, ht]
    exact cnt_le_length _ _
  · intro ht hn
    refine rk2_evenRank_le hK hL (B := 7) fun m hm _ => ?_
    simp only [rk2Mult, ht]
    exact cnt_le_length _ _
  · intro ht hn
    refine rk2_evenRank_le hK hL (B := 8) fun m hm _ => ?_
    simp only [rk2Mult, ht]
    exact cnt_le_length _ _
  · intro h
    subst h
    refine rk2_evenRank_le hK hL (B := 4) fun m hm h1 => ?_
    have hm2 := h1 rfl
    have hm1 : m ≠ 1 := by omega
    simp only [rk2Mult, hm1, ↓reduceIte]
    calc (8 + 1) / m ≤ (8 + 1) / 2 := Nat.div_le_div_left hm2 (by norm_num)
      _ = 4 := by norm_num
  · intro h
    subst h
    refine rk2_evenRank_le hK hL (B := 4) fun m hm h1 => ?_
    exact rk2Cnt_E6_le_four (h1 rfl)

end CFSG.LocalAnalysis.GLTheoremA
