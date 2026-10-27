module

public import CFSG.CGT.Timmesfeld75.Sec63Comm
public import CFSG.CGT.Timmesfeld75.Sec63Close
public import CFSG.CGT.Timmesfeld75.Sec63Numeric
public import CFSG.CGT.Timmesfeld75.Sec63Wlog

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem sec63_of_a6 (h215 : Lemma215Stmt) (h26 : Lemma26Input) (h48 : Sec48) (h62 : Sec62)
    (hA : Sec63A6) : Sec63 := by
  intro G _ T T₁ n m hc x hx hxT
  have hfin := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hlt := lt_of_le_of_ne (hc.card_centralizer_le hx hxT) hne1
  have hbig := hc.big_of_card_lt hx hlt fun ⟨h1, h2, h3⟩ => hne2 h1 h2 h3
  obtain ⟨g, hxg⟩ := exists_mem_conj_of_mem_classD hx.1
  have cfg : Sec63Cfg T T₁ n m x (conjSubgroup g T) := ⟨hc, hbig, hx, hxT, hlt, ⟨g, rfl⟩, hxg⟩
  obtain ⟨k, hk, hW⟩ := cfg.exists_conj_pGroup_sup
  exact sec63_core h215 h26 hA (hc.conj_normalizer hk) (cfg.conj_normalizer hk)
    ((cfg.conj_normalizer hk).nonempty_F h48 h62 hW)

end CFSG.CGT.Timmesfeld75
