module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def QSFamDL28 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyL28 → QSConcl p S B D K

@[expose] def QSFamDU38 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyU38 → QSConcl p S B D K

theorem qsFamD_of_parts (hL : QSFamDL28) (hU : QSFamDU38) : QSFamD := by
  intro p Ω _ _ S B T x D K hN hp3 hD
  rcases tyD_split hD with hL28 | hU38
  · exact hL p Ω S B T x D K hN hp3 hL28
  · exact hU p Ω S B T x D K hN hp3 hU38

private theorem s265d_primePower_p {q : TauCeti.PrimePower} {r s : ℕ} (hr : r.Prime) (hs : 0 < s)
    (h : q.card = r ^ s) : q.p = r := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [hm, hk] at h
  exact (Nat.Prime.pow_inj q.prime_p hr h).1

private theorem s265d_tyU38_imp_tyF (i : TauCeti.CFSGIndex) (h : tyU38 i) : tyF 3 i := by
  rcases i with _ | _ | ⟨⟨l, hl⟩⟩ | _
  · exact (h : False).elim
  · exact (h : False).elim
  · cases l with
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact (h : False).elim
      · exact (h : False).elim
      · have hq : q.card = 8 := h
        refine ⟨rfl, s265d_primePower_p Nat.prime_two (s := 3) (by norm_num) (hq.trans (by norm_num)),
          ?_⟩
        rw [hq]
        norm_num
      · exact (h : False).elim
    | _ => exact (h : False).elim
  · exact (h : False).elim

theorem qsFamDU38_of_qsFamF3 (h : QSFamF3) : QSFamDU38 := by
  intro p Ω _ _ S B T x D K hN hp3 hU
  subst hp3
  exact h 3 Ω S B T x D K hN rfl (catalogIs_imp s265d_tyU38_imp_tyF hU)

theorem qsFamD_of_L28_of_qsFamF3 (hL : QSFamDL28) (h : QSFamF3) : QSFamD :=
  qsFamD_of_parts hL (qsFamDU38_of_qsFamF3 h)

theorem qsFamDU38_of_qsFamF (h : QSFamF) : QSFamDU38 := by
  intro p Ω _ _ S B T x D K hN hp3 hU
  subst hp3
  exact h 3 Ω S B T x D K hN (catalogIs_imp s265d_tyU38_imp_tyF hU)

theorem qsFamD_of_L28_of_qsFamF (hL : QSFamDL28) (h : QSFamF) : QSFamD :=
  qsFamD_of_parts hL (qsFamDU38_of_qsFamF h)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
