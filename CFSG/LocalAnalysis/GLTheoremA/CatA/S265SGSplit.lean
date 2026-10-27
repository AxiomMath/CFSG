module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def QSF3Gen : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 → False

@[expose] def QSF3U38 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 K) S9.isU3eight → Nat.card B = 3 ^ 5 → False

theorem qsFamF3_of_parts (hG : QSF3Gen) (hU : QSF3U38) : QSFamF3 := by
  intro p Ω _ _ S B T x D K hN hp hty
  subst hp
  rcases SG.card_eq_of_tyF hN hty with h4 | ⟨hU38, h5⟩
  · exact (hG Ω S B T x D K hN hty h4).elim
  · exact (hU Ω S B T x D K hN hU38 h5).elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end
