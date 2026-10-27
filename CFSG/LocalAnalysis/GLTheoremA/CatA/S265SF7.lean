module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265


theorem qsFamF_of_low (h5 : QSFamF5U) (h3 : QSFamF3) : QSFamF := by
  intro p Ω _ _ S B T x D K hN hF
  rcases eq_or_ne p 3 with rfl | hp3
  · exact h3 3 Ω S B T x D K hN rfl hF
  have hp := hN.cfg.prime
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have := hN.cfg.odd
    omega
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := hN.cfg.std
  have hle : ∀ {R : Type} [Group R] (X : Subgroup (MulAut R)),
      Nat.card B = Nat.card D * Nat.card X → Nat.card X ≤ p ^ (p / p + 1) →
        Nat.card B ≤ p ^ 4 := fun X hBX hX => by
    rw [Nat.div_self hp.pos] at hX
    rw [hBX, hDcard, show p ^ 4 = p ^ 2 * p ^ (1 + 1) by ring]
    exact Nat.mul_le_mul_left _ hX
  rcases catalogIs_tyF hF with hL | hU
  · exfalso
    obtain ⟨F, _, _, _, hpF, ⟨θ⟩⟩ := SF.exists_psl_model hKcomp.2.2 hL
    obtain ⟨X, hX, hBX, hnl⟩ := SF.exists_aut_nl hN θ
    have h1 := (SF.pow_self_le_card_of_tyFLin hN hp5 hL).trans
      (hle X hBX (SF.card_le_of_nl_linear (by omega) hp hN.cfg.odd hpF hX hnl))
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  · rcases eq_or_ne p 5 with rfl | hp5'
    · exact h5 5 Ω S B T x D K hN rfl hU
    exfalso
    obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hU
    obtain ⟨X, hX, hBX, hnl⟩ := SF.exists_aut_nl hN θ
    have hq : 3 < 2 ^ m := by
      have := Nat.le_of_dvd (by positivity) hpm
      omega
    have h1 := (SF.pow_sub_one_le_card_of_tyFUni hN hU).trans
      (hle X hBX (SF.card_le_of_nl_unitary hFd (by omega) hp hq hpm hX hnl))
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265

end
