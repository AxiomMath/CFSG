module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
import CFSG.ClassicalInvolution.Asc77.AscT8SetupEng
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

variable {p f : ℕ} [Fact p.Prime]

theorem c27_nbr_proved : C27_nbr p f := by
  intro G _ _ _ Ω K hs hedge
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  exact c27_nbrE hΩ.conjInvariant (fun hA hB h => T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hA hB h)
    hs.trans hedge

theorem c27_setup_proved : C27_setup p f := by
  intro G _ _ _ Ω K hs hnt _ z hz J hJ t ht
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  obtain ⟨S, R, T, W, hR, hT, hW⟩ := c27_setupE hs.mem hJ
    (fun hM hR hRM => T3.isSylow2In_of_mem_RSet_of_le hp hΩ hM hR hRM)
    (fun S => (l6_9_proved p f hp hq G Ω hΩ S).1)
  exact ⟨S, R, T, W,
    { stand := hs, noTwins := hnt, hz := hz, hJ := hJ, ht := ht, hR := hR, hT := hT, hW := hW }⟩

end CFSG.ClassicalInvolution.Asc77
