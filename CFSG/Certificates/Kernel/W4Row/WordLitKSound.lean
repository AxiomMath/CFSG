module

public import Certificates.Data.Kernel.W4Row.WordLitK
public import CFSG.Certificates.Kernel.LocalQTTcPSound
public import CFSG.Certificates.Kernel.LocalQTTcPProved

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.LQT.TCK
  CFSG.QuasithinUnique.Setup.X1

variable {n w : ℕ}

theorem wordLit_of (hn : n < 2 ^ 32) (hid : idK n w (mask w) = true) {G GI : List ℕ}
    (hl : G.length = GI.length) (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true)
    {wd : List ℤ} {Y YI : ℕ} (h : wordLitK n w G GI wd Y YI = true) :
    PrP n w (pWord n (unpackP n w G GI) wd) Y YI := by
  unfold wordLitK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  obtain ⟨g, hg, hY⟩ := wordTc_sound hn (rp_idn hid) hl hz wd
  rw [Nat.eq_of_beq_eq_true h1] at hY
  obtain ⟨g', -, hs, hsi⟩ := rs_of_permOK h2
  obtain rfl := rp_unique hY hs.1
  exact ⟨g, hg, hs, hsi⟩

end CFSG.KC.W4E

end
