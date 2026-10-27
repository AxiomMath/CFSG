module

public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.BindAProof

public section

namespace CFSG.Certificates.BindA

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE

theorem relsA_sound {G : Type*} [Group G] (pg cval : ℕ → G) {cn cw PRT : ℕ → ℕ} {SB ns M mul R PR Hs : ℕ}
    (h : relsA cn cw PRT SB ns M mul R PR Hs = true)
    (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hinv : ∀ g, pg g * pg g = 1)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, wLen (PRT r) < 256 ∧ ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254)
    (hM : ∀ g < 127, mget M g < 255 → mul * mget M g < 256 ∧ cval (mul * mget M g) = pg g) :
    ∀ r < R, ((List.range (cn r)).map fun q => cval (wLet (cw r) q)).prod = 1 :=
  CFSG.Certificates.BindL.relsA_sound' pg cval h hsub hSB hinv hP hPL hM

theorem levelOK_sound {G : Type*} [Group G] (pg : ℕ → G) {ST PRT : ℕ → ℕ} {S Q n K SB ns PR : ℕ}
    (h : levelOK ST PRT S Q n K SB ns = true) (hS : S = stMap ST K) (h0 : S ≠ 0)
    (hIQ : invMap Q n ≠ 0)
    (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    Subgroup.closure ((fun j => bval pg (wWord (ST j)) (wLen (ST j))) '' {j | j < K}) =
      Subgroup.closure ((fun c => pg (mget Q c)) '' {c | c < n}) :=
  CFSG.Certificates.BindL.levelOK_sound' pg h hS h0 hIQ hsub hSB hP hPL

end CFSG.Certificates.BindA

end
