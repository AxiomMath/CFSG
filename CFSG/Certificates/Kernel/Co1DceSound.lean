module

public import Certificates.Data.Kernel.Co1Dce
import CFSG.Certificates.Kernel.Co1DceCover
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Certificates.Co1D

open CFSG.KC CFSG.KC.DceS

@[expose] noncomputable def rval {G : Type*} [Group G] (x : ℕ → G) (e : ℕ) : G :=
  ((List.range (rN e)).map fun q => x (wLet (rW e) q)).prod

@[expose] noncomputable def wcode (LT : ℕ → ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc c => pmul acc (Nat.land (LT c) m64)) idP

theorem dceOk_sound {blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : ℕ → ℕ}
    {NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
      hL hH hO hR hD P : ℕ}
    {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR
      IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0 X1 = true)
    (hN : 0 < nN)
    {G : Type*} [Group G] (x : ℕ → G)
    (hrels : ∀ r < NR, rval x (RT r) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wcode LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wcode LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod) :
    Finite (Subgroup.closure (x '' {c | c < NL})) ∧
      Nat.card (Subgroup.closure (x '' {c | c < NL})) ≤ nN * SUMIDX :=
  dceOk_bound h hN x hrels hρ hT

end CFSG.Certificates.Co1D

end
