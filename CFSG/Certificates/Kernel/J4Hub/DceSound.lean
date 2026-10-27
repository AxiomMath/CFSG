module

public import CFSG.Certificates.Kernel.J4RunSound

public section

namespace CFSG.Certificates.J4R

open CFSG.KJ4 CFSG.KJ4.R CFSG.KJ4.S CFSG.Sporadic.J4.Struct

@[expose] def dElt {G : Type*} [Group G] (x y : G) : G := (y * x) ^ 4 * y⁻¹ * x

@[expose] def zElt {G : Type*} [Group G] (x y t : G) : G := (y * ((dElt x y)⁻¹ * t * dElt x y)) ^ 3

@[expose] def dchBD (k : KD) (i : ℕ) : ℕ := (k.DCH.getD i (fun _ => 0, (0, ([], 0)))).2.2.2

theorem j4Ok_dc_sound {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} {PL : List ℕ}
    (h : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (hpts : j4Pts k PL = true)
    (hmfix : j4MFix k d = true) (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hfit : k.sw < 256 ^ k.sn ∧ wW k.PAW < 256 ^ wN k.PAW ∧ wN k.PAW + wN k.PBW + 2 < 65536)
    (hN : ∀ (H : Type) [Group H] (a b : H),
      (∀ r < 12, nOnly (wW (k.RT r)) (wN (k.RT r)) → wval (lets a b 1) (wW (k.RT r)) (wN (k.RT r)) = 1) →
      Finite (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) ≤ k.BN)
    {G : Type} [Group G] (x y t : G) (ht : t * t = 1)
    (hR : ∀ r < 12, wval (lets x y t) (wW (k.RT r)) (wN (k.RT r)) = 1) :
    Finite (Subgroup.closure {x, y, t}) ∧
      Nat.card (Subgroup.closure {x, y, zElt x y t}) ≤ k.BK ∧
      ∃ wr : ℕ → G, (∀ i, wr i ∈ Subgroup.closure {x, y, t}) ∧
        (∀ g ∈ Subgroup.closure {x, y, t}, g ∈ Subgroup.closure {x, y, zElt x y t} ∨
          ∃ i < k.DCH.length, g ∈ dcSet (Subgroup.closure {x, y, zElt x y t}) (wr i)) ∧
        ∀ i < k.DCH.length,
          (dcSet (Subgroup.closure {x, y, zElt x y t}) (wr i)).ncard * dchBD k i ≤
            Nat.card (Subgroup.closure {x, y, zElt x y t}) * k.BK := by
  have e : zElt x y t = CFSG.KJ4.MLevel.zv x y t := by
    rw [CFSG.KJ4.Asm.zv_eq]
    rfl
  rw [e]
  exact CFSG.KJ4.Asm.dc_bound h hfix hpts hmfix hL (relN_of_wval hN) hfit.1 hfit.2.1 hfit.2.2 x y t ht
    (rv_of_wval (CFSG.KJ4.Asm.j4Ok_kRange h) x y t hR)

end CFSG.Certificates.J4R

end
