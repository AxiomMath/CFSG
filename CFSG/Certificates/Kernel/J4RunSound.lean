module

public import CFSG.Certificates.Kernel.J4.AsmSound

public section

namespace CFSG.Certificates.J4R

open CFSG.KJ4 CFSG.KJ4.R CFSG.KJ4.S

@[expose] noncomputable def wval {G : Type*} [Group G] (ℓ : ℕ → G) (w n : ℕ) : G :=
  ((List.range n).map fun i => if wLet w i = 255 then 1 else ℓ (wLet w i)).prod

@[expose] noncomputable def lets {G : Type*} [Group G] (x y t : G) (c : ℕ) : G :=
  if c = 0 then x else if c = 1 then x⁻¹ else if c = 2 then y else if c = 3 then y⁻¹
  else if c = 4 then t else 1

@[expose] def nOnly (w n : ℕ) : Prop := ∀ i < n, wLet w i < 4

theorem rv_of_wval {k : KD} (hRg : kRange k = true) {G : Type*} [Group G] (x y t : G)
    (hR : ∀ r < 12, wval (lets x y t) (wW (k.RT r)) (wN (k.RT r)) = 1) :
    ∀ r < 12, CFSG.Certificates.J4KShape.rv (CFSG.Certificates.J4Words.jv x y t 1) (k.RT r) = 1 := by
  intro r hr
  rw [CFSG.KJ4.Models.rv_eq_prod, ← hR r hr]
  unfold wval
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  have h5 := CFSG.KJ4.Asm.kRange_lets hRg r hr i (List.mem_range.1 hi)
  generalize wLet (wW (k.RT r)) i = c at h5 ⊢
  interval_cases c <;> simp [CFSG.Certificates.J4Words.jv, lets]

theorem relN_of_wval {k : KD}
    (hN : ∀ (H : Type) [Group H] (a b : H),
      (∀ r < 12, nOnly (wW (k.RT r)) (wN (k.RT r)) → wval (lets a b 1) (wW (k.RT r)) (wN (k.RT r)) = 1) →
      Finite (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) ≤ k.BN) :
    ∀ (H : Type) [Group H] (a b : H), CFSG.KJ4.Models.relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN := by
  intro H _ a b hab
  refine hN H a b fun r hr hno => ?_
  have h1 := hab r hr hno
  rw [CFSG.KJ4.Models.rv_eq_prod] at h1
  rw [← h1]
  unfold wval
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  have h4 := hno i (List.mem_range.1 hi)
  generalize wLet (wW (k.RT r)) i = c at h4 ⊢
  interval_cases c <;> simp [CFSG.Certificates.J4Words.jv, lets]

theorem j4Ok_sound' {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} {PL : List ℕ}
    (h : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (hpts : j4Pts k PL = true)
    (hmfix : j4MFix k d = true) (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hfit : k.sw < 256 ^ k.sn ∧ wW k.PAW < 256 ^ wN k.PAW ∧ wN k.PAW + wN k.PBW + 2 < 65536)
    (hN : ∀ (H : Type) [Group H] (a b : H),
      (∀ r < 12, nOnly (wW (k.RT r)) (wN (k.RT r)) → wval (lets a b 1) (wW (k.RT r)) (wN (k.RT r)) = 1) →
      Finite (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) ≤ k.BN)
    {G : Type} [Group G] (x y t : G) (ht : t * t = 1)
    (hR : ∀ r < 12, wval (lets x y t) (wW (k.RT r)) (wN (k.RT r)) = 1) :
    Finite (Subgroup.closure {x, y, t}) ∧ Nat.card (Subgroup.closure {x, y, t}) ≤ k.BK * idxSum k :=
  CFSG.KJ4.Asm.card_bound h hfix hpts hmfix hL (relN_of_wval hN) hfit.1 hfit.2.1 hfit.2.2 x y t ht
    (rv_of_wval (CFSG.KJ4.Asm.j4Ok_kRange h) x y t hR)

end CFSG.Certificates.J4R

end
