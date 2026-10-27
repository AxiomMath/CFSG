module

public import CFSG.Certificates.Kernel.LocalQTR9K4041Sound
public import CFSG.Certificates.Kernel.LocalQTR9K4145Sound
public import CFSG.Certificates.Kernel.LocalQTR9K4048Sound
public import CFSG.Certificates.Kernel.LocalQTR9K4056Sound

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1

theorem s4041 (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (x1 u0 d2 : R9) (Tl : List R9)
    {X1 U0 D2 : ℕ} {TL w2 : List ℕ}
    {cent : List (List ℕ)} (hx : codeR x1 = X1) (hu : codeR u0 = U0) (hd : codeR d2 = D2)
    (ht : Tl.map codeR = TL) (hk : c4041 X1 U0 D2 TL w2 cent = true)
    (hs : ∀ c < 20, allSLc c (sl4041 X1 U0 D2 TL w2 cent) = true) :
    let I := L.filter fun r => r != rone && rmul r r == rone
    (∀ r ∈ L, rmul r x1 ≠ rmul (rcof x1) r)
    ∧ (∀ r ∈ L, rmul r (rcof r) = rone →
          ∃ h ∈ L, rmul r (rcof h) = h)
    ∧ (∀ r ∈ L, (∀ t ∈ Tl, rmul r (rcof t) = rmul t r) → rmul r (rcof r) = u0)
    ∧ (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, rmul a b = rmul b a → rmul a c = rmul c a →
          rmul b c = rmul c b → a ≠ b → c ≠ a → c ≠ b → c ≠ rmul a b → False)
    ∧ (∀ a ∈ I, ∀ b ∈ I, a ≠ b → rmul a b = rmul b a →
          ∃ g ∈ L, rmul g u0 = rmul a g ∧ rmul g d2 = rmul b g)
    ∧ (∀ r ∈ L, rmul r u0 = rmul u0 r → rmul r d2 = rmul d2 r →
          r = rone ∨ r = u0 ∨ r = d2 ∨ r = rmul u0 d2)
    ∧ (rmul d2 d2 = rone ∧ rmul u0 d2 = rmul d2 u0 ∧ d2 ≠ rone ∧ u0 ≠ d2 ∧
          rcof u0 = u0 ∧ rcof d2 = d2) := by
  exact s4041k L hL x1 u0 d2 Tl hx hu hd ht hk hs

theorem s4145 (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (u0 a b : S3) (Tl : List S3) (Ws : List (List Bool)) {U0 A B : ℕ}
    {TL wu : List ℕ} (hu : codeR (rr u0) = U0) (ha : codeR (rr a) = A) (hb : codeR (rr b) = B)
    (ht : (Tl.map rr).map codeR = TL)
    (hk : c4145 U0 A B TL Ws wu = true) (hs : ∀ c < 20, allSLc c (sl4145 U0 TL wu) = true) :
    (u0 ≠ 1)
    ∧ (u0 ^ 2 = 1)
    ∧ (Fintype.card S3 = 5616)
    ∧ (∀ r ∈ L,
          (((rmul r (rr u0) = rmul (rr u0) r ∧ rmul r (rmul r r) = rone) ↔ r ∈ Tl.map rr) ∧
            (rmul r (rr u0) = rmul (rr u0) r → (∀ t ∈ Tl.map rr, rmul t r = rmul r t) →
              r = rone ∨ r = rr u0) ∧
            ((∀ t ∈ Tl.map rr, rmul r t = rmul t r) → r = rone ∨ r = rr u0)))
    ∧ (∀ u ∈ L, u ≠ rone → rmul u u = rone →
          ∃ g ∈ L, rmul g (rr u0) = rmul u g)
    ∧ (∀ t ∈ Tl, ∃ w ∈ Ws, t = evB a b w)
    ∧ (u0 = evB a b [true, false, true, false])
    ∧ (a ≠ 1 ∧ b ≠ 1 ∧ (a * b) ^ 2 ≠ 1 ∧ (a * b) ^ 4 = 1)
    ∧ (((Tl.product Tl).filter
          (fun p => decide (p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ (p.1 * p.2) ^ 2 ≠ 1 ∧ (p.1 * p.2) ^ 4 = 1))).length
        ≤ 24) := by
  exact s4145k L hL u0 a b Tl Ws hu ha hb ht hk hs

open CFSG.QuasithinUnique.Unc25L33 in
theorem s4048 (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (sa sb : R9) (P0 W : List R9) {SA SB : ℕ} {LP LI LW PR : List ℕ}
    (ha : codeR sa = SA) (hb : codeR sb = SB) (hp : P0.map codeR = LP) (hw : W.map codeR = LW)
    (hk : c4048 SA SB LP LI LW PR = true)
    (hs : ∀ c < 20, allSLc c (sl4048 SA SB LP LI PR) = true) :
    let I := P0.filter fun x => x != rone && rmul x x == rone
    (rdet sa = 1 ∧ rdet sb = 1 ∧ rpw sa 8 = rone ∧ rmul sb sb = rone ∧
            rmul sb sa = rmul (rpw sa 3) sb ∧ P0.Nodup ∧ P0.length = 16 ∧ rone ∈ P0 ∧ sa ∈ P0 ∧
            sb ∈ P0 ∧ (∀ x ∈ P0, ∀ y ∈ P0, rmul x y ∈ P0) ∧ (∀ x ∈ P0, rpw x 16 = rone) ∧
            (∀ w ∈ W, rdet w = 1) ∧
            (∀ t ∈ I, ∀ s ∈ I, t ≠ s → rmul t s = rmul s t →
              ∃ w ∈ W, rpw w 3 = rone ∧ w ≠ rone ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w t = rmul u w) ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w s = rmul u w)))
    ∧ (∀ g ∈ L,
          (∃ p ∈ P0, rmul g sa = rmul p g) → (∃ q ∈ P0, rmul g sb = rmul q g) → g ∈ P0)
    ∧ (∀ g ∈ L, ∀ t ∈ I, ∀ s ∈ I, rmul g t = rmul t g → rmul g s = rmul s g → t ≠ s →
          rmul t s = rmul s t → g = rone ∨ g = t ∨ g = s ∨ g = rmul t s)
    ∧ (∀ g ∈ L, ∀ t ∈ I, ∀ s ∈ I, rmul g (rcof t) = rmul t g →
          rmul g (rcof s) = rmul s g → t ≠ s → rmul t s = rmul s t →
          (∃ p ∈ P0, rmul g (rcof sa) = rmul p g) ∧ (∃ q ∈ P0, rmul g (rcof sb) = rmul q g))
    ∧ (∀ g ∈ L,
          ¬ (rmul g (rcof sa) = rmul sa g ∧ rmul g (rcof sb) = rmul sb g)) := by
  exact s4048k L hL sa sb P0 W ha hb hp hw hk hs

open CFSG.QuasithinUnique.Fin253 in
theorem s4056 (M : ListModel S3 R9) (hm : M.mul = rmul) (h1 : M.one = rone) (hi : M.inv = rinv)
    (hL : ∀ r, r ∈ M.elems ↔ rdet r = 1) (hn : M.elems.Nodup) {G R WO WT S0 C0 : List ℕ}
    {CI : List (List ℕ)} {T0 : ℕ}
    (hk : c4056 G R WO CI T0 WT S0 C0 = true)
    (hs : ∀ c < 20, allSLc c (sl4056 G R WO CI T0 WT S0 C0) = true) :
    let I := M.elems.filter fun t => decide (t ≠ M.one ∧ M.mul t t = M.one)
    let O := M.elems.filter fun u => decide (lpow M.mul M.one u 4 = M.one ∧
      lpow M.mul M.one u 2 ≠ M.one)
    (CenterOK M.mul M.one M.elems)
    ∧ (OddOK M.mul M.one 351 M.elems I O)
    ∧ (QuatAll M.mul M.one M.elems I)
    ∧ (CoreAll M.mul M.one M.inv M.elems I) := by
  exact s4056k M hm h1 hi hL hn hk hs

end CFSG.KC.LQT.R

end
