module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import Certificates.Data.Kernel.W4C1K
public import CFSG.GF2Type.Smith1979.W4C1Check

public section

namespace CFSG.KC.W4C1

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KD.W4C1 CFSG.KC.Loop
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.GF2Type.Smith1979.W4C1

abbrev Enc (a : List ℕ) (A : ℕ) : Prop := canon6 a = true ∧ pk a = A

theorem eqE {a b : List ℕ} {A B : ℕ} (ha : Enc a A) (hb : Enc b B) : (a == b) = Nat.beq A B := by
  rw [beq_pk ha.1 hb.1, ha.2, hb.2]

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem all_syG {G : ℕ → ℕ} (hg : ∀ s < 5, Enc (syG.getD s []) (G s)) {f : List ℕ → Bool}
    {F : ℕ → Bool} (hf : ∀ s S, Enc s S → f s = F S) : syG.all f = all5 G F := by
  have e : syG.all f = (f (syG.getD 0 []) && (f (syG.getD 1 []) && (f (syG.getD 2 []) &&
      (f (syG.getD 3 []) && (f (syG.getD 4 []) && true))))) := rfl
  rw [e, hf _ _ (hg 0 (by decide)), hf _ _ (hg 1 (by decide)), hf _ _ (hg 2 (by decide)),
    hf _ _ (hg 3 (by decide)), hf _ _ (hg 4 (by decide))]
  rfl

variable {G : ℕ → ℕ} (hg : ∀ s < 5, Enc (syG.getD s []) (G s))
include hg

theorem centralInv_eq {z : List ℕ} {Z : ℕ} (hz : Enc z Z) : centralInv z = cInvF G Z := by
  unfold centralInv cInvF
  rw [all_syG hg (f := fun s => mul6 s z == mul6 z s) (F := fun S => Nat.beq (MULF S Z) (MULF Z S))
      (fun s S hs => eqE (mulE hs hz) (mulE hz hs)),
    eqE (mulE hz hz) one_pk, eqE hz one_pk]

theorem condX_eq {z x : List ℕ} {Z X : ℕ} (hz : Enc z Z) (hx : Enc x X) :
    condX z x = condXF G Z X := by
  unfold condX condXF
  rw [all_syG hg (f := fun s => mul6 s x == mul6 x s || mul6 s x == mul6 (mul6 x z) s)
      (F := fun S => Nat.beq (MULF S X) (MULF X S) || Nat.beq (MULF S X) (MULF (MULF X Z) S))
      (fun s S hs => by
        rw [eqE (mulE hs hx) (mulE hx hs), eqE (mulE hs hx) (mulE (mulE hx hz) hs)]),
    eqE (mulE hx hx) one_pk, eqE hx one_pk, eqE hx hz, eqE (mulE hx hz) (mulE hz hx)]

theorem condY_eq {z x y : List ℕ} {Z X Y : ℕ} (hz : Enc z Z) (hx : Enc x X) (hy : Enc y Y) :
    condY z x y = condYF G Z X Y := by
  unfold condY condYF
  rw [all_syG hg (f := fun s => mul6 s y == mul6 y s || mul6 s y == mul6 (mul6 y z) s ||
        mul6 s y == mul6 (mul6 y x) s || mul6 s y == mul6 (mul6 y (mul6 x z)) s)
      (F := fun S => Nat.beq (MULF S Y) (MULF Y S) || Nat.beq (MULF S Y) (MULF (MULF Y Z) S) ||
        Nat.beq (MULF S Y) (MULF (MULF Y X) S) ||
        Nat.beq (MULF S Y) (MULF (MULF Y (MULF X Z)) S))
      (fun s S hs => by
        rw [eqE (mulE hs hy) (mulE hy hs), eqE (mulE hs hy) (mulE (mulE hy hz) hs),
          eqE (mulE hs hy) (mulE (mulE hy hx) hs),
          eqE (mulE hs hy) (mulE (mulE hy (mulE hx hz)) hs)]),
    eqE (mulE hy hy) one_pk, eqE hy one_pk, eqE hy hz, eqE hy hx, eqE hy (mulE hx hz),
    eqE (mulE hy hz) (mulE hz hy), eqE (mulE hy hx) (mulE hx hy)]

omit hg in
theorem inT8_eq {z x y w : List ℕ} {Z X Y W : ℕ} (hz : Enc z Z) (hx : Enc x X) (hy : Enc y Y)
    (hw : Enc w W) : inT8 z x y w = inT8F Z X Y W := by
  unfold inT8 inT8F
  rw [eqE hw (mulE hy (mulE hx hz)), eqE hw (mulE hy hx), eqE hw (mulE hy hz),
    eqE hw (mulE hx hz), eqE hw one_pk, eqE hw hz, eqE hw hx, eqE hw hy]

omit hg in
theorem mem_tab {T : Array (List ℕ)} {n : ℕ} (hT : T.size = n) {z : List ℕ} (hz : z ∈ T.toList) :
    ∃ t < n, T.getD t [] = z := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, hT ▸ ht, by simp [Array.getD, ht]⟩

theorem chainOK_of {R : ℕ → ℕ} {o W hi : ℕ} (hS : syT.size = 512)
    (hr : ∀ t < 512, Enc (syT.getD t []) (recX R o t)) (hw : Enc w2C W) (hm : 512 ≤ 64 * hi)
    (h : chainK R o G W hi = true) : chainOK = true := by
  unfold chainOK
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_tab hS hz
  have h1 := CFSG.KC.G2Three.allBelow_g2 h hm a ha
  simp only [letB_eq, chainZ] at h1
  rw [centralInv_eq hg (hr a ha)]
  cases hc : cInvF G (recX R o a)
  · rfl
  rw [hc, Bool.not_true, Bool.false_or] at h1
  rw [Bool.not_true, Bool.false_or, List.all_eq_true]
  intro x hx
  obtain ⟨b, hb, rfl⟩ := mem_tab hS hx
  have h2 := CFSG.KC.G2Three.allBelow_g2 h1 hm b hb
  simp only [letB_eq, chainX] at h2
  rw [condX_eq hg (hr a ha) (hr b hb)]
  cases hc2 : condXF G (recX R o a) (recX R o b)
  · rfl
  rw [hc2, Bool.not_true, Bool.false_or] at h2
  rw [Bool.not_true, Bool.false_or, List.all_eq_true]
  intro y hy
  obtain ⟨c, hc3, rfl⟩ := mem_tab hS hy
  have h3 := CFSG.KC.G2Three.allBelow_g2 h2 hm c hc3
  rw [condY_eq hg (hr a ha) (hr b hb) (hr c hc3), inT8_eq (hr a ha) (hr b hb) (hr c hc3) hw]
  exact h3

omit hg in
theorem contains_of {T : Array (List ℕ)} {R : ℕ → ℕ} {o n i : ℕ} {w : List ℕ} (hT : T.size = n)
    (hr : ∀ t < n, Enc (T.getD t []) (recX R o t)) (hi : i < n) (hw : Enc w (recX R o i)) :
    T.contains w = true := by
  have e : T.getD i [] = w := pk_inj (hr i hi).1 hw.1 (by rw [(hr i hi).2, hw.2])
  have hi' : i < T.size := by rw [hT]; exact hi
  rw [Array.contains_iff_mem, ← e]
  simp only [Array.getD, hi', dite_true]
  exact Array.getElem_mem hi'

end CFSG.KC.W4C1

end
