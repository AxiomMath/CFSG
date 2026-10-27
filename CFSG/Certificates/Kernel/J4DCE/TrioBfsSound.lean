module

public import Certificates.Data.Kernel.J4DCE.TrioSteps
public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.ImgSound

public section

namespace CFSG.KC.J4DCE

open CFSG.Quasithin.H13.AS91.M24G

local notation "T3" => Nat × Nat × Nat

private abbrev jS : Type := Array T3 × Std.HashMap Nat Nat × Nat

private def jInner (t : T3) (g : Array Nat) (st : Array T3 × Std.HashMap Nat Nat) :
    Id (ForInStep (Array T3 × Std.HashMap Nat Nat)) :=
  if (!st.2.contains (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.imgTrioTab g t))) = true then
    pure (.yield (st.1.push (CFSG.J4DCE.Native.imgTrioTab g t),
      st.2.insert (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.imgTrioTab g t)) st.1.size))
  else pure (.yield (st.1, st.2))

private def jOuter (_ : Nat) (st : jS) : Id (ForInStep jS) :=
  if st.2.2 < st.1.size then do
    let r ← forIn [CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab] (st.1, st.2.1)
      (jInner st.1[st.2.2]!)
    pure (.yield (r.1, r.2, st.2.2 + 1))
  else pure (.done st)

private def jInit : jS :=
  (#[CFSG.J4DCE.Native.baseTrio ()],
    (∅ : Std.HashMap Nat Nat).insert (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.baseTrio ())) 0, 0)

private theorem bfsTrios_loop (fuel : Nat) :
    CFSG.J4DCE.Native.bfsTrios fuel = (Id.run (forIn (List.range' 0 fuel) jInit jOuter)).1 := by
  unfold CFSG.J4DCE.Native.bfsTrios
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private abbrev kS : Type := Array T3 × Array Nat × Array Nat × Std.HashMap Nat Nat × Nat

private def kInner (x : T3) (h : Nat) (s : T3 → T3) (st : kS) : Id (ForInStep kS) :=
  if (!st.2.2.2.1.contains (CFSG.J4DCE.Native.key (s x))) = true then
    pure (.yield (st.1.push (s x), st.2.1.push h, st.2.2.1.push st.2.2.2.2,
      st.2.2.2.1.insert (CFSG.J4DCE.Native.key (s x)) st.1.size, st.2.2.2.2 + 1))
  else pure (.yield (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 + 1))

private def kOuter (steps : List (T3 → T3)) (_ : Nat) (st : kS) : Id (ForInStep kS) :=
  if st.2.2.2.2 < st.1.size then do
    let t ← forIn steps (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0) (kInner st.1[st.2.2.2.2]! st.2.2.2.2)
    pure (.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, st.2.2.2.2 + 1))
  else pure (.done st)

private def kInit (base : T3) : kS :=
  (#[base], #[0], #[0], (∅ : Std.HashMap Nat Nat).insert (CFSG.J4DCE.Native.key base) 0, 0)

private theorem bfs_loop (steps : List (T3 → T3)) (base : T3) (fuel : Nat) :
    Native.bfs CFSG.J4DCE.Native.key steps base fuel =
      (let s := Id.run (forIn (List.range' 0 fuel) (kInit base) (kOuter steps))
       (s.1, s.2.1, s.2.2.1)) := by
  unfold Native.bfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def proj (st : kS) : jS := (st.1, st.2.2.2.1, st.2.2.2.2)

private theorem inner_sim (x : T3) (h : Nat) :
    ∀ (tabs : List (Array Nat)) (st : kS),
      ((Id.run (forIn (tabs.map CFSG.J4DCE.Native.imgTrioTab) st (kInner x h))).1,
        (Id.run (forIn (tabs.map CFSG.J4DCE.Native.imgTrioTab) st (kInner x h))).2.2.2.1) =
      Id.run (forIn tabs (st.1, st.2.2.2.1) (jInner x))
  | [], st => rfl
  | g :: tabs, st => by
    rw [List.map_cons, List.forIn_cons, List.forIn_cons]
    by_cases hc : (!st.2.2.2.1.contains
        (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.imgTrioTab g x))) = true
    · have e1 : kInner x h (CFSG.J4DCE.Native.imgTrioTab g) st =
          pure (.yield (st.1.push (CFSG.J4DCE.Native.imgTrioTab g x), st.2.1.push h,
            st.2.2.1.push st.2.2.2.2, st.2.2.2.1.insert
              (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.imgTrioTab g x)) st.1.size,
            st.2.2.2.2 + 1)) := if_pos hc
      have e2 : jInner x g (st.1, st.2.2.2.1) =
          pure (.yield (st.1.push (CFSG.J4DCE.Native.imgTrioTab g x), st.2.2.2.1.insert
              (CFSG.J4DCE.Native.key (CFSG.J4DCE.Native.imgTrioTab g x)) st.1.size)) := if_pos hc
      rw [e1, e2]
      exact inner_sim x h tabs _
    · have e1 : kInner x h (CFSG.J4DCE.Native.imgTrioTab g) st =
          pure (.yield (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 + 1)) := if_neg hc
      have e2 : jInner x g (st.1, st.2.2.2.1) = pure (.yield (st.1, st.2.2.2.1)) := if_neg hc
      rw [e1, e2]
      exact inner_sim x h tabs _

private theorem outer_sim :
    ∀ (l : List Nat) (st : kS),
      proj (Id.run (forIn l st (kOuter ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
        CFSG.J4DCE.Native.imgTrioTab)))) = Id.run (forIn l (proj st) jOuter)
  | [], st => rfl
  | i :: l, st => by
    rw [List.forIn_cons, List.forIn_cons]
    by_cases hlt : st.2.2.2.2 < st.1.size
    · have hi := inner_sim st.1[st.2.2.2.2]! st.2.2.2.2
        [CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab] (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
      have e1 : kOuter ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
          CFSG.J4DCE.Native.imgTrioTab) i st = pure (.yield
            ((Id.run (forIn ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
              CFSG.J4DCE.Native.imgTrioTab) (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
              (kInner st.1[st.2.2.2.2]! st.2.2.2.2))).1,
            (Id.run (forIn ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
              CFSG.J4DCE.Native.imgTrioTab) (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
              (kInner st.1[st.2.2.2.2]! st.2.2.2.2))).2.1,
            (Id.run (forIn ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
              CFSG.J4DCE.Native.imgTrioTab) (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
              (kInner st.1[st.2.2.2.2]! st.2.2.2.2))).2.2.1,
            (Id.run (forIn ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
              CFSG.J4DCE.Native.imgTrioTab) (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
              (kInner st.1[st.2.2.2.2]! st.2.2.2.2))).2.2.2.1,
            st.2.2.2.2 + 1)) := by
        simp only [kOuter, if_pos hlt]
        rfl
      have e2 : jOuter i (proj st) = pure (.yield
          ((Id.run (forIn [CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab] (st.1, st.2.2.2.1)
              (jInner st.1[st.2.2.2.2]!))).1,
            (Id.run (forIn [CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab] (st.1, st.2.2.2.1)
              (jInner st.1[st.2.2.2.2]!))).2, st.2.2.2.2 + 1)) := by
        have hlt' : (proj st).2.2 < (proj st).1.size := hlt
        simp only [jOuter, if_pos hlt']
        rfl
      rw [e1, e2, ← hi]
      exact outer_sim l _
    · have e1 : kOuter ([CFSG.J4DCE.Native.xTab, CFSG.J4DCE.Native.yTab].map
          CFSG.J4DCE.Native.imgTrioTab) i st = pure (.done st) := if_neg hlt
      have e2 : jOuter i (proj st) = pure (.done (proj st)) := if_neg hlt
      rw [e1, e2]
      rfl

theorem bfsTrios_eq (fuel : Nat) :
    CFSG.J4DCE.Native.bfsTrios fuel = (Native.bfs CFSG.J4DCE.Native.key
      [CFSG.J4DCE.Native.imgTrioTab CFSG.J4DCE.Native.xTab,
        CFSG.J4DCE.Native.imgTrioTab CFSG.J4DCE.Native.yTab]
      (CFSG.J4DCE.Native.baseTrio ()) fuel).1 := by
  rw [bfsTrios_loop, bfs_loop]
  have h := outer_sim (List.range' 0 fuel) (kInit (CFSG.J4DCE.Native.baseTrio ()))
  exact (congrArg Prod.fst h).symm

theorem imgTrioTab_eq (g : Array Nat) (hg : ∀ x ∈ g.toList, x < 24) :
    CFSG.J4DCE.Native.imgTrioTab g = CFSG.KC.M24G.imgTrioF g.toList := by
  funext t
  have hm : ∀ m, CFSG.J4DCE.Native.imgMaskTab g m = CFSG.KC.M24G.imgF
      (CFSG.KC.M24G.imgTab g.toList) m := fun m =>
    (rfl : CFSG.J4DCE.Native.imgMaskTab g m = Native.img g m).trans
      (CFSG.KC.M24G.img_eq_imgF g hg m)
  have hs : ∀ a b c, CFSG.J4DCE.Native.sort3 a b c = Native.sort3 a b c := fun _ _ _ => rfl
  simp only [CFSG.J4DCE.Native.imgTrioTab, CFSG.KC.M24G.imgTrioF, hm, hs]

theorem j4Steps_eq : [CFSG.J4DCE.Native.imgTrioTab CFSG.J4DCE.Native.xTab,
    CFSG.J4DCE.Native.imgTrioTab CFSG.J4DCE.Native.yTab] = j4StepsF := by
  rw [imgTrioTab_eq _ (by decide), imgTrioTab_eq _ (by decide)]
  rfl

theorem j4Base_eq : CFSG.J4DCE.Native.baseTrio () = j4Base := by
  decide +kernel

end CFSG.KC.J4DCE
