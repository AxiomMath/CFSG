module

public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.KC.YModel.Bfs

open CFSG.YGroups.ModelNative

inductive Reach (steps : Array (Array Nat)) (root : Nat) : Nat → Prop
  | root : Reach steps root root
  | step {x : Nat} (j : Nat) (hj : j < steps.size) :
      Reach steps root x → Reach steps root (steps[j]![x]!)

@[expose] def Mem (pts : Array Nat) (y : Nat) : Prop := ∃ a < pts.size, pts[a]! = y

abbrev St := Array Nat × Array Nat × Array Nat × Array Nat

@[expose] def innerF (n : Nat) (steps : Array (Array Nat)) (h x j : Nat) (s : St) :
    Id (ForInStep St) :=
  if (s.1[steps[j]![x]!]! == n) = true then
    pure (ForInStep.yield (s.1.set! steps[j]![x]! s.2.1.size, s.2.1.push steps[j]![x]!,
      s.2.2.1.push h, s.2.2.2.push j))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerF (n : Nat) (steps : Array (Array Nat)) (h : Nat) (s : St) : Id (ForInStep St) :=
  if h < s.2.1.size then do
    let s' ← forIn (List.range' 0 steps.size) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerF n steps h s.2.1[h]!)
    pure (ForInStep.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def init (n root : Nat) : St := ((Array.replicate n n).set! root 0, #[root], #[0], #[0])

theorem orbitSearch_eq (n root : Nat) (steps : Array (Array Nat)) :
    orbitSearch n root steps =
      (fun s : St => ({ pts := s.2.1, pos := s.1, par := s.2.2.1, lab := s.2.2.2 } : Orbit))
        (forIn (m := Id) (List.range' 0 n) (init n root) (outerF n steps)) := by
  unfold orbitSearch
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

end CFSG.KC.YModel.Bfs

end
