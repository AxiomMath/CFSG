
module

public import Certificates.Data.ASVolIK42
public import CFSG.Certificates.Kernel.HMathieu.GreedySound

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat

variable {P Q : Type*}

theorem quadBasisOK_map (n : Nat) {act : P → Nat → Nat} {act' : Q → Nat → Nat} (g : P → Q)
    {l : List P} (h : ∀ x ∈ l, act x = act' (g x)) :
    quadBasisOK n act l = quadBasisOK n act' (l.map g) := by
  unfold quadBasisOK
  simp only [List.all_map, Function.comp_def]
  refine all_congr_mem fun s hs => all_congr_mem fun t ht => ?_
  rw [h s hs, h t ht]

theorem noQuadRank3_map (n : Nat) {act : P → Nat → Nat} {act' : Q → Nat → Nat} (g : P → Q)
    {l : List P} (h : ∀ x ∈ l, act x = act' (g x)) :
    noQuadRank3 n act l = noQuadRank3 n act' (l.map g) := by
  unfold noQuadRank3
  rw [quadBasisOK_map n g h, List.length_map]

theorem fixMasks_map (n : Nat) {act : P → Nat → Nat} {act' : Q → Nat → Nat} (g : P → Q)
    {l : List P} (h : ∀ x ∈ l, act x = act' (g x)) :
    fixMasks n act l = fixMasks n act' (l.map g) := by
  unfold fixMasks
  refine List.filter_congr fun m _ => ?_
  simp only [List.all_map, Function.comp_def]
  exact all_congr_mem fun s hs => by rw [h s hs]

theorem predQ_map (n : Nat) {act : P → Nat → Nat} {act' : Q → Nat → Nat} (g : P → Q)
    (strict : Bool) {l : List P} (h : ∀ x ∈ l, act x = act' (g x)) :
    predQ n act strict l = predQ n act' strict (l.map g) := by
  unfold predQ
  rw [quadBasisOK_map n g h, fixMasks_map n g h, List.length_map, List.isEmpty_map]

end CFSG.KC.HMathieu

end
