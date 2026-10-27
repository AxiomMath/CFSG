module

public import CFSG.ClassicalInvolution.Q3.Q3VChainNodes

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3V.Chain

local notation "F3" => GaloisField 3 1

variable {m : ℕ} {G : Type} [Group G]

structure NodeDataW (Ω : Set (Subgroup G)) (K : Fin (m + 1) → Subgroup G)
    (A B : StatedSp m F3 →* G) (pA pB : Fin (m + 1) → Fin m) : Prop where
  hm : 3 ≤ m
  nonab : ∀ M ∈ Ω, ¬ Commutes M M
  frame : IsMemberFrame Ω K
  locA : IsLocLift m Ω (K (Fin.last m)) A
  locB : IsLocLift m Ω (K 0) B
  labA : ∀ c, c ≠ Fin.last m → (planeGroup (stdPlane F3 m (pA c))).map A = K c
  labB : ∀ c, c ≠ 0 → (planeGroup (stdPlane F3 m (pB c))).map B = K c
  valB : ∀ c, (pB c).val = c.val - 1
  valA0 : ∀ c, c.val = 0 → (pA c).val = m - 1
  valA : ∀ c, c.val ≠ 0 → (pA c).val = c.val - 1
  coh : ∀ i : Fin (m + 1), i.val + 2 = m → ∀ x ∈ shortSub F3 (pB i) (pB (nxt i)), A x = B x
  disj : ∀ i j : Fin (m + 1), i.val + 1 < j.val → j.val < m →
    Commutes (layerSub Ω K i (nxt i)) (layerSub Ω K j (nxt j))

section Data

variable {Ω : Set (Subgroup G)} {K : Fin (m + 1) → Subgroup G} {A B : StatedSp m F3 →* G}
  {pA pB : Fin (m + 1) → Fin m}

theorem NodeDataW.injA (D : NodeDataW Ω K A B pA pB) {c d : Fin (m + 1)} (hc : c ≠ Fin.last m)
    (hd : d ≠ Fin.last m) (e : pA c = pA d) : c = d := by
  have hc' := val_lt_of_ne_last hc
  have hd' := val_lt_of_ne_last hd
  have hm := D.hm
  have e' := congrArg Fin.val e
  by_cases h0 : c.val = 0 <;> by_cases h1 : d.val = 0
  · exact Fin.ext (by omega)
  · rw [D.valA0 c h0, D.valA d h1] at e'
    omega
  · rw [D.valA c h0, D.valA0 d h1] at e'
    omega
  · rw [D.valA c h0, D.valA d h1] at e'
    exact Fin.ext (by omega)

theorem NodeDataW.injB (D : NodeDataW Ω K A B pA pB) {c d : Fin (m + 1)} (hc : c ≠ 0) (hd : d ≠ 0)
    (e : pB c = pB d) : c = d := by
  have hc' := val_ne_zero_of_ne_zero hc
  have hd' := val_ne_zero_of_ne_zero hd
  have e' := congrArg Fin.val e
  rw [D.valB c, D.valB d] at e'
  exact Fin.ext (by omega)

theorem NodeDataW.nodeFamily_le (D : NodeDataW Ω K A B pA pB) {i : Fin (m + 1)} (hi : i.val < m) :
    nodeFamily K A B pA pB i ≤ layerSub Ω K i (nxt i) := by
  have hm := D.hm
  have hn := nxt_val i
  by_cases h1 : i.val + 1 < m
  · rw [nodeFamily_of_lt h1]
    refine shortNode_le_layerSub hm D.nonab D.frame D.locA D.labA
      (fun c d hc hd e => D.injA hc hd e) hi ?_ ?_
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
  · have h2 : i.val + 1 = m := by omega
    rw [nodeFamily_of_eq h2]
    refine shortNode_le_layerSub hm D.nonab D.frame D.locB D.labB
      (fun c d hc hd e => D.injB hc hd e) hi ?_ ?_
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_zero] at this; omega
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_zero] at this; omega

theorem NodeDataW.node_commute (D : NodeDataW Ω K A B pA pB) {i j : Fin (m + 1)}
    (hij : i.val + 1 < j.val) :
    ∀ a ∈ nodeFamily K A B pA pB i, ∀ b ∈ nodeFamily K A B pA pB j, a * b = b * a := by
  have hm := D.hm
  have hjm := j.isLt
  have hi : i.val < m := by omega
  have hin := nxt_val i
  intro a ha b hb
  have ha' := D.nodeFamily_le hi ha
  by_cases hj : j.val = m
  · have hjl : j = Fin.last m := eq_last_of_val hj
    rw [hjl, nodeFamily_last (by omega)] at hb
    refine Frame.layerSub_le_centralizer (K := K) (Ω := Ω) ?_ ?_ a ha' b hb
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
  · have hj' : j.val < m := by omega
    exact D.disj i j hij hj' a ha' b (D.nodeFamily_le hj' hb)

end Data

end CFSG.ClassicalInvolution.Q3.Q3V.Chain3
