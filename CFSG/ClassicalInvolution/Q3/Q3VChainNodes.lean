module

public import CFSG.ClassicalInvolution.Q3.Q3VChainModel
public import CFSG.ClassicalInvolution.Q3.Q3VFrameDisj
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.Q3.Q3VFrameMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs

local notation "F3" => GaloisField 3 1

variable {m : ℕ} {G : Type} [Group G]

@[expose] def nxt (i : Fin (m + 1)) : Fin (m + 1) := ⟨min (i.val + 1) m, by omega⟩

theorem nxt_val (i : Fin (m + 1)) : (nxt i).val = min (i.val + 1) m := rfl

theorem ne_nxt {i : Fin (m + 1)} (h : i.val < m) : i ≠ nxt i := by
  intro e
  have := congrArg Fin.val e
  rw [nxt_val] at this
  omega

theorem val_lt_of_ne_last {c : Fin (m + 1)} (hc : c ≠ Fin.last m) : c.val < m := by
  have h1 := c.isLt
  have h2 : c.val ≠ m := fun h => hc (Fin.ext (by rw [Fin.val_last]; exact h))
  omega

theorem val_ne_zero_of_ne_zero {c : Fin (m + 1)} (hc : c ≠ 0) : c.val ≠ 0 := fun h =>
  hc (Fin.ext (by rw [Fin.val_zero]; exact h))

theorem eq_last_of_val {c : Fin (m + 1)} (h : c.val = m) : c = Fin.last m :=
  Fin.ext (by rw [Fin.val_last]; exact h)

@[expose] noncomputable def shortNode (Θ' : StatedSp m F3 →* G) (p : Fin (m + 1) → Fin m)
    (i : Fin (m + 1)) : Subgroup G :=
  (shortSub F3 (p i) (p (nxt i))).map Θ'

theorem shortNode_le_layerSub (hm : 3 ≤ m) {Ω : Set (Subgroup G)}
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G}
    (hK : IsMemberFrame Ω K) {l : Fin (m + 1)} {Θ' : StatedSp m F3 →* G}
    (hΘ : IsLocLift m Ω (K l) Θ') {p : Fin (m + 1) → Fin m}
    (hp : ∀ c, c ≠ l → (planeGroup (stdPlane F3 m (p c))).map Θ' = K c)
    (hpinj : ∀ c d, c ≠ l → d ≠ l → p c = p d → c = d) {i : Fin (m + 1)} (hi : i.val < m)
    (hil : i ≠ l) (hil' : nxt i ≠ l) : shortNode Θ' p i ≤ layerSub Ω K i (nxt i) := by
  have hne : i ≠ nxt i := ne_nxt hi
  have hpab : p i ≠ p (nxt i) := fun e => hne (hpinj i _ hil hil' e)
  rw [Frame.layerSub_eq hm hnonab hK hΘ p hp hpinj hil hil' hne hpab]
  exact Subgroup.map_mono (shortSub_le_range_pairEmbed hpab)

structure NodeData (Ω : Set (Subgroup G)) (K : Fin (m + 1) → Subgroup G)
    (A B : StatedSp m F3 →* G) (pA pB : Fin (m + 1) → Fin m) : Prop where
  hm : 4 ≤ m
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
  third : ∀ l, ∃ Θ' : StatedSp m F3 →* G, IsLabLift m Ω K l Θ'

section Data

variable {Ω : Set (Subgroup G)} {K : Fin (m + 1) → Subgroup G} {A B : StatedSp m F3 →* G}
  {pA pB : Fin (m + 1) → Fin m}

theorem NodeData.injA (D : NodeData Ω K A B pA pB) {c d : Fin (m + 1)} (hc : c ≠ Fin.last m)
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

theorem NodeData.injB (D : NodeData Ω K A B pA pB) {c d : Fin (m + 1)} (hc : c ≠ 0) (hd : d ≠ 0)
    (e : pB c = pB d) : c = d := by
  have hc' := val_ne_zero_of_ne_zero hc
  have hd' := val_ne_zero_of_ne_zero hd
  have e' := congrArg Fin.val e
  rw [D.valB c, D.valB d] at e'
  exact Fin.ext (by omega)

@[expose] noncomputable def nodeFamily (K : Fin (m + 1) → Subgroup G) (A B : StatedSp m F3 →* G)
    (pA pB : Fin (m + 1) → Fin m) (i : Fin (m + 1)) : Subgroup G :=
  if i.val + 1 < m then shortNode A pA i else if i.val + 1 = m then shortNode B pB i else K i

theorem nodeFamily_of_lt {i : Fin (m + 1)} (h : i.val + 1 < m) :
    nodeFamily K A B pA pB i = shortNode A pA i := ite_eq_left h

theorem nodeFamily_of_eq {i : Fin (m + 1)} (h : i.val + 1 = m) :
    nodeFamily K A B pA pB i = shortNode B pB i := by
  have h1 : ¬ (i.val + 1 < m) := by omega
  unfold nodeFamily
  rw [ite_eq_right h1, ite_eq_left h]

theorem nodeFamily_last (_hm : 1 ≤ m) :
    nodeFamily K A B pA pB (Fin.last m) = K (Fin.last m) := by
  have h1 : ¬ ((Fin.last m).val + 1 < m) := by rw [Fin.val_last]; omega
  have h2 : ¬ ((Fin.last m).val + 1 = m) := by rw [Fin.val_last]; omega
  unfold nodeFamily
  rw [ite_eq_right h1, ite_eq_right h2]

theorem NodeData.nodeFamily_le (D : NodeData Ω K A B pA pB) {i : Fin (m + 1)} (hi : i.val < m) :
    nodeFamily K A B pA pB i ≤ layerSub Ω K i (nxt i) := by
  have hm := D.hm
  have hn := nxt_val i
  by_cases h1 : i.val + 1 < m
  · rw [nodeFamily_of_lt h1]
    refine shortNode_le_layerSub (by omega) D.nonab D.frame D.locA D.labA
      (fun c d hc hd e => D.injA hc hd e) hi ?_ ?_
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_last] at this; omega
  · have h2 : i.val + 1 = m := by omega
    rw [nodeFamily_of_eq h2]
    refine shortNode_le_layerSub (by omega) D.nonab D.frame D.locB D.labB
      (fun c d hc hd e => D.injB hc hd e) hi ?_ ?_
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_zero] at this; omega
    · exact fun e => by have := congrArg Fin.val e; rw [Fin.val_zero] at this; omega

theorem NodeData.node_commute (D : NodeData Ω K A B pA pB) {i j : Fin (m + 1)}
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
    have hb' := D.nodeFamily_le hj' hb
    have hjn := nxt_val j
    choose Θ' hΘ' using D.third
    refine Frame.commutes_layerSub_layerSub hm D.nonab D.frame hΘ' ?_ ?_ ?_ ?_ ?_ ?_ a ha' b hb'
    · exact fun e => by have := congrArg Fin.val e; omega
    · exact fun e => by have := congrArg Fin.val e; omega
    · exact fun e => by have := congrArg Fin.val e; omega
    · exact fun e => by have := congrArg Fin.val e; omega
    · exact fun e => by have := congrArg Fin.val e; omega
    · exact fun e => by have := congrArg Fin.val e; omega

end Data

end CFSG.ClassicalInvolution.Q3.Q3V.Chain
