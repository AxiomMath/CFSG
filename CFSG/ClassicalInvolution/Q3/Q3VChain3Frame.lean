module

public import CFSG.ClassicalInvolution.Q3.Q3VChain3Main
public import CFSG.ClassicalInvolution.Q3.Q3VChainFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3V.Chain
open CFSG.ClassicalInvolution.WeakCT (blk blockSL spBlock spBlock_one_eq_longBlock
  spBlock_zero_eq_shortBlock)
open scoped MatrixGroups

local notation "F3" => GaloisField 3 1

variable {m : ℕ} {G : Type} [Group G]

section Props

variable {Ω : Set (Subgroup G)} {K : Fin (m + 1) → Subgroup G} {A B : StatedSp m F3 →* G}
  {pA pB : Fin (m + 1) → Fin m} (D : NodeDataW Ω K A B pA pB)

include D

theorem NodeDataW.pA_ne {i : Fin (m + 1)} (hi : i.val + 1 < m) : pA i ≠ pA (nxt i) := by
  have hm := D.hm
  have hn := nxt_val i
  have hl1 : i ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  have hl2 : nxt i ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  exact fun e => ne_nxt (by omega) (D.injA hl1 hl2 e)

theorem NodeDataW.pB_ne {i : Fin (m + 1)} (hi : i.val + 1 = m) : pB i ≠ pB (nxt i) := by
  have hm := D.hm
  have hn := nxt_val i
  have hl1 : i ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  have hl2 : nxt i ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  exact fun e => ne_nxt (by omega) (D.injB hl1 hl2 e)

theorem NodeDataW.pA_ne3 {i : Fin (m + 1)} (hi : i.val + 2 < m) :
    pA i ≠ pA (nxt i) ∧ pA (nxt i) ≠ pA (nxt (nxt i)) ∧ pA i ≠ pA (nxt (nxt i)) := by
  have hm := D.hm
  have hn := nxt_val i
  have hn2 := nxt_val (nxt i)
  have hl1 : i ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  have hl2 : nxt i ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  have hl3 : nxt (nxt i) ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  refine ⟨fun e => ne_nxt (by omega) (D.injA hl1 hl2 e),
    fun e => ne_nxt (by omega) (D.injA hl2 hl3 e), fun e => ?_⟩
  have := congrArg Fin.val (D.injA hl1 hl3 e)
  omega

theorem NodeDataW.pB_ne3 {i : Fin (m + 1)} (hi : i.val + 2 = m) :
    pB i ≠ pB (nxt i) ∧ pB (nxt i) ≠ pB (nxt (nxt i)) ∧ pB i ≠ pB (nxt (nxt i)) := by
  have hm := D.hm
  have hn := nxt_val i
  have hn2 := nxt_val (nxt i)
  have hl1 : i ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  have hl2 : nxt i ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  have hl3 : nxt (nxt i) ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  refine ⟨fun e => ne_nxt (by omega) (D.injB hl1 hl2 e),
    fun e => ne_nxt (by omega) (D.injB hl2 hl3 e), fun e => ?_⟩
  have := congrArg Fin.val (D.injB hl1 hl3 e)
  omega

theorem NodeDataW.nodeRho_lt {i : Fin (m + 1)} (hi : i.val + 1 < m) :
    nodeRho A B pA pB i = A.comp (shortBlock F3 (D.pA_ne hi)) := by
  unfold nodeRho
  rw [ite_eq_left hi, shortBlockOf_of_ne (D.pA_ne hi)]

theorem NodeDataW.nodeRho_eq {i : Fin (m + 1)} (hi : i.val + 1 = m) :
    nodeRho A B pA pB i = B.comp (shortBlock F3 (D.pB_ne hi)) := by
  have h1 : ¬ i.val + 1 < m := by omega
  unfold nodeRho
  rw [ite_eq_right h1, ite_eq_left hi, shortBlockOf_of_ne (D.pB_ne hi)]

theorem NodeDataW.nodeRho_inj (k : Fin (m + 1)) : Function.Injective (nodeRho A B pA pB k) := by
  have hm := D.hm
  by_cases h1 : k.val + 1 < m
  · rw [D.nodeRho_lt h1]
    exact comp_shortBlock_injective (by omega) (D.pA_ne h1) A D.locA.ker_le
  · by_cases h2 : k.val + 1 = m
    · rw [D.nodeRho_eq h2]
      exact comp_shortBlock_injective (by omega) (D.pB_ne h2) B D.locB.ker_le
    · have hk : k = Fin.last m := Fin.ext (by rw [Fin.val_last]; have := k.isLt; omega)
      subst hk
      rw [NodeData.nodeRho_last]
      have hl0 : Fin.last m ≠ 0 := fun e => by
        have := congrArg Fin.val e
        rw [Fin.val_last, Fin.val_zero] at this
        omega
      have hj0 : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ 0 := fun e => by
        have := congrArg Fin.val e
        rw [Fin.val_zero] at this
        simp at this
        omega
      have hab : pB ⟨m - 1, by omega⟩ ≠ pB (Fin.last m) := fun e => by
        have := congrArg Fin.val (D.injB hj0 hl0 e)
        rw [Fin.val_last] at this
        simp at this
        omega
      exact comp_longBlock_injective (by omega) hab B D.locB.ker_le

theorem NodeDataW.nodeRho_range (k : Fin (m + 1)) :
    (nodeRho A B pA pB k).range = nodeFamily K A B pA pB k := by
  have hm := D.hm
  by_cases h1 : k.val + 1 < m
  · rw [D.nodeRho_lt h1, MonoidHom.range_comp, nodeFamily_of_lt h1, shortNode,
      shortSub_of_ne (D.pA_ne h1)]
  · by_cases h2 : k.val + 1 = m
    · rw [D.nodeRho_eq h2, MonoidHom.range_comp, nodeFamily_of_eq h2, shortNode,
        shortSub_of_ne (D.pB_ne h2)]
    · have hk : k = Fin.last m := Fin.ext (by rw [Fin.val_last]; have := k.isLt; omega)
      subst hk
      have hl0 : Fin.last m ≠ 0 := fun e => by
        have := congrArg Fin.val e
        rw [Fin.val_last, Fin.val_zero] at this
        omega
      rw [NodeData.nodeRho_last, MonoidHom.range_comp, nodeFamily_last (by omega)]
      have h := D.labB (Fin.last m) hl0
      rw [planeGroup_stdPlane_eq_range] at h
      exact h

theorem NodeDataW.nodePsi_zero (i j : Fin (m + 1)) (hj : j.val = i.val + 1)
    (hi : i.val + 2 < m + 1) :
    (nodePsi A B pA pB i).comp (WeakCT.blk F3 0) = nodeRho A B pA pB j := by
  have hm := D.hm
  have hjn : j = nxt i := Fin.ext (by rw [hj, nxt_val]; omega)
  subst hjn
  have hn := nxt_val i
  have hrev : (0 : Fin 2).rev = 1 := rfl
  by_cases hA : i.val + 2 < m
  · obtain ⟨h12, h23, h13⟩ := D.pA_ne3 hA
    have h1 : (nxt i).val + 1 < m := by omega
    rw [D.nodeRho_lt h1]
    unfold nodePsi
    rw [ite_eq_left hA, leviOf_of_ne h12 h23 h13,
      comp_blockSwapAut_blk (A.comp (leviSL3 F3 h12 h23 h13)) 0, hrev]
    show (A.comp (leviSL3 F3 h12 h23 h13)).comp (blockSL F3 3 2 1 (by omega)) = _
    rw [MonoidHom.comp_assoc, leviSL3_comp_blockSL_one]
  · have hB : i.val + 2 = m := by omega
    obtain ⟨h12, h23, h13⟩ := D.pB_ne3 hB
    have h1 : (nxt i).val + 1 = m := by omega
    rw [D.nodeRho_eq h1]
    unfold nodePsi
    rw [ite_eq_right hA, leviOf_of_ne h12 h23 h13,
      comp_blockSwapAut_blk (B.comp (leviSL3 F3 h12 h23 h13)) 0, hrev]
    show (B.comp (leviSL3 F3 h12 h23 h13)).comp (blockSL F3 3 2 1 (by omega)) = _
    rw [MonoidHom.comp_assoc, leviSL3_comp_blockSL_one]

theorem NodeDataW.nodePsi_one (i : Fin (m + 1)) (hi : i.val + 2 < m + 1) :
    (nodePsi A B pA pB i).comp (WeakCT.blk F3 1) = nodeRho A B pA pB i := by
  have hm := D.hm
  have h1i : i.val + 1 < m := by omega
  have hrev : (1 : Fin 2).rev = 0 := rfl
  by_cases hA : i.val + 2 < m
  · obtain ⟨h12, h23, h13⟩ := D.pA_ne3 hA
    rw [D.nodeRho_lt h1i]
    unfold nodePsi
    rw [ite_eq_left hA, leviOf_of_ne h12 h23 h13,
      comp_blockSwapAut_blk (A.comp (leviSL3 F3 h12 h23 h13)) 1, hrev]
    show (A.comp (leviSL3 F3 h12 h23 h13)).comp (blockSL F3 3 2 0 (by omega)) = _
    rw [MonoidHom.comp_assoc, leviSL3_comp_blockSL_zero]
  · have hB : i.val + 2 = m := by omega
    obtain ⟨h12, h23, h13⟩ := D.pB_ne3 hB
    have hn := nxt_val i
    rw [D.nodeRho_lt h1i]
    unfold nodePsi
    rw [ite_eq_right hA, leviOf_of_ne h12 h23 h13,
      comp_blockSwapAut_blk (B.comp (leviSL3 F3 h12 h23 h13)) 1, hrev]
    show (B.comp (leviSL3 F3 h12 h23 h13)).comp (blockSL F3 3 2 0 (by omega)) =
      A.comp (shortBlock F3 (D.pA_ne h1i))
    rw [MonoidHom.comp_assoc, leviSL3_comp_blockSL_zero]
    have e1 : pA i = pB i := Fin.ext (by rw [D.valA i (by omega), D.valB])
    have e2 : pA (nxt i) = pB (nxt i) := Fin.ext (by
      rw [D.valA (nxt i) (by omega), D.valB])
    rw [shortBlock_congr e1 e2 (D.pA_ne h1i) h12]
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply]
    refine (D.coh i hB _ ?_).symm
    rw [shortSub_of_ne h12]
    exact ⟨x, rfl⟩

theorem NodeDataW.nodePsi4_long (a : Fin (m + 1)) (ha : a.val + 1 = m + 1) :
    (nodePsi4 B pB).comp (spBlock F3 1) = nodeRho A B pA pB a := by
  have hm := D.hm
  have hal : a = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
  subst hal
  have hl0 : Fin.last m ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last, Fin.val_zero] at this
    omega
  have hj0 : lastButOne m ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    simp [lastButOne] at this
    omega
  have hab : pB (lastButOne m) ≠ pB (Fin.last m) := fun e => by
    have := congrArg Fin.val (D.injB hj0 hl0 e)
    rw [Fin.val_last] at this
    simp [lastButOne] at this
    omega
  unfold nodePsi4
  rw [pairOf_of_ne hab, spBlock_one_eq_longBlock, NodeData.nodeRho_last, MonoidHom.comp_assoc]
  exact congrArg B.comp (spEmbed_comp_longBlock hab)

theorem NodeDataW.nodePsi4_short (b : Fin (m + 1)) (hb : b.val + 2 = m + 1) :
    (nodePsi4 B pB).comp (spBlock F3 0) = nodeRho A B pA pB b := by
  have hm := D.hm
  have hbl : b = lastButOne m := Fin.ext (by simp [lastButOne]; omega)
  rw [hbl]
  have hn : nxt (lastButOne m) = Fin.last m :=
    Fin.ext (by rw [nxt_val, Fin.val_last]; simp [lastButOne]; omega)
  have h1 : (lastButOne m).val + 1 = m := by simp [lastButOne]; omega
  have hab := D.pB_ne h1
  rw [hn] at hab
  rw [D.nodeRho_eq h1]
  unfold nodePsi4
  rw [pairOf_of_ne hab, spBlock_zero_eq_shortBlock, MonoidHom.comp_assoc]
  have e2 : (pairEmbed F3 hab).comp (shortBlock F3 (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      shortBlock F3 hab := spEmbed_comp_shortBlock hab
  rw [e2]
  exact congrArg B.comp (shortBlock_congr rfl (by rw [hn]) hab (D.pB_ne h1))

@[expose] noncomputable def NodeDataW.spFrame : SpFrame3 (m + 1) (nodeFamily K A B pA pB) where
  ρ := nodeRho A B pA pB
  ρ_inj := D.nodeRho_inj
  ρ_range := D.nodeRho_range
  ψ := fun i _ => nodePsi A B pA pB i
  ψ_zero := fun i j h hj => D.nodePsi_zero i j hj h
  ψ_one := fun i h => D.nodePsi_one i h
  ψ4 := nodePsi4 B pB
  ψ4_long := fun a ha => D.nodePsi4_long a ha
  ψ4_short := fun b hb => D.nodePsi4_short b hb

theorem NodeDataW.exists_psi :
    ∃ Ψ : StatedSp (m + 1) F3 →* G, Ψ.ker ≤ Subgroup.center (StatedSp (m + 1) F3) ∧
      (longBlock F3 (m + 1) (Fin.last m)).range.map Ψ = K (Fin.last m) := by
  have hm := D.hm
  obtain ⟨Ψ, hker, -, -, -, hblk⟩ := weakCT3_of_spFrame3_subgroup (n := m + 1) (by omega)
    (nodeFamily K A B pA pB) (fun i j h => D.node_commute h) D.spFrame
  refine ⟨Ψ, hker, ?_⟩
  rw [range_longBlock_eq_rankOne (by show ¬ m + 1 < m + 1; omega)]
  exact (hblk (Fin.last m)).trans (nodeFamily_last (by omega))

end Props


theorem oddLieType_of_local_four [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) {Kf : Fin 4 → Subgroup G}
    (hK : IsMemberFrame (conjClass3 K) Kf) {Θ : Fin 4 → (StatedSp 3 F3 →* G)}
    (hΘ : ∀ l, IsLabLift 3 (conjClass3 K) Kf l (Θ l))
    (R1 : Commutes (layerSub (conjClass3 K) Kf 0 1) (layerSub (conjClass3 K) Kf 2 3))
    (R1' : Commutes (layerSub (conjClass3 K) Kf 0 3) (layerSub (conjClass3 K) Kf 1 2)) :
    Blueprint.OddLieType G := by
  have hK₀ : ¬ Commutes K K := Q3W.not_commutes_self3 hR.cls
  obtain ⟨A, pA, pB, D⟩ := exists_nodeDataW_four (conjInvariant_conjClass3 K)
    (nonab_conjClass3 hK₀) hK hΘ R1 R1'
  obtain ⟨Ψ, hker, hlong⟩ := D.exists_psi
  exact oddLieType_of_psi_psp3_rank (by norm_num) hnab hR hshape hO3 Ψ hker
    (hlong ▸ hK.mem (Fin.last 3))

end CFSG.ClassicalInvolution.Q3.Q3V.Chain3
