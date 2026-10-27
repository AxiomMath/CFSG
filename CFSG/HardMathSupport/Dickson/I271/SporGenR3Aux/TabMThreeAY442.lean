module

public import Certificates.Certificate10105
public import CFSG.YGroups.Y433.Relabel
public import CFSG.YGroups.Y443.OddInvolutionDiagram

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.YGroups
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem rels_y442_y443 : ∀ w ∈ yRels 4 4 2, w.map (fun c => c) ∈ yRels 4 4 3 := by
  decide +kernel

@[expose] noncomputable def y442Iota : YGroup 4 4 2 →* YGroup 4 4 3 :=
  yHom (fun c => c) rels_y442_y443

theorem y442Iota_yGen {c : ℕ} (hc : c < 11) : y442Iota (yGen 4 4 2 c) = yGen 4 4 3 c :=
  yHom_yGen (fun c => c) rels_y442_y443 hc

theorem y442_card_le :
    Finite (YGroup 4 4 2) ∧ Nat.card (YGroup 4 4 2) ≤ 6 * 1255205709190661721292800 :=
  ⟨Certificates.certificate10105.1,
    Certificates.certificate10105.2.trans (by norm_num)⟩

@[expose] def y442Adj (i j : Fin 11) : Prop :=
  ((i : ℕ), (j : ℕ)) ∈ yEdges 4 4 2 ∨ ((j : ℕ), (i : ℕ)) ∈ yEdges 4 4 2

instance (i j : Fin 11) : Decidable (y442Adj i j) := by
  unfold y442Adj
  infer_instance

theorem y442Adj_irrefl : ∀ i : Fin 11, ¬ y442Adj i i := by decide +kernel

@[expose] def y442Graph : SimpleGraph (Fin 11) where
  Adj := y442Adj
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => y442Adj_irrefl i h⟩

@[expose] def y442Parent (i : Fin 11) : Fin 11 :=
  match i.val with
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | 10 => 9
  | _ => 0

theorem y442Parent_spec :
    ∀ i : Fin 11, i ≠ 0 → (y442Parent i).val < i.val ∧ y442Adj (y442Parent i) i := by
  decide +kernel

theorem y442Graph_connected : y442Graph.Connected := by
  have r : ∀ n, ∀ i : Fin 11, i.val = n → y442Graph.Reachable 0 i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      by_cases h0 : i = 0
      · subst h0
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨hlt, hadj⟩ := y442Parent_spec i h0
        exact (ih _ (hi ▸ hlt) _ rfl).trans (SimpleGraph.Adj.reachable hadj)
  exact ⟨fun a b => (r _ a rfl).symm.trans (r _ b rfl)⟩

theorem y442_edge_lt : ∀ e ∈ yEdges 4 4 2, e.1 < e.2 := by decide +kernel

theorem y442_pow_three_of_adj {i j : Fin 11} (h : y442Adj i j) :
    (yGen 4 4 2 i * yGen 4 4 2 j) ^ 3 = 1 := by
  rcases h with h | h
  · have hp := Y443.yGen_pair_pow (p := 4) (q := 4) (r := 2) (s := i) (t := j)
      (y442_edge_lt _ h) j.isLt
    rwa [show pairExp 4 4 2 i j = 3 by simp [pairExp, h]] at hp
  · have hp := Y443.yGen_pair_pow (p := 4) (q := 4) (r := 2) (s := j) (t := i)
      (y442_edge_lt _ h) i.isLt
    rw [show pairExp 4 4 2 j i = 3 by simp [pairExp, h]] at hp
    exact Y443.pow_eq_one_of_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) hp

@[expose] def y442Far (k i : Fin 11) : Prop := k ≠ i ∧ ¬ y442Adj k i

instance (k i : Fin 11) : Decidable (y442Far k i) := by
  unfold y442Far
  infer_instance

theorem commute_of_y442Far {k i : Fin 11} (h : y442Far k i) :
    Commute (yGen 4 4 2 k) (yGen 4 4 2 i) :=
  Relabel.commute_yGen_of_not_edge k.isLt i.isLt (fun e => h.1 (Fin.ext e))
    (fun e => h.2 (Or.inl e)) (fun e => h.2 (Or.inr e))

@[expose] def y442Witness (i j : Fin 11) : Fin 11 :=
  if i.val = 7 ∨ i.val = 8 ∨ j.val = 7 ∨ j.val = 8 then 4 else 8

theorem y442Witness_spec :
    ∀ i j : Fin 11, y442Adj i j → y442Far (y442Witness i j) i ∧ y442Far (y442Witness i j) j := by
  decide +kernel

theorem y442_exists_commute {i j : Fin 11} (h : y442Adj i j) :
    ∃ k : Fin 11, Commute (yGen 4 4 2 k) (yGen 4 4 2 i) ∧
      Commute (yGen 4 4 2 k) (yGen 4 4 2 j) :=
  ⟨y442Witness i j, commute_of_y442Far (y442Witness_spec i j h).1,
    commute_of_y442Far (y442Witness_spec i j h).2⟩

theorem y442_closure :
    Subgroup.closure (Set.range fun k : Fin 11 => yGen 4 4 2 k) = ⊤ := by
  rw [← closure_yGen 4 4 2]
  congr 1
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.isLt, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

theorem y442_commutator_commutator :
    ⁅commutator (YGroup 4 4 2), commutator (YGroup 4 4 2)⁆ = commutator (YGroup 4 4 2) :=
  OddInvolutionDiagram.commutator_commutator_eq y442Graph (fun k : Fin 11 => yGen 4 4 2 k)
    y442Graph_connected y442_closure (fun _ => yGen_mul_self _ _ _ _)
    (fun _ _ h => ⟨3, by decide, y442_pow_three_of_adj h⟩) (fun _ _ h => y442_exists_commute h)

theorem yGen_mul_yGen_mem_commutator {i j : ℕ} (hi : i < 11) (hj : j < 11) :
    yGen 4 4 2 i * yGen 4 4 2 j ∈ commutator (YGroup 4 4 2) :=
  OddInvolutionDiagram.pair_mem_commutator y442Graph (fun k : Fin 11 => yGen 4 4 2 k)
    y442Graph_connected (fun _ => yGen_mul_self _ _ _ _)
    (fun _ _ h => ⟨3, by decide, y442_pow_three_of_adj h⟩) ⟨i, hi⟩ ⟨j, hj⟩

theorem evalWord_mem_commutator :
    ∀ n (w : List ℕ), w.length = 2 * n → (∀ c ∈ w, c < 11) →
      evalWord (yGen 4 4 2) w ∈ commutator (YGroup 4 4 2)
  | 0, [], _, _ => by
    rw [evalWord_nil]
    exact one_mem _
  | n + 1, c :: d :: w, hl, hw => by
    rw [evalWord_cons, evalWord_cons, ← mul_assoc]
    refine mul_mem (yGen_mul_yGen_mem_commutator (hw c (by simp)) (hw d (by simp)))
      (evalWord_mem_commutator n w (by simp at hl; omega) fun x hx => hw x (by simp [hx]))
  | 0, _ :: _, hl, _ => by simp at hl
  | n + 1, [], hl, _ => by simp at hl
  | n + 1, [_], hl, _ => by simp at hl; omega

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
