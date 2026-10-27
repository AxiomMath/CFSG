module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import Certificates.Data.CFSGNative.SporLat.Spec
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

structure LabAct (Lab : Type) where
  act : Array ℕ → Lab → Lab

structure LabLawful (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)] {Lab : Type}
    (A : LabAct Lab) (valid : Lab → Prop) : Prop where
  valid_act : ∀ (g : Γ) {L : Lab}, valid L → valid (A.act (tab n g).toArray L)
  act_mul : ∀ (g h : Γ) {L : Lab}, valid L →
    A.act (tab n (g * h)).toArray L = A.act (tab n g).toArray (A.act (tab n h).toArray L)
  act_one : ∀ {L : Lab}, valid L → A.act (tab n (1 : Γ)).toArray L = L

theorem sortN_perm (l : List ℕ) : List.Perm (sortN l) l := List.mergeSort_perm l _

theorem sortN_sorted (l : List ℕ) : (sortN l).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun _ _ _ hab hbc => by simpa using Nat.le_trans (by simpa using hab) (by simpa using hbc))
    (fun a b => by simpa using Nat.le_total a b) l
  unfold sortN
  simpa using this

theorem sortN_eq_of_perm {l₁ l₂ : List ℕ} (h : List.Perm l₁ l₂) : sortN l₁ = sortN l₂ :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba)
    (sortN_sorted l₁) (sortN_sorted l₂) (((sortN_perm l₁).trans h).trans (sortN_perm l₂).symm)

theorem sortN_of_pairwise {l : List ℕ} (h : l.Pairwise (· ≤ ·)) : sortN l = l :=
  List.mergeSort_of_pairwise (by simpa using h)

theorem mem_sortN {l : List ℕ} {a : ℕ} : a ∈ sortN l ↔ a ∈ l := List.mem_mergeSort

@[expose] def ptLab : LabAct (List ℕ) := ⟨ptAct⟩

@[expose] def PtValid (n : ℕ) (L : List ℕ) : Prop := L.Pairwise (· ≤ ·) ∧ ∀ p ∈ L, p < n

instance (n : ℕ) (L : List ℕ) : Decidable (PtValid n L) := by
  unfold PtValid; infer_instance

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem sortN_map_sortN (f : ℕ → ℕ) (l : List ℕ) : sortN ((sortN l).map f) = sortN (l.map f) :=
  sortN_eq_of_perm ((sortN_perm l).map f)

theorem ptAct_tab (g : Γ) (L : List ℕ) :
    ptAct (tab n g).toArray L = sortN (L.map fun p => act n g p) := by
  unfold ptAct
  congr 1
  apply List.map_congr_left
  intro p _
  exact img_tab g p

theorem ptLab_lawful : LabLawful Γ n ptLab (PtValid n) where
  valid_act g L hL := by
    refine ⟨sortN_sorted _, fun p hp => ?_⟩
    have hp' : p ∈ ptAct (tab n g).toArray L := hp
    rw [ptAct_tab, mem_sortN] at hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact act_lt g (hL.2 q hq)
  act_mul g h L hL := by
    show ptAct (tab n (g * h)).toArray L = ptAct (tab n g).toArray (ptAct (tab n h).toArray L)
    rw [ptAct_tab, ptAct_tab, ptAct_tab, sortN_map_sortN, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact act_mul g h (hL.2 p hp)
  act_one {L} hL := by
    show ptAct (tab n (1 : Γ)).toArray L = L
    rw [ptAct_tab]
    have : (L.map fun p => act n (1 : Γ) p) = L :=
      (List.map_congr_left (g := fun p => p) fun p hp => act_one (hL.2 p hp)).trans
        (List.map_id' L)
    rw [this]
    exact sortN_of_pairwise hL.1

end CFSG.QuasithinUnique.Ch1.SporLat
