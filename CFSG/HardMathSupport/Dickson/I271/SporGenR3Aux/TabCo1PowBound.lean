module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block


theorem card_inf_GA_le_of_powBound {k : GL24} {kR : Native.Rows} (rk : MRep kR k) (n : ℕ)
    {base : List ℕ} {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)}
    {comb : List ℕ}
    (h : boundOK (colsOf (powList kR n)) n base conds cnts span comb = true) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set GL24) ⊓ GA) ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (powList kR n) ((List.range n).map fun a => k ^ a) := by
    unfold powList
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun a _ => ?_
    exact rk.pow a
  have hlen : (powList kR n).length = n := by simp [powList]
  have hcomm : ∀ g ∈ Subgroup.centralizer ({k} : Set GL24) ⊓ GA,
      ∀ β ∈ (List.range n).map (fun a => k ^ a), g * β = β * g := by
    intro g hg β hβ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hβ
    have h0 := (Subgroup.mem_inf.1 hg).1
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 h0
    exact comm_pow_aux h1 a
  exact card_le_of_listBound hr inf_le_right hcomm hlen h

theorem card_centralizer_GA_eq_inf {G : Type} [Group G] (P : Subgroup G) (x : ↥P) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥P)) =
      Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P) := by
  refine Nat.card_congr
    { toFun := fun k => ⟨(k.1 : G), Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp k.2)), k.1.2⟩
      invFun := fun m => ⟨⟨m.1, m.2.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2.1))⟩
      left_inv := fun k => rfl
      right_inv := fun m => rfl }

end CFSG.HardMathSupport.Dickson.I271.TabCo1
