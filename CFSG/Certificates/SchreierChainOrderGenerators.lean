module

public import CFSG.Certificates.SchreierOrbitSearch
public import CFSG.Certificates.SchreierSift

public section

namespace CFSG.Certificates

theorem schreier_vector_get_mem_toList {α : Type*} {r : ℕ}
    (v : Vector α r) (j : Fin r) : v.get j ∈ v.toList := by
  rw [Vector.mem_toList_iff]
  exact Vector.getElem_mem j.isLt

theorem schreier_vector_mem_toList_iff_get {α : Type*} {r : ℕ}
    (v : Vector α r) (a : α) : a ∈ v.toList ↔ ∃ j : Fin r, v.get j = a := by
  rw [Vector.mem_toList_iff, Vector.mem_iff_getElem]
  exact ⟨fun ⟨j, hj, heq⟩ => ⟨⟨j, hj⟩, heq⟩,
    fun ⟨j, heq⟩ => ⟨j.val, j.isLt, heq⟩⟩

theorem schreierWordValue_mem_subgroup {G : Type*} [Group G] {r j : ℕ}
    (S : Fin r → G) (hj : j ≤ r) (w : List (SchreierLetter j)) (H : Subgroup G)
    (hS : ∀ a : Fin j, S ⟨a.val, a.isLt.trans_le hj⟩ ∈ H) :
    schreierWordValue S j hj w ∈ H := by
  apply (Subgroup.closure_le _).2 ?_
    (Quiver.SchreierGraph.evalWord_mem_closure
      (fun a : Fin j => S ⟨a.val, a.isLt.trans_le hj⟩) w)
  rintro _ ⟨a, rfl⟩
  exact hS a

namespace RawSchreierDatum

@[expose] def originalSubgroup {n : ℕ} (Q : RawSchreierDatum n) :
    Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure {g | g ∈ Q.original.toList}

theorem strong_get_mem_originalSubgroup {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (j : Fin Q.strongCount) :
    Q.strong.get j ∈ Q.originalSubgroup := by
  have hvalid := (validSchreier_iff Q).1 hQ
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount,
      j.val = a → Q.strong.get j ∈ Q.originalSubgroup := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · let l : Fin Q.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE Q.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, hvalid.1 l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList Q.original l)
      · rw [hvalid.2.1 j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup Q.strong.get
          (Nat.le_of_lt j.isLt) (Q.derivation j (Nat.le_of_not_gt hj)) Q.originalSubgroup
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

theorem strong_mem_originalSubgroup {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.strong.toList) :
    g ∈ Q.originalSubgroup := by
  obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.strong g).1 hg
  exact Q.strong_get_mem_originalSubgroup hQ j

theorem levelSubgroup_zero_eq_original {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) : Q.levelSubgroup 0 = Q.originalSubgroup := by
  rw [levelSubgroup, Q.levelGenerators_zero]
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    exact Q.strong_mem_originalSubgroup hQ
  · apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.original g).1 hg
    rw [← ((validSchreier_iff Q).1 hQ).1 j]
    exact Subgroup.subset_closure
      (schreier_vector_get_mem_toList Q.strong (Fin.castLE Q.originalCount_le j))

theorem levelGenerators_subset {n : ℕ} (Q : RawSchreierDatum n)
    (i j : ℕ) (hij : i ≤ j) : Q.levelGenerators j ⊆ Q.levelGenerators i := by
  intro s hs
  obtain ⟨hstrong, hfix⟩ := (Q.mem_levelGenerators_iff j s).1 hs
  apply (Q.mem_levelGenerators_iff i s).2
  exact ⟨hstrong, fun b hb => hfix b (List.take_subset_take_left Q.base.toList hij hb)⟩

theorem levelSubgroup_antitone {n : ℕ} (Q : RawSchreierDatum n)
    (i j : ℕ) (hij : i ≤ j) : Q.levelSubgroup j ≤ Q.levelSubgroup i :=
  Subgroup.closure_mono (Q.levelGenerators_subset i j hij)

theorem transversal_mem_earlier_level {n : ℕ} (Q : RawSchreierDatum n)
    (i : ℕ) (j : Fin Q.baseCount) (hij : i ≤ j.val)
    (x : Fin n) (t : Equiv.Perm (Fin n)) (ht : Q.transversal? j x = some t) :
    t ∈ Q.levelSubgroup i :=
  Q.levelSubgroup_antitone i j.val hij (Q.transversal_sound j x t ht).1

theorem sift_mem_levelSubgroup {n : ℕ} (Q : RawSchreierDatum n) (i : ℕ)
    (h : Equiv.Perm (Fin n)) (hsift : Q.sift h i = true) : h ∈ Q.levelSubgroup i :=
  Q.sift_mem_of_transversals i h (Q.levelSubgroup i)
    (fun j hj x t ht => Q.transversal_mem_earlier_level i j hj x t ht) hsift

theorem levelSubgroup_terminal_eq_bot {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) : Q.levelSubgroup Q.baseCount = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro s hs
    exact Subgroup.mem_bot.2 (((validSchreier_iff Q).1 hQ).2.2.1 s hs)
  · exact bot_le

theorem levelSubgroup_succ_le_stabilizer {n : ℕ} (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) :
    Q.levelSubgroup (i.val + 1) ≤
      Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) := by
  intro g hg
  exact ⟨Q.levelSubgroup_antitone i.val (i.val + 1) (Nat.le_succ _) hg,
    MulAction.mem_stabilizer_iff.2
      (Q.levelSubgroup_fixes_base_index (i.val + 1) g hg i (Nat.lt_succ_self _))⟩

end RawSchreierDatum

end CFSG.Certificates
