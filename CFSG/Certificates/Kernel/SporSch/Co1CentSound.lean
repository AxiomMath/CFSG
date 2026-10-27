module

public import Certificates.Data.Kernel.SporSch.Co1Cent
public import CFSG.Certificates.Kernel.SporSch.Co1TowerSound
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound
public import CFSG.Sporadic.Co1Block.CentCheck

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block.Native CFSG.KS.Raw
  CFSG.KS.SporSch.VOrb CFSG.Sporadic.SmallF2.Native

theorem commK_sound {M : Nat → Nat} {P : Nat} : ∀ {l : List Nat}, commK M P l = true →
    ∀ j ∈ l, mulK (M (j - 1)) P = mulK P (M (j - 1))
  | [], _ => by simp
  | j :: l, h => by
    change Bool.rec false (commK M P l) (Nat.beq (mulK (M (j - 1)) P) (mulK P (M (j - 1)))) =
      true at h
    cases hb : Nat.beq (mulK (M (j - 1)) P) (mulK P (M (j - 1)))
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact Nat.eq_of_beq_eq_true hb
      · exact commK_sound h k hk

theorem bindFromK_sound {M M' : Nat → Nat} : ∀ {l : List Nat} {k : Nat},
    bindFromK M M' l k = true → ∀ (i : Nat) (hi : i < l.length), M' (k + i) = M (l[i] - 1)
  | [], _, _ => by simp
  | j :: l, k, h => by
    change Bool.rec false (bindFromK M M' l (k + 1)) (Nat.beq (M' k) (M (j - 1))) = true at h
    cases hb : Nat.beq (M' k) (M (j - 1))
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      intro i hi
      rcases i with _ | i
      · exact Nat.eq_of_beq_eq_true hb
      · rw [← Nat.add_assoc, Nat.add_right_comm]
        exact bindFromK_sound h i (by simpa using hi)

theorem mul_unpackK (X Y : Nat) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = unpack 24 24 (mulK X Y) :=
  mulEqK_sound (Z := mulK X Y) (Nat.beq_refl _)

theorem brayElts_of_K {tR : Rows} {d₁ : List (List Int)} {bidx : List Nat}
    {M MI M' : Nat → Nat} {N : Nat}
    (hb : [aR, bR, tR] = (List.range 3).map fun i => unpack 24 24 (M i))
    (hD : dagIK M MI 3 N d₁ = true)
    (hidx : bidx.all (fun j => decide (3 < j) && decide (j ≤ N)) = true)
    (hbind : bindK M M' bidx = true) :
    brayElts (brayRows tR d₁) bidx = (List.range bidx.length).map fun i => unpack 24 24 (M' i) := by
  have e₁ : brayRows tR d₁ = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := dagIK_sound hb hD
  have hj : ∀ j ∈ bidx, 3 < j ∧ j ≤ N := fun j hj => by
    simpa using List.all_eq_true.1 hidx j hj
  have hget : ∀ j ∈ bidx, ((List.range N).map fun i => unpack 24 24 (M i)).getD (j - 1) (one ()) =
      unpack 24 24 (M (j - 1)) := fun j hj' => by
    have := hj j hj'
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hbi : ∀ (i : Nat) (hi : i < bidx.length), M' i = M (bidx[i] - 1) := fun i hi => by
    simpa using bindFromK_sound (k := 0) hbind i hi
  rw [e₁]
  apply List.ext_getElem (by simp [brayElts])
  intro i h₁ h₂
  simp only [brayElts, List.length_map] at h₁
  simp only [brayElts, List.getElem_map, List.getElem_range]
  rw [hget _ (List.getElem_mem h₁), ← hbi i h₁]

theorem centCheckOf_of_K {tR : Rows} {d₁ d₂ : List (List Int)} {bidx base sizes : List Nat}
    {gens : List (List Nat)} {M MI M' MI' : Nat → Nat} {P N N' : Nat}
    (ht : tR = unpack 24 24 P)
    (hb : [aR, bR, tR] = (List.range 3).map fun i => unpack 24 24 (M i))
    (hD : dagIK M MI 3 N d₁ = true)
    (hidx : bidx.all (fun j => decide (3 < j) && decide (j ≤ N)) = true)
    (hbind : bindK M M' bidx = true)
    (hD' : dagIK M' MI' bidx.length N' d₂ = true)
    (hc : commK M P bidx = true)
    (hn : ∀ i < base.length, 0 < sizes.getD i 0 ∧ sizes.getD i 0 < 131072)
    (hl : ∀ i < base.length, ∃ (T E S C : Nat → Nat) (NS L : Nat),
      levelHd N' (gens.getD i []) (base.getD i 0) T = true ∧ C 0 = 1 ∧
        C NS = sizes.getD i 0 ∧ sizes.getD i 0 ≤ NS * L ∧
        (∀ s < NS, levelSl M' (gens.getD i []) (sizes.getD i 0) T E (s * L) L (C s) (C (s + 1)) =
          true) ∧
        (∀ s < NS, permSl S T (sizes.getD i 0) (s * L) L = true) ∧
        fixesK M' (gens.getD i []) base i = true) :
    centCheckOf tR d₁ bidx d₂ base gens sizes = true := by
  have e₁ : brayRows tR d₁ = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := dagIK_sound hb hD
  have hj : ∀ j ∈ bidx, 3 < j ∧ j ≤ N := fun j hj => by
    simpa using List.all_eq_true.1 hidx j hj
  have hbi : ∀ (i : Nat) (hi : i < bidx.length), M' i = M (bidx[i] - 1) := fun i hi => by
    simpa using bindFromK_sound (k := 0) hbind i hi
  have hB := brayElts_of_K hb hD hidx hbind
  have e₂ := dagIK_sound hB hD'
  have hcols : (((List.range N').map fun i => unpack 24 24 (M' i)).toArray.map (transposeRows 24)) =
      Array.ofFn (n := N') fun j => transposeRows 24 (unpack 24 24 (M' j.val)) := by
    apply Array.ext (by simp)
    intro i h₁ h₂
    simp
  have hcm := commK_sound hc
  dsimp only [centCheckOf]
  rw [e₂, hB, e₁, hcols, tower_sound hn hl]
  simp only [Bool.and_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true, List.length_map,
    List.length_range, decide_eq_true_eq]
  refine ⟨fun j hj' => hj j hj', fun g hg => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  have hi' : i < bidx.length := List.mem_range.1 hi
  rw [ht, mul_unpackK, mul_unpackK, hbi i hi', hcm _ (List.getElem_mem hi')]
  exact beq_self_eq_true _

end CFSG.KS.SporSch.M24

end
