module

public import Certificates.Data.Kernel.ThBfs.Defs
public import CFSG.Sporadic.Schreier.LyBFS
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.ThBfs

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.Sporadic.LySchreier
open CFSG.KC.Misc.Clos (sortAt sort_distinct)

theorem bfsAt_spec {A : ℕ → ℕ → ℕ} {B nG n : ℕ} {R C S : ℕ → ℕ} {i : ℕ}
    (h : bfsAt A B nG n R C S i = true) :
    keyAt R i < B ∧ sortAt n (keyAt R) S i = true ∧
      (∀ k < nG, C (nG * i + k) < n ∧ keyAt R (C (nG * i + k)) = A (keyAt R i) k ∧
        (C (nG * i + k) = 0 ∨ discAt R (C (nG * i + k)) ≤ nG * i + k)) ∧
      (0 < i → discAt R i < nG * i ∧ C (discAt R i) = i ∧
        (i + 1 < n → discAt R i < discAt R (i + 1))) := by
  unfold bfsAt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := (andB_iff.1 h).imp_right fun h =>
    (andB_iff.1 h).imp_right fun h => andB_iff.1 h
  refine ⟨blt_iff.1 h1, h2, fun k hk => ?_, fun hi => ?_⟩
  · have hk' := (allN_iff _ _).1 h3 k hk
    unfold imgAt at hk'
    rw [letB_eq, letB_eq] at hk'
    obtain ⟨a, hk'⟩ := andB_iff.1 hk'
    obtain ⟨b, c⟩ := andB_iff.1 hk'
    refine ⟨blt_iff.1 a, beq_iff.1 b, ?_⟩
    rcases orB_iff.1 c with c | c
    · exact Or.inl (beq_iff.1 c)
    · exact Or.inr (Nat.le_of_ble_eq_true c)
  · unfold treeK at h4
    have h5 := impB_iff.1 h4 (blt_iff.2 hi)
    obtain ⟨a, h5⟩ := andB_iff.1 h5
    obtain ⟨b, c⟩ := andB_iff.1 h5
    exact ⟨blt_iff.1 a, beq_iff.1 b, fun hn => blt_iff.1 (impB_iff.1 c (blt_iff.2 hn))⟩

theorem bfsAt_sound {M : Type*} [DecidableEq M] (gs : List (M → M)) (dec : ℕ → M)
    {A : ℕ → ℕ → ℕ} {B : ℕ}
    (hA : ∀ e < B, ∀ k (hk : k < gs.length), dec (A e k) = gs[k] (dec e))
    (hdec : ∀ a < B, ∀ b < B, dec a = dec b → a = b)
    {n : ℕ} {R C S : ℕ → ℕ} (hn : 1 ≤ n) (hall : ∀ i < n, bfsAt A B gs.length n R C S i = true)
    {root : M} (h0 : dec (keyAt R 0) = root) {N : ℕ} (hN : n ≤ N + 1) :
    bfsList gs root N = (List.range n).map fun i => dec (keyAt R i) := by
  have hs := fun i (hi : i < n) => bfsAt_spec (hall i hi)
  have hdisc : ∀ j, discPos gs (fun j => discAt R j / gs.length)
      (fun j => discAt R j % gs.length) j = discAt R j := fun j => by
    unfold discPos
    exact Nat.div_add_mod' _ _
  have hdist := sort_distinct fun i hi => (hs i hi).2.1
  refine bfsList_eq (img := fun k i => C (gs.length * i + k)) (par := fun j => discAt R j / gs.length)
    (lab := fun j => discAt R j % gs.length) ?_ ?_ ?_ ?_ ?_ hn h0 hN
  · intro j hj hjn
    rw [hdisc, hdisc]
    exact ((hs j (by omega)).2.2.2 (by omega)).2.2 hjn
  · intro i hi j hj hij
    exact hdist i hi j hj (hdec _ (hs i hi).1 _ (hs j hj).1 hij)
  · intro i hi k hk
    obtain ⟨h1, h2, -⟩ := (hs i hi).2.2.1 k hk
    refine ⟨h1, ?_⟩
    change gs[k] (dec (keyAt R i)) = dec (keyAt R (C (gs.length * i + k)))
    rw [h2, hA _ (hs i hi).1 k hk]
  · intro j hj hjn
    obtain ⟨h1, h2, -⟩ := (hs j hjn).2.2.2 (by omega)
    have hpos : 0 < gs.length := by
      rcases Nat.eq_zero_or_pos gs.length with h | h
      · rw [h, Nat.zero_mul] at h1
        omega
      · exact h
    refine ⟨(Nat.div_lt_iff_lt_mul hpos).2 (by rw [Nat.mul_comm]; exact h1),
      Nat.mod_lt _ hpos, ?_⟩
    change C (gs.length * (discAt R j / gs.length) + discAt R j % gs.length) = j
    rw [Nat.div_add_mod]
    exact h2
  · intro i hi k hk
    obtain ⟨-, -, h3⟩ := (hs i hi).2.2.1 k hk
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · right
      change discPos gs _ _ (C (gs.length * i + k)) ≤ i * gs.length + k
      rw [hdisc, Nat.mul_comm i]
      exact h3

end CFSG.KC.ThBfs

end
