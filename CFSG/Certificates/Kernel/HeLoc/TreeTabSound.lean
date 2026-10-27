module

public import Certificates.Data.Kernel.HeLoc.TreeTab
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.HeLoc

open CFSG.KS.SporSch CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Misc.Clos (allN_iff)
open CFSG.KS (bAnd_iff)

variable {n : Nat} {gp : Nat → Equiv.Perm (Fin n)} {P Lb T : Nat → Nat} {gs : Array (Array Nat)}
  {g rd : Nat → Nat → Nat} {ng N : Nat} {bs : List Nat}

theorem strictB_tab (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem repF_of_eqOnL {f f' : Nat → Nat} {σ : Equiv.Perm (Fin n)} (hbs : ∀ x < n, x ∈ bs)
    (h : eqOnL bs f f' = true) (h' : RepF n f' σ) : RepF n f σ := fun x hx => by
  rw [(eqOnL_iff bs f f').1 h x (hbs x hx)]
  exact h' x hx

theorem repF_tab (ht : TreeOK ng N P Lb) (hg : ∀ k < ng, RepF n (g k) (gp k))
    (hbs : ∀ x < n, x ∈ bs) (hT : ∀ i < N, tabAtK g rd T P Lb bs i = true) :
    ∀ i < N, RepF n (rd (T i)) (treePerm gp P Lb i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hN
    have h := hT i hN
    unfold tabAtK at h
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [treePerm_zero]
      simp only [strictB_tab] at h
      exact repF_of_eqOnL hbs h RepF.one
    · obtain ⟨hp, hl⟩ := ht i hN h0
      rw [treePerm_pos ⟨h0, hp⟩]
      simp only [strictB_tab, beq_zero_false h0] at h
      exact repF_of_eqOnL hbs h ((hg (Lb i) hl).comp (ih (P i) hp (by omega)))

theorem edges_of_edgeTK (ht : TreeOK ng N P Lb) (hg : ∀ k < ng, RepF n (g k) (gp k))
    (hgs : ∀ k < ng, Rep n gs[k]! (gp k)) (hbs : ∀ x < n, x ∈ bs)
    (hT : ∀ i < N, tabAtK g rd T P Lb bs i = true) {E : Nat → Nat → Nat}
    (hE : ∀ i < N, edgeTK g rd T E N ng bs i = true) :
    ∀ i < N, ∀ k < ng, E i k < N ∧
      treeArr n gs P Lb (E i k) = compA n gs[k]! (treeArr n gs P Lb i) := by
  intro i hi k hk
  have h := hE i hi
  unfold edgeTK at h
  rw [strictB_tab] at h
  have h1 := (allN_iff _ _).1 h k hk
  simp only [strictB_tab, bAnd_iff, Nat.blt_eq] at h1
  obtain ⟨hlt, heq⟩ := h1
  have hperm : treePerm gp P Lb (E i k) = gp k * treePerm gp P Lb i :=
    RepF.unique (repF_tab ht hg hbs hT (E i k) hlt)
      (repF_of_eqOnL hbs heq ((hg k hk).comp (repF_tab ht hg hbs hT i hi)))
  refine ⟨hlt, arr_eq_of_rep (x := treePerm gp P Lb (E i k)) (size_treeArr _) (by simp [compA])
    (rep_treeArr ht hgs _ hlt) ?_⟩
  rw [hperm]
  exact rep_compA (hgs k hk) (rep_treeArr ht hgs i hi)

end CFSG.KC.HeLoc

end
