module

public import CFSG.Certificates.Kernel.HeLoc.GroupTabSound
public import CFSG.Certificates.Kernel.HeLoc.GroupBfsSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound

public section

namespace CFSG.KC.HeLoc

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartOne

variable {n : Nat}

theorem conjPointOK_of_table {c : CFSG.Monster.B.Fischer.ArrCert} {ps : List Nat} {N : Nat}
    {X : Nat → Equiv.Perm (Fin n)} {MT : Nat → Nat → Nat} {IV : Nat → Nat}
    (hN : c.pts.size = N) (hrep : ∀ i < N, Rep n c.pts[i]! (X i))
    (hsz : ∀ i < N, c.pts[i]!.size = n) (hN0 : 0 < N) (h0 : c.pts[0]! = idA n)
    (hkey : ∀ a < N, ∀ b < N, keyA n ps c.pts[a]! = keyA n ps c.pts[b]! → a = b)
    (hmt : ∀ a < N, ∀ b < N, MT a b < N ∧ X (MT a b) = X a * X b)
    (hiv : ∀ a < N, IV a < N ∧ X (IV a) = (X a)⁻¹) {r : Nat} (hr : r < N)
    {par lab dep : Nat → Nat}
    (ht : ∀ i < N, i = 0 ∨ (par i < N ∧ lab i < N ∧ dep i = dep (par i) + 1 ∧
      MT (MT (MT (lab i) r) (IV (lab i))) (par i) = i)) :
    conjPointOK n ps c r (enumBfs n (conjGens n c r) ps (c.pts.size + 1)) = true := by
  have hval : ∀ i < N, validA n c.pts[i]! = true := fun i hi =>
    CFSG.RankThree.Native.F2.validA_of_rep (hrep i hi)
  have hconj : ∀ j < N, Rep n (conjA n c.pts[j]! c.pts[r]!) (X j * X r * (X j)⁻¹) := fun j hj => by
    have h := rep_conjA (hval j hj) (hrep r hr)
    rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep (hrep j hj)] at h
  have hgs : (conjGens n c r).size = N := by rw [conjGens_size, hN]
  have hstep : ∀ k < N, ∀ i < N, MT (MT (MT k r) (IV k)) i < N ∧
      compA n (conjGens n c r)[k]! c.pts[i]! = c.pts[MT (MT (MT k r) (IV k)) i]! := by
    intro k hk i hi
    obtain ⟨h1, e1⟩ := hmt k hk r hr
    obtain ⟨h2, e2⟩ := hiv k hk
    obtain ⟨h3, e3⟩ := hmt _ h1 _ h2
    obtain ⟨h4, e4⟩ := hmt _ h3 i hi
    refine ⟨h4, ?_⟩
    rw [conjGens_get (by rw [hN]; exact hk)]
    refine arr_eq_of_rep (by simp [compA]) (hsz _ h4) (rep_compA (hconj k hk) (hrep i hi)) ?_
    rw [← e2, ← e1, ← e3, ← e4]
    exact hrep _ h4
  have hreach := reach_of_tree (n := n) (gs := conjGens n c r) (U := fun i => c.pts[i]!) (N := N)
    (par := par) (lab := lab) (dep := dep) h0 fun i hi => by
      rcases ht i hi with h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, by rw [hgs]; exact h2, h3, ?_⟩
        change c.pts[i]! = compA n (conjGens n c r)[lab i]! c.pts[par i]!
        rw [(hstep _ h2 _ h1).2, h4]
  have h := enumOK_of_reach (n := n) (ps := ps) (fuel := c.pts.size + 1) (gs := conjGens n c r)
    (N := N) (U := fun i => c.pts[i]!) hN0 hval ⟨0, hN0, h0⟩
    (fun i hi k hk => by
      rw [hgs] at hk
      exact ⟨_, (hstep k hk i hi).1, (hstep k hk i hi).2⟩)
    hkey hreach
    (fun k hk => by
      rw [hgs] at hk
      rw [conjGens_get (by rw [hN]; exact hk)]
      exact CFSG.RankThree.Native.F2.validA_of_rep (hconj k hk))
    (by omega)
  unfold conjPointOK
  rw [h.1, h.2, Bool.true_and]
  exact beq_iff_eq.2 hN.symm

end CFSG.KC.HeLoc

end
