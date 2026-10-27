module

public import Certificates.Data.Kernel.Ivk8NormPC
public import CFSG.Certificates.Kernel.Ivk8NormPGlue
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.PK Subgroup

variable {n : ℕ}

theorem chkPC_spec (hn : n < 2 ^ 32) {r : VP n} {ps : List ℕ} {hss : List (List (ℕ × ℕ))}
    {L : List (VP n)} (h : chkPC n (wd n) r.1.1 ps hss (L.map fun y => y.1.1) = true) :
    ∀ y ∈ L, pkp y * pkp r = pkp r * pkp y → ∀ p ∈ ps, ∀ hs ∈ hss,
      chkP n (wd n) p hs [y.1.1] = true := by
  intro y hy hc p hp hs hhs
  have h1 := List.all_eq_true.1 h _ (List.mem_map_of_mem hy)
  have heq : cmpF n (wd n) y.1.1 r.1.1 = cmpF n (wd n) r.1.1 y.1.1 := by
    refine eq_of_repF (shr_cmp hn _ _) (shr_cmp hn _ _)
      (repF_cmp hn (repF_fst y) (repF_fst r)) ?_
    rw [hc]
    exact repF_cmp hn (repF_fst r) (repF_fst y)
  simp only [heq, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  simp only [chkP, List.all_cons, List.all_nil, Bool.and_true]
  exact h1 p hp hs hhs

theorem hN_of_chkPC (hn : n < 16777216) (hw : n + 1 < 2 ^ wd n) {p : ℕ} (hp : p.Prime)
    {H : Subgroup (Equiv.Perm (Fin n))} {xs : List (VP n)} (hxs : ∀ x ∈ xs, pkp x ∈ H)
    (c : VP n) {r : VP n} {ps : List ℕ} {hss : List (List (ℕ × ℕ))} {L : List (VP n)}
    (h : chkPC n (wd n) r.1.1 ps hss (L.map fun y => y.1.1) = true) (hpp : p ∈ ps)
    (hc : (subprodsV (xs.map (conjV (invV c)))).tail.map Subtype.val ∈ hss) :
    ∀ y ∈ L, pkp y * pkp r = pkp r * pkp y → orderOf (pkp y) = p → ∃ g ∈ H, g ∉ normalizer
      (zpowers (pkp c * pkp y * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n))) := by
  intro y hy hyc hyo
  exact hN_of_chkP hn hw hp hxs c (L := [y]) (chkPC_spec (by omega) h y hy hyc p hpp _ hc) y
    List.mem_cons_self hyo

theorem hhAll_spec {us L : List (VP n)} (h : hhAll us L = true) :
    ∀ y ∈ L, pkp y ≠ 1 → ∃ u ∈ us, pkp u * pkp u = 1 ∧
      (pkp y * pkp u * (pkp y)⁻¹) * (pkp y * pkp u * (pkp y)⁻¹) = 1 ∧
      pkp u * (pkp y * pkp u * (pkp y)⁻¹) = (pkp y * pkp u * (pkp y)⁻¹) * pkp u ∧
      pkp y * (pkp y * pkp u * (pkp y)⁻¹) * (pkp y)⁻¹ = pkp u * (pkp y * pkp u * (pkp y)⁻¹) ∧
      pkp y * pkp u * (pkp y)⁻¹ ≠ pkp u := by
  intro y hy hy1
  have h1 := List.all_eq_true.1 h y hy
  have hd : difV y (oneV n) = true := by
    rw [difV_eq_true_iff, pkp_oneV]
    exact hy1
  rw [hd, Bool.not_true, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨u, hu, hh⟩ := h1
  simp only [hhV, invoV, commV, Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hh
  have e1 := eq_of_not_difV h1
  have e2 := eq_of_not_difV h2
  have e3 := eq_of_not_difV h3
  have e4 := eq_of_not_difV h4
  rw [difV_eq_true_iff] at h5
  simp only [pkp_mulV, pkp_oneV, pkp_conjV] at e1 e2 e3 e4 h5
  exact ⟨u, hu, e1, e2, e3, e4, h5⟩

end CFSG.KS.Ivk8NormP

end
