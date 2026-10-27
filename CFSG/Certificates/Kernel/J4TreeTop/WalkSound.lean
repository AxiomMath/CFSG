module

public import CFSG.Certificates.Kernel.J4TreeNode.Node
public import Certificates.Data.Kernel.J4TreeTopWalk

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

theorem walkOK_two_spec {T : Tabs} {B : List ℕ} {H : WHd} {e Ki ce m : ℕ} {l : List ℕ}
    (h : walkOK T B H e (2 :: Ki :: ce :: m :: l) = true) :
    invK (T.kel e) Ki = true ∧ ce < 2048 ∧ (e ≠ 0 ∨ ce = 0) ∧ (l.take m).length = m ∧
      (∀ i ∈ l.take m, i < H.vs.length) ∧
      (∀ b ∈ B, commK (M (T.eta ce) (T.kel e)) b = true) ∧
      spanAll (H.vas.map (fun c => translK (T.eta c)) ++ commV T (T.kel e) Ki H.vs ++
        ((l.take m).map fun i => H.vs.getD i 0).map (fun c => translK (T.eta c)) ++
        H.ws.map fun c => translK (T.eta c)) = true ∧
      ∀ I < 2 ^ m, wLeaf (H.gs.map (ccT T)) e ((l.drop m).headD 0)
        (prodFrom (M (T.eta ce) (T.kel e))
          (((l.take m).map fun i => H.vs.getD i 0).map fun c => M (M Ki (T.eta c)) (T.kel e)) I)
        I = true := by
  simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hinv, hce⟩, he⟩, hlen⟩, his⟩, hcomm⟩, hspan⟩, henum⟩ := h
  refine ⟨hinv, hce, he, hlen, his, hcomm, hspan, fun I hI => ?_⟩
  have := enumOK_spec henum I (by rw [List.length_map, List.length_map, hlen]; exact hI)
  simpa using this

theorem wLeaf_spec {G : List ℕ} {e L X I : ℕ} (h : wLeaf G e L X I = true) (hsq : sqOneK X = true)
    (h1 : e ≠ 0 ∨ I ≠ 0) : L.testBit I = true ∧ ∃ s ∈ G, commK s X = false := by
  unfold wLeaf at h
  have h0 : (e == 0 && I == 0) = false := by
    rcases h1 with h1 | h1 <;> simp [h1]
  rw [hsq, h0] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at h
  exact h


theorem walk_leaf_sound {T : Tabs} (hT : tabsOK T = true) {H : WHd}
    (hgs : H.gs.all coordOK = true) {e L X I : ℕ}
    (h : wLeaf (H.gs.map (ccT T)) e L X I = true) {x : J} (hx : PK x X) (hsq : x * x = 1)
    (h1 : e ≠ 0 ∨ I ≠ 0) :
    L.testBit I = true ∧ ∃ s ∈ H.gs.map burnsideJ4NP_treeElt, s * x ≠ x * s := by
  obtain ⟨hL, S, hS, hSc⟩ := wLeaf_spec h ((pk_sq hx).mp hsq) h1
  refine ⟨hL, ?_⟩
  have hG2 := forall₂_cc hT _ (List.all_eq_true.mp hgs)
  obtain ⟨s, hs, hsS⟩ := forall₂_exists' hG2 S hS
  exact ⟨s, hs, fun he => by rw [(pk_comm hsS hx).mp he] at hSc; exact Bool.noConfusion hSc⟩

end CFSG.KC.J4TreeT
