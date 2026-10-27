module

public import Certificates.Data.Kernel.A6h2SwapK
public import CFSG.Certificates.Kernel.AE6TriSound

public section

namespace CFSG.KC.A6h2Swap

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri
  Certificates.AE6Model Certificates.A6h2Swap

theorem aeWord_append (u v : List Nat) :
    aeWord (curtisPerms ()) (u ++ v) = aeWord (curtisPerms ()) u * aeWord (curtisPerms ()) v := by
  simp [aeWord, List.map_append, List.prod_append]

theorem aeWord_nil : aeWord (curtisPerms ()) [] = 1 := rfl

theorem k0Elts_eq : k0Elts () =
    [1, aeWord (curtisPerms ()) (kWords.getD 0 []), (aeWord (curtisPerms ()) (kWords.getD 0 []))⁻¹,
      aeWord (curtisPerms ()) (kWords.getD 1 []), (aeWord (curtisPerms ()) (kWords.getD 1 []))⁻¹,
      aeWord (curtisPerms ()) (kWords.getD 0 []) * aeWord (curtisPerms ()) (kWords.getD 1 []),
      (aeWord (curtisPerms ()) (kWords.getD 0 []) * aeWord (curtisPerms ()) (kWords.getD 1 []))⁻¹,
      aeWord (curtisPerms ()) (kWords.getD 0 []) * aeWord (curtisPerms ()) (kWords.getD 0 [])] :=
  rfl

theorem mem_k0 : ∀ pq ∈ pqW,
    aeWord (curtisPerms ()) pq.1 * (aeWord (curtisPerms ()) pq.2)⁻¹ ∈ k0Elts () := by
  intro pq hpq
  rw [k0Elts_eq]
  simp only [pqW, List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [aeWord_nil, aeWord_append]

theorem swapCheck_of {G : List Nat}
    (hG : ∀ c, Orb.PRep 360 9 (G.getD c (pidn 360 9)) ((curtisPerms ()).getD c 1))
    (h : swapKN G = true) : swapCheck () = true := by
  have hw : ∀ w, Orb.PRep 360 9 (awN G w) (aeWord (curtisPerms ()) w) := prep_awN hG
  unfold swapKN at h
  unfold swapCheck
  simp only [List.all_eq_true, List.any_eq_true] at h ⊢
  intro k hk w hwk
  obtain ⟨pq, hpq, he⟩ := h k hk w hwk
  have e := (eqN_iff (hw _) (hw _)).1 he
  rw [aeWord_append, aeWord_append, aeWord_append] at e
  have key : (aeWord (curtisPerms ()) (swapConj.getD k []))⁻¹ * aeWord (curtisPerms ()) (imW k w) *
      aeWord (curtisPerms ()) (swapConj.getD k []) =
      aeWord (curtisPerms ()) pq.1 * (aeWord (curtisPerms ()) pq.2)⁻¹ := by
    calc _ = (aeWord (curtisPerms ()) (swapConj.getD k []))⁻¹ *
          (aeWord (curtisPerms ()) (imW k w) * aeWord (curtisPerms ()) (swapConj.getD k []) *
            aeWord (curtisPerms ()) pq.2) * (aeWord (curtisPerms ()) pq.2)⁻¹ := by group
      _ = _ := by rw [e]; group
  exact List.elem_iff.2 (key ▸ mem_k0 pq hpq)

end CFSG.KC.A6h2Swap
