module

public import Certificates.Data.Kernel.HMathieu.Normal
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Quasithin.Background.HFCodeInputs

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {T : PT 24} [hT : Fact (T.check = true)] {E invL P : List Nat}

theorem E_eq (H : Packed T E) : (List.finRange T.n).map (fun i => pk E (T.elemEquiv.symm i)) = E := by
  apply List.ext_getElem (by simp [n_eq H])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange]
  unfold pk
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, PT.elemEquiv]

theorem all_E (H : Packed T E) (F : Nat → Bool) :
    E.all F = (List.finRange T.n).all fun i => F (pk E (T.elemEquiv.symm i)) := by
  conv_lhs => rw [← E_eq H]
  rw [List.all_map]
  rfl

theorem pk_idxOf (H : Packed T E) (I : InvData T E invL P) {x : T.Elem}
    (hx : x ∈ T.invols ∨ x = 1) : P.getD (T.invols.idxOf x) 0 = pk E x := by
  rw [← pk_el H I (idxOf_le x), el_idxOf hx]

theorem normalChainB_eq (H : Packed T E) (I : InvData T E invL P)
    (hid : E.getD 0 0 = pidn 24 5) {l : List T.Elem} (hl : IsCommInvol l)
    (hR : ∀ x ∈ l, x ∈ T.invols) :
    normalChainB T l = normK E P (l.map T.invols.idxOf) ((subprods l).map T.invols.idxOf) := by
  have hS : ∀ s ∈ subprods l, s ∈ T.invols ∨ s = 1 := by
    intro s hs
    by_cases h1 : s = 1
    · exact Or.inr h1
    · exact Or.inl (mem_invols_iff.2 ⟨h1, sq_eq_one_of_mem_subprods hl s hs⟩)
  have hSP : ((subprods l).map T.invols.idxOf).map (fun s => P.getD s 0) =
      (subprods l).map (pk E) := by
    rw [List.map_map]
    exact List.map_congr_left fun s hs => pk_idxOf H I (hS s hs)
  unfold normalChainB normK
  rw [hSP, all_E H]
  refine all_congr_mem fun i _ => ?_
  rw [List.all_map]
  refine all_congr_mem fun a ha => ?_
  simp only [Function.comp_apply]
  have haR := hR a ha
  rw [pk_idxOf H I (Or.inl haR)]
  set g := T.elemEquiv.symm i
  have hc : conjP (pk E g) (pk E a) = pk E (g * a * g⁻¹) := by
    rw [conjP, pk_mul H, pk_mul H, pk_inv H hid]
  rw [hc, Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem, List.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨s, hs, e⟩
    rwa [← eq_of_pk H e]

end CFSG.KC.HMathieu

end
