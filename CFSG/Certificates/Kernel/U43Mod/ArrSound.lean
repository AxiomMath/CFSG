module

public import Certificates.Data.U43Model
public import CFSG.Certificates.Kernel.U43Mod.WordSound
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.U43Mod

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.U43

variable {n : ℕ}

theorem isInvA_of_rep {t r : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hr : Rep n r g⁻¹) : isInvA n t r = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ht.apply hi]
  refine ⟨(g ⟨i, hi⟩).2, ?_⟩
  rw [hr.apply (g ⟨i, hi⟩).2]
  simp

theorem invArrs_size (G : Array (Array ℕ)) : (invArrs n G).size = G.size := Array.size_map ..

theorem invArrs_get {G : Array (Array ℕ)} {i : ℕ} (hi : i < G.size) :
    (invArrs n G)[i]! = invCand n G[i]! := by
  rw [getElem!_pos (invArrs n G) i (by rw [invArrs_size]; exact hi), getElem!_pos G i hi]
  exact Array.getElem_map ..

theorem rep_invArrs {G : Array (Array ℕ)} {i : ℕ} {g : Equiv.Perm (Fin n)} (hi : i < G.size)
    (h : Rep n G[i]! g) : Rep n (invArrs n G)[i]! g⁻¹ := by
  rw [invArrs_get hi]
  exact CFSG.KS.Raw.rep_invCand h

theorem invsOK_invArrs {G : Array (Array ℕ)} (h : ∀ i < G.size, ∃ g, Rep n G[i]! g) :
    invsOK n G (invArrs n G) = true := by
  rw [invsOK, Bool.and_eq_true, beq_iff_eq, invArrs_size, allLt_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨g, hg⟩ := h i hi
  exact isInvA_of_rep hg (rep_invArrs hi hg)

@[expose] def ArrRep (n : ℕ) (G Gi : Array (Array ℕ)) (g : ℕ → Equiv.Perm (Fin n)) (i : ℕ) :
    Prop :=
  Rep n G[i]! (g i) ∧ Rep n Gi[i]! (g i)⁻¹

theorem rep_lettArr {G Gi : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin n)} {l : ℕ × Bool}
    (h : ArrRep n G Gi g l.1) : Rep n (lettArr G Gi l) (letterVal g l) := by
  obtain ⟨i, s⟩ := l
  cases s
  · simpa [lettArr, letterVal] using h.2
  · simpa [lettArr, letterVal] using h.1

theorem rep_evalArr {G Gi : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin n)} :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, ArrRep n G Gi g l.1) → Rep n (evalArr n G Gi w) (evalG g w)
  | [], _ => by
    rw [evalArr]
    simpa [evalG] using (rep_idA : Rep n (idA n) 1)
  | l :: w, hw => by
    rw [evalArr, evalG_cons]
    exact rep_compA (rep_lettArr (hw l List.mem_cons_self))
      (rep_evalArr w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem arrRep_genAB {tA tB : Array ℕ} {gA gB : Equiv.Perm (Fin n)} (hA : Rep n tA gA)
    (hB : Rep n tB gB) {i : ℕ} (hi : i < 2) :
    ArrRep n (genAB tA tB) (invArrs n (genAB tA tB)) (fun i => if i = 0 then gA else gB) i := by
  have hs : (genAB tA tB).size = 2 := rfl
  have h : Rep n (genAB tA tB)[i]! (if i = 0 then gA else gB) := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simpa [genAB] using hA
    · simpa [genAB] using hB
  exact ⟨h, rep_invArrs (hs ▸ hi) h⟩

theorem rep_wArr {tA tB : Array ℕ} {gA gB : Equiv.Perm (Fin n)} (hA : Rep n tA gA)
    (hB : Rep n tB gB) {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 2) :
    Rep n (wArr n tA tB w) (evalG (fun i => if i = 0 then gA else gB) w) :=
  rep_evalArr w fun l hl => arrRep_genAB hA hB (hw l hl)

end CFSG.KS.U43Mod

end
