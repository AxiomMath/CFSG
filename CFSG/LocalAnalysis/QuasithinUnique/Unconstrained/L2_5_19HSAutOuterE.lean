module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def qPerm (l : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (qGenT l)

@[expose] noncomputable def qWordPerm (ls : List ℕ) : Equiv.Perm (Fin 3850) := (ls.map qPerm).prod

@[expose] noncomputable def e1 : Equiv.Perm (Fin 3850) := qWordPerm e1Letters

@[expose] noncomputable def e2 : Equiv.Perm (Fin 3850) := qWordPerm e2Letters

@[expose] noncomputable def outerE : Subgroup (Equiv.Perm (Fin 3850)) :=
  Subgroup.closure ({e1, e2} : Set (Equiv.Perm (Fin 3850)))

theorem tabRep_natArr {T : CFSG.Sporadic.Th.Native.Table} (hsz : T.size = 3850)
    (hp : permOK 3850 T = true) :
    TabRep (natArr T) (tp 3850 T) :=
  ⟨by simp [natArr, hsz], fun i =>
    (co2Rep_natArr_iff (n := 3850)).2 (rep_tp hp) i⟩

theorem e1Letters_lt : ∀ l ∈ e1Letters, l < 4 := by decide

theorem e2Letters_lt : ∀ l ∈ e2Letters, l < 4 := by decide

theorem tabRep_qWordTab' (hq : ∀ l < 4, TabRep (natArr (qGenT l)) (qPerm l)) :
    ∀ {ls : List ℕ}, (∀ l ∈ ls, l < 4) → TabRep (qWordTab ls) (qWordPerm ls)
  | [], _ => by
    simpa [qWordTab, qWordPerm] using
      (TabRep.idTab : TabRep (idTab 3850) (1 : Equiv.Perm (Fin 3850)))
  | l :: ls, h => by
    have h1 := hq l (h l List.mem_cons_self)
    have h2 := tabRep_qWordTab' hq (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simpa [qWordTab, qWordPerm] using h1.comp h2

end CFSG.QuasithinUnique.Id2519.HSAut

end
