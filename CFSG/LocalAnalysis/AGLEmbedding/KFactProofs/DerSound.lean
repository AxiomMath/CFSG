module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs
public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native

section

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true)

theorem der_mem (T : Subgroup (certMonoid c d sA sB)ˣ) :
    ∀ (ds : List Der) (av : List Nat), (∀ e ∈ ds, ∀ f ∈ e.facts, f ∈ C.facts) →
      (∀ r ∈ av, regUnit Sp hC r ∈ T ∧ ∃ o, MFact.ord r o ∈ C.facts) → derWf av ds = true →
      ∀ e ∈ ds, regUnit Sp hC e.reg ∈ T ∧ ∃ o, MFact.ord e.reg o ∈ C.facts
  | [], _, _, _, _ => fun _ he => absurd he List.not_mem_nil
  | e :: ds, av, hf, hav, hw => by
    simp only [derWf, Bool.and_eq_true] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hord : MFact.ord e.reg e.ord ∈ C.facts :=
      hf e List.mem_cons_self _ (by simp [Der.facts])
    have heq : MFact.eq [(e.reg, 1)] e.w ∈ C.facts :=
      hf e List.mem_cons_self _ (by simp [Der.facts])
    have hletter : ∀ q ∈ e.w, regUnit Sp hC q.1 ∈ T ∧ ∃ o, MFact.ord q.1 o ∈ C.facts :=
      fun q hq => hav q.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hw1 q hq))
    have hu : HasOrd C [(e.reg, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha
      rw [ha]
      exact ⟨e.ord, hord⟩
    have hmem : regUnit Sp hC e.reg ∈ T := by
      have := regUnit_eq Sp hC heq hu (fun q hq => (hletter q hq).2)
      have e1 : wordUnit Sp hC [(e.reg, 1)] = regUnit Sp hC e.reg := by simp [wordUnit]
      rw [e1] at this
      rw [this]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC T e.w
        fun q hq => (hletter q hq).1
    have hav' : ∀ r ∈ e.reg :: av, regUnit Sp hC r ∈ T ∧ ∃ o, MFact.ord r o ∈ C.facts := by
      intro r hr
      rcases List.mem_cons.1 hr with h | h
      · rw [h]
        exact ⟨hmem, e.ord, hord⟩
      · exact hav r h
    intro e' he'
    rcases List.mem_cons.1 he' with h | h
    · rw [h]
      exact ⟨hmem, e.ord, hord⟩
    · exact der_mem T ds (e.reg :: av) (fun e'' he'' => hf e'' (List.mem_cons_of_mem _ he''))
        hav' hw2 e' h

end

end CFSG.AGLEmbedding.R3
