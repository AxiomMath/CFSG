module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {D : RSpec} {tabs : List RLin}

include Sp in
theorem rankLiftDatum_of_check (hp : D.p.Prime)
    (h : rlCheck O sA sB nregs prog D tabs = true) :
    RankLiftDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold rlCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩, hlin⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [RSpec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [RSpec.facts]
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [RSpec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [RSpec.facts]
  have hpcf : ∀ q ∈ D.pc, ∀ f ∈ q.facts D.p, f ∈ D.facts := by
    intro q hq f hf
    simp only [RSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨q, hq, hf⟩))
  have hmodf : ∀ m ∈ D.mods, ∀ f ∈ m.facts D.p, f ∈ D.facts := by
    intro m hm f hf
    simp only [RSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨m, hm, hf⟩)
  have hderf : ∀ e ∈ D.ders, ∀ f ∈ e.facts, f ∈ C.facts := by
    intro e he f hf
    show f ∈ D.facts
    simp only [RSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hf⟩
  unfold RSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨-, hpcwf⟩, hmodwf⟩, hderwf⟩, hseedwf⟩ := hwf
  unfold RSpec.linOK at hlin
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hlin
  obtain ⟨hlen, hlinall⟩ := hlin
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ D.pc, u = regUnit Sp hC' q.reg}
  have hP : IsPGroup D.p P := chain_isPGroup Sp hC' D.pc hpcwf hpcf
  have hactord : ∀ m ∈ D.mods, ∀ g ∈ m.nm.acts, MFact.ord g.reg g.ord ∈ C.facts := by
    intro m hm g hg
    apply hmodf m hm
    simp only [RMod.facts, List.mem_append, NMod.facts, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨g, hg, by simp⟩)
  have hmods : ∀ i : Fin D.mods.length, ∃ DS : ModuleSpec (certMonoid c d sA sB)ˣ D.p,
      ((3 ≤ DS.n ∧ DS.NoAlt) ∨ (2 ≤ DS.n ∧ DS.NoAlt ∧ DS.NoFun)) ∧ DS.span ≤ P ∧
      ∀ g ∈ (D.mods.get i).nm.acts, regUnit Sp hC' g.reg ∈ Set.range DS.g := by
    intro i
    set m : RMod := D.mods.get i with hmdef
    have hm : m ∈ D.mods := List.get_mem _ _
    have hgetD : D.mods.getD i.val default = m := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
      rfl
    have hlin1 := hlinall i.val i.2
    rw [hgetD] at hlin1
    obtain ⟨halt, hfunor⟩ := hlin1
    have hmw := List.all_eq_true.1 hmodwf m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmw
    obtain ⟨⟨⟨hwfm, hrank⟩, hwlen⟩, hwords⟩ := hmw
    have hf : ∀ f ∈ m.nm.facts D.p, f ∈ C.facts := by
      intro f hf
      apply hmodf m hm
      simp only [RMod.facts, List.mem_append]
      exact Or.inl hf
    let DS := NMod.spec Sp hC' m.nm hf hwfm
    have hDSn : DS.n = m.nm.basis.length := rfl
    refine ⟨DS, ?_, ?_, ?_⟩
    · have hNA : DS.NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
      rcases Bool.or_eq_true_iff.1 hfunor with h3 | hfun
      · left
        exact ⟨by rw [hDSn]; exact of_decide_eq_true h3, hNA⟩
      · right
        exact ⟨by rw [hDSn]; exact hrank, hNA, fun v hv => noFun_of_funOK hfun v hv⟩
    ·
      rw [ModuleSpec.span, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      have hk : k.val < m.nm.basis.length := k.2
      have hkw : k.val < m.ws.length := by rw [hwlen]; exact hk
      have hword : (m.ws.getD k.val []).all (fun a => D.pc.any (·.reg == a.1)) = true := by
        apply List.all_eq_true.1 hwords
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkw, Option.getD_some]
        exact List.getElem_mem hkw
      have hfeq : MFact.eq [(m.nm.basis.getD k.val 0, 1)] (m.ws.getD k.val []) ∈ D.facts := by
        apply hmodf m hm
        simp only [RMod.facts, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨k.val, hk, rfl⟩
      have hb : MFact.ord (m.nm.basis.getD k.val 0) D.p ∈ C.facts := basis_ord_N hf hk
      have hu : HasOrd C [(m.nm.basis.getD k.val 0, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hb⟩
      have := regUnit_eq Sp hC' hfeq hu (hasOrd_of_chain D.pc hpcf hword)
      have e : wordUnit Sp hC' [(m.nm.basis.getD k.val 0, 1)] =
          regUnit Sp hC' (m.nm.basis.getD k.val 0) := by simp [wordUnit]
      rw [e] at this
      show regUnit Sp hC' (m.nm.basis.getD k.val 0) ∈ P
      rw [this]
      exact wordUnit_mem_chain Sp hC' D.pc hword
    · intro g hg
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
      exact ⟨j, rfl⟩
  choose Dm hDm hDmP hDmR using hmods
  refine ⟨D.mods.length, Dm, P, hP, hDmP, hDm, ?_⟩
  set T : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure (⋃ i, Set.range (Dm i).g) with hT
  have hav : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈ T ∧ ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    simp only [RSpec.actRegs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨m, hm, g, hg, rfl⟩ := hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hm
    exact ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hDmR i g hg⟩),
      g.ord, hactord _ (List.get_mem _ _) g hg⟩
  have hders := der_mem Sp hC' T D.ders D.actRegs hderf hav hderwf
  have hseeds : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈ T ∧ ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    have := List.contains_iff_mem.1 (List.all_eq_true.1 hseedwf q hq)
    rcases List.mem_append.1 this with h1 | h1
    · obtain ⟨e, he, heq⟩ := List.mem_map.1 h1
      rw [← heq]
      exact hders e he
    · exact hav _ h1
  have hrA' : D.rA < C.nregs := hrA
  have hrB' : D.rB < C.nregs := hrB
  have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rA) =
      NativeSporadic.decode c d 1 sA := by
    rw [val_regUnit Sp hC' fordA, Sp.toMat_eq (reg_ok Sp hC' hrA').1 (Sp.decode_wf sA) hAeq,
      Sp.toMat_decode]
  have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rB) =
      NativeSporadic.decode c d 1 sB := by
    rw [val_regUnit Sp hC' fordB, Sp.toMat_eq (reg_ok Sp hC' hrB').1 (Sp.decode_wf sB) hBeq,
      Sp.toMat_decode]
  have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top (certMonoid c d sA sB) rfl
    (regUnit Sp hC' D.rA) (regUnit Sp hC' D.rB) hvalA hvalB
  have hAw : regUnit Sp hC' D.rA = wordUnit Sp hC' D.wA := by
    have := regUnit_eq Sp hC' feA (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
      (fun q hq => (hseeds q (List.mem_append.2 (Or.inl hq))).2)
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (fun q hq => (hseeds q (List.mem_append.2 (Or.inr hq))).2)
    simpa [wordUnit] using this
  refine eq_top_iff.mpr ?_
  rw [← htop, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · rw [hAw]
    exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
      (hseeds q (List.mem_append.2 (Or.inl hq))).1
  · rw [hBw]
    exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
      (hseeds q (List.mem_append.2 (Or.inr hq))).1

end Main

end CFSG.AGLEmbedding.R3
