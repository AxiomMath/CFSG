module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveSlp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Sporadic.LySchreier.Native

section Main

variable {nregs : ℕ} {prog : List Op} {Dz : L5ZSpec} {Dc : L5CSpec}

theorem coverPointDatum_of_ly5check
    (hp : Dc.p.Prime)
    (h : ly5Check (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
      [(pairAt asArr 2).1, (pairAt asArr 3).1, (pairAt asArr 4).1, (pairAt asArr 5).1,
        (pairAt asArr 6).1] (fun X => !stabOK X) nregs prog Dz Dc = true) :
    CoverPointDatum NativeSporadic.Ly Dc.p := by
  have : Fact Dc.p.Prime := ⟨hp⟩
  set Sp := specP 5 111 with hSp
  unfold ly5Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC0, -⟩, -⟩, hlen⟩, -⟩, hall⟩, hstab⟩, hsame⟩, hNF⟩, -⟩, hcwf⟩ := h
  let C : MCert := ⟨nregs, prog, Dz.facts ++ Dc.facts⟩
  have hC' : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true :=
    hC0
  have hmodf : ∀ f ∈ Mod.facts Dc.p Dc.m, f ∈ C.facts := by
    intro f hf
    simp only [C, L5CSpec.facts, List.mem_append]
    exact Or.inr (Or.inl (Or.inl hf))
  have hptf : ∀ b ∈ Dc.pts, ∀ f ∈ b.facts Dc.p, f ∈ C.facts := by
    intro b hb f hf
    simp only [C, L5CSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl (Or.inr ⟨b, hb, hf⟩))
  have hgenf : ∀ f ∈ Dc.gen.facts, f ∈ C.facts := by
    intro f hf
    simp only [C, L5CSpec.facts, List.mem_append]
    exact Or.inr (Or.inr hf)
  have hactord : ∀ g ∈ Dc.m.acts, MFact.ord g.reg g.ord ∈ C.facts := by
    intro g hg
    apply hmodf
    simp only [Mod.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  have hhord : ∀ b ∈ Dc.pts, ∀ k ∈ b.hs, MFact.ord k.reg k.ord ∈ C.facts := by
    intro b hb k hk
    apply hptf b hb
    simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨k, hk, by simp⟩
  have hb0 : MFact.ord Dc.m.b0 Dc.p ∈ C.facts := hmodf _ (by simp [Mod.facts])
  have hb1 : MFact.ord Dc.m.b1 Dc.p ∈ C.facts := hmodf _ (by simp [Mod.facts])
  have hb2 : MFact.ord Dc.m.b2 Dc.p ∈ C.facts := hmodf _ (by simp [Mod.facts])
  unfold L5CSpec.wf at hcwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcwf
  obtain ⟨⟨⟨-, hptwf⟩, hind⟩, hgenwf⟩ := hcwf
  have hindep : ∀ v ∈ nonzeroTriples Dc.p, ∃ q ∈ Dc.m.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2 := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
    simp only [Bool.and_eq_true, beq_iff_eq] at hqv
    exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
  obtain ⟨DS, h3, hact, hspan⟩ := exists_moduleSpec_core Sp hC' Dc.m hmodf hindep
  have hNFDS : DS.NoFun := noFun_of_entries h3 DS.M Dc.m.acts
    (fun g hg => by obtain ⟨j, -, hj⟩ := hact g hg; exact ⟨j, hj⟩)
    (fun v hv => noFun_of_bool (D := ⟨Dc.p, Dc.m, Dc.pts, 0, 0, 0, 0, [], [], []⟩) hNF v hv)
  have hbasis : ∀ w : Word, (∀ q ∈ w, q.1 = Dc.m.b0 ∨ q.1 = Dc.m.b1 ∨ q.1 = Dc.m.b2) →
      HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h | h
    · exact ⟨Dc.p, h ▸ hb0⟩
    · exact ⟨Dc.p, h ▸ hb1⟩
    · exact ⟨Dc.p, h ▸ hb2⟩
  have hptspan : ∀ b ∈ Dc.pts, regUnit Sp hC' b.reg ∈ DS.span ∧ regUnit Sp hC' b.reg ≠ 1 := by
    intro b hb
    have hbo : MFact.ord b.reg Dc.p ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
    have hbw := List.all_eq_true.1 hptwf b hb
    have hw' : ∀ q ∈ b.w, q.1 = Dc.m.b0 ∨ q.1 = Dc.m.b1 ∨ q.1 = Dc.m.b2 := by
      intro q hq
      have := List.all_eq_true.1 hbw q hq
      simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
    refine ⟨?_, ?_⟩
    · have hf : MFact.eq [(b.reg, 1)] b.w ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
      have hu : HasOrd C [(b.reg, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨Dc.p, hbo⟩
      have := regUnit_eq Sp hC' hf hu (hbasis b.w hw')
      have e : wordUnit Sp hC' [(b.reg, 1)] = regUnit Sp hC' b.reg := by simp [wordUnit]
      rw [e] at this
      rw [this, hspan]
      refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ b.w fun q hq => ?_
      apply Subgroup.subset_closure
      rcases hw' q hq with h | h | h
      · exact ⟨0, by simp [Mod.basis, h]⟩
      · exact ⟨1, by simp [Mod.basis, h]⟩
      · exact ⟨2, by simp [Mod.basis, h]⟩
    · have hf : MFact.ne [(b.reg, 1)] [] b.t ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
      have hu : HasOrd C [(b.reg, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨Dc.p, hbo⟩
      have := regUnit_ne Sp hC' hf hu (hasOrd_nil C)
      simpa [wordUnit] using this
  let hh : (j : Fin Dc.pts.length) → Fin (Dc.pts.get j).hs.length →
      NativeSporadic.Ly := fun j i => regUnit Sp hC' ((Dc.pts.get j).hs.get i).reg
  let S : Set NativeSporadic.Ly := Set.range DS.g ∪ ⋃ j, Set.range (hh j)
  have hactG : ∀ r ∈ Dc.actRegs, regUnit Sp hC' r ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    rcases List.mem_append.1 hr with h1 | h1
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j, hj, -⟩ := hact g hg
      exact ⟨Subgroup.subset_closure (Or.inl ⟨j, by rw [hj]⟩), g.ord, hactord g hg⟩
    · obtain ⟨b, hb, h2⟩ := List.mem_flatMap.1 h1
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h2
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hk
      exact ⟨Subgroup.subset_closure (Or.inr (Set.mem_iUnion.2 ⟨j, ⟨i, rfl⟩⟩)), _,
        hhord _ hb _ hk⟩
  have hel : ∀ j < 5, (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[(Dc.gen.els.getD j default).reg]! (pairAt asArr (j + 2)).1 =
        true := by
    intro j hj
    have := List.all_eq_true.1 hall j (List.mem_range.2 hj)
    rw [hsame.1]
    interval_cases j <;> exact this
  have hs : stabOK (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[
      Dc.gen.rs]! = false := by
    rw [hsame.2]
    simpa using hstab
  have hlen' : Dc.gen.els.length = 5 := by rw [hsame.1]; exact hlen
  have hgen : Subgroup.closure S = ⊤ :=
    ly_gen_top5 hC' Dc.gen hgenf hlen' hel hs fun q hq =>
      hactG q.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hgenwf q hq))
  refine ⟨DS, Dc.pts.length, fun j => regUnit Sp hC' (Dc.pts.get j).reg,
    fun j => (Dc.pts.get j).hs.length, hh, fun j i => ((Dc.pts.get j).hs.get i).e,
    Or.inl h3.ge, hNFDS, fun j => hptspan _ (List.get_mem _ _), ?_, hgen⟩
  intro j i
  show regUnit Sp hC' ((Dc.pts.get j).hs.get i).reg * regUnit Sp hC' (Dc.pts.get j).reg *
    (regUnit Sp hC' ((Dc.pts.get j).hs.get i).reg)⁻¹ =
      regUnit Sp hC' (Dc.pts.get j).reg ^ ((Dc.pts.get j).hs.get i).e
  have hb := List.get_mem Dc.pts j
  have hk := List.get_mem (Dc.pts.get j).hs i
  have hf : MFact.conj ((Dc.pts.get j).hs.get i).reg [((Dc.pts.get j).reg, 1)]
      [((Dc.pts.get j).reg, ((Dc.pts.get j).hs.get i).e)] ∈ C.facts := by
    apply hptf _ hb
    simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨_, hk, by simp⟩
  have hbo : MFact.ord (Dc.pts.get j).reg Dc.p ∈ C.facts := hptf _ hb _ (by simp [CpPt.facts])
  have hu : HasOrd C [((Dc.pts.get j).reg, 1)] := fun a ha => by
    simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨Dc.p, hbo⟩
  have hw : HasOrd C [((Dc.pts.get j).reg, ((Dc.pts.get j).hs.get i).e)] := fun a ha => by
    simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨Dc.p, hbo⟩
  have := regUnit_conj Sp hC' hf (hhord _ hb _ hk) hu hw
  simpa [wordUnit] using this

end Main

end CFSG.AGLEmbedding.R3
