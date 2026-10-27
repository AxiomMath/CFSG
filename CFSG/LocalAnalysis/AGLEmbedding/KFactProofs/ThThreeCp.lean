module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeSlp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.Th

section Main

variable {nregs : ℕ} {prog : List Op} {D : CZSpec}

theorem coverPointDatum_of_zcheck
    (hp : D.p.Prime)
    (h : czCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 nregs prog D = true) :
    CoverPointDatum NativeSporadic.Th D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  set Sp := spec2 248 with hSp
  unfold czCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hC, hAeq⟩, hBeq⟩, hNF⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 C = true := hC
  have hslpf : ∀ f ∈ thSlpFacts, f ∈ D.facts := by
    intro f hf
    simp only [CZSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inl hf))
  have hmodf : ∀ f ∈ D.m.facts D.p, f ∈ D.facts := by
    intro f hf
    simp only [CZSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hf))
  have hptf : ∀ b ∈ D.pts, ∀ f ∈ b.facts D.p, f ∈ D.facts := by
    intro b hb f hf
    simp only [CZSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨b, hb, hf⟩)
  have hgenf : ∀ f ∈ D.gen.facts, f ∈ D.facts := by
    intro f hf
    simp only [CZSpec.facts, List.mem_append]
    exact Or.inr hf
  have hactord : ∀ g ∈ D.m.acts, MFact.ord g.reg g.ord ∈ D.facts := by
    intro g hg
    apply hmodf
    simp only [Mod.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  have hhord : ∀ b ∈ D.pts, ∀ k ∈ b.hs, MFact.ord k.reg k.ord ∈ D.facts := by
    intro b hb k hk
    apply hptf b hb
    simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨k, hk, by simp⟩
  have hb0 : MFact.ord D.m.b0 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  have hb1 : MFact.ord D.m.b1 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  have hb2 : MFact.ord D.m.b2 D.p ∈ D.facts := hmodf _ (by simp [Mod.facts])
  unfold CZSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨-, hptwf⟩, hind⟩, hgenwf⟩ := hwf
  have hindep : ∀ v ∈ nonzeroTriples D.p, ∃ q ∈ D.m.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2 := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
    simp only [Bool.and_eq_true, beq_iff_eq] at hqv
    exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
  obtain ⟨DS, h3, hact, hspan⟩ := exists_moduleSpec_core Sp hC' D.m hmodf hindep
  have hNFDS : DS.NoFun := noFun_of_entries h3 DS.M D.m.acts
    (fun g hg => by obtain ⟨j, -, hj⟩ := hact g hg; exact ⟨j, hj⟩)
    (fun v hv => noFun_of_bool (D := ⟨D.p, D.m, D.pts, 0, 0, 0, 0, [], [], []⟩) hNF v hv)
  have hbasis : ∀ w : Word, (∀ q ∈ w, q.1 = D.m.b0 ∨ q.1 = D.m.b1 ∨ q.1 = D.m.b2) →
      HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h | h
    · exact ⟨D.p, h ▸ hb0⟩
    · exact ⟨D.p, h ▸ hb1⟩
    · exact ⟨D.p, h ▸ hb2⟩
  have hptspan : ∀ b ∈ D.pts, regUnit Sp hC' b.reg ∈ DS.span ∧ regUnit Sp hC' b.reg ≠ 1 := by
    intro b hb
    have hbo : MFact.ord b.reg D.p ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
    have hbw := List.all_eq_true.1 hptwf b hb
    have hw' : ∀ q ∈ b.w, q.1 = D.m.b0 ∨ q.1 = D.m.b1 ∨ q.1 = D.m.b2 := by
      intro q hq
      have := List.all_eq_true.1 hbw q hq
      simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
    refine ⟨?_, ?_⟩
    · have hf : MFact.eq [(b.reg, 1)] b.w ∈ C.facts := hptf b hb _ (by simp [CpPt.facts])
      have hu : HasOrd C [(b.reg, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
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
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
      have := regUnit_ne Sp hC' hf hu (hasOrd_nil C)
      simpa [wordUnit] using this
  let hh : (j : Fin D.pts.length) → Fin (D.pts.get j).hs.length →
      NativeSporadic.Th := fun j i => regUnit Sp hC' ((D.pts.get j).hs.get i).reg
  let S : Set NativeSporadic.Th := Set.range DS.g ∪ ⋃ j, Set.range (hh j)
  have hactG : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈ Subgroup.closure S ∧
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
  have hwordsG : ∀ q ∈ D.gen.words, regUnit Sp hC' q.1 ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts := fun q hq =>
    hactG q.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hgenwf q hq))
  have hOrdW : ∀ w : Word, (∀ q ∈ w, q ∈ D.gen.words) → HasOrd C w :=
    fun w hw q hq => (hwordsG q (hw q hq)).2
  have hmemW : ∀ w : Word, (∀ q ∈ w, q ∈ D.gen.words) →
      wordUnit Sp hC' w ∈ Subgroup.closure S := fun w hw =>
    CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ w fun q hq =>
      (hwordsG q (hw q hq)).1
  obtain ⟨e0, -, e17, e19⟩ := thSlp_ident hC' hslpf hAeq hBeq
  have hO0 : HasOrd C [(0, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨2, hslpf _ (by simp [thSlpFacts])⟩
  have hO17 : HasOrd C [(17, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨2, hslpf _ (by simp [thSlpFacts])⟩
  have hO19 : HasOrd C [(19, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨6, hslpf _ (by simp [thSlpFacts])⟩
  have hOrg : MFact.ord D.gen.rg D.gen.og ∈ C.facts := hgenf _ (by simp [ZGen.facts])
  have hOt2 : HasOrd C [(D.gen.rt2, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨2, hgenf _ (by simp [ZGen.facts])⟩
  have hOx2 : HasOrd C [(D.gen.rx2, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨2, hgenf _ (by simp [ZGen.facts])⟩
  have hOy2 : HasOrd C [(D.gen.ry2, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨6, hgenf _ (by simp [ZGen.facts])⟩
  have hxw : regUnit Sp hC' 17 = wordUnit Sp hC' D.gen.wx := by
    have := regUnit_eq Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.eq [(17, 1)] D.gen.wx ∈
      D.gen.facts)) hO17 (hOrdW D.gen.wx fun q hq => by simp [ZGen.words, hq])
    simpa [wordUnit] using this
  have hyw : regUnit Sp hC' 19 = wordUnit Sp hC' D.gen.wy := by
    have := regUnit_eq Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.eq [(19, 1)] D.gen.wy ∈
      D.gen.facts)) hO19 (hOrdW D.gen.wy fun q hq => by simp [ZGen.words, hq])
    simpa [wordUnit] using this
  have hx2w : regUnit Sp hC' D.gen.rx2 = wordUnit Sp hC' D.gen.wx2 := by
    have := regUnit_eq Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.eq [(D.gen.rx2, 1)]
      D.gen.wx2 ∈ D.gen.facts)) hOx2 (hOrdW D.gen.wx2 fun q hq => by simp [ZGen.words, hq])
    simpa [wordUnit] using this
  have hy2w : regUnit Sp hC' D.gen.ry2 = wordUnit Sp hC' D.gen.wy2 := by
    have := regUnit_eq Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.eq [(D.gen.ry2, 1)]
      D.gen.wy2 ∈ D.gen.facts)) hOy2 (hOrdW D.gen.wy2 fun q hq => by simp [ZGen.words, hq])
    simpa [wordUnit] using this
  have hgx : regUnit Sp hC' D.gen.rg * regUnit Sp hC' 17 * (regUnit Sp hC' D.gen.rg)⁻¹ =
      regUnit Sp hC' D.gen.rx2 := by
    have := regUnit_conj Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.conj D.gen.rg [(17, 1)]
      [(D.gen.rx2, 1)] ∈ D.gen.facts)) hOrg hO17 hOx2
    simpa [wordUnit] using this
  have hgy : regUnit Sp hC' D.gen.rg * regUnit Sp hC' 19 * (regUnit Sp hC' D.gen.rg)⁻¹ =
      regUnit Sp hC' D.gen.ry2 := by
    have := regUnit_conj Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.conj D.gen.rg [(19, 1)]
      [(D.gen.ry2, 1)] ∈ D.gen.facts)) hOrg hO19 hOy2
    simpa [wordUnit] using this
  have hgt : regUnit Sp hC' D.gen.rg * regUnit Sp hC' 0 * (regUnit Sp hC' D.gen.rg)⁻¹ =
      regUnit Sp hC' D.gen.rt2 := by
    have := regUnit_conj Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.conj D.gen.rg [(0, 1)]
      [(D.gen.rt2, 1)] ∈ D.gen.facts)) hOrg hO0 hOt2
    simpa [wordUnit] using this
  have hne : regUnit Sp hC' D.gen.rg * regUnit Sp hC' 0 * (regUnit Sp hC' D.gen.rg)⁻¹ ≠
      regUnit Sp hC' 0 := by
    rw [hgt]
    have := regUnit_ne Sp hC' (hgenf _ (by simp [ZGen.facts] : MFact.ne [(0, 1)]
      [(D.gen.rt2, 1)] D.gen.tne ∈ D.gen.facts)) hO0 hOt2
    simpa [wordUnit] using this.symm
  have hmemWx : ∀ w : Word, (∀ q ∈ w, q ∈ D.gen.words) → ∀ {u : NativeSporadic.Th},
      u = wordUnit Sp hC' w → u ∈ Subgroup.closure S := fun w hw u hu => hu ▸ hmemW w hw
  have hgen : Subgroup.closure S = ⊤ := by
    refine th_closure_eq_top (t := regUnit Sp hC' 0) (x := regUnit Sp hC' 17)
      (y := regUnit Sp hC' 19) (g := regUnit Sp hC' D.gen.rg) e0 e17 e19 hne ?_ ?_ ?_ ?_
    · exact hmemWx _ (fun q hq => by simp [ZGen.words, hq]) hxw
    · exact hmemWx _ (fun q hq => by simp [ZGen.words, hq]) hyw
    · rw [hgx]; exact hmemWx _ (fun q hq => by simp [ZGen.words, hq]) hx2w
    · rw [hgy]; exact hmemWx _ (fun q hq => by simp [ZGen.words, hq]) hy2w
  refine ⟨DS, D.pts.length, fun j => regUnit Sp hC' (D.pts.get j).reg,
    fun j => (D.pts.get j).hs.length, hh, fun j i => ((D.pts.get j).hs.get i).e,
    Or.inl h3.ge, hNFDS, fun j => hptspan _ (List.get_mem _ _), ?_, hgen⟩
  intro j i
  show regUnit Sp hC' ((D.pts.get j).hs.get i).reg * regUnit Sp hC' (D.pts.get j).reg *
    (regUnit Sp hC' ((D.pts.get j).hs.get i).reg)⁻¹ =
      regUnit Sp hC' (D.pts.get j).reg ^ ((D.pts.get j).hs.get i).e
  have hb := List.get_mem D.pts j
  have hk := List.get_mem (D.pts.get j).hs i
  have hf : MFact.conj ((D.pts.get j).hs.get i).reg [((D.pts.get j).reg, 1)]
      [((D.pts.get j).reg, ((D.pts.get j).hs.get i).e)] ∈ C.facts := by
    apply hptf _ hb
    simp only [CpPt.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨_, hk, by simp⟩
  have hbo : MFact.ord (D.pts.get j).reg D.p ∈ C.facts := hptf _ hb _ (by simp [CpPt.facts])
  have hu : HasOrd C [((D.pts.get j).reg, 1)] := fun a ha => by
    simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
  have hw : HasOrd C [((D.pts.get j).reg, ((D.pts.get j).hs.get i).e)] := fun a ha => by
    simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hbo⟩
  have := regUnit_conj Sp hC' hf (hhord _ hb _ hk) hu hw
  simpa [wordUnit] using this

end Main

end CFSG.AGLEmbedding.R3
