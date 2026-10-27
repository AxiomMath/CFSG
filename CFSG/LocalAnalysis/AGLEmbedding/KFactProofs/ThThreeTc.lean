module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeSlp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.Th

theorem pRank_bot_eq_zero {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) :
    Open.pRank p (⊥ : Subgroup X) = 0 := by
  refine Nat.le_zero.1 (csSup_le' fun k hk => ?_)
  obtain ⟨E, hE, -, hcard⟩ := hk
  have hEb : E = ⊥ := le_bot_iff.1 hE
  subst hEb
  rw [Subgroup.card_bot] at hcard
  have := (Nat.pow_eq_one.1 hcard.symm)
  rcases this with h | h
  · exact absurd h hp.ne_one
  · exact h.le

theorem fusionGenerationOf_of_tc {X : Type} [Group X] [Finite X] [Nontrivial X] {p : ℕ}
    (hp : p.Prime) (h : TCGenDatum X p) :
    CFSG.RankThree.PartOne.CTP.Fus.FusionGenerationOf X p := by
  obtain ⟨r, U, P, S, hP, hUP, hU, hS, hSU⟩ := h
  have hUne : ∀ i, U i ≠ ⊥ := by
    intro i hi
    have := (hU i).1
    rw [hi, pRank_bot_eq_zero hp] at this
    omega
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Subgroup.closure_empty] at hS
    exact (bot_ne_top (α := Subgroup X)) hS
  obtain ⟨g0, hg0⟩ := hSne
  obtain ⟨i0, -⟩ := hSU g0 hg0
  have hPne : P ≠ ⊥ := by
    intro hPb
    apply hUne i0
    exact le_bot_iff.1 (hPb ▸ hUP i0)
  refine ⟨P, S, hP, hPne, hS, fun g hg => ?_⟩
  obtain ⟨i, hi⟩ := hSU g hg
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hUne i)
  refine ⟨(e : X), hUP i e.2, fun h1 => he (Subtype.ext h1), ?_⟩
  have hmem := (Subgroup.mem_normalizer_iff.1 hi) (e : X)
  exact hUP i (hmem.1 e.2)

section Main

variable {nregs : ℕ} {prog : List Op} {D : TZSpec}

theorem tcGenDatum_of_zcheck
    (hp : D.p.Prime)
    (h : tzCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 nregs prog D = true) :
    TCGenDatum NativeSporadic.Th D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  set Sp := spec2 248 with hSp
  unfold tzCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hC, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 C = true := hC
  have hslpf : ∀ f ∈ thSlpFacts, f ∈ D.facts := by
    intro f hf
    simp only [TZSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inl hf))
  have hpcf : ∀ q ∈ D.pc, ∀ f ∈ q.facts D.p, f ∈ D.facts := by
    intro q hq f hf
    simp only [TZSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨q, hq, hf⟩))
  have hsubf : ∀ s ∈ D.subs, ∀ f ∈ s.facts D.p, f ∈ D.facts := by
    intro s hs f hf
    simp only [TZSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨s, hs, hf⟩)
  have hgenf : ∀ f ∈ D.gen.facts, f ∈ D.facts := by
    intro f hf
    simp only [TZSpec.facts, List.mem_append]
    exact Or.inr hf
  have hactord : ∀ s ∈ D.subs, ∀ g ∈ s.acts, MFact.ord g.reg g.ord ∈ D.facts := by
    intro s hs g hg
    apply hsubf s hs
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  unfold TZSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨-, hpcwf⟩, hsubwf⟩, hgenwf⟩ := hwf
  let P : Subgroup NativeSporadic.Th :=
    Subgroup.closure {u | ∃ q ∈ D.pc, u = regUnit Sp hC' q.reg}
  have hP : IsPGroup D.p P := chain_isPGroup Sp hC' D.pc hpcwf hpcf
  have hsubs : ∀ s ∈ D.subs, ∃ U : Subgroup NativeSporadic.Th, U ≤ P ∧
      2 ≤ Open.pRank D.p U ∧
      3 ≤ Open.pRank D.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set NativeSporadic.Th))) ∧
      ∀ g ∈ s.acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set NativeSporadic.Th) := by
    intro s hs
    have hsw := List.all_eq_true.1 hsubwf s hs
    unfold TSub.wfIn at hsw
    simp only [Bool.and_eq_true] at hsw
    obtain ⟨⟨⟨⟨⟨hgw, hv0⟩, hv1⟩, hv2⟩, hind⟩, hact⟩ := hsw
    refine tc_sub Sp hC' hp D.pc s hpcf (hsubf s hs)
      (fun u hu => List.all_eq_true.1 hgw u hu) hv0 hv1 hv2 ?_ ?_
    · intro v hv
      obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
      simp only [Bool.and_eq_true, beq_iff_eq] at hqv
      exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
    · intro g hg
      have hg' := List.all_eq_true.1 hact g hg
      simp only [Bool.and_eq_true] at hg'
      refine ⟨fun cc hcc => ?_, fun u hu => List.all_eq_true.1 hg'.2 u hu⟩
      have := List.all_eq_true.1 hg'.1 cc hcc
      simp only [Bool.and_eq_true] at this
      exact this
  have hex : ∀ i : Fin D.subs.length, ∃ U : Subgroup NativeSporadic.Th, U ≤ P ∧
      2 ≤ Open.pRank D.p U ∧
      3 ≤ Open.pRank D.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set NativeSporadic.Th))) ∧
      ∀ g ∈ (D.subs.get i).acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set NativeSporadic.Th) :=
    fun i => hsubs _ (List.get_mem _ _)
  choose U hUP hr2 hr3 hnorm using hex
  let S : Set NativeSporadic.Th :=
    {g | ∃ s ∈ D.subs, ∃ a ∈ s.acts, g = regUnit Sp hC' a.reg}
  have hact : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    obtain ⟨s, hs, hr'⟩ := List.mem_flatMap.1 hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr'
    exact ⟨Subgroup.subset_closure ⟨s, hs, g, hg, rfl⟩, g.ord, hactord s hs g hg⟩
  have hwordsG : ∀ q ∈ D.gen.words, regUnit Sp hC' q.1 ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts := fun q hq =>
    hact q.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hgenwf q hq))
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
  refine ⟨D.subs.length, U, P, S, hP, hUP, fun i => ⟨hr2 i, hr3 i⟩, hgen, ?_⟩
  rintro _ ⟨s, hs, a, ha, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hs
  exact ⟨i, hnorm i a ha⟩

end Main

end CFSG.AGLEmbedding.R3
