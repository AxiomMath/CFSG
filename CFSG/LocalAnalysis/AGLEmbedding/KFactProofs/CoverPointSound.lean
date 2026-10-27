module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness

theorem fixesVec_of_invariant {p : ℕ} [Fact p.Prime] (g : Act) (v : Fin 3 → ZMod p)
    (h : Matrix.vecMul v (actMat p g) = v) :
    g.fixesVec p (v 0).val (v 1).val (v 2).val = true := by
  have key : ∀ i : Fin 3, Matrix.vecMul v (actMat p g) i = v i := fun i => by rw [h]
  have e0 := key 0
  have e1 := key 1
  have e2 := key 2
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, actMat, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.reduceMul, Nat.reduceAdd, mul_zero, zero_add, add_zero] at e0 e1 e2
  have dv : ∀ x : ℤ, ((x : ℤ) : ZMod p) = 0 → x % (p : ℤ) = 0 := fun x hx =>
    Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 hx)
  unfold Act.fixesVec
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨dv _ ?_, dv _ ?_⟩, dv _ ?_⟩
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e0
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e1
  · push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination e2

theorem noFun_of_bool {D : CpSpec} [Fact D.p.Prime] (h : D.noFun = true) (v : Fin 3 → ZMod D.p)
    (hv : ∀ g ∈ D.m.acts, Matrix.vecMul v (actMat D.p g) = v) : v = 0 := by
  by_contra hne
  have hmem : ((v 0).val, (v 1).val, (v 2).val) ∈ nonzeroTriples D.p := by
    rw [mem_nonzeroTriples]
    refine ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ?_⟩
    rintro ⟨h0, h1, h2⟩
    apply hne
    ext k
    fin_cases k
    · exact (ZMod.val_eq_zero _).1 h0
    · exact (ZMod.val_eq_zero _).1 h1
    · exact (ZMod.val_eq_zero _).1 h2
  unfold CpSpec.noFun at h
  obtain ⟨g, hg, hgf⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hmem)
  rw [fixesVec_of_invariant g v (hv g hg)] at hgf
  exact Bool.false_ne_true hgf

theorem noFun_of_entries {p : ℕ} [Fact p.Prime] {n m : ℕ} (hn : n = 3)
    (M : Fin m → Matrix (Fin n) (Fin n) (ZMod p)) (acts : List Act)
    (hMe : ∀ g ∈ acts, ∃ j : Fin m, ∀ k i : Fin n,
      M j k i = ((g.mat.getD (3 * k.val + i.val) 0 : ℕ) : ZMod p))
    (hNF : ∀ v : Fin 3 → ZMod p,
      (∀ g ∈ acts, Matrix.vecMul v (actMat p g) = v) → v = 0) :
    ∀ v : Fin n → ZMod p, (∀ j, Matrix.vecMul v (M j) = v) → v = 0 := by
  subst hn
  intro v hv
  refine hNF v fun g hg => ?_
  obtain ⟨j, hj⟩ := hMe g hg
  have : M j = actMat p g := by ext k i; exact hj k i
  rw [← this]
  exact hv j

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {D : CpSpec}

include Sp in
theorem coverPointDatum_of_check (hp : D.p.Prime)
    (h : cpCheck O sA sB nregs prog D = true) (hNF : D.noFun = true) :
    CoverPointDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold cpCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [CpSpec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [CpSpec.facts]
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [CpSpec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [CpSpec.facts]
  have hmodf : ∀ f ∈ D.m.facts D.p, f ∈ D.facts := by
    intro f hf
    simp only [CpSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hf))
  have hptf : ∀ b ∈ D.pts, ∀ f ∈ b.facts D.p, f ∈ D.facts := by
    intro b hb f hf
    simp only [CpSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨b, hb, hf⟩)
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
  unfold CpSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨-, hptwf⟩, hind⟩, hderwf⟩, hseedwf⟩ := hwf
  have hindep : ∀ v ∈ nonzeroTriples D.p, ∃ q ∈ D.m.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2 := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
    simp only [Bool.and_eq_true, beq_iff_eq] at hqv
    exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
  obtain ⟨DS, h3, hact, hspan⟩ := exists_moduleSpec_core Sp hC' D.m hmodf hindep
  have hNFDS : DS.NoFun := noFun_of_entries h3 DS.M D.m.acts
    (fun g hg => by obtain ⟨j, -, hj⟩ := hact g hg; exact ⟨j, hj⟩)
    (fun v hv => noFun_of_bool hNF v hv)
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
      (certMonoid c d sA sB)ˣ := fun j i => regUnit Sp hC' ((D.pts.get j).hs.get i).reg
  have hactG : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) ∧
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
  have hderf : ∀ e ∈ D.der, ∀ f ∈ e.facts, f ∈ D.facts := by
    intro e he f hf
    simp only [CpSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hf⟩
  have hderG := der_mem Sp hC'
    (Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j))) D.der D.actRegs hderf hactG hderwf
  have hseedG : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    rcases List.mem_append.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hseedwf q hq)) with h | h
    · exact hactG q.1 h
    · obtain ⟨e, he, hq1⟩ := List.mem_map.1 h
      rw [← hq1]
      exact hderG e he
  have hOrdGens : ∀ w : Word, (∀ q ∈ w, q ∈ D.wA ++ D.wB) → HasOrd C w :=
    fun w hw q hq => (hseedG q (hw q hq)).2
  have hΓreg : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈
      Subgroup.closure (Set.range DS.g ∪ ⋃ j, Set.range (hh j)) :=
    fun q hq => (hseedG q hq).1
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
      (hOrdGens D.wA fun q hq => List.mem_append.2 (Or.inl hq))
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (hOrdGens D.wB fun q hq => List.mem_append.2 (Or.inr hq))
    simpa [wordUnit] using this
  refine ⟨DS, D.pts.length, fun j => regUnit Sp hC' (D.pts.get j).reg,
    fun j => (D.pts.get j).hs.length, hh, fun j i => ((D.pts.get j).hs.get i).e,
    Or.inl h3.ge, hNFDS, fun j => hptspan _ (List.get_mem _ _), ?_, ?_⟩
  · intro j i
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
  · refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hAw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inl hq))
    · rw [hBw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inr hq))

end Main

end CFSG.AGLEmbedding.R3
