module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeSlp

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
  CFSG.SectionRank.LocalWitness CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Sporadic.LySchreier.Native

theorem isCoatom_lyG0 :
    IsCoatom lyG0 := by
  have hHeq : lyH = lyG0 := (seven_space_centralizer_bound).1
  rw [← hHeq, ← stabilizer_omegaE]
  have : MulAction.IsPreprimitive J (MulAction.orbit J Omega.opE) := ly_certificate.2.2.2.2.2.1
  have : Nontrivial (MulAction.orbit J Omega.opE) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_omega]
    norm_num
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive J _

theorem stabOK_of_mem_stabU
    {X : Mat} {g : J} (hX : RepM X g) (hg : g ∈ stabU) : stabOK X = true := by
  unfold stabOK
  rw [beq_iff_eq]
  have e : toMatU (mulXU X) = toMatU (mulUR (restrArr X)) := by
    rw [toMatU_mulXU, toMatU_mulUR, mat7_restrArr hX, hX]
    exact hg
  unfold mulXU mulUR
  congr 1
  funext i
  congr 1
  funext m
  have h1 := congrFun (congrFun e i) m
  simp only [toMatU, mulXU, mulUR, Matrix.of_apply, ofFn_get!' _ i.isLt, ofFn_get!' _ m.isLt] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 h1
  simpa [Nat.mod_mod] using h2

theorem ly_rep_reg {C : MCert}
    (hC : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true)
    {r e : ℕ} (hf : MFact.ord r e ∈ C.facts) :
    RepM (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[r]!
      (lyEquivJ (regUnit (specP 5 111) hC r)) := by
  have h2 : valHom (certMonoid 5 111 NativeSporadic.LySeed1 NativeSporadic.LySeed2)
      (regUnit (specP 5 111) hC r) = (specP 5 111).toMat
        (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[r]! :=
    val_regUnit (specP 5 111) hC hf
  show toMat 5 111 _ = _
  exact (h2.symm.trans (lyEquivJ_val _).symm)

section Gen5

variable {C : MCert}
  (hC : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true)

theorem ly_gen_top5
    (G : HGen) (hG : ∀ f ∈ G.facts, f ∈ C.facts) (hlen : G.els.length = 5)
    (hel : ∀ j < 5, (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[(G.els.getD j default).reg]! (pairAt asArr (j + 2)).1 = true)
    (hs : stabOK (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[G.rs]! =
      false)
    {S : Set NativeSporadic.Ly}
    (hw : ∀ q ∈ G.words, regUnit (specP 5 111) hC q.1 ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts) : Subgroup.closure S = ⊤ := by
  set Sp := specP 5 111 with hSp
  set L : Subgroup J := (Subgroup.closure S).map (lyEquivJ : NativeSporadic.Ly →* J) with hL
  have haj : ∀ j < 5, aStar (j + 2) ∈ L := by
    intro j hj
    have hj' : j < G.els.length := by omega
    set e := G.els.getD j default with he
    have hem : e ∈ G.els := by
      rw [he, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    have ford : MFact.ord e.reg e.ord ∈ C.facts := by
      apply hG
      simp only [HGen.facts, List.mem_append, List.mem_flatMap]
      right
      exact ⟨e, hem, by simp⟩
    have feq : MFact.eq [(e.reg, 1)] e.w ∈ C.facts := by
      apply hG
      simp only [HGen.facts, List.mem_append, List.mem_flatMap]
      right
      exact ⟨e, hem, by simp⟩
    have hid : lyEquivJ (regUnit Sp hC e.reg) = aStar (j + 2) :=
      ly_ident_of_rep hC ford (repM_asArr (j + 2)).1 (hel j hj)
    have hqw : ∀ q ∈ e.w, q ∈ G.words := by
      intro q hq
      simp only [HGen.words, List.mem_append, List.mem_flatMap]
      left
      exact ⟨e, hem, hq⟩
    have hOw : HasOrd C e.w := fun q hq => (hw q (hqw q hq)).2
    have hOr : HasOrd C [(e.reg, 1)] := fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨e.ord, ford⟩
    have hweq := regUnit_eq Sp hC feq hOr hOw
    have hm : wordUnit Sp hC e.w ∈ Subgroup.closure S :=
      CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ e.w fun q hq =>
        (hw q (hqw q hq)).1
    have hr : regUnit Sp hC e.reg ∈ Subgroup.closure S := by
      have : regUnit Sp hC e.reg = wordUnit Sp hC e.w := by simpa [wordUnit] using hweq
      rw [this]; exact hm
    rw [← hid]
    exact ⟨_, hr, rfl⟩
  have hHeq : lyH = lyG0 := (seven_space_centralizer_bound).1
  have hG0 : lyG0 ≤ L := by
    rw [← hHeq, lyH, Subgroup.closure_le]
    rintro _ ⟨j, ⟨h2, h6⟩, rfl⟩
    have := haj (j - 2) (by omega)
    rwa [show j - 2 + 2 = j by omega] at this
  have hord : MFact.ord G.rs G.os ∈ C.facts := hG _ (by simp [HGen.facts])
  have hsmem : lyEquivJ (regUnit Sp hC G.rs) ∈ L :=
    ⟨_, (hw (G.rs, 1) (by simp [HGen.words])).1, rfl⟩
  have hsnot : lyEquivJ (regUnit Sp hC G.rs) ∉ lyG0 := by
    intro hmem
    have hstab : lyEquivJ (regUnit Sp hC G.rs) ∈ stabU := lyH_le_stabU (by rw [hHeq]; exact hmem)
    have := stabOK_of_mem_stabU (ly_rep_reg hC hord) hstab
    rw [hs] at this
    exact absurd this (by simp)
  have hlt : lyG0 < L := lt_of_le_of_ne hG0 (fun h => hsnot (h ▸ hsmem))
  have htop : L = ⊤ := isCoatom_lyG0.2 L hlt
  have : Subgroup.comap (lyEquivJ : NativeSporadic.Ly →* J) L = Subgroup.closure S :=
    Subgroup.comap_map_eq_self_of_injective lyEquivJ.injective _
  rw [← this, htop, Subgroup.comap_top]

end Gen5

end CFSG.AGLEmbedding.R3
