module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

theorem nontrivial_pSimple_of_innDiagOn {Y : Type} [Group Y] {p : ℕ} {A X : Subgroup Y}
    (h : InnDiagOn p A X) : Nontrivial (PSimple p X) := by
  have hm : HasLabel (PQuot p X) (fun _ : GLALabel => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) h.2
  have hq := CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_isQuasisimple hm
  haveI : IsSimpleGroup (PSimple p X) := hq.2
  infer_instance

theorem hasLabel_of_centerQuot {X : Type} [Group X] {S : GLALabel → Prop}
    (hX : CFSG.Open.IsQuasisimple X) (h : HasLabel (X ⧸ Subgroup.center X) S) : HasLabel X S := by
  have hbot := CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hX
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_equiv_centerQuot (X := X ⧸ Subgroup.center X)
    (Y := X) hX.1 ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) h

theorem hasLabel_of_innDiagKind {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (h : InnDiagKind S labK α) : HasLabel S (fun l : GLALabel => l = labK) :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hl => hl.1) h

theorem i167C_innDiag {Y : Type} [Group Y] [Finite Y] {p : ℕ} {B X : Subgroup Y} {x : Y}
    (hX : CFSG.Open.IsQuasisimple ↥X)
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) (hxB : x ∈ B)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) :
    ∃ labK : GLALabel, HasLabel ↥X (fun l : GLALabel => l = labK) ∧
      InnDiagKind (↥X ⧸ Subgroup.center ↥X) labK
        (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩) := by
  have hcomp : GLAPComponent p X X :=
    glaPComponent_self_of_nontrivial hX (nontrivial_pSimple_of_innDiagOn hinn)
  have hidm : InnerDiagMarking (Subgroup.zpowers x) X :=
    (CFSG.LocalAnalysis.GLTheoremA.S10.innDiagOn_iff hcomp hX).2 hinn
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set Y) :=
    Subgroup.zpowers_le.2 (hBN hxB)
  obtain ⟨labK, hlab⟩ := CFSG.LocalAnalysis.GLTheoremA.FStdDiag.fstd_innDiagKind hX hzN hidm
  have h1 := hlab ⟨x, Subgroup.mem_zpowers x⟩
  exact ⟨labK, hasLabel_of_centerQuot hX (hasLabel_of_innDiagKind h1), h1⟩

theorem i167C_comp {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {B X J : Subgroup Y} {x : Y}
    (hBN : B ≤ Subgroup.normalizer (X : Set Y)) (hxB : x ∈ B)
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer ({x} : Set Y)) J) :
    GLAPComponent p (fixSubgroup (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩))
        ((J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X))) ∧
      Nonempty (PSimple p J ≃*
        PSimple p ((J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X)))) := by
  have hxN : x ∈ Subgroup.normalizer (X : Set Y) := hBN hxB
  obtain ⟨hJX, hJ0⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_fixSubgroup_conjAut' hp X hxN hJ
  have hJ1 : GLAPComponent p (fixSubgroup (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩))
      ((J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X))) :=
    glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center ↥X))
      (by rw [QuotientGroup.ker_mk'])
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.conjAut' X x hxN)
      (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩)
      (fun k => (normalizerConjAutOfMem_comp_mk X B hBN ⟨x, hxB⟩ k)) (QuotientGroup.mk'_surjective _)
      hp hJ0
  refine ⟨hJ1, ?_⟩
  haveI : Finite ↥X := inferInstance
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map hp
    (QuotientGroup.mk' (Subgroup.center ↥X)) hJ0 hJ1
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.K144.pSimple_subgroupOf_equiv (p := p) hJX
  exact ⟨e₂.symm.trans e₁⟩

theorem i167C_family {X : Type} [Group X] {labK : GLALabel} (hExc : K1419.K1419ClsExcOutFact)
    (hX : CFSG.Open.IsQuasisimple X) (hlab : HasLabel X (fun l : GLALabel => l = labK))
    (hcat : catalogIs (X ⧸ Subgroup.center X) K1419.I1419Classical2) :
    Y10GField.FamLin labK ∨ Y10GField.FamUni labK ∨ Y10GField.FamSymp labK ∨ Y10GField.FamOrth labK := by
  have hne := hExc X labK hX hlab hcat
  rcases Y10GField.fam_cover labK with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd h hne

theorem halfSplit16_mono {p : ℕ} {lab : GLALabel} {c c' : Prop} (hcc : c → c')
    (h : GLAHalfSplit16 p lab c) : GLAHalfSplit16 p lab c' := by
  rcases h with h | h | h | ⟨h1, h2, h3, h4⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hcc h3, h4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem i167C_halfSplitLab {Y : Type} [Group Y] {p : ℕ} {X : Subgroup Y} {labK : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput) (hlab : HasLabel ↥X (fun l : GLALabel => l = labK))
    (hhs : HalfSplit16At p X) : HalfSplitLab p labK := by
  obtain ⟨lab, hlabX, hhs16⟩ := hhs
  obtain ⟨hlam, -, hG⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlabX
  obtain ⟨hlamK, -, hGK⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  exact ⟨lab, hRig lab labK (↥X ⧸ Subgroup.center ↥X) hlam hlamK hG hGK,
    halfSplit16_mono (fun _ => trivial) hhs16⟩

theorem type167J_of_equiv {G G' : Type} [Group G] [Group G'] {p : ℕ} {J : Subgroup G} {J' : Subgroup G'}
    (e : PSimple p J ≃* PSimple p J') (h : Type167J p J) : Type167J p J' := by
  rcases h with ⟨hp, n, h1, h2, h3⟩ | ⟨hp, n, h1, h2, h3⟩ | ⟨n, k, h1, h2, h3, h4, h5, h6⟩
  · subst hp
    exact Or.inl ⟨rfl, n, h1, h2, (catalogIs_congr e).1 h3⟩
  · subst hp
    exact Or.inr (Or.inl ⟨rfl, n, h1, h2, (catalogIs_congr e).1 h3⟩)
  · exact Or.inr (Or.inr ⟨n, k, h1, h2, h3, h4, h5, (catalogIs_congr e).1 h6⟩)

theorem type167_of_type167S {Y : Type} [Group Y] {p : ℕ} {X J : Subgroup Y} {S : Type} [Group S]
    {J' : Subgroup S} (eX : S ≃* PSimple p X) (eJ : PSimple p J ≃* PSimple p J')
    (h : Type167S p S J') : Type167 p X J := by
  have hX : ∀ {Q : TauCeti.CFSGIndex → Prop}, catalogIs S Q → catalogIs (PSimple p X) Q :=
    fun h => (catalogIs_congr eX).1 h
  have hJ : ∀ {Q : TauCeti.CFSGIndex → Prop}, catalogIs (PSimple p J') Q → catalogIs (PSimple p J) Q :=
    fun h => (catalogIs_congr eJ).2 h
  rcases h with ⟨hp, n, h1, h2, h3 | h3⟩ | ⟨hp, n, h1, h2, h3 | h3⟩ | ⟨n, k, h1, h2, h3, h4, h5⟩
  · subst hp
    exact Or.inl ⟨rfl, n, h1, hJ h2, Or.inl (hX h3)⟩
  · subst hp
    exact Or.inl ⟨rfl, n, h1, hJ h2, Or.inr (hX h3)⟩
  · subst hp
    exact Or.inr (Or.inl ⟨rfl, n, h1, hJ h2, Or.inl (hX h3)⟩)
  · subst hp
    exact Or.inr (Or.inl ⟨rfl, n, h1, hJ h2, Or.inr (hX h3)⟩)
  · refine Or.inr (Or.inr ⟨n, k, h1, h2, h3, hJ h4, ?_⟩)
    rcases h5 with h5 | h5 | ⟨h6, h7, h8, h9⟩
    · exact Or.inl (hX h5)
    · exact Or.inr (Or.inl (hX h5))
    · exact Or.inr (Or.inr ⟨h6, h7, h8, hX h9⟩)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
