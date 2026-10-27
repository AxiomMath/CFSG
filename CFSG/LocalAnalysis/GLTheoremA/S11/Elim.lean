module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma119

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Ctx11 (G : Type) [Group G] [Finite G] (m : ℕ) : Prop where
  ctx : ThmACtx G m
  sf : StageFacts G m
  inp : Inputs114 G
  no114 : ¬ ∃ p ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
    IsSStarMax p B x L ∧ SplitInnerDiagMarking16 p B L

theorem Ctx11.nosplit {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (C : Ctx11 G m) (hR : RQuad G m p B x L) : NoSplit16 p L :=
  S11.noSplit_of_not_114 C.inp.idiag C.no114 hR

namespace S11

variable {G : Type} [Group G] [Finite G] {m p p' : ℕ} {B B' : Subgroup G} {x x' : G} {L L' J : Subgroup G}

theorem labelOf_lam2 {lab : GLALabel} (h : LabelOf L lab) : GLAInLambda2 lab := by
  obtain ⟨-, lab', hlab', hs⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h
  obtain ⟨R, _, I, F, θ, -, -, rfl⟩ := hs
  exact hlab'

theorem lemma1111 (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab)
    (htag : (lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) (hz : 3 ∣ Nat.card (Subgroup.center ↥L)) : False := by
  have hns := C.nosplit hR
  obtain ⟨p', B', x', L', J, S⟩ := exists_succ C.ctx C.sf C.inp hR hns
  obtain ⟨hJL, hp3, hx'L, -⟩ := S.cfg.cfg.su_case hz ⟨lab, hlab, htag⟩
  have hxJ : x' ∈ J := hJL ▸ hx'L
  have hxL' : x' ∈ L' := S.c117.J_le hxJ
  have hZ' : Subgroup.center ↥L' ≠ ⊥ := by
    intro hbot
    have hmem : (⟨x', hxL'⟩ : ↥L') ∈ Subgroup.center ↥L' := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (S.c117.comp'.1 g.2)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact S.cfg.cfg.ne_one (congrArg Subtype.val hmem)
  have hns' := C.nosplit S.R'
  obtain ⟨lab', hlab', hl110'⟩ := (cor112_full C.ctx C.sf C.inp.toInputs111 S.R' hns').half
  have hi61 := C.inp.i61 L' lab' (isChev2_of_innerDiag S.R'.2.2) hlab'
  obtain ⟨htag', hz3'⟩ := hi61.2 ⟨p', hl110'⟩ hZ'
  obtain ⟨-, hodd⟩ := hi61.1 htag' hz3'
  exact hns' lab' hlab' (hp3 ▸ split16_three_of_twisted_odd htag' hodd)

theorem center_bot (C : Ctx11 G m) (hR : RQuad G m p B x L) : Subgroup.center ↥L = ⊥ := by
  by_contra hne
  have hns := C.nosplit hR
  obtain ⟨lab, hlab, hl110⟩ := (cor112_full C.ctx C.sf C.inp.toInputs111 hR hns).half
  obtain ⟨htag, hz3⟩ := (C.inp.i61 L lab (isChev2_of_innerDiag hR.2.2) hlab).2 ⟨p, hl110⟩ hne
  exact lemma1111 C hR hlab htag hz3

theorem exists_typ (C : Ctx11 G m) (hR : RQuad G m p B x L) : ∃ lab : GLALabel, LabelOf L lab ∧ LabTyp m p lab := by
  have hns := C.nosplit hR
  have hH := rquad_hyp C.sf hR
  have hcor := cor112_full C.ctx C.sf C.inp.toInputs111 hR hns
  have hZ := center_bot C hR
  obtain ⟨lab, hlab, hl110⟩ := hcor.half
  refine ⟨lab, hlab, hH.prime, hH.ne_two, C.ctx.1.four_le, labelOf_lam2 hlab, ?_, ?_, ?_⟩
  · rwa [eq_true hZ] at hl110
  · have h := C.inp.eTable L lab hlab
    rw [hcor.e_eq] at h
    rwa [eq_true hZ] at h
  · intro heq
    exact hcor.not_E62 (heq ▸ hlab)

theorem step_of_succ (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab)
    (ht : LabTyp m p lab) :
    ∃ (p' : ℕ) (B' : Subgroup G) (x' : G) (L' : Subgroup G) (lab' labJ : GLALabel),
      RQuad G m p' B' x' L' ∧ LabelOf L' lab' ∧ LStep m p lab p' lab' labJ := by
  have hns := C.nosplit hR
  have hH := rquad_hyp C.sf hR
  obtain ⟨p', B', x', L', J, S⟩ := exists_succ C.ctx C.sf C.inp hR hns
  obtain ⟨lab', hlab', ht'⟩ := exists_typ C S.R'
  obtain ⟨labJ, hlabJ, hshape⟩ := S.cfg.cfg.shape lab hlab
  have hz3 : ¬ (3 ∣ Nat.card (Subgroup.center ↥L)) := by
    rw [center_bot C hR]
    simp
  rw [eq_false hz3] at hshape
  refine ⟨p', B', x', L', lab', labJ, S.R', hlab', ht, ht', S.cfg.splits lab hlab, hshape,
    S.field lab' labJ hlab' hlabJ, ?_⟩
  exact C.inp.i14neg p L' J x lab' labJ hH.prime hH.ne_two (isChev2_of_innerDiag S.R'.2.2) S.cfg.cfg.chev2
    S.c117.x_norm (hH.elem.2 x hH.mem) S.c117.J_layer.2 hlab' hlabJ

theorem g10i (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    ¬ (p = 5 ∧ lab = ⟨.A, 5, 2⟩) := by
  rintro ⟨hp, hl⟩
  obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
  exact lemma1010i hs hp hl

theorem g10ii (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    ¬ (p = 7 ∧ lab = ⟨.A, 8, 1⟩) := by
  rintro ⟨hp, hl⟩
  obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
  exact lemma1010ii hs hp hl

theorem g12a (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    ¬ (lab.tag = .twE6 ∧ 2 ≤ lab.n) := by
  rintro ⟨htw, hn⟩
  obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
  exact lemma1012a hs htw hn

theorem g12b (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    lab ≠ ⟨.E6, 0, 2⟩ := by
  intro hl
  obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
  obtain ⟨htw, hn2⟩ := lemma1010iii hs (p_eq_five_of_E6 ht hl) hl
  exact g12a C hR' hlab' hs.typ' ⟨htw, by omega⟩

theorem excl12 (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    Excl12 p lab :=
  ⟨g10i C hR hlab ht, g10ii C hR hlab ht, g12a C hR hlab ht, g12b C hR hlab ht⟩

theorem g13 (C : Ctx11 G m) :
    ∀ (n : ℕ) {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}, RQuad G m p B x L → ∀ {lab : GLALabel},
      LabelOf L lab → LabTyp m p lab → TypeA p lab → lab.n = n → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p B x L hR lab hlab ht hA hn
    obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
    exact lemma1013 hs hA (excl12 C hR' hlab' hs.typ') fun hA' hlt => ih lab'.n (hn ▸ hlt) hR' hlab' hs.typ' hA' rfl

theorem g14 (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    ¬ (lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n) := by
  intro hU
  obtain ⟨p', B', x', L', lab', labJ, hR', hlab', hs⟩ := step_of_succ C hR hlab ht
  exact lemma1014 hs hU
    { excl12 C hR' hlab' hs.typ' with l13 := fun hA => g13 C lab'.n hR' hlab' hs.typ' hA rfl }

theorem excl (C : Ctx11 G m) (hR : RQuad G m p B x L) {lab : GLALabel} (hlab : LabelOf L lab) (ht : LabTyp m p lab) :
    Excl p lab :=
  { excl12 C hR hlab ht with
    l13 := fun hA => g13 C lab.n hR hlab ht hA rfl
    l14 := g14 C hR hlab ht }

theorem no_R (C : Ctx11 G m) (hR : RQuad G m p B x L) : False := by
  obtain ⟨lab, hlab, ht⟩ := exists_typ C hR
  exact label_closing ht (excl C hR hlab ht)

end S11

end CFSG.LocalAnalysis.GLTheoremA
