module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2 (mulEquivPSL)
open scoped MatrixGroups commutatorElement

theorem commutator_le_inner_of_isCyclic {S : Type} [Group S] (h : IsCyclic (Outer S)) :
    commutator (MulAut S) ≤ inner S := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ g' _
  have hcomm : Commute (QuotientGroup.mk g : Outer S) (QuotientGroup.mk g') :=
    (IsCyclic.commGroup (α := Outer S)).mul_comm _ _
  have : (QuotientGroup.mk ⁅g, g'⁆ : Outer S) = 1 := by
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    exact (commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq)
  exact (QuotientGroup.eq_one_iff _).1 this

theorem isCyclic_outer_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : IsCyclic (Outer H)) : IsCyclic (Outer G) := by
  haveI := h
  exact isCyclic_of_surjective (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e.symm)
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e.symm).surjective

theorem isCyclic_outer_of_hom {G A : Type} [Group G] [Group A] [IsCyclic A] (Θ : MulAut G →* A)
    (hker : Θ.ker = inner G) : IsCyclic (Outer G) := by
  let f : Outer G →* A := QuotientGroup.lift (inner G) Θ (by rw [← hker])
  refine isCyclic_of_injective f ((injective_iff_map_eq_one f).2 fun x hx => ?_)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : Θ y = 1 := hx
  rw [QuotientGroup.eq_one_iff, ← hker]
  exact hy

theorem solvesAt_rankOne {p : ℕ} (hN1 : KD264OutCyc) (hN2 : KD264OuterIdx) (d : ValidLieTypeIndex)
    (hchar : p ≠ d.1.characteristic)
    (h3 : ¬ (p = 3 ∧
      ((∃ q : PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : PrimePower, d.1 = .trialityD4 q))))
    (h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2))
    (hab : commutator (MulAut (CFSGIndex.lie d).Group) ≤ inner (CFSGIndex.lie d).Group)
    (h2 : TwoLocalRankLE1 p (CFSGIndex.lie d).Group) : SolvesAt p d := by
  intro hp hp2 Y _ _ K B h he hc
  obtain ⟨e⟩ := he
  haveI : Finite (CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  exact Or.inl (kConcl_of_N1_N2 hp hp2 hN1 hN2 h d e hchar h3 h5 hab h2 hc)

theorem l2_equiv {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2) :
    Nonempty ((CFSGIndex.lie ⟨LieTypeIndex.A 1 q, hv⟩).Group ≃* SL(2, GaloisField 2 q.exponent)) := by
  obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2)
    (n := q.exponent) (d := ⟨LieTypeIndex.A 1 q, hv⟩) ⟨q, rfl, hq2, rfl⟩
  exact ⟨e2.trans (mulEquivPSL (GaloisField 2 q.exponent)).symm⟩

theorem l2_out_cyclic {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2) :
    IsCyclic (Outer (CFSGIndex.lie ⟨LieTypeIndex.A 1 q, hv⟩).Group) := by
  obtain ⟨e3⟩ := l2_equiv hv hq2
  have := isCyclic_ringEquiv_galoisField q.exponent
  exact isCyclic_of_surjective _ (outer_surjective e3)

theorem l2_twoLocal {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2) :
    TwoLocalRankLE1 3 (CFSGIndex.lie ⟨LieTypeIndex.A 1 q, hv⟩).Group := by
  obtain ⟨e3⟩ := l2_equiv hv hq2
  intro E T hE _ _ _
  exact CFSG.LocalAnalysis.GLTheoremA.List93.card_le_three_of_sl2 e3 E hE

theorem solvesAt_A1 (hN1 : KD264OutCyc) (hN2 : KD264OuterIdx) {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2) (hq8 : q.card ≠ 8) :
    SolvesAt 3 ⟨LieTypeIndex.A 1 q, hv⟩ := by
  refine solvesAt_rankOne hN1 hN2 _ ?_ ?_ ?_
    (commutator_le_inner_of_isCyclic (l2_out_cyclic hv hq2)) (l2_twoLocal hv hq2)
  · have hc : (LieTypeIndex.A 1 q).characteristic = 2 := by simpa using hq2
    show 3 ≠ (LieTypeIndex.A 1 q).characteristic
    rw [hc]
    norm_num
  · rintro ⟨-, ⟨q', hq' | hq', hq'8⟩ | ⟨q', hq'⟩⟩
    · have : q = q' := by injection hq'
      subst this
      exact hq8 hq'8
    · cases hq'
    · cases hq'
  · rintro ⟨h5, -⟩
    omega

end CFSG.LocalAnalysis.GLTheoremA.HDesc
