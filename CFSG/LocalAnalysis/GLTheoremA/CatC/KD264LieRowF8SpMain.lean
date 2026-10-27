module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8SpDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8SpCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

theorem kerSp_model {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (A : Subgroup (MulAut (StatedProj (StatedSp 3 K)))) (hA : IsElemAbelian 3 A)
    (hout : ∀ a ∈ A, a ∉ (MulAut.conj : StatedProj (StatedSp 3 K) →*
        MulAut (StatedProj (StatedSp 3 K))).range →
      ∀ E : Subgroup (StatedProj (StatedSp 3 K)), E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A)
    (hnot : ¬ A ≤ innAutDerived (StatedProj (StatedSp 3 K))) :
    KD264F8Datum (StatedProj (StatedSp 3 K)) A := by
  classical
  haveI hchar : CharP K 2 := charP_two_of_card_eight hK
  have h3 : 3 ≤ 3 := le_rfl
  obtain ⟨stdIso⟩ := exists_stdIso 3
  obtain ⟨E0S, -, hE0S, hE0Scard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    (H := (⊤ : Subgroup (StatedSp 3 (ZMod 2)))) (k := 3) Nat.prime_three
    (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp (K := ZMod 2) (n := 3)
      (r := 3) Nat.prime_three (by rw [Nat.card_zmod]; norm_num))
  refine F8Asm.datum_of_core (P := StatedProj (StatedSp 3 K))
    (G₀ := ↥(TauCeti.BilinForm.isometryGroup (stdForm 3)))
    (center_sp_eq_bot h3) A hA hnot (sp_outCyc h3 A hA) ?_ hout 3
    (E0S.map stdIso.toMonoidHom) (isElemAbelian_map_gen _ hE0S) ?_ ?_ ?_
  · intro a ha
    have := ha.2
    rw [sp_innAutDerived_eq_inner h3] at this
    exact this
  · rw [Subgroup.card_map_of_injective (K := E0S) stdIso.injective, hE0Scard]
  · intro b hb hbout
    obtain ⟨ι, hιinj, hιfix, hιrange⟩ := exists_descent_sp h3 hK b (hA.2 b hb) (fun h => hbout (
      inner_le_innAutDerived _ h))
    refine ⟨ι, hιinj, hιfix, fun x hx v => ?_, fun x hx _ => hιrange x hx⟩
    exact ι.range.mul_mem (ι.range.mul_mem (hιrange x hx) ⟨v, rfl⟩) (ι.range.inv_mem (hιrange x hx))
  · intro E hE hcard
    haveI : Fintype E := Fintype.ofFinite E
    have := sp_core_c (stdForm 3) (stdForm_isAlt 3) (stdForm_nondeg 3) (stdForm_finrank 3) E hE
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    obtain ⟨c, hcE, hc1, L, hLc, hLs, hLq, hLd⟩ := this
    exact ⟨c, hcE, hc1, L, hLc, hLs, hLq, hLd⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.RankThree.PartTwo.Census.Carrier.SpinB

theorem KD264F8KerSp_holds : KD264F8KerSp := by
  unfold KD264F8KerSp KD264F8Kernel
  intro d _hfin _hns _hk2 _hk3 _hov hP A hA
  obtain ⟨d1, hd1⟩ := d
  rcases hP with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
  · have hp2 : q.p = 2 := by
      have hdvd : q.p ∣ 2 ^ 3 := by
        have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
        rw [← h8, TauCeti.PrimePower.card_def]
        exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
        (q.prime_p.dvd_of_dvd_pow hdvd)
    haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
      (⟨TauCeti.LieTypeIndex.B 3 q, hd1⟩ : TauCeti.ValidLieTypeIndex)
    let e := typeBGroupEquivStatedProj 3 q hd1 hp2 le_rfl
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
        (⟨TauCeti.LieTypeIndex.B 3 q, hd1⟩ : TauCeti.ValidLieTypeIndex)) = 8 := by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField,
        TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show TauCeti.ValidLieTypeIndex.characteristic
            (⟨TauCeti.LieTypeIndex.B 3 q, hd1⟩ : TauCeti.ValidLieTypeIndex) = q.p from
          TauCeti.LieTypeIndex.characteristic_B 3 q,
        show TauCeti.ValidLieTypeIndex.fieldExponent
            (⟨TauCeti.LieTypeIndex.B 3 q, hd1⟩ : TauCeti.ValidLieTypeIndex) = q.exponent from
          TauCeti.LieTypeIndex.fieldExponent_B 3 q,
        ← TauCeti.PrimePower.card_def]
      exact hq
    obtain ⟨hAab, hout, hnot⟩ := F8Trans.hyp_transport e A hA
    exact F8Trans.datum_of_equiv e A (F8Sp.kerSp_model hcardK _ hAab hout hnot)
  · exfalso
    have hv := (TauCeti.LieTypeIndex.valid_iff _).1 hd1
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hv.1
    have hp2 : q.p = 2 := by
      have hdvd : q.p ∣ 2 ^ 3 := by
        have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
        rw [← h8, TauCeti.PrimePower.card_def]
        exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
        (q.prime_p.dvd_of_dvd_pow hdvd)
    exact hr.2 hp2

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
