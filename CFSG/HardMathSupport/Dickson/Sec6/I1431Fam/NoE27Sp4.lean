module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27L3U3
public import CFSG.RankThree.PartTwo.Sec4.Item413Classical

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem card_le_nine_statedProj_sp_two {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedSp 2 K))) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  let ρ : ↥(StatedSp 2 K) →* StatedProj (StatedSp 2 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
  refine CFSG.RankThree.PartTwo.Sec4.card_le_of_surjective_of_ker ρ (QuotientGroup.mk'_surjective _)
    (m := 2) (by norm_num) ?_ ?_ E (fun x hx y hy => congrArg Subtype.val
      (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE.2
  · intro s hs
    have hs' : s ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) :=
      (QuotientGroup.eq_one_iff s).1 hs
    obtain ⟨c, hc⟩ := hs'
    have hcs : (s : GL (Fin 2 ⊕ Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c :=
      hc.symm
    have hsq : c ^ 2 = 1 :=
      CFSG.RankThree.PartTwo.Sec4.sq_of_scalar_mem_closure_sp (n := 2) (by norm_num)
        (by rw [← hcs]; exact s.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcs, ← map_pow, hsq, map_one]
    rfl
  · intro P hPc hPe
    have := CFSG.RankThree.PartTwo.Sec4.card_sq_le_of_mem_closure_sp h3
      (P.map (StatedSp 2 K).subtype) (by
        rintro _ ⟨x, -, rfl⟩
        exact x.2)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (hPc x hx y hy))
      (by
        rintro _ ⟨x, hx, rfl⟩
        exact congrArg Subtype.val (hPe x hx))
    rw [Subgroup.card_map_of_injective (StatedSp 2 K).subtype_injective] at this
    norm_num at this
    nlinarith

theorem noE27_pspLow : NoE27At FamPspLow := by
  intro P _ _ t n p f hadm ht hF hm
  obtain ⟨rfl, rfl, hp3⟩ := hF
  have hC : StatedClassicalModel P .PSp 2 p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have h3 : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  refine NoE27.of_mulEquiv e0 ?_
  rintro ⟨E, hE, hc⟩
  have := card_le_nine_statedProj_sp_two h3 E hE
  omega

end CFSG.HardMathSupport.Dickson.Sec6.I1431
