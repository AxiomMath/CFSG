module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank
public import CFSG.LargeExtraspecial.OutSix
public import CFSG.GF2Type.ModelPSU
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem u4Out_nonempty_timmesfeldPSU_six {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 6 2 1) : Nonempty (X ≃* timmesfeldPSU 6) := by
  rcases h with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have := Fintype.ofFinite F
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hc : Fintype.card F = Fintype.card (GaloisField 2 2) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card 2 2 (by norm_num)]
      norm_num
    exact ⟨(e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1))).trans
      (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 6).symm⟩
  all_goals exact absurd h0 (by norm_num)

theorem u4Out_index_u6two {P : Type} [Group P] [Finite P] (h : catalogIs P S9.isU6two) :
    (innerAut P).index = 6 := by
  haveI : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := U62RankSound.lieIndex_isU6two h
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two (s := 1)
    (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' 5 q hv e
  rw [h1, h2] at hm
  obtain ⟨e'⟩ := u4Out_nonempty_timmesfeldPSU_six (hm.toBlueprint (by decide))
  have hO : Nat.card (MulAut P ⧸ innerAut P) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (timmesfeldPSU 6)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv
  change Nat.card (MulAut P ⧸ innerAut P) = 6
  rw [hO, CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU_six]

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
