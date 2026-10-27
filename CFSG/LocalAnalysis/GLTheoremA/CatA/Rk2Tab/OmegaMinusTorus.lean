module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType CFSG.Assembly CFSG.LieType.Universal.Spin

private theorem exists_card_eq_two_pow (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ n : ℕ, Nat.card F = 2 ^ n := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩

private noncomputable def projMinusEquiv (m : ℕ) (F : Type) [Field F] [CharP F 2] (b c : F) :
    OrthRest.RMinus F m b c ≃* StatedProj (StatedOmega (StatedQuadMinus (m + 1) F b c)) := by
  have hbotL : (LargeEvenScalars (LargeEvenMinusIdx m) F).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus m b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c
  have hbotS : (StatedScalars (Fin m ⊕ Fin m ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus (m + 1) F b c)) = ⊥ := by
    refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus (m + 1) F b c) (coe_quadMinus (m + 1) F b c) ?_
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [quadMinus_apply]
    simp
  exact (QuotientGroup.quotientMulEquivOfEq hbotL).trans
    ((QuotientGroup.quotientBot).trans
      ((LayerCyc.largeEvenOmegaMinusEquiv m F b c).trans
        ((QuotientGroup.quotientMulEquivOfEq hbotS).trans QuotientGroup.quotientBot).symm))

private theorem exists_elemAbelian_normalizer_map {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {p r : ℕ} {E X : Subgroup G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ r) (hEX : E ≤ Subgroup.normalizer (X : Set G)) :
    ∃ E' X' : Subgroup H, X' ≠ ⊥ ∧ IsPGroup 2 X' ∧ IsElemAbelian p E' ∧ Nat.card E' = p ^ r ∧
      E' ≤ Subgroup.normalizer (X' : Set H) := by
  refine ⟨E.map e.toMonoidHom, X.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective X e.injective]; exact hX
  · exact hX2.map e.toMonoidHom
  · exact CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.injective, hEcard]
  · exact (Subgroup.map_mono hEX).trans (Subgroup.le_normalizer_map e.toMonoidHom)

theorem rk2SplitTwDOmegaTorus_holds {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ p : ℕ}
    (hℓ : 4 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ E X : Subgroup (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c))),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (ℓ - 1) ∧
        E ≤ Subgroup.normalizer
          (X : Set (StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)))) := by
  obtain ⟨n, hn⟩ := exists_card_eq_two_pow F
  have hpn : p ∣ 2 ^ n + 1 := by rw [← hn]; exact hpq
  obtain ⟨U, E, hU, hU2, hEU, hEab, hEcard⟩ :=
    OrthRestTail.torus_minus (m := ℓ - 1) (K := F) (n := n) b c hn (by omega) hp hp2 hpn hirr
  have h := exists_elemAbelian_normalizer_map (projMinusEquiv (ℓ - 1) F b c) hU hU2 hEab hEcard hEU
  have hsub : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel (by omega)
  rw [hsub] at h
  exact h

end CFSG.LocalAnalysis.GLTheoremA
