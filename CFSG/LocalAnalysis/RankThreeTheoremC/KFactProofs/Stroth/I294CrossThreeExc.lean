module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRest
public import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankSL2
import CFSG.RankThree.PartOne.KF.ClsExcE6Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open TauCeti
open scoped MatrixGroups

theorem le_pRank_three_of_commuting_sl2_family {K : Type} [Field K] {X : Type} [Group X] [Finite X]
    {n : ℕ} (φ : Fin n → SL(2, K) →* X) (hφ : ∀ i, Function.Injective (φ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  refine CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank.le_pRank_three_of_central_ker
    (MonoidHom.id X) (fun z hz => by rw [show z = 1 from hz]; exact Subgroup.one_mem _)
    (fun i => φ i (CFSG.LieType.Chevalley.sl2Three (K := K)))
    (fun i => φ i (CFSG.LieType.Steinberg.sl2Upper (1 : K))) ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [← map_pow, CFSG.LieType.Chevalley.sl2Three_pow_three, map_one]
  · intro i h
    apply CFSG.LieType.Chevalley.sl2Three_not_commute (K := K)
    have := h.eq
    rw [← map_mul, ← map_mul] at this
    exact hφ i this
  · intro i h
    apply CFSG.LieType.Chevalley.sl2Three_sq_not_commute (K := K)
    have := h.eq
    rw [← map_pow, ← map_mul, ← map_mul] at this
    exact hφ i this
  · intro i j hij
    exact hc j i (Ne.symm hij) _ _
  · intro i j hij
    exact hc i j hij _ _

private theorem exists_field_card' (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p f, inferInstance, inferInstance, GaloisField.card p f (by omega)⟩

theorem four_le_pRank_three_of_untwistedBridge
    {τ : CFSG.Blueprint.Chevalley.Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {X : Type} [Group X] [Finite X]
    {q : PrimePower} {hv : (c q).Valid} (e : X ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨K, _, _, hK⟩ := exists_field_card' q.p q.exponent q.prime_p q.exponent_pos
  obtain ⟨b⟩ := hB q hv K (by rw [hK, PrimePower.card_def])
  have : Finite (CFSG.Blueprint.AdjointQuotient τ K) := Finite.of_equiv X (e.trans b.symm).toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans b.symm)]
  exact CFSG.LieType.Chevalley.four_le_pRank_three_adjointQuotient_any hτ

theorem four_le_pRank_three_of_isExcBig
    {L : Type} [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex) (hd : I294CrossIsExcBig d.1)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | F4 q =>
    exact four_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (Or.inl rfl) e
  | E6 q =>
    exact four_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (Or.inr (Or.inl rfl)) e
  | E7 q =>
    exact four_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (Or.inr (Or.inr (Or.inl rfl))) e
  | E8 q =>
    exact four_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (Or.inr (Or.inr (Or.inr rfl))) e
  | twistedE6 q =>
    obtain ⟨K, _, _, -, φ, hφ1, hφ2⟩ :=
      CFSG.RankThree.PartOne.KFU.exists_four_commuting_SL2_twistedE6 q hv
    exact le_pRank_three_of_commuting_sl2_family
      (fun i => e.symm.toMonoidHom.comp (φ i))
      (fun i => e.symm.injective.comp (hφ1 i))
      (fun i j hij A B => by
        change e.symm (φ i A) * e.symm (φ j B) = e.symm (φ j B) * e.symm (φ i A)
        rw [← map_mul, ← map_mul, hφ2 i j hij A B])
  | _ => exact (hd : False).elim

theorem i294CrossThreeRankTwoExc_holds :
    I294CrossThreeRankTwoExc := by
  intro L _ _ _ _ d hd _ hLe _ _ hr _ _ _
  obtain ⟨e⟩ := hLe
  have := four_le_pRank_three_of_isExcBig d hd e
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
