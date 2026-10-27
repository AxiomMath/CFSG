module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankNode
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Linear

open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

variable {m : ℕ} {F : Type} [Field F]

theorem quasiNode_sl [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (h4 : 4 ≤ Nat.card F)
    (hpq : p ^ 2 ∣ Nat.card F ^ 2 - 1) (i : Fin m) :
    QuasiNode (SpecialLinear.rootDatum m F) p i := by
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  have hrange := rankOne_eq_range_of_sl2 SL.isParametrization hx hy
  exact QuasiNode.of_equiv_sl2 hp h4 hpq
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hφ).symm)

theorem exists_quasisimple_psl {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hNJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) (hJL : J ≤ L)
    (hnB : ∀ T' : Subgroup Y, IsSylowTwoOf T' L → J ≠ L ⊓ Subgroup.normalizer (T' : Set Y))
    {n f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) (hpq : p ^ 2 ∣ 2 ^ f - 1) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ^ 2 ∣ Nat.card X := by
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hC
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hle : p ^ 2 ≤ 2 ^ f - 1 := Nat.le_of_dvd (by omega) hpq
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    omega
  have hpq' : p ^ 2 ∣ Nat.card F ^ 2 - 1 := by
    rw [hcard]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
    rw [one_pow] at this
    exact hpq.trans this
  exact exists_quasisimple_of_borelQuotient hT hNJ hJL hnB
    (borelQuotient_sl ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm)) hp
    (quasiNode_sl hp h4 hpq')

end Linear

end CFSG.AGLEmbedding.LieOut
