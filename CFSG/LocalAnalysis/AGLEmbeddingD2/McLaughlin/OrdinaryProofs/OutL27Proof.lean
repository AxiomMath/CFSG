module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankRow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem outL27_proved : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutL27 := by
  intro X _ hX
  have hsimple : IsSimpleGroup X := isLThreeTwo_simple hX
  have hcard168 : Nat.card X = 168 := isLThreeTwo_card_eq hX
  have hcardAut : Nat.card (MulAut X) = 336 := by
    obtain ⟨d, hd, ⟨e⟩⟩ := hX
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨e2⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (isLinTwoIndex_seven_one hd)
    rw [Nat.card_congr (MulAut.congr (e.trans e2)).toEquiv]
    exact (card_mulAut_psl2GF 7 1 le_rfl).trans (by norm_num)
  have hcenter : Subgroup.center X = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp h
      have hp := Group.is_simple_iff_prime_card.mp hsimple
      rw [hcard168] at hp
      norm_num at hp
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h1 := DFunLike.congr_fun hg h
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hcenter, Subgroup.mem_bot] at hgc
    exact hgc
  have hInn : Nat.card (MulAut.conj : X →* MulAut X).range = 168 := by
    rw [← hcard168]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hindex : (MulAut.conj : X →* MulAut X).range.index = 2 := by
    have h := Subgroup.index_mul_card (H := (MulAut.conj : X →* MulAut X).range)
    rw [hInn, hcardAut] at h
    omega
  have : (MulAut.conj : X →* MulAut X).range.Normal := Subgroup.normal_of_index_eq_two hindex
  intro ψ k hψ
  have hit : ∀ (n : ℕ) (x : X), (ψ ^ n) x = ψ^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  have hpow : ψ ^ (3 ^ k) = 1 := by
    apply MulEquiv.ext
    intro x
    rw [hit, hψ]
    rfl
  have hq : (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ^ (3 ^ k) = 1 := by
    rw [← map_pow, hpow, map_one]
  have hqcard : Nat.card (MulAut X ⧸ (MulAut.conj : X →* MulAut X).range) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hord2 : orderOf (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ∣ 2 := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ)
    rwa [hqcard] at h
  have hord3 : orderOf (QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hq
  have hord1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)) hord2 hord3
  have hq1 : QuotientGroup.mk' (MulAut.conj : X →* MulAut X).range ψ = 1 :=
    orderOf_eq_one_iff.mp hord1
  have hmem : ψ ∈ (MulAut.conj : X →* MulAut X).range := (QuotientGroup.eq_one_iff ψ).mp hq1
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨a, fun x => ?_⟩
  rw [← ha, MulAut.conj_apply]

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
