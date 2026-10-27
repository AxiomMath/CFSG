module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

section L34Aut

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound (exists_equiv_projectiveSL_of_l34Index)
open CFSG.RankThree.PartTwo.KFacts.L34 (card_mulAut card_projectiveSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

private theorem card_dvd_of_l34 {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nat.card X ∣ 241920 ∧ Nat.card K = 20160 := by
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  refine ⟨?_, by rw [Nat.card_congr ψ.toEquiv, card_projectiveSL hF]⟩
  have hθ : Function.Injective (MulAut.conjNormal : X →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 : g * k * g⁻¹ = k :=
        (MulAut.conjNormal_apply g ⟨k, hk⟩).symm.trans
          (congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hg)
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hC] at hmem
    exact hmem
  let ι : X →* MulAut (projectiveSL 3 F) :=
    (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal
  have hι : Function.Injective ι := (MulAut.congr ψ).injective.comp hθ
  rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, ← card_mulAut hF]
  exact Subgroup.card_subgroup_dvd_card _

end L34Aut

variable {G : Type} [Group G] [Finite G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
  {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf3.rbar_inf_eq (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hc.almostSimple.normal
  obtain ⟨e⟩ := hc.iso
  have hK := (card_dvd_of_l34 hc.almostSimple.centralizer_eq_bot hc.l34 e).2
  have hp : IsPGroup 3 ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) :=
    Rbar.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : 3 ^ k ∣ 20160 := hk ▸ hK ▸ Subgroup.card_dvd_of_le inf_le_right
  have hk2 : k ≤ 2 := by
    by_contra h
    have := (pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd
    norm_num at this
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hc.almostSimple.A_le hc.le_K) ?_).symm
  rw [hk, hc.almostSimple.card_A]
  exact Nat.pow_le_pow_right (by norm_num) hk2

theorem D2L34BetaConf3.pow_three_eq_one (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    ∀ x ∈ R, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  set a : H := ⟨x, hc.esc.le_H hx⟩
  have hmem : QuotientGroup.mk' (primeComplementCore (G := H) 3) a ∈
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hc.rbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hp : IsPGroup 3
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) 3) a)) :=
    Rbar.isPGroup'.to_le (Subgroup.zpowers_le.mpr hmem)
  have h3 := Tits.S3AmalgamBound.kFactL34Exp3 d hc.l34 _ K hc.almostSimple.normal
    hc.almostSimple.centralizer_eq_bot hc.iso _ hp
  have ha3 : ((a ^ 3 : H) : G) ∈ R := by
    rw [Subgroup.coe_pow]
    exact R.pow_mem hx 3
  have h := eq_of_mk_eq_of_mem hc.esc.isPGroup ha3 (b := 1) R.one_mem
    (by rw [map_pow, h3, map_one])
  simpa [a] using congrArg Subtype.val h

theorem D2L34BetaConf3.card_R_eq_nine_or_27 (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    Nat.card R = 9 ∨ (Nat.card R = 27 ∧
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K =
        (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ∧
      (∀ x ∈ R, x ^ 3 = 1) ∧ ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hc.almostSimple.normal
  obtain ⟨e⟩ := hc.iso
  have hX := (card_dvd_of_l34 hc.almostSimple.centralizer_eq_bot hc.l34 e).1
  have hRR : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = Nat.card R := by
    rw [hc.rbar]
    exact hc.esc.card_map_eq le_rfl
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hc.esc.isPGroup
  have hdvd : 3 ^ n ∣ 241920 := hn ▸ hRR ▸ (Subgroup.card_subgroup_dvd_card _).trans hX
  have h9 : 3 ^ 2 ≤ 3 ^ n := hn ▸ hc.esc.card_A ▸ Subgroup.card_le_of_le hc.esc.A_le
  have hn2 : 2 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  have hn3 : n ≤ 3 := by
    by_contra h
    have := (pow_dvd_pow 3 (by omega : 4 ≤ n)).trans hdvd
    norm_num at this
  obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
  · left
    rw [hn]
    norm_num
  · right
    refine ⟨by rw [hn]; norm_num, hc.rbar_inf_eq, hc.pow_three_eq_one, fun hcomm => ?_⟩
    have hel : IsElemAbelian 3 R :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hc.pow_three_eq_one⟩
    have h3 := CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian Nat.prime_three hel hn
    rw [hc.esc.pRank_eq] at h3
    omega

theorem D2L34BetaConf3.isExtraspecialPGroup_of_card_R_eq_27
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (h27 : Nat.card R = 27) :
    CFSG.IsExtraspecialPGroup 3 R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hc.card_R_eq_nine_or_27 with h9 | ⟨-, -, hexp, hnc⟩
  · omega
  refine CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hc.esc.isPGroup
    (fun x => Subtype.ext (by simpa using hexp x x.2)) (by rw [h27]; norm_num)
    fun hcomm => hnc fun x hx y hy => ?_
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
