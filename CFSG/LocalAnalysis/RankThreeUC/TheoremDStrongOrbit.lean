module

public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_zpowers_eq_centralizer_of_sq_eq_one {g : G} (hg : g ^ 2 = 1) :
    normalizer ((zpowers g : Subgroup G) : Set G) = centralizer ({g} : Set G) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [mem_centralizer_singleton_iff]
    by_cases hg1 : g = 1
    · rw [hg1, mul_one, one_mul]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ((mem_normalizer_iff.mp hx g).mp (mem_zpowers g))
    have hk2 : g ^ k = 1 ∨ g ^ k = g := by
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left
        rw [← two_mul, zpow_mul, zpow_ofNat, hg, one_zpow]
      · right
        rw [zpow_add, zpow_mul, zpow_ofNat, hg, one_zpow, one_mul, zpow_one]
    rcases hk2 with h | h
    · exact absurd (by simpa using hk.symm.trans h) hg1
    · have h' : x * g * x⁻¹ = g := hk.symm.trans h
      calc x * g = (x * g * x⁻¹) * x := by group
        _ = g * x := by rw [h']
  · have h2 : centralizer ({g} : Set G) = centralizer ((zpowers g : Subgroup G) : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact h2.le.trans (centralizer_le_normalizer _)

omit [Finite G] in
theorem isPGroup_two_zpowers_of_sq_eq_one {g : G} (hg : g ^ 2 = 1) : IsPGroup 2 (zpowers g) := by
  intro x
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg,
    one_zpow]
  rfl

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem
    _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_of_two_le_pRank_inf_normalizer
    (hw : IsWitnessGen p P M) {Y : Subgroup G} (hY1 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y)
    (hgood : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Y : Set G))) : normalizer (Y : Set G) ≤ M :=
  hw.u2 _ ⟨Y, hY1, hY2, rfl⟩ (by rwa [inf_comm])

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.not_dvd_card_inf_normalizer_map_conj
    (hw : IsWitnessGen p P M)
    (hSE : IsStronglyPEmbedded p M) {Y : Subgroup G} (hY1 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y)
    (hgood : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Y : Set G))) {n : G} (hn : n ∉ M) :
    ¬ p ∣ Nat.card
      ↥(M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) := by
  have h2 : normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) ≤
      M.map (MulAut.conj n).toMonoidHom := by
    rw [← map_equiv_normalizer_eq Y (MulAut.conj n)]
    exact map_mono (hw.normalizer_le_of_two_le_pRank_inf_normalizer hY1 hY2 hgood)
  exact fun hdvd => hSE.2.2 n hn (hdvd.trans (card_dvd_of_le (inf_le_inf_left M h2)))

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.not_dvd_card_inf_centralizer_conj
    (hw : IsWitnessGen p P M)
    (hSE : IsStronglyPEmbedded p M) {g : G} (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1)
    (hgood : 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({g} : Set G))) {n : G} (hn : n ∉ M) :
    ¬ p ∣ Nat.card ↥(M ⊓ centralizer ({n * g * n⁻¹} : Set G)) := by
  have hb : (n * g * n⁻¹) ^ 2 = 1 := by rw [conj_pow, hg2]; group
  have h := hw.not_dvd_card_inf_normalizer_map_conj hSE (zpowers_eq_bot.not.mpr hg1)
    (isPGroup_two_zpowers_of_sq_eq_one hg2)
    (by rwa [normalizer_zpowers_eq_centralizer_of_sq_eq_one hg2]) hn
  rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    normalizer_zpowers_eq_centralizer_of_sq_eq_one hb] at h

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
