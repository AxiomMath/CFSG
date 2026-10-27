module

public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem l2_psu_cover (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable)
    {S : Type} [Group S] [Finite S] {n p f : ℕ} (hn : 8 ≤ n)
    (hX : CFSG.Blueprint.LieModel S .PSU n p f) {H : Type} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) (ρ : H →* S) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = center H) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(CFSG.Open.StatedSU n (p ^ f) K) →* S)
      (α : ↥(CFSG.Open.StatedSU n (p ^ f) K) →* H),
      p.Prime ∧ Nat.card K = (p ^ f) ^ 2 ∧ Function.Surjective π ∧
      π.ker = (CFSG.Open.StatedScalars (Fin n) K).subgroupOf
        (CFSG.Open.StatedSU n (p ^ f) K) ∧
      Function.Surjective α ∧ ρ.comp α = π := by
  classical
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨eS⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by omega : n ≠ 0)
  let π₀ : ↥(CFSG.Open.StatedSU n (p ^ f) K) →*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU n (p ^ f) K) :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf
      (CFSG.Open.StatedSU n (p ^ f) K))
  let π : ↥(CFSG.Open.StatedSU n (p ^ f) K) →* S := eS.symm.toMonoidHom.comp π₀
  have hπs : Function.Surjective π :=
    eS.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = (CFSG.Open.StatedScalars (Fin n) K).subgroupOf
      (CFSG.Open.StatedSU n (p ^ f) K) := by
    rw [MonoidHom.ker_comp_of_injective π₀ eS.symm.toMonoidHom eS.symm.injective,
      QuotientGroup.ker_mk']
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hSUperf : Group.IsPerfect (CFSG.Open.StatedSU n (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := p) (f := f) hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  obtain ⟨hcomm, ⟨eM⟩⟩ := hG S .PSU n p f hX
  have hSperf : Group.IsPerfect S := ⟨hcomm⟩
  have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) =
      Nat.gcd n (p ^ f + 1) := by
    rw [Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).symm.toEquiv,
      Nat.card_congr eM.toEquiv]
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU n p f =
        (Nat.gcd n (p ^ f + 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU n p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
  have hπc : π.ker ≤ Subgroup.center (CFSG.Open.StatedSU n (p ^ f) K) := by
    rw [hπk]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = Nat.card π.ker := by
    rw [hcardM, hπk, (CFSG.LinearGroups.unitary_scalar_kernel hadm.1 hK (by omega)).2.2]
  obtain ⟨α, hρα, hαs⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_hom_of_card_multiplier_eq hSperf hSUperf π hπs
      hπc hcard ρ hρs hρk.le
  exact ⟨K, hKf, hKfin, π, α, hadm.1, hK, hπs, hπk, hαs hq.1, hρα⟩

end CFSG.OddStandard.HigherRank.YamadaG23
