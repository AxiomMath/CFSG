module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.HardMathSupport.Curtis.Proving.AutomizerBridge
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterAutPSL
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_le_of_isPGroup_of_not_pow_four_dvd {A : Type*} [Group A] (R : Subgroup A)
    [Finite ↥R] (hR : IsPGroup 3 R) (h : ¬ 3 ^ 4 ∣ Nat.card A) : Nat.card R ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card A := Subgroup.card_subgroup_dvd_card R
  rw [hk] at hdvd ⊢
  by_contra hc
  have hk4 : 4 ≤ k := by
    by_contra hk4
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact h ((Nat.pow_dvd_pow 3 hk4).trans hdvd)

theorem relIndex_centralizer_le_of_psl_three {Y : Type*} [Group Y] [Finite Y] {L : Subgroup Y}
    [Group.IsPerfect ↥L] {e : ℕ} (he : 1 ≤ e) (h3 : ¬ 3 ∣ e)
    (ι : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 (GaloisField 2 e)) {U : Subgroup Y}
    (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U) :
    (U ⊓ Subgroup.centralizer (L : Set Y)).relIndex U ≤ 27 := by
  rw [CFSG.HardMathSupport.Curtis.Proving.relIndex_centralizer_eq_card_automizer L U hU]
  set f := CFSG.HardMathSupport.Curtis.Proving.automizerOn L U hU with hf
  set g : MulAut ↥L →* MulAut (projectiveSL 3 (GaloisField 2 e)) :=
    (MulAut.congr ι).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L) with hg
  have hginj : Function.Injective g :=
    (MulAut.congr ι).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L)
  have hker : (g.comp f).ker = f.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hginj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hcard : Nat.card f.range = Nat.card (g.comp f).range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker, hker]
  rw [hcard]
  refine card_le_of_isPGroup_of_not_pow_four_dvd _ ?_
    (not_pow_four_dvd_card_mulAut_psl_three he h3)
  exact hU3.of_surjective (g.comp f).rangeRestrict (g.comp f).rangeRestrict_surjective

end CFSG.HardMathSupport.Curtis.Coordinator
