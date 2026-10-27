module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2TwoModel
import CFSG.LocalAnalysis.StandardType.GGTwE6K1D4
import CFSG.LocalAnalysis.StandardType.GGTwE6K1A5
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Class
import CFSG.LargeExtraspecial.A2ModOrdCard
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAutCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.StandardType.SCFourCover (twE6MatFixDim_mem_of_pow_three
  statedClassicalModel_component_threeA2_two lieModel_rationalComponent_d4t2
  statedClassicalModel_rationalComponent_a5t1)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn (d5_class_strongModel)
open CFSG.LargeExtraspecial.A2Mod.Ord (card_of_lieModel_POmegaPlus card_of_lieModel_POmegaMinus
  card_of_lieModel_trialityD4)
open CFSG.Timmesfeld (card_statedClassicalModel_two)
open CFSG.ComponentClassification.CatLeaf (card_quotient_center_congr)

private theorem ringChar_eq_two_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) : ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  exact ringChar.eq K 2


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem card_centerQuot_twE6Line_of_dim (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    (twE6MatFixDim K σ h = 24 → Nat.card (↥J ⧸ Subgroup.center ↥J) = 5515776) ∧
    (twE6MatFixDim K σ h = 30 → Nat.card (↥J ⧸ Subgroup.center ↥J) = 174182400 ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 211341312) ∧
    (twE6MatFixDim K σ h = 36 → Nat.card (↥J ⧸ Subgroup.center ↥J) = 9196830720) ∧
    (twE6MatFixDim K σ h = 46 → Nat.card (↥J ⧸ Subgroup.center ↥J) = 25015379558400) := by
  have hchar := ringChar_eq_two_of_card_four hK
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have he : D.e = 1 := by
    have h1 := D.hqe
    rw [hchar] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (pow_one 2).symm)
  have h3q : 3 ∣ 2 + 1 := by norm_num
  obtain ⟨i, -, hJi⟩ := D.exists_rationalComponent hJ
  have hJR := card_quotient_center_congr
    ((J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi))
  refine ⟨fun h24 => ?_, fun h30 => ?_, fun h36 => ?_, fun h46 => ?_⟩
  ·
    obtain ⟨-, hm⟩ := statedClassicalModel_component_threeA2_two hK hσ hh1 hh3 h24 hJ
    exact ((card_statedClassicalModel_two hm).2.1 rfl).trans (by decide)
  ·
    rcases lieModel_rationalComponent_d4t2 D h3q h30 i with hm | hm <;> rw [hchar, he] at hm
    · exact Or.inl (hJR.trans ((card_of_lieModel_POmegaPlus hm).2.trans (by decide)))
    · exact Or.inr (hJR.trans (card_of_lieModel_trialityD4 hm))
  ·
    have hm := statedClassicalModel_rationalComponent_a5t1 D h3q h36 i
    rw [hchar, he] at hm
    exact hJR.trans (((card_statedClassicalModel_two hm).2.1 rfl).trans (by decide))
  ·
    obtain ⟨t, ht, Fr, hFr, hΦ0⟩ := D.hS
    obtain rfl : t = .E6 := by
      cases t
      · rfl
      · exact absurd ht (by decide)
    have hΦ : D.S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr :=
      MonoidHom.ext fun g => (hΦ0 g).trans rfl
    have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
    have hk : (kernelRoots (rootCharHom D.a)).ncard = 40 := by
      have := D.hker
      omega
    obtain ⟨r, e, hr, hqr, hmodel⟩ :=
      d5_class_strongModel D.S hFr hΦ D.hL3 D.hT D.hap (by rw [hq2]) hk i
    haveI := D.hchar
    obtain rfl : r = 2 := by rw [← hr, ringChar.eq (AlgebraicClosure K) (ringChar K), hchar]
    obtain rfl : e = 1 :=
      Nat.pow_right_injective (le_refl 2) (hqr.symm.trans (hq2.trans (pow_one 2).symm))
    exact hJR.trans ((card_of_lieModel_POmegaMinus hmodel.1).2.trans
      (by simp only [CFSG.Open.ordTwistedD]; decide))

theorem twE6MatFixDim_eq_28_of_card_u5two (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 13685760) : twE6MatFixDim K σ h = 28 := by
  have hK3 : ringChar K ≠ 3 := by rw [ringChar_eq_two_of_card_four hK]; decide
  obtain ⟨h24, h30, h36, h46⟩ := card_centerQuot_twE6Line_of_dim hK hσ hh3 hh1 hJ
  have hmem := twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hd | hd | hd | hd | hd
  · have := h24 hd
    omega
  · exact hd
  · rcases h30 hd with h' | h' <;> omega
  · have := h36 hd
    omega
  · have := h46 hd
    omega

theorem twE6MatFixDim_eq_28_or_36_of_card_u6two (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 9196830720) :
    twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36 := by
  have hK3 : ringChar K ≠ 3 := by rw [ringChar_eq_two_of_card_four hK]; decide
  obtain ⟨h24, h30, -, h46⟩ := card_centerQuot_twE6Line_of_dim hK hσ hh3 hh1 hJ
  have hmem := twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hd | hd | hd | hd | hd
  · have := h24 hd
    omega
  · exact Or.inl hd
  · rcases h30 hd with h' | h' <;> omega
  · exact Or.inr hd
  · have := h46 hd
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
