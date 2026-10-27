module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
public import CFSG.ClassicalInvolution.Q3.Q3T6DExact
public import CFSG.ClassicalInvolution.SmallCases.NDBG1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GAssembly
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal
import CFSG.ClassicalInvolution.Q3.Q3T6DSetupA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GCase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIIFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_commutator_mem_oddCore {M M' : Subgroup G} {w z : G}
    (hM'M : M' ≤ Subgroup.normalizer (M : Set G)) (hMM' : M ≤ Subgroup.normalizer (M' : Set G))
    (hz : z ∈ M ⊔ M') (hzz : z * z = 1)
    (hwM : ∀ m ∈ M, ⁅w, m⁆ ∈ oddCoreOf M) (hwM' : ∀ m ∈ M', ⁅w, m⁆ ∈ oddCoreOf M')
    (hzM : ∀ o ∈ oddCoreOf M, o * z = z * o) (hzM' : ∀ o ∈ oddCoreOf M', o * z = z * o) :
    w ∈ Subgroup.centralizer ({z} : Set G) := by
  have hOM : oddCoreOf M ≤ oddCoreOf (M ⊔ M') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self M).trans le_sup_left)
      (fun g hg => mem_normalizer_oddCore_of_mem_normalizer
        ((sup_le Subgroup.le_normalizer hM'M) hg)) (oddCoreOf_odd_natCard M)
  have hOM' : oddCoreOf M' ≤ oddCoreOf (M ⊔ M') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self M').trans le_sup_right)
      (fun g hg => mem_normalizer_oddCore_of_mem_normalizer
        ((sup_le hMM' Subgroup.le_normalizer) hg)) (oddCoreOf_odd_natCard M')
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M M' hM'M] at hz
  obtain ⟨m, hm, m', hm', hzmm⟩ := hz
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ oddCoreOf M, ∃ b ∈ oddCoreOf M', ⁅w, z⁆ = a * b :=
    ⟨⁅w, m⁆, hwM m hm, m * ⁅w, m'⁆ * m⁻¹,
      mem_normalizer_oddCoreOf_of_mem_normalizer (hMM' hm) (hwM' m' hm'), by
        rw [← hzmm]
        simp only [commutatorElement_def]
        group⟩
  have hn : ⁅w, z⁆ ∈ oddCoreOf (M ⊔ M') :=
    hab ▸ (oddCoreOf (M ⊔ M')).mul_mem (hOM ha) (hOM' hb)
  have hnz : ⁅w, z⁆ * z = z * ⁅w, z⁆ := by
    rw [hab, mul_assoc, hzM' b hb, ← mul_assoc, hzM a ha, mul_assoc]
  have hconj : ⁅w, z⁆ * z = w * z * w⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hnn : ⁅w, z⁆ * ⁅w, z⁆ = 1 := by
    calc ⁅w, z⁆ * ⁅w, z⁆ = ⁅w, z⁆ * ⁅w, z⁆ * (z * z) := by rw [hzz, mul_one]
      _ = ⁅w, z⁆ * (⁅w, z⁆ * z) * z := by group
      _ = ⁅w, z⁆ * (z * ⁅w, z⁆) * z := by rw [hnz]
      _ = (⁅w, z⁆ * z) * (⁅w, z⁆ * z) := by group
      _ = w * (z * z) * w⁻¹ := by rw [hconj]; group
      _ = 1 := by rw [hzz]; group
  have hn1 : ⁅w, z⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (M ⊔ M')) hn
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hnn)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hn1)

theorem omegaOfSet_subset_of_kl {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω) (hv : AViol Ω M J zM zJ)
    (hKL : ∀ N ∈ twinSet Ω M, ∀ o ∈ oddCoreOf N, o * zJ = zJ * o) :
    omegaOfSet Ω (twinSet Ω M) ⊆ omegaOfSet Ω (twinSet Ω J) := by
  intro L hLset
  obtain ⟨v, Ms, hVU, hVJ, -, hMsM, htw, hvv⟩ :=
    exists_hexagon_data3 hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMT : M ∈ twinSet Ω M := ⟨hM, zM, hv.hzK, hv.hzK⟩
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hMsΩ : Ms ∈ Ω := hMsT.1
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hzJM : zJ ∈ M ⊔ Ms := mem_sup_of_hexagon3 hΩ hv.hzJ hVU hVJ hvv
  have hLΩ : L ∈ Ω := hLset.1
  have hLnbr : L ∈ omegaNbr Ω M := hLset.2 M hMT
  obtain ⟨-, hLM, T, hTR, hTL, hTN⟩ := id hLnbr
  have hTsyl : IsSylow2In T L := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hLΩ hTR hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hTR
  have hLMs : L ≠ Ms := (hLset.2 Ms hMsT).2.1
  have hTC : T ≤ Subgroup.centralizer ({zM} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' hv.hzK hTN
  have hTMs : T ≤ Subgroup.normalizer (Ms : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hMsΩ hLΩ (Ne.symm hLMs) hzMs hTL hT2
      (by omega) hTC
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
  have hcM : ∀ x ∈ T, ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hM hLΩ (Ne.symm hLM)
      hv.hzK hzL hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hcMs : ∀ x ∈ T, ∀ m ∈ Ms, ⁅x, m⁆ ∈ oddCoreOf Ms := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hMsΩ hLΩ (Ne.symm hLMs)
      hzMs hzL hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hMsN : Ms ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hMsΩ hM hMsM hzMs hv.hzK
  have hMN : M ≤ Subgroup.normalizer (Ms : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hM hMsΩ (Ne.symm hMsM) hv.hzK hzMs
  have hTJ : T ≤ Subgroup.centralizer ({zJ} : Set G) := fun w hw =>
    mem_centralizer_of_commutator_mem_oddCore hMsN hMN hzJM hv.hzJ.sq (hcM w hw) (hcMs w hw)
      (hKL M hMT) (hKL Ms hMsT)
  refine ⟨hLΩ, fun J' hJ' => ?_⟩
  have hzJ' : IsUniqueInvolution J' zJ := isUniqueInvolution_of_mem_twinSet hv.hzJ hJ'
  have hLJ' : L ≠ J' := by
    rintro rfl
    have h1 : M ∈ omegaNbr Ω L := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM hLΩ hLnbr
    have hKP := (Q3T7M.l6_3 G Ω hΩ J hv.mem L hJ').1
    have h2 : M ∈ KPerp Ω J := by
      rw [hKP]
      exact Or.inr h1
    rcases h2 with h | h
    · exact hv.star.2.1 h.symm
    · exact hv.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hv.mem hM h)
  exact ⟨hLΩ, hLJ', T, hTR, hTL,
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ'.1 hLΩ (Ne.symm hLJ') hzJ' hTL hT2
      (by omega) hTJ⟩

end Transfer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
