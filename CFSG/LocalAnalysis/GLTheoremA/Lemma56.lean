module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5E
public import CFSG.LocalAnalysis.GLTheoremA.Sec5C
public import CFSG.LocalAnalysis.GLTheoremA.P51.Conj
public import CFSG.LocalAnalysis.GLTheoremA.P55.StepB
public import CFSG.LocalAnalysis.GLTheoremA.P55.StepC
public import CFSG.LocalAnalysis.GLTheoremA.P55.StepC2
public import CFSG.LocalAnalysis.GLTheoremA.P55.StepF
public import CFSG.LocalAnalysis.GLTheoremA.P55.StepG
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma56 {p : ℕ} (hc : Sec5Ctx G p) (hno : ¬ Prop55At G p) (h51 : Prop51At G p)
    (h113 : I113UsedAt G p) (h336 : I336UsedAt) (hdih : DihedralUsed) (h71 : I71UsedAt G p)
    {B L : Subgroup G} {x : G} (hBxL : IsS0Max p B x L) :
    ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J ∧ J ≠ L ∧
      ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
        (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  have hp := hc.prime
  have hp2 := hc.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := hBxL.1.1
  have hB : GLAIsBmax p B := hS.1
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB.1
  have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB.1 hS.2.1.1
  have hodd := odd_card_glaPPrimeCoreOf_of_not_prop55 hp hno hBxL
  have hBinv : ∀ K : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K →
      B ≤ Subgroup.normalizer (K : Set G) := fun K hK => lemma54 hc h51 h113 hBxL K hK
  obtain ⟨-, -, T₀, hT₀x, hT₀2, hBT₀, hT₀B, hQ8⟩ := hS.2.1
  obtain ⟨E, k, hEB, hk, hEk, hRB, U, hUR, hU, hUk⟩ :=
    P55.exists_codim_twoRank h336 hp hp2 hB.1 hT₀2 hBT₀ (by
      rw [Subgroup.commutator_comm] at hT₀B ⊢
      exact hT₀B) hQ8
  set R : Subgroup G := T₀ ⊓ Subgroup.centralizer (E : Set G) with hRdef
  have hR2 : IsPGroup 2 R := hT₀2.to_le inf_le_left
  have hRx : R ≤ Subgroup.centralizer ({x} : Set G) := inf_le_left.trans hT₀x
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := by
    intro b hb
    have h1 := mem_normalizer_iff_gLBConj_eq.1 (hBT₀ hb)
    have h2 : GLBConj b (Subgroup.centralizer (E : Set G)) = Subgroup.centralizer (E : Set G) :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer
        (Subgroup.mem_centralizer_iff.2 fun e he => isElemAbelian_commute hB.1 (hEB he) hb))
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
  have hRQ : (⁅oPPrimeP p (Subgroup.centralizer ({x} : Set G)), R⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
    by_cases h : ∃ r ∈ R, r ≠ 1 ∧ ∀ q ∈ oPPrimeP p (Subgroup.centralizer ({x} : Set G)),
        ⁅q, r⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))
    · exact P55.commutator_oPPrimeP_le_of_exists hp hp2 hB hBCx hR2 hRx hBR hodd h
    · exfalso
      refine P55.false_of_faithful hc h51 hdih hBxL hodd hT₀2 hT₀x hBT₀ hEB hEk hk hUR hU hUk
        fun u hu hq => ?_
      by_contra hu1
      exact h ⟨u, hUR hu, hu1, hq⟩
  set S : Subgroup G := ⁅R, B⁆ with hSdef
  have hSR : S ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr b hb
    rw [commutatorElement_def]
    have : b * r⁻¹ * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hBR hb) r⁻¹).1 (R.inv_mem hr)
    simpa [mul_assoc] using R.mul_mem hr this
  have hS2 : IsPGroup 2 S := hR2.to_le hSR
  have hSx : S ≤ Subgroup.centralizer ({x} : Set G) := hSR.trans hRx
  have hRp : ¬ p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hR2
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hSB : (⁅S, B⁆ : Subgroup G) = S :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hBp hBR hRp
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := by
    intro b hb
    have h1 : GLBConj b R = R := mem_normalizer_iff_gLBConj_eq.1 (hBR hb)
    have h2 : GLBConj b B = B := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hb)
    rw [mem_normalizer_iff_gLBConj_eq]
    unfold GLBConj at h1 h2 ⊢
    rw [Subgroup.map_commutator, h1, h2]
  have hSN : ∀ K : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K →
      S ≤ Subgroup.normalizer (K : Set G) := fun K hK => by
    have := P51.commutator_le_normalizer_of_forall hK hRx fun K' hK' _ => hBinv K' hK'
    rwa [Subgroup.commutator_comm] at this
  have hSne : S ≠ ⊥ := hRB
  obtain ⟨J, hJ, hJnc⟩ : ∃ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J ∧
      ¬ S ≤ centModSubgroup p J := by
    by_contra h
    push Not at h
    exact hSne (P55.eq_bot_of_le_centModSubgroup_forall hp hp2 hS2 hSx hodd
      ((Subgroup.commutator_mono le_rfl hSR).trans hRQ) h)
  have hinner := h71 B x J S hB hS.2.1 hJ (hBinv J hJ) hS2 hSx (hSN J hJ) hBS hSB
  have hoddJ : Odd (Nat.card (GLAPPrimeCoreOf p J)) := by
    have hle : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ.2.1]
      exact inf_le_right
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
  obtain ⟨T, hTJ, hT2, hBT, hTB⟩ := P55.exists_twoSubgroup_of_inducesInnerMod hp hp2 hJ hoddJ hBp
    (hBinv J hJ) hBS hS2 (hSN J hJ) hSB hinner hJnc
  refine ⟨J, hJ, ?_, T, hTJ, hT2, hBT, hTB⟩
  rintro rfl
  apply hno
  refine ⟨B, x, J, hBxL, T, hTJ.trans le_sup_left, fun hT => hTB ?_, hT2, hBT⟩
  rw [hT]
  exact Subgroup.commutator_bot_left B

end CFSG.LocalAnalysis.GLTheoremA
