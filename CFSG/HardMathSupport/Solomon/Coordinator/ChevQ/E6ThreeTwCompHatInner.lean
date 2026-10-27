module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompTypes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInndiagOuter

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Hat


variable {K : Type} [Field K] {σ : K ≃+* K} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {g₀ : ModGL Tag.E6 (AlgebraicClosure K)} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}

theorem twDec_decomp_shift {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n)
    {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    {ĝ : ModGL TwistTag.E6.tag K} (hĝ : ĝ ∈ twistedE6InndiagGL K σ) (hcomm : ĝ * h₀ = h₀ * ĝ) :
    ∃ τ ∈ twTorusHat K σ g₀, ∃ x : Fin 3 → unitarySU ℓ f K 3, ∃ k < 3,
      ĝ = τ * twLayerProd ρ x * n ^ k := by
  classical
  obtain ⟨hmadj, -⟩ := twLinePsi_inndiag hℓ hf pic hĝ
  obtain ⟨ω, hω3, hω1, hψh₀⟩ := pic.h₀_image
  have hmd : rootDiagUnit Tag.E6 (twLineChar ω) * twLinePsi K g₀ ĝ =
      twLinePsi K g₀ ĝ * rootDiagUnit Tag.E6 (twLineChar ω) := by
    have h1 := congrArg (twLinePsi K g₀) hcomm.symm
    rw [map_mul, map_mul, hψh₀] at h1
    exact h1
  obtain ⟨k, hk⟩ := twLine_conj_shift hω3 hω1 hmadj hmd
  have hshift : ∀ i, ∀ l ∈ L i, ĝ⁻¹ * l * ĝ ∈ L (i - k) := by
    intro i l hli
    obtain ⟨hlC, hlψ⟩ := (pic.mem_L i l).1 hli
    have hC : ĝ⁻¹ * l * ĝ ∈ twistedE6RootGroup K σ := by
      have h1 := (Subgroup.mem_normalizer_iff.1
        (twistedE6InndiagGL_le_normalizer K σ (inv_mem hĝ)) l).1 hlC
      rwa [inv_inv] at h1
    refine (pic.mem_L (i - k) _).2 ⟨hC, ?_⟩
    have h2 : twLinePsi K g₀ l ∈ (rootSpan Tag.E6 (AlgebraicClosure K)
        (twE6FrameS (i - k))).map (MulAut.conj (twLinePsi K g₀ ĝ)).toMonoidHom := by
      rw [hk (i - k), sub_add_cancel]
      exact hlψ
    obtain ⟨u, hu, hul⟩ := h2
    have hul' : twLinePsi K g₀ ĝ * u * (twLinePsi K g₀ ĝ)⁻¹ = twLinePsi K g₀ l := hul
    have h3 : twLinePsi K g₀ (ĝ⁻¹ * l * ĝ) = u := by
      rw [map_mul, map_mul, map_inv, ← hul']
      group
    rw [h3]
    exact hu
  obtain ⟨j, hj3, hpow⟩ := twLine_exists_pow hl.n_conj k
  have hnmem : n ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    rw [hl.centralizer_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hnc : Commute h₀ n :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hnmem).2 h₀ (Set.mem_singleton h₀)
  have hc : Commute h₀ (n ^ j)⁻¹ := (hnc.pow_right j).inv_right
  have hĝ' : ĝ * (n ^ j)⁻¹ ∈ twistedE6InndiagGL K σ :=
    mul_mem hĝ (inv_mem (pow_mem ((le_sup_left : twistedE6RootGroup K σ ≤
      twistedE6InndiagGL K σ) hl.n_mem) j))
  have hcomm' : ĝ * (n ^ j)⁻¹ * h₀ = h₀ * (ĝ * (n ^ j)⁻¹) := by
    calc ĝ * (n ^ j)⁻¹ * h₀ = ĝ * ((n ^ j)⁻¹ * h₀) := mul_assoc _ _ _
      _ = ĝ * (h₀ * (n ^ j)⁻¹) := by rw [hc.eq]
      _ = (ĝ * h₀) * (n ^ j)⁻¹ := (mul_assoc _ _ _).symm
      _ = (h₀ * ĝ) * (n ^ j)⁻¹ := by rw [hcomm]
      _ = h₀ * (ĝ * (n ^ j)⁻¹) := mul_assoc _ _ _
  have hnorm : ∀ i, ∀ l ∈ L i, (ĝ * (n ^ j)⁻¹)⁻¹ * l * (ĝ * (n ^ j)⁻¹) ∈ L i := by
    intro i l hli
    have h1 : n ^ j * (ĝ⁻¹ * l * ĝ) * (n ^ j)⁻¹ ∈
        (L (i - k)).map (MulAut.conj (n ^ j)).toMonoidHom := ⟨_, hshift i l hli, rfl⟩
    rw [hpow (i - k), sub_add_cancel] at h1
    have e : (ĝ * (n ^ j)⁻¹)⁻¹ * l * (ĝ * (n ^ j)⁻¹) = n ^ j * (ĝ⁻¹ * l * ĝ) * (n ^ j)⁻¹ := by
      group
    rw [e]
    exact h1
  obtain ⟨τ, hτ, x, hx⟩ := twDec_decomp hℓ hf hl pic hρ hĝ' hcomm' hnorm
  refine ⟨τ, hτ, x, j, hj3, ?_⟩
  rw [← hx, inv_mul_cancel_right]

end Hat

section Package


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.twExists_hat_torsion (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) (hconj : TwE6ThreeA2ConjAt K σ) :
    ∃ e ∈ twTorusHat K σ g₀, e ∉ T ∧ e ^ 3 = 1 := by
  haveI : Finite K := F.twFinite
  obtain ⟨d, hd, hdC⟩ :=
    twExists_inndiag_notMem_root σ F.pic.card_eq F.pic.σ_apply F.twThree_dvd
  obtain ⟨ĝ, hĝ, hĝC, hĝh⟩ := twExists_inndiag_comm_notMem_root hconj hl.h₀_mem hl.h₀_pow
    hl.finrank_fixed hd hdC
  obtain ⟨τ, hτ, x, k, -, hτeq⟩ :=
    twDec_decomp_shift hU.prime hU.one_le hl F.pic F.range hĝ hĝh
  have hτT : τ ∉ T := by
    intro hτT
    have hπ : twLayerProd ρ x ∈ twistedE6RootGroup K σ :=
      mul_mem (mul_mem (ρ 0 (x 0)).2 (ρ 1 (x 1)).2) (ρ 2 (x 2)).2
    apply hĝC
    rw [hτeq]
    exact mul_mem (mul_mem (hl.T_le hτT) hπ) (pow_mem hl.n_mem k)
  obtain ⟨χ, hχ, hχ3, hτχ⟩ := twCompQuot_exists_torsion (T := twTorusHat K σ g₀) (N := T)
    (fun τ' hτ' h9 =>
      twTorusHat_pow_three_of_pow_nine hU.prime hU.one_le F.pic F.twThree_dvd hτ' h9)
    (fun τ' hτ' => twTorusHat_pow_three_mem hU.prime hU.one_le F.pic hτ') hτ
  refine ⟨χ, hχ, fun hχT => hτT ?_, hχ3⟩
  have h := mul_mem hτχ hχT
  rwa [inv_mul_cancel_right] at h

theorem TwCompFrames.twComm_mem_layer_inner (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) (hconj : TwE6ThreeA2ConjAt K σ) :
    ∀ τ ∈ T, n * τ * n⁻¹ * τ⁻¹ ∈ T ⊓ ⨆ i, L i := by
  obtain ⟨e, he, heT, he3⟩ := F.twExists_hat_torsion hl hconj
  exact F.twComm_mem_layer hl (F.twCard_three_le_nine he heT he3)

end Package

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
