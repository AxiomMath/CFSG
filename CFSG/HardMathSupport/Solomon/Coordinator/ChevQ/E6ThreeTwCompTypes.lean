module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompHat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompLayerInner

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

section Package


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.twFinite (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A) : Finite K :=
  Nat.finite_of_card_ne_zero (by
    rw [F.pic.card_eq]
    exact pow_ne_zero _ (pow_ne_zero _ hU.prime.ne_zero))

theorem TwCompFrames.twThree_dvd (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A) :
    3 ∣ ℓ ^ f + 1 := by
  have h := F.mod_three
  omega

theorem TwCompFrames.twLe_torusHat (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A) :
    T ≤ twTorusHat K σ g₀ := fun τ hτ => by
  obtain ⟨hτC, hτH⟩ := (F.pic.mem_T τ).1 hτ
  exact mem_twTorusHat.2 ⟨twRootGroup_le_inndiagGL hτC, hτH⟩

theorem TwCompFrames.twCard_three_le_nine (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    {e : ModGL TwistTag.E6.tag K} (he : e ∈ twTorusHat K σ g₀) (heT : e ∉ T)
    (he3 : e ^ 3 = 1) :
    Nat.card {τ : ModGL TwistTag.E6.tag K // τ ∈ T ∧ τ ^ 3 = 1} ≤ 9 := by
  haveI : Finite K := F.twFinite
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have h1 := twCard_three_mul_le F.twLe_torusHat twTorusHat_comm he heT he3
  have h2 := twTorusHat_card_three_le hU.prime hU.one_le F.pic F.twThree_dvd
  omega

theorem TwCompFrames.twComm_mem_layer (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n)
    (hX : Nat.card {τ : ModGL TwistTag.E6.tag K // τ ∈ T ∧ τ ^ 3 = 1} ≤ 9) :
    ∀ τ ∈ T, n * τ * n⁻¹ * τ⁻¹ ∈ T ⊓ ⨆ i, L i := by
  haveI : Finite K := F.twFinite
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hTT := F.twLe_torusHat
  have hnT : ∀ τ, τ ∈ T ↔ n * τ * n⁻¹ ∈ T := F.pic.conj_mem_T hl.n_mem
  exact twConj_comm_mem_of_cube hl.T_comm inf_le_left
    (fun τ hτ h9 =>
      twTorusHat_pow_three_of_pow_nine hU.prime hU.one_le F.pic F.twThree_dvd (hTT hτ) h9)
    (fun τ hτ => Subgroup.mem_inf.2 ⟨pow_mem hτ 3,
      F.mem_layer_of_inner hl (pow_mem (hTT hτ) 3) (F.pow_three_inner (hTT hτ))⟩)
    hX (Subgroup.mem_inf.2 ⟨hl.h₀_mem_T, Subgroup.mem_iSup_of_mem 0 (hl.h₀_mem_L 0)⟩)
    hl.h₀_ne hl.h₀_pow hnT
    (fun τ => Subgroup.mem_inf.trans ((and_congr (hnT τ) (hl.conj_mem_iSup τ)).trans
      Subgroup.mem_inf.symm))
    (fun τ hτ => hl.pow_three_comm_mem hnT hτ)


theorem TwCompFrames.twExists_outer_torsion (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) {ε : MulAut (twistedE6RootGroup K σ)}
    (hε : ε ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hεi : ε ∉ twistedE6Inn K σ)
    (hcomm : ε * MulAut.conj s = MulAut.conj s * ε)
    (hrange : ∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range) :
    ∃ e ∈ twTorusHat K σ g₀, e ∉ T ∧ e ^ 3 = 1 := by
  haveI : Finite K := F.twFinite
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ĝ, hĝ, hεĝ, hĝh, hĝL⟩ :=
    twDec_of_aut hU.prime hU.one_le F.pic.card_eq F.pic.σ_apply F.range hs hε hcomm hrange
  obtain ⟨τ, hτ, x, rfl⟩ := twDec_decomp hU.prime hU.one_le hl F.pic F.range hĝ hĝh hĝL
  have hτT : τ ∉ T := by
    intro hτT
    have hπ : twLayerProd ρ x ∈ twistedE6RootGroup K σ :=
      mul_mem (mul_mem (ρ 0 (x 0)).2 (ρ 1 (x 1)).2) (ρ 2 (x 2)).2
    exact hεi (MonoidHom.mem_range.2 ⟨⟨_, mul_mem (hl.T_le hτT) hπ⟩,
      MulEquiv.ext fun c => Subtype.ext (hεĝ c).symm⟩)
  obtain ⟨χ, hχ, hχ3, hτχ⟩ := twCompQuot_exists_torsion (T := twTorusHat K σ g₀) (N := T)
    (fun τ' hτ' h9 =>
      twTorusHat_pow_three_of_pow_nine hU.prime hU.one_le F.pic F.twThree_dvd hτ' h9)
    (fun τ' hτ' => twTorusHat_pow_three_mem hU.prime hU.one_le F.pic hτ') hτ
  refine ⟨χ, hχ, fun hχT => hτT ?_, hχ3⟩
  have h := mul_mem hτχ hχT
  rwa [inv_mul_cancel_right] at h

end Package

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
