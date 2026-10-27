module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.Q3T7W21DStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc


section LiftConn

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinTriple_liftFam (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hl : HasLifts Φ)
    (hex : ExactSylow Φ) (htt : TwinTriple Φ) : TwinTriple (liftFam Φ) := by
  obtain ⟨K, hK, K', hK'tw, hne, J, hJK, hJK'⟩ := htt
  obtain ⟨hK'Φ, z, hzK, hzK'⟩ := hK'tw
  have hJΦ : J ∈ Φ := hJK.1
  obtain ⟨LK, uK, hLK⟩ := hl K hK
  obtain ⟨LK', uK', hLK'⟩ := hl K' hK'Φ
  obtain ⟨LJ, uJ, hLJ⟩ := hl J hJΦ
  have hMK := satU_mem_liftFam hK hLK
  have hMK' := satU_mem_liftFam hK'Φ hLK'
  have hMJ := satU_mem_liftFam hJΦ hLJ
  have hKM := hLK.le_sat
  have hK'M := hLK'.le_sat
  have hJM := hLJ.le_sat
  refine ⟨_, hMK, _, ⟨hMK', z, isUniqueInvolution_liftFam_of_le hMK hzK hKM,
    isUniqueInvolution_liftFam_of_le hMK' hzK' hK'M⟩, ?_,
    satU (.sl2 3 1) LJ uJ, ?_, ?_⟩
  · intro h
    apply hne
    exact hex.core_unique hΩ h2 hMK hK'Φ hK (h ▸ hK'M) hKM
  · exact (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hMK hK hKM hMJ hJΦ hJM).mpr hJK
  · exact (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hMK' hK'Φ hK'M hMJ hJΦ hJM).mpr hJK'

theorem dstarConnected_of_liftFam (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J)
    (hl : HasLifts Φ) (hex : ExactSylow Φ) (hc : T3.DStarConnected (liftFam Φ)) :
    T3.DStarConnected Φ := by
  intro K₁ hK₁ K₂ hK₂
  obtain ⟨L₁, u₁, hL₁⟩ := hl K₁ hK₁
  obtain ⟨L₂, u₂, hL₂⟩ := hl K₂ hK₂
  have hM₁ := satU_mem_liftFam hK₁ hL₁
  have hM₂ := satU_mem_liftFam hK₂ hL₂
  have key : ∀ M ∈ dstarComp (liftFam Φ) (satU (.sl2 3 1) L₁ u₁),
      M ∈ liftFam Φ ∧ ∃ J ∈ Φ, J ≤ M ∧ J ∈ dstarComp Φ K₁ := by
    intro M hM
    induction hM with
    | refl => exact ⟨hM₁, K₁, hK₁, hL₁.le_sat, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      rename_i b c
      obtain ⟨hb, J, hJ, hJb, hJc⟩ := ih
      obtain ⟨J', hJ', hJ'c⟩ := exists_core_of_mem_liftFam hbc.1
      refine ⟨hbc.1, J', hJ', hJ'c, hJc.tail ⟨hJ', ?_⟩⟩
      rcases hbc.2 with h | h
      · exact Or.inl ((hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hb hJ hJb hbc.1 hJ' hJ'c).mp h)
      · exact Or.inr ((hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hbc.1 hJ' hJ'c hb hJ hJb).mp h)
  obtain ⟨-, J, hJ, hJM, hJd⟩ := key _ (hc _ hM₁ _ hM₂)
  have : J = K₂ := hex.core_unique hΩ h2 hM₂ hJ hK₂ hJM hL₂.le_sat
  rwa [this] at hJd

theorem dstarConnected_of_lifts {n : ℕ} (hcit : CIT3Below n) (hlt : Nat.card X < n)
    (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hl : HasLifts Φ) (hex : ExactSylow Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hA : ∀ J ∈ Φ, AEmpty Φ J)
    (htt : TwinTriple Φ) : T3.DStarConnected Φ := by
  obtain ⟨K₀, hK₀, -⟩ := id htt
  have hne : Φ.Nonempty := ⟨K₀, hK₀⟩
  obtain ⟨L₀, u₀, hL₀⟩ := hl K₀ hK₀
  have hM₀ := satU_mem_liftFam hK₀ hL₀
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam Φ) := hypOmegaModU_liftFam hΩ.conjInvariant
  have hgenΛ : omegaGen (liftFam Φ) = ⊤ :=
    (inClass3_liftFam hΩ.conjInvariant hne hl hgen).generated
  have htransΛ := liftFam_trans hΩ hM₀ hL₀.le_sat (fun J' hJ' => htrans K₀ hK₀ J' hJ')
  have hS : Q3T7.TransSect3 (liftFam Φ) :=
    ⟨hΛ, hO, hgenΛ, fun K hK L hL => by
      obtain ⟨g, hg⟩ := htransΛ K hK
      obtain ⟨g', hg'⟩ := htransΛ L hL
      exact ⟨g' * g⁻¹, by rw [conjSub_mul, ← hg, conjSub_inv_conjSub, hg']⟩,
      ExactSylow.aEmpty_liftFam hΩ h2 hl hex hA⟩
  obtain ⟨D, hD⟩ := Q3T7.exists_omegaLieU_sect
    ((Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit) hlt hΛ hO hgenΛ
    hS.trans ⟨_, hM₀⟩
  exact dstarConnected_of_liftFam hΩ h2 hl hex
    (Q3T7.dstarConnected_of_twinTriple3 hS D hD (twinTriple_liftFam hΩ h2 hl hex htt))

end LiftConn

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
