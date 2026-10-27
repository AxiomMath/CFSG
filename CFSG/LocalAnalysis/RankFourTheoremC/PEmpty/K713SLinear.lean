module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearHigher
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearTwo

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter

theorem outLift_projectiveSL_ge_three {ℓ n : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {K : Type}
    [Field K] [Finite K] (hn : 3 ≤ n) (hdiag : ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1)) :
    OutLift ℓ (projectiveSL n K) := by
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, hEnorm, -, hcyc, -, hindex, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  haveI : (linearAutGroup n K).Normal := GL83.I713.normal_of_subgroupOf_top hgen hDnorm
  rw [hgen, ← Subgroup.relIndex, Subgroup.relIndex_top_right] at hindex
  have hDFE : linearAutGroup n K ⊔ (fieldAut n K).range = semilinearAutGroup n K := by
    rw [semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range,
      Subgroup.closure_eq]
  refine outLift_of_chain hℓ (D := linearAutGroup n K) (F := (fieldAut n K).range) hID ?_ ?_ ?_
  · rw [eq_bot_iff]
    rintro x ⟨⟨σ, rfl⟩, hxD⟩
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hxD
    have h1 : conjAut n K A⁻¹ * fieldAut n K σ = 1 := by rw [map_inv, hA, inv_mul_cancel]
    rw [(eq_one_of_conjAut_mul_fieldAut_eq_one hn _ σ h1).1, map_one]
    exact Subgroup.one_mem _
  · exact fun h => hdiag (h.trans
      (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (by omega : 1 ≤ n)))
  · rw [hDFE]
    intro h
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h
    have := hℓ.two_le
    omega

theorem outLift_coordinateG {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (K : Type) [Field K] [Finite K]
    [Finite (coordinateG K)] : OutLift ℓ (coordinateG K) := by
  let ι := semilinearEquivCoordinateE K
  let Ψ : PGammaL2 K ≃* MulAut (coordinateG K) := ι.trans (coordinateConjugationEquiv K)
  set D : Subgroup (MulAut (coordinateG K)) :=
    ((coordinateD K).subgroupOf (coordinateE K)).map (coordinateConjugation K) with hD
  have hDeq : D = (pGammaL2PGLRange K).map Ψ.toMonoidHom := by
    rw [hD, ← semilinearPGLRange_map K, Subgroup.map_map]
    rfl
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner (coordinateG K) =
      (pGammaL2PSLRange K).map Ψ.toMonoidHom := by
    rw [← coordinateConjugation_G_image K, ← semilinearPSLRange_map K, Subgroup.map_map]
    rfl
  have hDn : D.Normal := by
    rw [hDeq]
    exact (inferInstance : (pGammaL2PGLRange K).Normal).map Ψ.toMonoidHom Ψ.surjective
  have hPSL_le : pGammaL2PSLRange K ≤ pGammaL2PGLRange K := by
    rintro x ⟨y, rfl⟩
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, rfl⟩
  have hID : CFSG.ComponentClassification.OuterAutomorphisms.inner (coordinateG K) ≤ D := by
    rw [hinner, hDeq]
    exact Subgroup.map_mono hPSL_le
  set F : Subgroup (MulAut (coordinateG K)) :=
    (Ψ.toMonoidHom.comp (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K)).range with hF
  have hFD : F ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨σ, rfl⟩, hxD⟩
    rw [hDeq] at hxD
    obtain ⟨y, hy, hyx⟩ := hxD
    have hyσ : y = SemidirectProduct.inr σ := Ψ.injective hyx
    obtain ⟨g, hg⟩ := hy
    have h1 : (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K))
        (SemidirectProduct.inl g) = 1 := SemidirectProduct.rightHom_inl g
    have h2 : (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K))
        (SemidirectProduct.inr σ) = σ := SemidirectProduct.rightHom_inr σ
    have hσ : σ = 1 := by rw [← h2, ← hyσ, ← hg, h1]
    rw [hσ]
    simp
  have htop : D ⊔ F = ⊤ := by
    refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective α
    have hx : Ψ x = Ψ (SemidirectProduct.inl x.left) * Ψ (SemidirectProduct.inr x.right) := by
      rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right]
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [hDeq]
      exact ⟨_, ⟨x.left, rfl⟩, rfl⟩
    · exact ⟨x.right, rfl⟩
  have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner (coordinateG K)).relIndex D ∣
      2 := by
    rw [← coordinateConjugation_G_image K, hD,
      Subgroup.relIndex_map_map_of_injective _ _ (coordinateConjugation_injective K),
      Subgroup.relIndex_subgroupOf (coordinateD_le_E K)]
    exact GL83.I713.relIndex_coordinateG_D_dvd_two K
  haveI := hDn
  have h2 : ¬ ℓ ∣ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
  exact outLift_of_chain hℓ (D := D) (F := F) hID hFD (fun h => h2 (h.trans hrel))
    (by rw [htop, Subgroup.index_top]; exact hℓ.not_dvd_one)

theorem liftClause_classical_PSL {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .PSL n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, -, ⟨eT⟩⟩ := h
  let e' : S ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        n K))
  haveI : Finite (LinearFlag.projectiveSL n K) := Finite.of_equiv S e'.toEquiv
  refine OutLift.of_mulEquiv e' ?_
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · let eT₂ : LinearFlag.projectiveSL 2 K ≃* coordinateG K :=
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 2 K)).trans
        (pslEquivCoordinateG K)
    haveI : Finite (coordinateG K) := Finite.of_equiv _ eT₂.toEquiv
    exact OutLift.of_mulEquiv eT₂ (outLift_coordinateG hℓ hℓ2 K)
  · refine outLift_projectiveSL_ge_three hℓ hℓ2 hn3 fun hpd => ?_
    have h2 := GL83.I713.two_le_pRank_projectiveSL_of_dvd hn3 hℓ hℓ2 hpd
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e'.symm] at h2
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
