module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidTypeANT
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidTypeBW
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualFR
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

section Conj

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem isometryConjugationHom_mem_image (a : matrixIsometries (coordinateQuadPlus n K)) :
    isometryConjugationHom _ a ∈ matrixProjectiveImage (coordinateQuadPlus n K) :=
  ⟨_, rfl⟩

theorem spCoreReadE_conj [CharP K 2]
    {fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K)}
    {s : matrixIsometries (coordinateQuadPlus n K)}
    (h : SpCoreReadE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))))
    (a : matrixIsometries (coordinateQuadPlus n K)) :
    SpCoreReadE (matrixProjectiveImage (coordinateQuadPlus n K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ (a * s * a⁻¹)))) := by
  rw [isometryCore_conj]
  exact coreReadE_map fp h (isometryConjugationHom_mem_image a)

end Conj

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spCoreReadE_plusFour {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus 4 K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus 4 K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (s : matrixIsometries (coordinateQuadPlus 4 K))
    (hs : orderOf (isometryConjugationHom _ s) = 2)
    (hr : 2 ≤ (((s : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) - 1).rank) :
    SpCoreReadE (matrixProjectiveImage (coordinateQuadPlus 4 K)) fp
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  have hss : s * s = 1 := mul_self_eq_one_of_orderOf_plus (by norm_num) hs
  rw [matrixRank_sub_one_eq_finrank_sNil] at hr
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  have hℓn := finrank_range_sNil_le (congrArg Subtype.val hss)
  by_cases hQW : ∀ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus 4 K w = 0
  ·
    obtain ⟨r, hr'⟩ := even_finrank_range_sNil_of_typeA hreg.1 hss hQW
    have h2r : 2 * r ≤ 4 := by omega
    set P : LowPairing 4 (2 * r) := LowPairing.std h2r
    have hdim₀ : finrank K (LinearMap.range (sNil (lowRep (K := K) P).val)) = 2 * r := by
      rw [sNil_lowRep, range_lowNil, finrank_lowSpan h2r]
    have hA₀ : ∀ w ∈ LinearMap.range (sNil (lowRep (K := K) P).val),
        coordinateQuadPlus 4 K w = 0 := by
      rw [sNil_lowRep, range_lowNil]
      exact fun w hw => coordinateQuadPlus_lowSpan hw
    obtain ⟨a, ha⟩ := exists_conj_eq_of_typeA hreg.1 hss (lowRep_mul_self P) hQW hA₀
      (by rw [hdim₀]; omega) (by rw [hdim₀]; omega)
    have hdata : SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus 4 K)) fp
        (typeACore K P) := by
      rcases (show r = 1 ∨ r = 2 by omega) with h1 | h2
      · exact spLeviDataE_lowRep_nSubTwo (by norm_num) hq4 fp hfp P (by omega)
      · exact spLeviDataE_lowRep_of_top (by norm_num) hq4 fp hfp P (Or.inl (by omega))
    rw [ha]
    exact spCoreReadE_conj (spCoreReadE_of_spLeviDataE _ fp hK hq4 hdata) a
  ·
    have hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus 4 K w ≠ 0 := by
      simpa only [not_forall, exists_prop] using hQW
    refine spCoreReadE_of_spLeviDataE _ fp hK hq4 ?_
    rcases (show finrank K (LinearMap.range (sNil s.val)) = 2 ∨
        3 ≤ finrank K (LinearMap.range (sNil s.val)) by omega) with h2 | h3
    · exact spLeviDataE_typeC_two (by norm_num) hq4 fp hfp s hss h2 hW
    · have hB := hreg.1
      have hadj := polar_sNil_left s hss
      have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
      obtain ⟨z, hz⟩ := exists_wallDual (sNil s.val) hadj hNN hB
      rcases quad_wallDual (sNil s.val) hz (polar_sNil_self s) with h0 | h1
      · obtain ⟨w₁, hw₁, hQw₁⟩ := exists_mem_range_quad_eq_one hW
        obtain ⟨zy, rfl⟩ := hw₁
        have heven := even_finrank_range_of_zero (sNil s.val) hadj hNN hz (polar_sNil_self s) h0
          hQw₁ hB
        have hℓ4 : 4 ≤ finrank K (LinearMap.range (sNil s.val)) := by
          obtain ⟨k, hk⟩ := heven
          omega
        exact spLeviDataE_typeC (by norm_num) hq4 fp hfp s hss hW hℓ4 hz h0 hQw₁
      · exact spLeviDataE_typeB (by norm_num) hq4 fp hfp s hss hW h3 hz h1

theorem plusFourHigherRankCoresRigidE {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    PlusFourHigherRankCoresRigidE K hK := by
  intro s₁ s₂ h₁ h₂ hr₁ hr₂
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hfp := plusImageFieldPart_kappa (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    (show 3 ≤ 4 by norm_num)
  exact fieldRigidInOfE_of_spCoreReadE _ _ (spCoreReadE_plusFour hK hq4 _ hfp s₁ h₁ hr₁)
    (spCoreReadE_plusFour hK hq4 _ hfp s₂ h₂ hr₂)

end Four

theorem omegaPlusFourResidualInput : OmegaPlusFourResidualInput :=
  omegaPlusFourResidualInput_of_higherRankCoresRigidE fun _ _ _ _ _ hK hf2 _ =>
    plusFourHigherRankCoresRigidE hK hf2

end CFSG.SeitzReduction.OmegaPilot
