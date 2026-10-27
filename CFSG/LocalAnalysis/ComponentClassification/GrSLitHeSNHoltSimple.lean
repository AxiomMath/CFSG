module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNFinal
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import Certificates.Certificate43
public import Certificates.Certificate113
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNAlt
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNBender
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem false_of_holtSimple_outcome
    (hMax : MaximalTwoComponentInputHe)
    (hout : (∃ M : Subgroup X, CFSG.IsStronglyEmbedded M) ∨
      ∃ n : ℕ, Odd n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) : False := by
  have : IsSimpleGroup X := h.simple
  obtain ⟨eL⟩ := h.held
  rcases hout with ⟨M, hM⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨A, -, hAe, hA64, -⟩ := h.wGroup_eq
    obtain ⟨V, hVA, hV4⟩ := exists_le_card_four hAe.isPGroup (by omega)
    exact false_of_isStronglyEmbedded hM hV4 (fun v hv => by rw [pow_two]; exact hAe.2 v (hVA hv))
      h.orderOf_eq h.le_centralizer eL
  · exact false_of_mulEquiv_alternatingGroup e h.orderOf_eq h.le_centralizer
      (h.centralizer_le_normalizer hMax) h.isPComponent eL

theorem false_of_le_normalizer_of_mem_holtSimple
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hMult : TBLit.HeldTrivialMultiplier)
    (hGen : HeldFourGroupGeneration) (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hKn : ¬ normalizer (W : Set X) ≤ normalizer (K : Set X)) {T : Subgroup X}
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set X))) (hTN : T ≤ normalizer (K : Set X))
    (haT : a ∈ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := h.simple
  obtain ⟨e₁⟩ := h.heldK
  have hGWB := h.gwTwoBalanced
  obtain ⟨A, hAL, hAe, hA64, hWA⟩ := h.wGroup_eq
  have hT2 := hTsyl.isPGroup
  have h1024 : Nat.card ↥(T ⊓ K) = 1024 := by
    have hTKs : IsSylowTwoIn T (T ⊔ K) :=
      GrS4.isSylowTwoIn_of_le hTsyl le_sup_left (sup_le hTsyl.1 h.le_normalizer)
    exact HeNormal.card_inf_eq_of_normal e₁ le_sup_right (sup_le hTN le_normalizer) hTKs
  have h3 := HeNormal.isThreeConnected_of_normal e₁ h64 hOut hT2 hTN h1024
  have hTsylA : IsSylowTwoIn T (normalizer (wGroup A : Set X)) := by rw [hWA]; exact hTsyl
  obtain ⟨⟨P₀, hP₀⟩, hfus⟩ :=
    sylow_and_fusion_of_threeConnected hGWB hAe (by omega) hTsylA h3
  obtain ⟨m₀, hm₀M, hm₀K⟩ := IsConcreteLE.not_le_iff_exists.mp hKn
  have hK₂M : conjugate K m₀ ≤ normalizer (W : Set X) := conjugate_le_of_mem h.le_normalizer hm₀M
  have hK₂c := isPComponent_conjugate_subgroupOf hm₀M h.isPComponent_K
  have hK₂k : conjugate K m₀ ≤ coreActionKernel K :=
    le_coreActionKernel_of_ne h.le_normalizer hK₂M h.isPComponent_K hK₂c
      fun e => hm₀K (mem_normalizer_of_conjugate_eq e.symm)
  have hev : 2 ∣ Nat.card ↥(conjugate K m₀) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (GrS4.not_odd_card_of_isPComponent hK₂M hK₂c))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjugate K m₀)) 2 hev
  have hy2 : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hTH : IsSylowTwoIn T (normalizer (W : Set X) ⊓ normalizer (K : Set X)) :=
    GrS4.isSylowTwoIn_of_le hTsyl (le_inf hTsyl.1 hTN) inf_le_left
  have hyH : (y : X) ∈ normalizer (W : Set X) ⊓ normalizer (K : Set X) :=
    mem_inf.mpr ⟨hK₂M y.2, (mem_coreActionKernel.mp (hK₂k y.2)).1⟩
  obtain ⟨c, hcH, hcy⟩ := hTH.exists_conj_le (zpowers_le.mpr hyH) (isPGroup_zpowers hy2)
  have hcy' : c * y * c⁻¹ ∈ T ⊓ coreActionKernel K :=
    mem_inf.mpr ⟨hcy _ (mem_zpowers _),
      HeDiag.conj_mem_coreActionKernel_of_mem (mem_inf.mp hcH).2 (hK₂k y.2)⟩
  have hne : T ⊓ coreActionKernel K ≠ ⊥ := by
    intro hb
    rw [hb, mem_bot, mul_inv_eq_one, mul_eq_left] at hcy'
    rw [hcy', orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hTn : T ≤ normalizer ((T ⊓ coreActionKernel K : Subgroup X) : Set X) := by
    intro t ht
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hx).1) (inv_mem ht),
      HeDiag.conj_mem_coreActionKernel_of_mem (hTN ht) (mem_inf.mp hx).2⟩
  obtain ⟨z, hzP, hz2, hzc⟩ := exists_central_involution hT2 inf_le_left hTn hne
  obtain ⟨hzT, hzK⟩ := mem_inf.mp hzP
  obtain ⟨Lz, hLzr, -, hCN, ⟨ez⟩, -, -⟩ :=
    h.exists_target hMax hS hHN h64 hMult hz2 (hzc a haT) hzK
  have hTC : T ≤ centralizer ({z} : Set X) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hTNz : IsSylowTwoIn T (normalizer (Lz : Set X)) :=
    GrS4.isSylowTwoIn_of_le_of_sylow ⟨P₀, hP₀⟩ (hTC.trans hCN)
  have h1024z := card_inf_eq_1024 ez hTNz
  obtain ⟨E, hET, hTE, hEe, hE64⟩ :=
    exists_elem_sixtyFour ez h64 inf_le_right (hT2.to_le inf_le_left) h1024z
  have hTLz : T ⊓ Lz ≠ ⊥ := fun hb => by rw [hb, card_bot] at h1024z; omega
  obtain ⟨z₀, hz₀, hz₀2, hz₀c⟩ := exists_central_involution hT2 (inf_le_left : T ⊓ Lz ≤ T)
    (le_normalizer_inf_left (hTC.trans hCN)) hTLz
  have hNLz : normalizer (Lz : Set X) ≤ normalizer (wGroup E : Set X) :=
    HeldCor32Data.normalizer_L_le (d := ⟨T, E, z₀, z, hTNz, hET, hTE, hEe, hE64, h3, hz₀,
      hz₀2, hz₀c, hzT, hLzr, hz2, hzc⟩) ez hGen hGWB
  have hWE : wGroup E = W := by
    obtain ⟨c, hcM, hcA⟩ :=
      hTsyl.exists_conj_le (hAL.trans (le_normalizer.trans h.normalizer_le)) hAe.isPGroup
    have hA'T : A.map (MulAut.conj c).toMonoidHom ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcA x hx
    have hA'r : IsAbelianTwoOfRank 3 (A.map (MulAut.conj c).toMonoidHom) :=
      (hAe.map_conj c).isAbelianTwoOfRank
        (by rw [card_map_of_injective (MulAut.conj c).injective, hA64]; norm_num)
    have hA'W : wGroup (A.map (MulAut.conj c).toMonoidHom) = W := by
      rw [wGroup_map_conj, hWA]
      exact mem_normalizer_iff_map_conj_eq.mp hcM
    have hEr : IsAbelianTwoOfRank 3 E := hEe.isAbelianTwoOfRank (by rw [hE64]; norm_num)
    rw [wGroup_eq_of_le_threeConnected hGWB h3 hA'T hA'r (hET.trans inf_le_left) hEr, hA'W]
  have hCzM : centralizer ({z} : Set X) ≤ normalizer (W : Set X) := by
    rw [← hWE]
    exact hCN.trans hNLz
  have hzM : z ∈ normalizer (W : Set X) := hTsyl.1 hzT
  have hext : IsExtremalIn T z := by
    obtain ⟨-, P, hP⟩ := GrS4.isSylowTwoIn_of_le_of_sylow ⟨P₀, hP₀⟩ hTC
    exact ⟨hzT, P, by rw [inf_of_le_left hTC]; exact hP⟩
  have key : ∀ g : X, g⁻¹ * z * g ∈ normalizer (W : Set X) → g ∈ normalizer (W : Set X) := by
    intro g hg
    have hgz : orderOf (g⁻¹ * z * g) = 2 := by
      rw [← hz2]
      exact SemiconjBy.orderOf_eq g (show g * (g⁻¹ * z * g) = z * g by group)
    obtain ⟨n, hnM, hny⟩ := hTsyl.exists_conj_le (zpowers_le.mpr hg) (isPGroup_zpowers hgz)
    have hy'T : n * (g⁻¹ * z * g) * n⁻¹ ∈ T := hny _ (mem_zpowers _)
    have hy'2 : n * (g⁻¹ * z * g) * n⁻¹ * (n * (g⁻¹ * z * g) * n⁻¹) = 1 := by
      have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
      calc n * (g⁻¹ * z * g) * n⁻¹ * (n * (g⁻¹ * z * g) * n⁻¹)
          = n * g⁻¹ * (z * z) * g * n⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hrk := HeNormal.three_le_pRank_centralizer_of_sq e₁ h64 hOut hT2 hTN h1024 hy'T
      (by rw [hy'2]; exact one_mem _)
    obtain ⟨m, hmA, hm⟩ := hfus z _ hy'T hext ⟨n * g⁻¹, by group⟩ hrk
    rw [hWA] at hmA
    have hu : m * n * g⁻¹ ∈ centralizer ({z} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc m * n * g⁻¹ * z = m * (n * (g⁻¹ * z * g) * n⁻¹) * (n * g⁻¹) := by group
        _ = m * (m⁻¹ * z * m) * (n * g⁻¹) := by rw [hm]
        _ = z * (m * n * g⁻¹) := by group
    have h1 := mul_mem (inv_mem (mul_mem hmA hnM)) (hCzM hu)
    rw [show (m * n)⁻¹ * (m * n * g⁻¹) = g⁻¹ by group] at h1
    simpa using inv_mem h1
  have hfix : ∃! q : X ⧸ normalizer (W : Set X), z • q = q := by
    refine ⟨((1 : X) : X ⧸ normalizer (W : Set X)), ?_, fun ω' hω' => ?_⟩
    · show z • ((1 : X) : X ⧸ normalizer (W : Set X)) = ((1 : X) : X ⧸ normalizer (W : Set X))
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
      exact inv_mem hzM
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω'
      change z • (g : X ⧸ normalizer (W : Set X)) = (g : X ⧸ normalizer (W : Set X)) at hω'
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul] at hω'
      rw [QuotientGroup.eq, mul_one]
      have hzi : z⁻¹ = z := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz2, pow_orderOf_eq_one]
      have h1 : g⁻¹ * z * g ∈ normalizer (W : Set X) := by
        rw [mul_inv_rev, hzi] at hω'
        simpa [mul_assoc] using hω'
      exact inv_mem (key g h1)
  have hS2 : ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ centralizer ({z} : Set X) :=
    ⟨P₀, by rw [hP₀]; exact hzT, by rw [hP₀]; exact hTC⟩
  exact h.false_of_holtSimple_outcome hMax
    (hHS X h.nonabelian _ h.normalizer_ne_top z hz2 hS2 hfix)

theorem false_of_le_normalizer_holtSimple
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hMult : TBLit.HeldTrivialMultiplier)
    (hGen : HeldFourGroupGeneration) (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hKn : ¬ normalizer (W : Set X) ≤ normalizer (K : Set X)) {T : Subgroup X}
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set X))) (hTN : T ≤ normalizer (K : Set X)) :
    False := by
  have hTH : IsSylowTwoIn T (normalizer (W : Set X) ⊓ normalizer (K : Set X)) :=
    GrS4.isSylowTwoIn_of_le hTsyl (le_inf hTsyl.1 hTN) inf_le_left
  have haH : a ∈ normalizer (W : Set X) ⊓ normalizer (K : Set X) :=
    mem_inf.mpr ⟨h.mem_M hMax, (mem_coreActionKernel.mp (h.mem_kernel hMax)).1⟩
  obtain ⟨c, hcH, hca⟩ := hTH.exists_conj_le (zpowers_le.mpr haH) (isPGroup_zpowers h.orderOf_eq)
  obtain ⟨hcM, hcK⟩ := mem_inf.mp hcH
  refine h.false_of_le_normalizer_of_mem_holtSimple hMax hS hHN h64 hOut hMult hGen hHS hKn
    (isSylowTwoIn_conjugate hTsyl hcM) (fun x hx => ?_) ?_
  · rw [mem_conjugate_iff] at hx
    rw [show x = c⁻¹ * (c * x * c⁻¹) * c by group]
    exact mul_mem (mul_mem (inv_mem hcK) (hTN hx)) hcK
  · rw [mem_conjugate_iff]
    exact hca a (mem_zpowers a)

end Setting

theorem heldSingleNormalStep_of_holtSimple
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hMult : TBLit.HeldTrivialMultiplier)
    (hGen : HeldFourGroupGeneration) (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) :
    HeldSingleNormalStep := by
  have hE : HeldSingleNormalEvenStep := heldSingleNormalEvenStep_of_residue hMax h64 hOut
    (heldSingleNormalResidue_holds hMax hS hHN h64 hOut hMult)
  intro X _ _ L hset S hSyl W hW hWodd hWB hNL K hKM hKc hsupM
  obtain ⟨a, h⟩ := setting_of hS hHN h64 hset hSyl hW hWodd hWB hNL hKM hKc hsupM
  by_contra hKn
  obtain ⟨T, hTsyl, haT, hTK, hTa⟩ := h.exists_sylow hMax
  by_cases hTN : T ≤ normalizer (K : Set X)
  · exact h.false_of_le_normalizer_holtSimple hMax hS hHN h64 hOut hMult hGen hHS hKn hTsyl hTN
  · exact hE X a L W K T h ⟨hTsyl, haT, hTK, hTa, hTN,
      h.inf_coreKernel_eq_bot hMax hS hHN h64 hMult hTsyl.isPGroup hTsyl.1 haT hTN⟩

end CFSG.ComponentClassification.GrSLit.HeSN
