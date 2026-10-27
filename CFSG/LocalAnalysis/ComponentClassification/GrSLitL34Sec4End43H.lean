module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43W
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowTwoIn_le' {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup G, IsSylowTwoIn T H ∧ Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, ⟨map_subtype_le _, P, ?_⟩, ?_⟩
  · exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  · intro q hq
    exact ⟨⟨q, hQH hq⟩, hP (mem_subgroupOf.mpr hq), rfl⟩

theorem three_le_pRank_of_held
    {K : Subgroup G}
    (e : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup G}
    (hT : IsSylowTwoIn T (normalizer (K : Set G))) {s : G} (hs : s ∈ T) (hss : s * s = 1) :
    3 ≤ pRank 2 ↥(T ⊓ centralizer ({s} : Set G)) := by
  have hT2 : IsPGroup 2 ↥(T ⊓ K) := hT.isPGroup.to_le inf_le_left
  obtain ⟨E, hET, hTE, hEe, hE64⟩ :=
    exists_elem_sixtyFour e h64 inf_le_right hT2 (card_inf_eq_1024 e hT)
  by_cases hsLK : s ∈ K ⊔ coreActionKernel K
  · have hsTP := inf_sup_coreActionKernel_le e hT (mem_inf.mpr ⟨hs, hsLK⟩)
    have hPT : T ⊓ coreActionKernel K ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      (inf_le_left : T ⊓ coreActionKernel K ≤ T).trans (le_normalizer_inf_left hT.1)
    have hsset : s ∈ ((T ⊓ K : Subgroup G) : Set G) * ((T ⊓ coreActionKernel K :
        Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPT]
      exact hsTP
    obtain ⟨t', ht', p', hp', rfl⟩ := hsset
    have hcomm := commute_inf_left_inf_kernel hT
    have ht'2 : t' * t' = 1 := by
      have h1 : t' * t' = (t' * p') * (t' * p') * (p' * p')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc t' * t' * (p' * p') = t' * (t' * p') * p' := by group
          _ = t' * (p' * t') * p' := by rw [hcomm t' ht' p' hp']
          _ = t' * p' * (t' * p') := by group
      have h2 : t' * t' ∈ (T ⊓ K) ⊓ (T ⊓ coreActionKernel K) := by
        refine mem_inf.mpr ⟨mul_mem ht' ht', ?_⟩
        rw [h1, hss, one_mul]
        exact inv_mem (mul_mem hp' hp')
      rw [inf_left_inf_kernel_eq_bot e hT, mem_bot] at h2
      exact h2
    have hc := card_le_card_inf_centralizer_sq hEe (hTE ht') ht'2
    rw [hE64] at hc
    have h8 : 8 ≤ Nat.card ↥(E ⊓ centralizer ({t'} : Set G)) :=
      (le_card_of_le_card_sq (hEe.isPGroup.to_le inf_le_left)).2 (by omega)
    refine three_le_pRank_of_le (hEe.mono inf_le_left) h8 fun f hf => ?_
    obtain ⟨hfE, hft⟩ := mem_inf.mp hf
    refine mem_inf.mpr ⟨(mem_inf.mp (hET hfE)).1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := mem_centralizer_singleton_iff.mp hft
    have h2 := hcomm f (hET hfE) p' hp'
    calc f * (t' * p') = f * t' * p' := by group
      _ = t' * f * p' := by rw [h1]
      _ = t' * (f * p') := by group
      _ = t' * (p' * f) := by rw [h2]
      _ = t' * p' * f := by group
  · obtain ⟨F, hFT, hFs, -, hFe, hF8⟩ := exists_outer_eight e hOut inf_le_right hT2
      (card_inf_eq_1024 e hT) (hT.1 hs) (le_normalizer_inf_left hT.1 hs) hsLK
      (by rw [hss]; exact one_mem _) (one_mem _) (mul_one 1) (by group)
    exact three_le_pRank_of_le hFe (by omega) (le_inf (hFT.trans inf_le_left) hFs)

theorem exists_mem_normalizer_of_extremal {W T : Subgroup G}
    (hWT : ∀ F : Subgroup G, F ≤ T → IsAbelianTwoOfRank 3 F → wGroup F = W) {x₀ y k : G}
    (hx₀ : IsExtremalIn T x₀) (hy : y = k⁻¹ * x₀ * k)
    (hrank : 3 ≤ pRank 2 ↥(T ⊓ centralizer ({y} : Set G))) :
    ∃ h ∈ normalizer (W : Set G), y = h⁻¹ * x₀ * h := by
  obtain ⟨F, hFC, hF, hF8⟩ := exists_isElemTwo_of_three_le_pRank hrank
  have hFT : F ≤ T := hFC.trans inf_le_left
  have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank hF8
  have hVC : F.map (MulAut.conj k).toMonoidHom ≤ centralizer ({x₀} : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    have hfy := mem_centralizer_singleton_iff.mp (mem_inf.mp (hFC hf)).2
    rw [mem_centralizer_singleton_iff]
    show k * f * k⁻¹ * x₀ = x₀ * (k * f * k⁻¹)
    have hx : x₀ = k * y * k⁻¹ := by rw [hy]; group
    rw [hx, show k * f * k⁻¹ * (k * y * k⁻¹) = k * (f * y) * k⁻¹ by group, hfy]
    group
  obtain ⟨-, P, hP⟩ := hx₀
  have hSylC : IsSylowTwoIn (T ⊓ centralizer ({x₀} : Set G)) (centralizer ({x₀} : Set G)) :=
    ⟨inf_le_right, P, hP⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_isSylowTwoIn hSylC hVC (hF.isPGroup.map _)
  set h : G := k⁻¹ * c with hhdef
  have hFhT : F.map (MulAut.conj h⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 := (mem_inf.mp (hc _ (mem_map_of_mem (MulAut.conj k).toMonoidHom hf))).1
    convert h1 using 1
    simp only [hhdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_inv_rev]
    group
  have hhW : h⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_of_map_le' hWT hFT hFr hFhT
  refine ⟨h⁻¹, hhW, ?_⟩
  have hcx : c⁻¹ * x₀ * c = x₀ := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hcC, ← mul_assoc, inv_mul_cancel,
      one_mul]
  calc y = k⁻¹ * x₀ * k := hy
    _ = k⁻¹ * (c * (c⁻¹ * x₀ * c) * c⁻¹) * k := by group
    _ = (h⁻¹)⁻¹ * x₀ * h⁻¹ := by rw [hcx, hhdef]; group

end CFSG.ComponentClassification.GrSLit.GrS4
