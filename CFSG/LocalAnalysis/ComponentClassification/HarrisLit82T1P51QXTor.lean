module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToralRigid

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootDiagUnit_of_commute_kernelRoots
    [Finite K] (hK5 : 5 ≤ Nat.card K) {c : Fin τ.rank → Kˣ}
    (hW : ∀ w ∈ rootCharStabilizer c, (∀ β ∈ posRoots (rootCharKernel c), w • β = β) → w = 1)
    {g : ModGL τ K} (hg : g ∈ toralCentralizer τ K c)
    (hcomm : ∀ β ∈ rootCharKernel c, ∀ t : K, g * pinnedX τ K β t = pinnedX τ K β t * g) :
    ∃ l : Fin τ.rank → Kˣ, g = rootDiagUnit τ l := by
  classical
  have hgG : g ∈ adjointGroup τ K := (Subgroup.mem_inf.1 hg).1
  obtain ⟨l₁, hl₁⟩ := exists_unit_sq_ne_one hK5
  have hT : ∀ β : Fin τ.rank → ℤ, ∃ a' : Fin τ.rank → Kˣ, IsRoot τ β →
      rootTorusSL2 τ K β l₁ = rootDiagUnit τ a' ∧ rootChar a' β = l₁ ^ 2 := by
    intro β
    by_cases hβ : IsRoot τ β
    · obtain ⟨a', h1, h2⟩ := exists_rootTorusSL2_eq_rootDiagUnit (K := K) hβ l₁
      exact ⟨a', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose A hA using hT
  have hgT : ∀ β ∈ rootCharKernel c, g ∈ toralCentralizer τ K (A β) := by
    intro β hβ
    have h1 := commute_rootSL2_of_commute hβ.1 (hcomm β hβ)
      (hcomm (-β) (neg_mem_rootCharKernel hβ)) (HSL l₁)
    change g * rootTorusSL2 τ K β l₁ = rootTorusSL2 τ K β l₁ * g at h1
    rw [(hA β hβ.1).1] at h1
    exact Subgroup.mem_inf.2 ⟨hgG, Subgroup.mem_centralizer_singleton_iff.2 h1⟩
  obtain ⟨hfac, -, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K c
  obtain ⟨w, hwc, h₀, hh₀, u, hu, v, hv, hgf⟩ := hfac g hg
  have hu' : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hv' : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hparts := fun β (hβ : β ∈ rootCharKernel c) =>
    conj_eq_of_mem_toralCentralizer_bruhat (A β) (hgT β hβ) hh₀ hu' hv' hgf
  have hu1 : u = 1 := eq_one_of_conj_rootDiagUnit_eq
    (S := rootCharKernel c ∩ {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hα.2)
    (closedRoots_inter closedRoots_pos) hu A (fun β hβ => (hparts β hβ.1).1)
    (fun β hβ => by rw [(hA β hβ.1.1).2]; exact hl₁)
  have hv1 : v = 1 := eq_one_of_conj_rootDiagUnit_eq
    (S := rootCharKernel c ∩ inversionSet w) (fun α hα => inversionSet_pos hα.2)
    (closedRoots_inter (closedRoots_inversionSet w)) hv A (fun β hβ => (hparts β hβ.1).2)
    (fun β hβ => by rw [(hA β hβ.1.1).2]; exact hl₁)
  rw [hu1, hv1, mul_one, mul_one] at hgf
  have hwfix : ∀ β ∈ posRoots (rootCharKernel c), w • β = β := by
    intro β hβ
    have hβr : IsRoot τ β := hβ.1.1
    have h1 : g * pinnedX τ K β 1 * g⁻¹ = pinnedX τ K β 1 := by
      rw [hcomm β hβ.1 1, mul_inv_cancel_right]
    have h2 : g * pinnedX τ K β 1 * g⁻¹ ∈ rootSubgroup τ K (w • β) := by
      rw [hgf]
      have e : h₀ * canonicalRep (coxeterSystem τ) K w * pinnedX τ K β 1 *
          (h₀ * canonicalRep (coxeterSystem τ) K w)⁻¹ =
          h₀ * (canonicalRep (coxeterSystem τ) K w * pinnedX τ K β 1 *
            (canonicalRep (coxeterSystem τ) K w)⁻¹) * h₀⁻¹ := by group
      rw [e]
      have h3 : canonicalRep (coxeterSystem τ) K w * pinnedX τ K β 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ rootSubgroup τ K (w • β) := by
        rw [← (canonical_weyl_root_transport τ K).2.1 w β hβr]
        exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
      exact (Subgroup.mem_normalizer_iff.1
        (torusGroup_le_normalizer_rootSubgroup (IsRoot.smul hβr w) hh₀) _).1 h3
    rw [h1] at h2
    obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 h2
    exact eq_of_pinnedX_eq_pinnedX_of_pos' (IsRoot.smul hβr w) hβr hβ.2 one_ne_zero hc'
  rw [hW w hwc hwfix, canonicalRep_one, mul_one] at hgf
  obtain ⟨l₀, hl₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh₀
  exact ⟨l₀, hgf.trans hl₀⟩

theorem weyl_eq_one_of_fix_posKernel
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hK2 : ringChar K ≠ 2)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1) :
    ∀ w ∈ rootCharStabilizer c, (∀ β ∈ posRoots (rootCharKernel c), w • β = β) → w = 1 := by
  intro w hwc hwfix
  have hkerχ : rootCharKernel c = kernelRoots (maskChar (signTupleBits c)) :=
    rootCharKernel_eq_kernelRoots hK2 hc
  have hwK : w ∈ kernelPosStabilizer (maskChar (signTupleBits c)) := by
    refine ⟨(mem_rootCharStabilizer_iff hK2 hc).1 hwc, ?_⟩
    rw [← hkerχ]
    calc (w • ·) '' posRoots (rootCharKernel c) = id '' posRoots (rootCharKernel c) :=
          Set.image_congr fun β hβ => hwfix β hβ
      _ = posRoots (rootCharKernel c) := Set.image_id _
  obtain ⟨-, -, -, -, -, -, hcard1, -, -⟩ :=
    sign_kernel_positive_Weyl_component_representatives τ (maskChar (signTupleBits c))
  have hsub : Subsingleton (kernelPosStabilizer (maskChar (signTupleBits c))) :=
    (Nat.card_eq_one_iff_unique.1 (hcard1 hτ)).1
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨w, hwK⟩ : kernelPosStabilizer (maskChar (signTupleBits c))) 1)

theorem single_eq_smul_single (j : Fin τ.rank) (n : ℤ) :
    (Pi.single j n : Fin τ.rank → ℤ) = n • Pi.single j 1 := by
  ext k
  by_cases h : k = j
  · subst h
    simp
  · simp [h]

theorem weyl_eq_one_of_fix_single
    {i : Fin τ.rank} {w : WeylGroup τ}
    (hj : ∀ j, j ≠ i → w • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1)
    {β : Fin τ.rank → ℤ} (hβ : w • β = β) (hβi : β i ≠ 0) : w = 1 := by
  classical
  have hdec : ∀ v : Fin τ.rank → ℤ,
      w • v = ∑ j, v j • (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [single_eq_smul_single j (v j), smul_comm]
  have hsum : ∀ v : Fin τ.rank → ℤ, ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) = v := by
    intro v
    conv_rhs => rw [← Finset.univ_sum_single v]
    exact Finset.sum_congr rfl fun j _ => (single_eq_smul_single j (v j)).symm
  have hei : w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1 := by
    have h3 : ∑ j, β j • (w • (Pi.single j 1 : Fin τ.rank → ℤ) - Pi.single j 1) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← hdec β, hβ, hsum β, sub_self]
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hj j hji, sub_self, smul_zero])
      (fun h => absurd (Finset.mem_univ i) h)] at h3
    rcases smul_eq_zero.1 h3 with h | h
    · exact absurd h hβi
    · exact sub_eq_zero.1 h
  refine ext_single fun j => ?_
  rw [one_smul]
  by_cases hji : j = i
  · rw [hji]
    exact hei
  · exact hj j hji

theorem weyl_eq_one_of_fix_posKernel_single
    {c : Fin τ.rank → Kˣ} {i : Fin τ.rank}
    (hci : ∀ j, j ≠ i → c j = 1) {β : Fin τ.rank → ℤ} (hβ : β ∈ posRoots (rootCharKernel c))
    (hβi : β i ≠ 0) :
    ∀ w ∈ rootCharStabilizer c, (∀ γ ∈ posRoots (rootCharKernel c), w • γ = γ) → w = 1 := by
  intro w _ hfix
  refine weyl_eq_one_of_fix_single (i := i) (fun j hj => hfix _ ⟨⟨isRoot_single τ j, ?_⟩, ?_⟩)
    (hfix β hβ) hβi
  · have h := rootChar_nsmul_single c j 1
    rw [one_smul, pow_one] at h
    rw [h, hci j hj]
  · rw [height_single]
    exact one_pos

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
