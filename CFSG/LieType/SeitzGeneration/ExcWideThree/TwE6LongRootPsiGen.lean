module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiAdd
public import CFSG.LieType.Chevalley.E6PinnedAdjoint

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

variable {K : Type} [Field K]

theorem Psi.isRoot_of_mem_degOneRoots
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ degOneRoots) : IsRoot TwistTag.E6.tag δ :=
  mem_rootFinset.1 (Finset.mem_filter.1 hδ).1

set_option maxHeartbeats 400000 in
theorem psi_pinnedX_degOne
    (K : Type) [Field K] {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ degOneRoots) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧ ∀ c : K,
      psi K (pinnedX TwistTag.E6.tag K δ c) = (s * c) • Pi.single (⟨δ, hδ⟩ : Dr) (1 : K) := by
  have hrt : IsRoot TwistTag.E6.tag (-e6HighestRoot + δ) := by
    rw [neg_add_eq_sub]
    exact isRoot_sub_highest ⟨δ, hδ⟩
  obtain ⟨s, hs, hX⟩ := E6PinnedAdjoint.pinnedX_rootVec_of_add_root (K := K)
    (isRoot_of_mem_degOneRoots hδ) isRoot_neg_highest hrt
  refine ⟨s, hs, fun c => ?_⟩
  ext γ
  have h1 : (-e6HighestRoot : Fin TwistTag.E6.tag.rank → ℤ) ≠ γ.1 - e6HighestRoot := by
    intro h
    have := congrFun h (e6Idx 1)
    simp only [Pi.sub_apply, Pi.neg_apply, degOne_apply γ.2] at this
    linarith
  have h2 : (-e6HighestRoot + δ = γ.1 - e6HighestRoot) ↔ γ = ⟨δ, hδ⟩ := by
    rw [neg_add_eq_sub, sub_left_inj, Subtype.ext_iff]
    exact eq_comm
  rw [psi_apply]
  change ((pinnedX TwistTag.E6.tag K δ c : Module.End K (RootModule TwistTag.E6.tag K))
    (rootVec TwistTag.E6.tag K (-e6HighestRoot))) (lab γ) = _
  rw [hX c, Finsupp.add_apply, Finsupp.smul_apply, rootVec_apply_lab, rootVec_apply_lab,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp only [h1, h2, if_false]
  split_ifs <;> simp

theorem psi_pinnedX_highest (c : K) :
    psi K (pinnedX TwistTag.E6.tag K e6HighestRoot c) = 0 := by
  ext γ
  rw [psi_apply, v0_eq, Pi.zero_apply]
  by_contra hne
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift (R := K) isRoot_e6HighestRoot c (lab γ) lab0 (by
    rw [Finsupp.single_apply, if_neg (lab_ne_lab0 γ).symm]
    with_reducible exact hne)
  have h2 := congrFun hw (e6Idx 1)
  have h3 : lblDeg (lab γ) = lblDeg lab0 + k * e6HighestRoot (e6Idx 1) := by
    simpa [lblDeg] using h2
  rw [lblDeg_lab, lblDeg_lab0, e6HighestRoot_idx_one] at h3
  omega

section Prod

noncomputable def Psi.sgnD (K : Type) [Field K] (γ : Dr) : K :=
  Classical.choose (psi_pinnedX_degOne K γ.2)

theorem Psi.sgnD_spec (γ : Dr) :
    (sgnD K γ = 1 ∨ sgnD K γ = -1) ∧ ∀ c : K,
      psi K (pinnedX TwistTag.E6.tag K γ.1 c) = (sgnD K γ * c) • Pi.single γ (1 : K) :=
  Classical.choose_spec (psi_pinnedX_degOne K γ.2)

noncomputable def Psi.prodD (c : Dr → K) : ModGL TwistTag.E6.tag K :=
  ((Finset.univ : Finset Dr).toList.map fun γ => pinnedX TwistTag.E6.tag K γ.1 (c γ)).prod

theorem Psi.prodD_mem (c : Dr → K) : prodD c ∈ Qbar K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
  exact pinnedX_mem_Qbar (Finset.mem_insert_of_mem γ.2) _

theorem Psi.psi_prodD (c : Dr → K) : psi K (prodD c) = fun γ => sgnD K γ * c γ := by
  classical
  rw [prodD, psi_list_prod, List.map_map]
  · rw [Finset.sum_map_toList]
    funext γ₀
    rw [Finset.sum_congr rfl fun γ _ =>
      show (psi K ∘ fun γ => pinnedX TwistTag.E6.tag K γ.1 (c γ)) γ =
        (sgnD K γ * c γ) • Pi.single γ (1 : K) from (sgnD_spec γ).2 (c γ)]
    simp [Finset.sum_apply, Pi.single_apply]
  · intro x hx
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_Qbar (Finset.mem_insert_of_mem γ.2) _

theorem Psi.prodD_zero : prodD (fun _ : Dr => (0 : K)) = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
  exact pinnedX_zero _ _ _

theorem Psi.Qbar_roots_closed :
    ∀ α ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0),
      ∀ β ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0), ∀ a b : ℕ,
        1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
          a • α + b • β ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0) := by
  intro α hα β hβ a b ha hb hr
  obtain ⟨-, hαh, hα1⟩ := mem_S_iff.1 (mem_Qbar_roots_iff.1 hα)
  obtain ⟨-, hβh, hβ1⟩ := mem_S_iff.1 (mem_Qbar_roots_iff.1 hβ)
  refine mem_Qbar_roots_iff.2 (mem_S_iff.2 ⟨hr, ?_, ?_⟩)
  · rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

end Prod

section Kernel

theorem ker_psi {z : ModGL TwistTag.E6.tag K} (hz : z ∈ Qbar K) (h : psi K z = 0) :
    z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
  classical
  set L : List (Fin TwistTag.E6.tag.rank → ℤ) :=
    e6HighestRoot :: ((Finset.univ : Finset Dr).toList.map Subtype.val) with hL
  have hnodup : L.Nodup := by
    refine List.nodup_cons.2 ⟨?_, (Finset.nodup_toList _).map Subtype.val_injective⟩
    intro hmem
    obtain ⟨γ, -, hγ⟩ := List.mem_map.1 hmem
    have := congrFun hγ (e6Idx 1)
    rw [degOne_apply γ.2, e6HighestRoot_idx_one] at this
    omega
  have hmem : ∀ α, α ∈ L ↔
      α ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0) := by
    intro α
    rw [mem_Qbar_roots_iff, Finset.mem_insert, hL, List.mem_cons, List.mem_map]
    refine or_congr Iff.rfl ⟨?_, fun hα => ⟨⟨α, hα⟩, by simp, rfl⟩⟩
    rintro ⟨γ, -, rfl⟩
    exact γ.2
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq K (S := parabolicRadicalRoots TwistTag.E6.tag
    (TwistTag.E6.orbitUnion J0)) (fun α hα => (mem_S_iff.1 (mem_Qbar_roots_iff.1 hα)).imp_right
      (·.1)) Qbar_roots_closed hnodup hmem hz
  rw [hL, List.map_cons, List.prod_cons, List.map_map] at hc
  change pinnedX TwistTag.E6.tag K e6HighestRoot (c e6HighestRoot) * prodD (fun γ : Dr => c γ.1) =
    z at hc
  have hXβ : pinnedX TwistTag.E6.tag K e6HighestRoot (c e6HighestRoot) ∈ Qbar K :=
    pinnedX_mem_Qbar (Finset.mem_insert_self _ _) _
  have hpsi : psi K z = fun γ => sgnD K γ * c γ.1 := by
    rw [← hc, psi_mul hXβ (prodD_mem _), psi_pinnedX_highest, zero_add, psi_prodD]
  have hc0 : ∀ γ : Dr, c γ.1 = 0 := by
    intro γ
    have h1 := congrFun (hpsi.symm.trans h) γ
    rcases (sgnD_spec (K := K) γ).1 with h2 | h2 <;> simpa [h2] using h1
  have hP1 : prodD (fun γ : Dr => c γ.1) = 1 := by
    have : (fun γ : Dr => c γ.1) = fun _ => (0 : K) := funext hc0
    rw [this, prodD_zero]
  rw [← hc, hP1, mul_one]
  exact Subgroup.subset_closure ⟨c e6HighestRoot, rfl⟩

theorem psi_eq_zero_imp_mem {z : ModGL TwistTag.E6.tag K} (hz : z ∈ Qbar K) (h : psi K z = 0) :
    z ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
  ker_psi hz h

end Kernel

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
