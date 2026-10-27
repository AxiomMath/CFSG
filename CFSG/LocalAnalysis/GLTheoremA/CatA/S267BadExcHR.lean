module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_mulSingle (j : Fin τ.rank) (c : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle j c) v = c ^ (v j) := by
  unfold rootChar
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [Pi.mulSingle_eq_of_ne hij, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

theorem eq_zero_of_zpow_eq_one {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) {n : ℤ} (hn : |n| ≤ 2)
    (h : c ^ n = 1) : n = 0 := by
  rcases abs_le.1 hn with ⟨h1, h2⟩
  have hn' : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl | rfl | rfl
  · exact absurd (by rw [zpow_neg, inv_eq_one] at h; exact_mod_cast h) hc2
  · exact absurd (by rw [zpow_neg, inv_eq_one, zpow_one] at h; exact h) hc1
  · rfl
  · exact absurd (by rw [zpow_one] at h; exact h) hc1
  · exact absurd (by exact_mod_cast h) hc2

theorem rootCharKernel_mulSingle {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2) :
    rootCharKernel (Pi.mulSingle (highNode τ) c) = perpRoots τ := by
  ext γ
  constructor
  · rintro ⟨hγ, h⟩
    rw [rootChar_mulSingle] at h
    exact ⟨hγ, eq_zero_of_zpow_eq_one hc1 hc2 (hk γ hγ) h⟩
  · rintro ⟨hγ, h⟩
    exact ⟨hγ, by rw [rootChar_mulSingle, h, zpow_zero]⟩

theorem perpRoots_subset_rootCharKernel (c : Kˣ) :
    perpRoots τ ⊆ rootCharKernel (Pi.mulSingle (highNode τ) c) := fun _ ⟨hγ, h⟩ =>
  ⟨hγ, by rw [rootChar_mulSingle, h, zpow_zero]⟩

theorem weyl_smul_eq_sum (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _

theorem smul_apply_highNode_eq {c : Kˣ} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθk : highRoot τ (highNode τ) = 2) {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) c)) (v : Fin τ.rank → ℤ) :
    (w • v) (highNode τ) = v (highNode τ) := by
  set j₀ := highNode τ with hj₀
  have hoff : ∀ i, i ≠ j₀ → (w • (Pi.single i 1 : Fin τ.rank → ℤ)) j₀ = 0 := by
    intro i hi
    have h := hw (Pi.single i 1)
    rw [rootChar_mulSingle, rootChar_mulSingle, Pi.single_eq_of_ne' hi, zpow_zero] at h
    exact eq_zero_of_zpow_eq_one hc1 hc2 (hk _ (IsRoot.smul (IsRoot.basis i) w)) h
  set m := (w • (Pi.single j₀ 1 : Fin τ.rank → ℤ)) j₀ with hm
  have hlin : ∀ u : Fin τ.rank → ℤ, (w • u) j₀ = u j₀ * m := by
    intro u
    rw [weyl_smul_eq_sum, Finset.sum_apply, Finset.sum_eq_single j₀]
    · rw [Pi.smul_apply, smul_eq_mul]
    · intro i _ hi
      rw [Pi.smul_apply, hoff i hi, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have hθ := hk _ (IsRoot.smul (isRoot_highRoot τ) w)
  rw [hlin, hθk] at hθ
  have hm0 : m ≠ 0 := by
    intro h0
    have h := hlin (w⁻¹ • (Pi.single j₀ 1 : Fin τ.rank → ℤ))
    rw [smul_inv_smul, h0, mul_zero, Pi.single_eq_same] at h
    exact one_ne_zero h
  have hm1 : m ≠ -1 := by
    intro h1
    have h := hw (Pi.single j₀ 1)
    rw [rootChar_mulSingle, rootChar_mulSingle, Pi.single_eq_same, ← hm, h1, zpow_neg,
      zpow_one] at h
    apply hc2
    rw [sq]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel c
  have hm' : m = 1 := by
    rcases abs_le.1 hθ with ⟨h1, h2⟩
    omega
  rw [hlin, hm', mul_one]

theorem mem_rootCharStabilizer_mulSingle {c : Kˣ} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθk : highRoot τ (highNode τ) = 2) {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) c)) (c' : Kˣ) :
    w ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) c') := fun v => by
  rw [rootChar_mulSingle, rootChar_mulSingle, smul_apply_highNode_eq hc1 hc2 hk hθk hw]

section Centralizer


theorem toralCentralizer_mulSingle_le {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2) (hθk : highRoot τ (highNode τ) = 2) (c' : Kˣ) :
    toralCentralizer τ K (Pi.mulSingle (highNode τ) c) ≤
      toralCentralizer τ K (Pi.mulSingle (highNode τ) c') := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K _).2.2.2]
  refine sup_le (sup_le (torusGroup_le_toralCentralizer _) ?_) ?_
  · rw [rootCharKernel_mulSingle hc1 hc2 hk]
    exact (rootSpan_mono (perpRoots_subset_rootCharKernel c')).trans
      (le_sup_right.trans (toralRootGroup_le _))
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact canonicalRep_mem_toralCentralizer (mem_rootCharStabilizer_mulSingle hc1 hc2 hk hθk hw c')

theorem toralCentralizer_le_normalizer_rootSpan_rootCharKernel (a : Fin τ.rank → Kˣ) :
    toralCentralizer τ K a ≤
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a) : Set (ModGL τ K)) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K _).2.2.2]
  refine sup_le (sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    Subgroup.le_normalizer) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  refine mem_normalizer_of_map_eq ?_
  rw [(canonical_weyl_root_transport τ K).1 w (rootCharKernel a) fun _ hα => hα.1,
    image_rootCharKernel hw]

theorem toralCentralizer_mulSingle_le_normalizer {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2) :
    toralCentralizer τ K (Pi.mulSingle (highNode τ) c) ≤
      Subgroup.normalizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
  have h := toralCentralizer_le_normalizer_rootSpan_rootCharKernel (K := K)
    (Pi.mulSingle (highNode τ) c)
  rwa [rootCharKernel_mulSingle hc1 hc2 hk] at h

theorem rootSpan_perpRoots_le_toralCentralizer (c : Kˣ) :
    rootSpan τ K (perpRoots τ) ≤ toralCentralizer τ K (Pi.mulSingle (highNode τ) c) :=
  (rootSpan_mono (perpRoots_subset_rootCharKernel c)).trans
    (le_sup_right.trans (toralRootGroup_le _))

end Centralizer

theorem mem_rootCharKernel_neg_one (hK : ringChar K ≠ 2)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθ2 : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rootCharKernel (Pi.mulSingle (highNode τ) (-1 : Kˣ))) :
    γ ∈ perpRoots τ ∨ γ = highRoot τ ∨ γ = -highRoot τ := by
  obtain ⟨hr, h⟩ := hγ
  rw [rootChar_mulSingle] at h
  have hne : (-1 : Kˣ) ≠ 1 := fun h1 =>
    hK ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h1))
  rcases abs_le.1 (hk γ hr) with ⟨h1, h2⟩
  have hcases : γ (highNode τ) = -2 ∨ γ (highNode τ) = -1 ∨ γ (highNode τ) = 0 ∨
      γ (highNode τ) = 1 ∨ γ (highNode τ) = 2 := by omega
  rcases hcases with h' | h' | h' | h' | h'
  · right; right
    have h'' : (-γ) (highNode τ) = 2 := by rw [Pi.neg_apply, h']; norm_num
    rw [← hθ2 _ (IsRoot.neg hr) h'', neg_neg]
  · rw [h', zpow_neg_one, inv_neg_one] at h
    exact absurd h hne
  · exact Or.inl ⟨hr, h'⟩
  · rw [h', zpow_one] at h
    exact absurd h hne
  · exact Or.inr (Or.inl (hθ2 γ hr h'))

theorem image_perpRoots_of_mem_rootCharStabilizer_neg_one
    (hK : ringChar K ≠ 2)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθ2 : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ)
    (hθform : ∀ v, CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) v = 0 ↔ v (highNode τ) = 0)
    (hnbr : ∀ i, i ≠ highNode τ → ∃ i', i' ≠ highNode τ ∧ i' ≠ i ∧
      CFSG.LieType.Steinberg.Adjoint.iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i' 1) ≠ 0)
    {w : WeylGroup τ} (hw : w ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) (-1 : Kˣ))) :
    (fun α => w • α) '' perpRoots τ = perpRoots τ := by
  have key : ∀ u : WeylGroup τ, u ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) (-1 : Kˣ)) →
      ∀ γ ∈ perpRoots τ, u • γ ∈ perpRoots τ := by
    intro u hu
    set j₀ := highNode τ with hj₀
    have hker : ∀ γ ∈ rootCharKernel (Pi.mulSingle j₀ (-1 : Kˣ)),
        u • γ ∈ rootCharKernel (Pi.mulSingle j₀ (-1 : Kˣ)) := fun γ hγ => by
      rw [← image_rootCharKernel hu]
      exact ⟨γ, hγ, rfl⟩
    have he : ∀ i, i ≠ j₀ → (Pi.single i 1 : Fin τ.rank → ℤ) ∈ perpRoots τ := fun i hi =>
      ⟨IsRoot.basis i, Pi.single_eq_of_ne' hi 1⟩
    have hsep : ∀ i i', i' ≠ i → ∀ ε ε' : ℤ, (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
        u • (Pi.single i 1 : Fin τ.rank → ℤ) = ε • highRoot τ →
        u • (Pi.single i' 1 : Fin τ.rank → ℤ) = ε' • highRoot τ → False := by
      intro i i' hii' ε ε' hε hε' h h'
      have hθ : ε' • ε • u • (Pi.single i 1 : Fin τ.rank → ℤ) =
          u • (Pi.single i' 1 : Fin τ.rank → ℤ) := by
        rw [h, h', smul_smul, smul_smul]
        congr 1
        rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
      rw [smul_comm ε u, smul_comm ε' u] at hθ
      have h1 := congrFun (smul_left_cancel u hθ) i'
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne hii', smul_zero, smul_zero,
        Pi.single_eq_same] at h1
      exact zero_ne_one h1
    have hoff : ∀ i, i ≠ j₀ → (u • (Pi.single i 1 : Fin τ.rank → ℤ)) j₀ = 0 := by
      intro i hi
      have hpm : ∀ γ ∈ rootCharKernel (Pi.mulSingle j₀ (-1 : Kˣ)), γ ∈ perpRoots τ ∨
          ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ γ = ε • highRoot τ := fun γ hγ => by
        rcases mem_rootCharKernel_neg_one hK hk hθ2 hγ with h | h | h
        · exact Or.inl h
        · exact Or.inr ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
        · exact Or.inr ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
      rcases hpm _ (hker _ (perpRoots_subset_rootCharKernel _ (he i hi))) with h | ⟨ε, hε, h⟩
      · exact h.2
      · exfalso
        obtain ⟨i', hi', hii', hne⟩ := hnbr i hi
        have hform : CFSG.LieType.Steinberg.Adjoint.iform
            (u • (Pi.single i 1 : Fin τ.rank → ℤ)) (u • Pi.single i' 1) ≠ 0 := by
          rw [iform_smul]; exact hne
        rw [h, CFSG.LieType.Steinberg.Adjoint.iform_smul_left] at hform
        rcases hpm _ (hker _ (perpRoots_subset_rootCharKernel _ (he i' hi'))) with
          h' | ⟨ε', hε', h'⟩
        · exact hform (by rw [(hθform _).2 h'.2, mul_zero])
        · exact hsep i i' hii' ε ε' hε hε' h h'
    intro γ ⟨hγ, hγ0⟩
    refine ⟨IsRoot.smul hγ u, ?_⟩
    rw [weyl_smul_eq_sum, Finset.sum_apply, Finset.sum_eq_single j₀]
    · rw [Pi.smul_apply, hγ0, zero_smul]
    · intro i _ hi
      rw [Pi.smul_apply, hoff i hi, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have hw' : w⁻¹ ∈ rootCharStabilizer (Pi.mulSingle (highNode τ) (-1 : Kˣ)) :=
    (rootCharStabilizerSubgroup _).inv_mem hw
  refine Set.Subset.antisymm ?_ fun γ hγ => ⟨w⁻¹ • γ, key _ hw' γ hγ, smul_inv_smul w γ⟩
  rintro _ ⟨γ, hγ, rfl⟩
  exact key w hw γ hγ

section Involution


theorem eq_smul_highRoot_of_coeff (hθ2 : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h : γ (highNode τ) = ε * 2) : γ = ε • highRoot τ := by
  rcases hε with rfl | rfl
  · rw [one_smul]
    exact hθ2 γ hγ (by rw [h]; norm_num)
  · rw [neg_one_smul]
    have h' : (-γ) (highNode τ) = 2 := by rw [Pi.neg_apply, h]; norm_num
    rw [← hθ2 _ (IsRoot.neg hγ) h', neg_neg]

theorem rootSubgroup_highRoot_le_centralizer {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθ2 : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ)
    (hθk : highRoot τ (highNode τ) = 2) :
    rootSubgroup τ K (ε • highRoot τ) ≤
      Subgroup.centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
  have hθr : IsRoot τ (ε • highRoot τ) := by
    rcases hε with rfl | rfl
    · rw [one_smul]; exact isRoot_highRoot τ
    · rw [neg_one_smul]; exact IsRoot.neg (isRoot_highRoot τ)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  have hle : rootSpan τ K (perpRoots τ) ≤ Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
    refine iSup₂_le fun β hβ y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hβ0 : β ≠ 0 := hβ.1.ne_zero
    refine (commute_of_forall_not_isRoot hθr hβ.1 ?_ ?_ ?_ K x hx y hy).eq.symm
    · intro h
      have := congrFun h (highNode τ)
      rw [Pi.smul_apply, hθk, hβ.2, smul_eq_mul] at this
      rcases hε with rfl | rfl <;> omega
    · intro h
      have := congrFun h (highNode τ)
      rw [Pi.smul_apply, hθk, Pi.neg_apply, hβ.2, smul_eq_mul] at this
      rcases hε with rfl | rfl <;> omega
    · intro a b ha hb hr
      have hc := hk _ hr
      have hcoord0 : (a • (ε • highRoot τ) + b • β) (highNode τ) = (a : ℤ) * (ε * 2) := by
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hθk, hβ.2, smul_zero,
          add_zero, smul_eq_mul, nsmul_eq_mul]
      rw [hcoord0] at hc
      have ha1 : a = 1 := by
        rw [abs_le] at hc
        rcases hε with rfl | rfl <;> omega
      subst ha1
      have heq := eq_smul_highRoot_of_coeff hθ2 hε hr (by rw [hcoord0]; push_cast; ring)
      rw [one_smul] at heq
      have hb0 : b • β = 0 := add_left_cancel (heq.trans (add_zero _).symm)
      rcases smul_eq_zero.1 hb0 with h | h
      · exact absurd h (Nat.pos_iff_ne_zero.1 hb)
      · exact hβ0 h
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem toralCentralizer_neg_one_le_normalizer (hK : ringChar K ≠ 2)
    (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    (hθ2 : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ)
    (hθk : highRoot τ (highNode τ) = 2)
    (hθform : ∀ v, CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) v = 0 ↔ v (highNode τ) = 0)
    (hnbr : ∀ i, i ≠ highNode τ → ∃ i', i' ≠ highNode τ ∧ i' ≠ i ∧
      CFSG.LieType.Steinberg.Adjoint.iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i' 1) ≠ 0) :
    toralCentralizer τ K (Pi.mulSingle (highNode τ) (-1 : Kˣ)) ≤
      Subgroup.normalizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K _).2.2.2]
  refine sup_le (sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) ?_) ?_
  · refine iSup₂_le fun β hβ => ?_
    rcases mem_rootCharKernel_neg_one hK hk hθ2 hβ with h | rfl | rfl
    · exact (le_iSup₂_of_le β h le_rfl : rootSubgroup τ K β ≤ rootSpan τ K (perpRoots τ)).trans
        Subgroup.le_normalizer
    · have := rootSubgroup_highRoot_le_centralizer (K := K) (Or.inl rfl) hk hθ2 hθk
      rw [one_smul] at this
      exact this.trans (Subgroup.centralizer_le_normalizer _)
    · have := rootSubgroup_highRoot_le_centralizer (K := K) (Or.inr rfl) hk hθ2 hθk
      rw [neg_one_smul] at this
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    refine mem_normalizer_of_map_eq ?_
    rw [(canonical_weyl_root_transport τ K).1 w (perpRoots τ) fun _ hα => hα.1,
      image_perpRoots_of_mem_rootCharStabilizer_neg_one hK hk hθ2 hθform hnbr hw]

end Involution

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
