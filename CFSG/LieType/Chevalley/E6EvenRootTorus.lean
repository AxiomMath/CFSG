module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.E6GraphLeviTheta

public noncomputable section

namespace CFSG.LieType.Chevalley.RootTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot

variable {τ : Tag} {K : Type} [Field K]

theorem conj_rootDiagUnit_mem_subsystemGroup
    (J : Set (Fin τ.rank))
    (a : Fin τ.rank → Kˣ) {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ ∈ subsystemGroup τ K J := by
  have hle : subsystemGroup τ K J ≤ (subsystemGroup τ K J).comap
      (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation τ K a).1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation τ K a).2.1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  exact hle hg

theorem torusGroup_le_normalizer_subsystemGroup
    (J : Set (Fin τ.rank)) :
    torusGroup τ K ≤ Subgroup.normalizer (subsystemGroup τ K J : Set (ModGL τ K)) := by
  intro h hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_rootDiagUnit_mem_subsystemGroup J a, fun hg => ?_⟩
  have h1 := conj_rootDiagUnit_mem_subsystemGroup J a⁻¹ hg
  rwa [← rootDiagUnit_inv, inv_inv, show (rootDiagUnit τ a)⁻¹ *
    (rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a = g by group] at h1

theorem torusGroup_mul_comm
    {h h' : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (hh' : h' ∈ torusGroup τ K) : h * h' = h' * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hh'

theorem rootChar_mulSingle (j : Fin τ.rank) (c : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle j c) v = c ^ v j := by
  rw [rootChar, Finset.prod_eq_single j
    (fun i _ hi => by rw [Pi.mulSingle_eq_of_ne hi, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

theorem zpow_ne_one {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) {n : ℤ}
    (hn : n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2) : c ^ n ≠ 1 := by
  rcases hn with rfl | rfl | rfl | rfl
  · intro h
    exact hc2 (by simpa [zpow_neg] using h)
  · intro h
    exact hc1 (by simpa using h)
  · intro h
    exact hc1 (by simpa using h)
  · intro h
    exact hc2 (by simpa using h)

theorem rootCharKernel_mulSingle_subset (j : Fin τ.rank)
    (hcoef : ∀ α, IsRoot τ α → -2 ≤ α j ∧ α j ≤ 2) {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) :
    rootCharKernel (Pi.mulSingle j c) ⊆ parabolicRoots τ {i | i ≠ j} := by
  rintro α ⟨hα, h1⟩
  refine ⟨hα, fun i hi => ?_⟩
  obtain rfl : i = j := by simpa using hi
  rw [rootChar_mulSingle] at h1
  obtain ⟨hlo, hhi⟩ := hcoef α hα
  by_contra h0
  exact zpow_ne_one hc1 hc2 (by omega) h1

theorem rootCharStabilizer_mulSingle_subset
    (j : Fin τ.rank) {θ : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (hform : ∀ v, iform θ v = v j)
    (hcheck : ∀ β, IsRoot τ β → β ≠ θ → ∃ i, iform (β - θ) (Pi.single i 1) = -2 ∨
      iform (β - θ) (Pi.single i 1) = -1 ∨ iform (β - θ) (Pi.single i 1) = 1 ∨
      iform (β - θ) (Pi.single i 1) = 2)
    {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) :
    rootCharStabilizer (Pi.mulSingle j c) ⊆ parabolicWeylGroup τ {i | i ≠ j} := by
  intro w hw
  have hw' : ∀ v : Fin τ.rank → ℤ, c ^ (w • v) j = c ^ v j := fun v => by
    simpa only [rootChar_mulSingle] using hw v
  have hβ : w⁻¹ • θ = θ := by
    by_contra hne
    obtain ⟨i, hi⟩ := hcheck _ (IsRoot.smul hθ w⁻¹) hne
    have h1 := hw' (Pi.single i 1)
    have e1 : (w • (Pi.single i 1 : Fin τ.rank → ℤ)) j = iform (w⁻¹ • θ) (Pi.single i 1) := by
      rw [← hform (w • Pi.single i 1), ← iform_smul w (w⁻¹ • θ), smul_inv_smul]
    rw [e1, ← hform (Pi.single i 1)] at h1
    have h2 : c ^ iform (w⁻¹ • θ - θ) (Pi.single i 1) = 1 := by
      rw [iform_sub_left, zpow_sub, h1, mul_inv_cancel]
    exact zpow_ne_one hc1 hc2 hi h2
  have hwθ : w • θ = θ := by
    calc w • θ = w • (w⁻¹ • θ) := by rw [hβ]
      _ = θ := smul_inv_smul w θ
  have hmem : w ∈ (parabolicWeylGroup τ {i | i ≠ j} : Set (WeylGroup τ)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer τ {i | i ≠ j}).1]
    intro v i hi
    obtain rfl : i = j := by simpa using hi
    rw [← hform (w • v), ← hform v, ← iform_smul w θ v, hwθ]
  exact hmem

theorem toralCentralizer_le_sup
    (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)}
    (hker : rootCharKernel a ⊆ parabolicRoots τ J)
    (hW : rootCharStabilizer a ⊆ parabolicWeylGroup τ J) :
    toralCentralizer τ K a ≤ torusGroup τ K ⊔ subsystemGroup τ K J := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2]
  refine sup_le (sup_le le_sup_left (iSup₂_le fun α hα =>
    (rootSubgroup_le_subsystemGroup (hker hα)).trans le_sup_right)) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact Subgroup.mem_sup_right (canonicalRep_mem_subsystemGroup (hW hw))

theorem exists_mul_of_mem_toralCentralizer
    (a : Fin τ.rank → Kˣ)
    {J : Set (Fin τ.rank)} (hker : rootCharKernel a ⊆ parabolicRoots τ J)
    (hW : rootCharStabilizer a ⊆ parabolicWeylGroup τ J) {g : ModGL τ K}
    (hg : g ∈ toralCentralizer τ K a) :
    ∃ h ∈ torusGroup τ K, h⁻¹ * g ∈ subsystemGroup τ K J := by
  have hg' : g ∈ ((torusGroup τ K ⊔ subsystemGroup τ K J : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) := toralCentralizer_le_sup a hker hW hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_subsystemGroup J)] at hg'
  obtain ⟨h, hh, l, hl, rfl⟩ := hg'
  exact ⟨h, hh, by rwa [inv_mul_cancel_left]⟩

@[expose] def E6Check (n : ℕ) : Prop :=
  (-2 ≤ TwistTag.E6.tag.rootCertificate.root n (e6Idx 1) ∧
      TwistTag.E6.tag.rootCertificate.root n (e6Idx 1) ≤ 2) ∧
    (TwistTag.E6.tag.rootCertificate.root n ≠ e6HighestRoot → ∃ i : Fin TwistTag.E6.tag.rank,
      (∑ l, TwistTag.E6.tag.cartan i l *
          (TwistTag.E6.tag.rootCertificate.root n l - e6HighestRoot l)) = -2 ∨
        (∑ l, TwistTag.E6.tag.cartan i l *
          (TwistTag.E6.tag.rootCertificate.root n l - e6HighestRoot l)) = -1 ∨
        (∑ l, TwistTag.E6.tag.cartan i l *
          (TwistTag.E6.tag.rootCertificate.root n l - e6HighestRoot l)) = 1 ∨
        (∑ l, TwistTag.E6.tag.cartan i l *
          (TwistTag.E6.tag.rootCertificate.root n l - e6HighestRoot l)) = 2)

instance (n : ℕ) : Decidable (E6Check n) := by
  unfold E6Check
  infer_instance

theorem e6Check : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, E6Check n := by
  decide +kernel

theorem symmetrizer_E6 (i : Fin TwistTag.E6.tag.rank) : TwistTag.E6.tag.symmetrizer i i = 1 := by
  revert i
  decide

theorem coef_e6
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    -2 ≤ α (e6Idx 1) ∧ α (e6Idx 1) ≤ 2 := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  exact (e6Check n hn).1

theorem check_e6
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hne : β ≠ e6HighestRoot) : ∃ i, iform (β - e6HighestRoot) (Pi.single i 1) = -2 ∨
      iform (β - e6HighestRoot) (Pi.single i 1) = -1 ∨
      iform (β - e6HighestRoot) (Pi.single i 1) = 1 ∨
      iform (β - e6HighestRoot) (Pi.single i 1) = 2 := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  obtain ⟨i, hi⟩ := (e6Check n hn).2 hne
  refine ⟨i, ?_⟩
  rw [iform_single_right, symmetrizer_E6, one_mul]
  exact hi

theorem sq_ne_one_of_two {k : Type} [Field k] (h2 : (2 : k) = 0) {c : kˣ} (hc : c ≠ 1) :
    c ^ 2 ≠ 1 := by
  intro h
  apply hc
  have h' : ((c : k)) ^ 2 = 1 := by
    have := congrArg (fun u : kˣ => (u : k)) h
    simpa using this
  have h0 : ((c : k) - 1) ^ 2 = 0 := by linear_combination h' + (1 - (c : k)) * h2
  exact Units.ext (by simpa [sub_eq_zero] using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0)

theorem exists_mul_of_mem_centralizer_thetaTorus
    {k : Type} [Field k]
    (h2 : (2 : k) = 0) {c : kˣ} (hc : c ≠ 1) {g : ModGL TwistTag.E6.tag k}
    (hg : g ∈ adjointGroup TwistTag.E6.tag k) (hgc : g ∈ Subgroup.centralizer
      (thetaTorus (RingHom.id k) : Set (ModGL TwistTag.E6.tag k))) :
    ∃ h ∈ torusGroup TwistTag.E6.tag k, h⁻¹ * g ∈ subsystemGroup TwistTag.E6.tag k setA := by
  have hc2 := sq_ne_one_of_two h2 hc
  have hmem : g ∈ toralCentralizer TwistTag.E6.tag k (Pi.mulSingle (e6Idx 1) c) := by
    refine Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ rfl
    exact Subgroup.mem_centralizer_iff.1 hgc (thetaTorusHom k c) ⟨c, rfl⟩
  exact exists_mul_of_mem_toralCentralizer _
    (rootCharKernel_mulSingle_subset (e6Idx 1) (fun _ hα => coef_e6 hα) hc hc2)
    (rootCharStabilizer_mulSingle_subset (e6Idx 1) isRoot_e6HighestRoot iform_e6HighestRoot
      (fun _ hβ hne => check_e6 hβ hne) hc hc2) hmem

end CFSG.LieType.Chevalley.RootTorus
