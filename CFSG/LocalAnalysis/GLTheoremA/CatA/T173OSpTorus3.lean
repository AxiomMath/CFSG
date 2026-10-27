module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpTorus2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.RankThree.Classical (spEnd spEnd_apply)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)
open CFSG.LieType.SeitzGeneration.RootPair
open CFSG.StandardType.TableBSymp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ n p : ℕ}

private def partnerCompl (X : Set (Fin ℓ ⊕ Fin ℓ)) : Set (Fin ℓ ⊕ Fin ℓ) :=
  {b | par b ∉ X}

private theorem mem_coordSpan_orthogonal_iff {X : Set (Fin ℓ ⊕ Fin ℓ)} {v : Fin ℓ ⊕ Fin ℓ → F} :
    (∀ u ∈ coordSpan (F := F) X, form u v = 0) ↔
      v ∈ coordSpan (F := F) (partnerCompl X) := by
  rw [mem_coordSpan_iff (F := F)]
  constructor
  · intro h b hb
    have hb' : par b ∈ X := by
      by_contra hb''
      exact hb hb''
    have h1 := h _ (Submodule.subset_span ⟨par b, hb', rfl⟩)
    have h2 : form (Pi.single (par b) (1 : F)) v = sgn F (par b) * v b := by
      rw [form_apply]
      rw [Finset.sum_eq_single (par b)]
      · simp
      · intro a _ ha
        rw [Pi.single_eq_of_ne (M := fun _ : Fin ℓ ⊕ Fin ℓ => F) (i := par b) (i' := a)
          (fun h => ha h) 1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (sgn_ne_zero (par b))
  · intro hv u hu
    rw [form_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a ∈ X
    · have h1 : v (par a) = 0 := hv (par a) (fun h => h (by simpa using ha))
      rw [h1, mul_zero, mul_zero]
    · have h1 : u a = 0 := (mem_coordSpan_iff (F := F)).mp hu a ha
      rw [h1, zero_mul]

private theorem partnerCompl_image {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} (hτ : CommutesPar τ)
    (X : Set (Fin ℓ ⊕ Fin ℓ)) :
    partnerCompl (τ '' X) = τ '' partnerCompl X := by
  ext b
  have h1 : b ∈ partnerCompl (τ '' X) ↔ τ.symm (par b) ∉ X := by
    rw [partnerCompl, Set.mem_setOf_eq, Set.mem_image_equiv]
  have h2 : b ∈ τ '' partnerCompl X ↔ par (τ.symm b) ∉ X := by
    rw [Set.mem_image_equiv, partnerCompl, Set.mem_setOf_eq]
  rw [h1, h2, hτ.symm b]

private theorem form_spEnd (k : ↥(StatedSp ℓ F)) (u v : Fin ℓ ⊕ Fin ℓ → F) :
    form (spEnd k u) (spEnd k v) = form u v := by
  rw [spEnd_apply, spEnd_apply]
  exact form_mulVec k u v

private theorem orthogonal_invariant_of_preserves {K : Subgroup ↥(StatedSp ℓ F)}
    {X : Set (Fin ℓ ⊕ Fin ℓ)}
    (h : ∀ k ∈ K, ∀ w ∈ coordSpan (F := F) X,
      spEnd k w ∈ coordSpan (F := F) X) :
    ∀ k ∈ K, ∀ v, (∀ u ∈ coordSpan (F := F) X, form u v = 0) →
      ∀ u ∈ coordSpan (F := F) X, form u (spEnd k v) = 0 := by
  intro k hk v hv u hu
  have hu' : spEnd k⁻¹ u ∈ coordSpan (F := F) X := h k⁻¹ (inv_mem hk) u hu
  have h1 : form (spEnd k (spEnd k⁻¹ u)) (spEnd k v) = form (spEnd k⁻¹ u) v :=
    form_spEnd k _ _
  rw [show spEnd k (spEnd k⁻¹ u) = u from by
    rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one,
      Module.End.one_apply]] at h1
  rw [h1]
  exact hv (spEnd k⁻¹ u) hu'

private theorem mem_partnerCompl_iff {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} {X : Set (Fin ℓ ⊕ Fin ℓ)}
    {b : Fin ℓ ⊕ Fin ℓ} : b ∈ partnerCompl (τ '' X) ↔ τ.symm (par b) ∉ X := by
  rw [partnerCompl, Set.mem_setOf_eq, Set.mem_image_equiv]

private theorem special_inl {S : Set (Fin ℓ ⊕ Fin ℓ)} {i : Fin ℓ}
    (h1 : Sum.inl i ∈ S) (h2 : Sum.inr i ∉ S) :
    S ∩ partnerCompl ((sAll ℓ * pairSwap i) '' S) = {Sum.inl i} := by
  ext b
  constructor
  · rintro ⟨hbS, hbY⟩
    by_contra hb
    apply hbY
    refine ⟨pairSwap i b, ?_, ?_⟩
    · rcases b with j | j
      · have hj : j ≠ i := fun h => hb (by rw [h]; simp)
        rw [pairSwap, Equiv.swap_apply_of_ne_of_ne (fun h' => hj (Sum.inl_injective h'))
          Sum.inl_ne_inr]
        exact hbS
      · by_cases hj : j = i
        · subst hj; rw [pairSwap, Equiv.swap_apply_right]; exact h1
        · rw [pairSwap, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
            (fun h' => hj (Sum.inr_injective h'))]
          exact hbS
    · show (sAll ℓ * pairSwap i) (pairSwap i b) = par b
      rw [Equiv.Perm.mul_apply]
      show sAll ℓ (pairSwap i (pairSwap i b)) = par b
      rw [show pairSwap i (pairSwap i b) = b from by simp [pairSwap], sAll_apply]
  · rintro rfl
    refine ⟨h1, ?_⟩
    rw [mem_partnerCompl_iff, symm_sAll_pairSwap]
    have hinv : (sAll ℓ * pairSwap i) (par (Sum.inl i)) = Sum.inr i := by
      rw [Equiv.Perm.mul_apply]
      show sAll ℓ (pairSwap i (par (Sum.inl i))) = Sum.inr i
      rw [par_inl, show pairSwap i (Sum.inr i) = Sum.inl i from by
        rw [pairSwap, Equiv.swap_apply_right], sAll_apply, par_inl]
    rw [hinv]
    exact h2

private theorem special_inr {S : Set (Fin ℓ ⊕ Fin ℓ)} {i : Fin ℓ}
    (h1 : Sum.inr i ∈ S) (h2 : Sum.inl i ∉ S) :
    S ∩ partnerCompl ((pairSwap i * sAll ℓ) '' S) = {Sum.inr i} := by
  ext b
  constructor
  · rintro ⟨hbS, hbY⟩
    by_contra hb
    apply hbY
    refine ⟨pairSwap i b, ?_, ?_⟩
    · rcases b with j | j
      · by_cases hj : j = i
        · subst hj; rw [pairSwap, Equiv.swap_apply_left]; exact h1
        · rw [pairSwap, Equiv.swap_apply_of_ne_of_ne (fun h' => hj (Sum.inl_injective h'))
            Sum.inl_ne_inr]
          exact hbS
      · have hj : j ≠ i := fun h => hb (by rw [h]; simp)
        rw [pairSwap, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
          (fun h' => hj (Sum.inr_injective h'))]
        exact hbS
    · show (pairSwap i * sAll ℓ) (pairSwap i b) = par b
      rw [Equiv.Perm.mul_apply]
      show pairSwap i (sAll ℓ (pairSwap i b)) = par b
      rw [sAll_apply, commutesPar_pairSwap i (pairSwap i b),
        show pairSwap i (pairSwap i b) = b from by simp [pairSwap]]
  · rintro rfl
    refine ⟨h1, ?_⟩
    rw [mem_partnerCompl_iff, symm_pairSwap_sAll]
    have hinv : (pairSwap i * sAll ℓ) (par (Sum.inr i)) = Sum.inl i := by
      rw [Equiv.Perm.mul_apply]
      show pairSwap i (sAll ℓ (par (Sum.inr i))) = Sum.inl i
      rw [sAll_apply, par_par, pairSwap, Equiv.swap_apply_right]
    rw [hinv]
    exact h2

private theorem pair_not_mem_of_disjoint {S : Set (Fin ℓ ⊕ Fin ℓ)} {j : Fin ℓ}
    (hdisj : ({Sum.inl j, Sum.inr j} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅) :
    Sum.inl j ∉ S ∧ Sum.inr j ∉ S := by
  constructor
  · intro h
    have := Set.mem_inter (show Sum.inl j ∈ ({Sum.inl j, Sum.inr j} : Set _) from by simp) h
    rwa [hdisj] at this
  · intro h
    have := Set.mem_inter (show Sum.inr j ∈ ({Sum.inl j, Sum.inr j} : Set _) from by simp) h
    rwa [hdisj] at this

private theorem special_pair_subset {S : Set (Fin ℓ ⊕ Fin ℓ)} {i j : Fin ℓ} (hij : i ≠ j)
    (hpair : ∀ k, Sum.inl k ∈ S ↔ Sum.inr k ∈ S)
    (hsub : ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) ⊆ S)
    (hdisj : ({Sum.inl j, Sum.inr j} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅) :
    S ∩ partnerCompl ((Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j)) '' S) ⊆
      {Sum.inl i, Sum.inr i} := by
  rintro b ⟨hbS, hbY⟩
  rcases b with k | k
  · by_contra hk
    apply hbY
    rw [Set.mem_image_equiv, sumCongr_swap_symm]
    show Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (par (Sum.inl k)) ∈ S
    rw [par_inl]
    by_cases hkj : k = j
    · have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inr k) =
          Sum.inr i := by rw [hkj]; simp
      rw [hx]
      exact hsub (by simp)
    · have hki : k ≠ i := fun h => hk (by rw [h]; simp)
      have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inr k) =
          Sum.inr k := by simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hx]
      exact (hpair k).mp hbS
  · by_contra hk
    apply hbY
    rw [Set.mem_image_equiv, sumCongr_swap_symm]
    show Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (par (Sum.inr k)) ∈ S
    rw [par_inr]
    by_cases hkj : k = j
    · have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inl k) =
          Sum.inl i := by rw [hkj]; simp
      rw [hx]
      exact hsub (by simp)
    · have hki : k ≠ i := fun h => hk (by rw [h]; simp)
      have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inl k) =
          Sum.inl k := by simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hx]
      exact (hpair k).mpr hbS

private theorem special_pair_superset {S : Set (Fin ℓ ⊕ Fin ℓ)} {i j : Fin ℓ}
    (hij : i ≠ j)
    (hsub : ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) ⊆ S)
    (hdisj : ({Sum.inl j, Sum.inr j} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅) :
    {Sum.inl i, Sum.inr i} ⊆ S ∩ partnerCompl
      ((Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j)) '' S) := by
  have hj := pair_not_mem_of_disjoint hdisj
  rintro x (rfl | rfl)
  · refine ⟨hsub (by simp), ?_⟩
    rw [partnerCompl, Set.mem_setOf_eq, Set.mem_image_equiv, sumCongr_swap_symm]
    show Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (par (Sum.inl i)) ∉ S
    rw [par_inl]
    have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inr i) =
        Sum.inr j := by simp
    rw [hx]
    exact hj.2
  · refine ⟨hsub (by simp), ?_⟩
    rw [partnerCompl, Set.mem_setOf_eq, Set.mem_image_equiv, sumCongr_swap_symm]
    show Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (par (Sum.inr i)) ∉ S
    rw [par_inr]
    have hx : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) (Sum.inl i) =
        Sum.inl j := by simp
    rw [hx]
    exact hj.1

private theorem special_pair {S : Set (Fin ℓ ⊕ Fin ℓ)} {i j : Fin ℓ} (hij : i ≠ j)
    (hpair : ∀ k, Sum.inl k ∈ S ↔ Sum.inr k ∈ S)
    (hsub : ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) ⊆ S)
    (hdisj : ({Sum.inl j, Sum.inr j} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅) :
    S ∩ partnerCompl
        ((Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j)) '' S) =
      {Sum.inl i, Sum.inr i} :=
  Set.Subset.antisymm (special_pair_subset hij hpair hsub hdisj)
    (special_pair_superset hij hsub hdisj)

private theorem coordSpan_image_special {S T : Set (Fin ℓ ⊕ Fin ℓ)}
    {τ0 τ1 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hspecial : S ∩ partnerCompl (τ0 '' S) = T) (hτ1par : CommutesPar τ1) :
    coordSpan (F := F) (τ1 '' T) = coordSpan (F := F) (τ1 '' S) ⊓
      coordSpan (F := F) (partnerCompl (τ1 '' (τ0 '' S))) := by
  rw [← hspecial, Set.image_inter (Equiv.injective τ1), ← partnerCompl_image hτ1par,
    coordSpan_inter]

private theorem invariant_pair_of_monomial {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    {g0 : ↥(StatedSp ℓ F)} {τ0 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    {g1 : ↥(StatedSp ℓ F)} {τ1 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hg0N : g0 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ0mono : IsMonomial g0 τ0)
    (hg1N : g1 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ1mono : IsMonomial g1 τ1) :
    (∀ k ∈ K, ∀ w ∈ coordSpan (F := F) (τ1 '' S),
        spEnd k w ∈ coordSpan (F := F) (τ1 '' S)) ∧
      (∀ k ∈ K, ∀ w ∈ coordSpan (F := F) (partnerCompl (τ1 '' (τ0 '' S))),
        spEnd k w ∈ coordSpan (F := F) (partnerCompl (τ1 '' (τ0 '' S)))) := by
  refine ⟨coordSpan_image_invariant hWK hW hg1N hτ1mono, ?_⟩
  have h2 := coordSpan_image_invariant hWK hW (Subgroup.mul_mem _ hg1N hg0N)
    (isMonomial_mul hτ1mono hτ0mono)
  intro k hk w hw
  rw [← mem_coordSpan_orthogonal_iff] at hw ⊢
  rw [Set.image_image] at hw ⊢
  exact orthogonal_invariant_of_preserves (K := K) (X := (τ1 * τ0) '' S) h2 k hk w hw

private theorem coordSpan_singleton_invariant {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    {g0 : ↥(StatedSp ℓ F)} {τ0 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} {e0 : Fin ℓ ⊕ Fin ℓ}
    (hg0N : g0 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ0mono : IsMonomial g0 τ0)
    (hspec : S ∩ partnerCompl (τ0 '' S) = {e0})
    (hex : ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ (g1 : ↥(StatedSp ℓ F))
      (τ1 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)), g1 ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)) ∧ IsMonomial g1 τ1 ∧ CommutesPar τ1 ∧ τ1 e0 = b) :
    ∀ k ∈ K, ∀ b : Fin ℓ ⊕ Fin ℓ,
      spEnd k (Pi.single b (1 : F)) ∈ coordSpan (F := F) ({b} : Set (Fin ℓ ⊕ Fin ℓ)) := by
  intro k hk b
  obtain ⟨g1, τ1, hg1N, hτ1mono, hτ1par, hbmap⟩ := hex b
  obtain ⟨h1, h2'⟩ := invariant_pair_of_monomial hW hWK hg0N hτ0mono hg1N hτ1mono
  have h3 : coordSpan (F := F) ({b} : Set (Fin ℓ ⊕ Fin ℓ)) =
      coordSpan (F := F) (τ1 '' S) ⊓
        coordSpan (F := F) (partnerCompl (τ1 '' (τ0 '' S))) := by
    rw [show ({b} : Set (Fin ℓ ⊕ Fin ℓ)) = τ1 '' ({e0} : Set (Fin ℓ ⊕ Fin ℓ)) from by
      rw [Set.image_singleton, hbmap]]
    exact coordSpan_image_special hspec hτ1par
  have hsingle : Pi.single b (1 : F) ∈ coordSpan (F := F) ({b} : Set (Fin ℓ ⊕ Fin ℓ)) :=
    Submodule.subset_span (by simp)
  rw [h3, Submodule.mem_inf] at hsingle ⊢
  exact ⟨h1 k hk _ hsingle.1, h2' k hk _ hsingle.2⟩

private theorem preserves_lines_of_singleton {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    {g0 : ↥(StatedSp ℓ F)} {τ0 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} {e0 : Fin ℓ ⊕ Fin ℓ}
    (hg0N : g0 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ0mono : IsMonomial g0 τ0)
    (hspec : S ∩ partnerCompl (τ0 '' S) = {e0})
    (hex : ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ (g1 : ↥(StatedSp ℓ F))
      (τ1 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)), g1 ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)) ∧ IsMonomial g1 τ1 ∧ CommutesPar τ1 ∧ τ1 e0 = b) :
    ∀ k ∈ K, ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ c : F,
      spEnd k (Pi.single b (1 : F)) = c • Pi.single b (1 : F) := by
  intro k hk b
  have hmem := coordSpan_singleton_invariant hW hWK hg0N hτ0mono hspec hex k hk b
  rw [coordSpan_singleton, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

private theorem coordSpan_pair_invariant (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    {g0 : ↥(StatedSp ℓ F)} {τ0 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} {i0 : Fin ℓ}
    (hg0N : g0 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ0mono : IsMonomial g0 τ0)
    (hspec : S ∩ partnerCompl (τ0 '' S) = {Sum.inl i0, Sum.inr i0}) :
    ∀ k ∈ K, ∀ i : Fin ℓ, ∀ w ∈ coordSpan (F := F)
        ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)),
      spEnd k w ∈ coordSpan (F := F) ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) := by
  intro k hk i
  obtain ⟨g1, τ1, hg1N, hτ1mono, hτ1par, hbmap⟩ :=
    exists_isMonomial_map_inl hp hp2 hn hpq i0 (Sum.inl i)
  obtain ⟨h1, h2'⟩ := invariant_pair_of_monomial hW hWK hg0N hτ0mono hg1N hτ1mono
  have hpair_image : (τ1 '' ({Sum.inl i0, Sum.inr i0} : Set (Fin ℓ ⊕ Fin ℓ))) =
      {Sum.inl i, Sum.inr i} := by
    rw [Set.image_pair, hbmap]
    have h2'' : τ1 (Sum.inr i0) = par (τ1 (Sum.inl i0)) := by
      have h := hτ1par (Sum.inr i0)
      rw [par_inr] at h
      simpa using (congrArg par h).symm
    rw [h2'', hbmap, par_inl]
  have h3 : coordSpan (F := F) ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) =
      coordSpan (F := F) (τ1 '' S) ⊓
        coordSpan (F := F) (partnerCompl (τ1 '' (τ0 '' S))) := by
    rw [← hpair_image]
    exact coordSpan_image_special hspec hτ1par
  intro w hw
  rw [h3, Submodule.mem_inf] at hw ⊢
  exact ⟨h1 k hk _ hw.1, h2' k hk _ hw.2⟩

private theorem preserves_planes_of_pair (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    {g0 : ↥(StatedSp ℓ F)} {τ0 : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} {i0 : Fin ℓ}
    (hg0N : g0 ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)))
    (hτ0mono : IsMonomial g0 τ0)
    (hspec : S ∩ partnerCompl (τ0 '' S) = {Sum.inl i0, Sum.inr i0}) :
    ∀ k ∈ K, ∀ i : Fin ℓ, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ plane F i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ plane F i := by
  intro k hk i
  have hmem := coordSpan_pair_invariant hp hp2 hn hpq hW hWK hg0N hτ0mono hspec k hk i
  constructor
  · have h := hmem (Pi.single (Sum.inl i) (1 : F)) (Submodule.subset_span (by simp))
    rwa [coordSpan_pair] at h
  · have h := hmem (Pi.single (Sum.inr i) (1 : F)) (Submodule.subset_span (by simp))
    rwa [coordSpan_pair] at h

private theorem coordSupport_nonempty (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} (hW0 : W ≠ ⊥)
    (hWV : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W) :
    (coordSupport W).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hW0
  rw [eq_coordSpan_coordSupport hn hp hp2 hpq hWV, h]
  rw [coordSpan, Set.image_empty, Submodule.span_empty]

private theorem coordSupport_ne_univ (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} (hWtop : W ≠ ⊤)
    (hWV : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W) :
    coordSupport W ≠ Set.univ := by
  intro h
  apply hWtop
  have hUniv : coordSpan (F := F) (Set.univ : Set (Fin ℓ ⊕ Fin ℓ)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_coordSpan_iff]
    intro b hb
    exact absurd (Set.mem_univ b) hb
  rw [eq_coordSpan_coordSupport hn hp hp2 hpq hWV, h, hUniv]

private theorem exists_pair_support_data {S : Set (Fin ℓ ⊕ Fin ℓ)} (hSne : S.Nonempty)
    (hSproper : S ≠ Set.univ) (hpair : ∀ k, Sum.inl k ∈ S ↔ Sum.inr k ∈ S) :
    ∃ i0 j0 : Fin ℓ, i0 ≠ j0 ∧
      ({Sum.inl i0, Sum.inr i0} : Set (Fin ℓ ⊕ Fin ℓ)) ⊆ S ∧
      ({Sum.inl j0, Sum.inr j0} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅ := by
  obtain ⟨b0, hb0⟩ := hSne
  have hi0 : ∃ i0, ({Sum.inl i0, Sum.inr i0} : Set (Fin ℓ ⊕ Fin ℓ)) ⊆ S := by
    rcases b0 with k | k
    · exact ⟨k, by rintro x (rfl | rfl); exacts [hb0, (hpair k).mp hb0]⟩
    · exact ⟨k, by rintro x (rfl | rfl); exacts [(hpair k).mpr hb0, hb0]⟩
  obtain ⟨i0, hi0⟩ := hi0
  have hb1 : ∃ b1, b1 ∉ S := by
    by_contra h
    push Not at h
    exact hSproper (Set.eq_univ_of_forall h)
  obtain ⟨b1, hb1⟩ := hb1
  have hj0 : ∃ j0, ({Sum.inl j0, Sum.inr j0} : Set (Fin ℓ ⊕ Fin ℓ)) ∩ S = ∅ := by
    rcases b1 with k | k
    · refine ⟨k, Set.not_nonempty_iff_eq_empty.mp ?_⟩
      rintro ⟨x, hx, hxS⟩
      rcases hx with rfl | rfl
      · exact hb1 hxS
      · exact hb1 ((hpair k).mpr hxS)
    · refine ⟨k, Set.not_nonempty_iff_eq_empty.mp ?_⟩
      rintro ⟨x, hx, hxS⟩
      rcases hx with rfl | rfl
      · exact hb1 ((hpair k).mp hxS)
      · exact hb1 hxS
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨i0, j0, ?_, hi0, hj0⟩
  intro h
  have h1 : Sum.inl i0 ∈ S := hi0 (by simp)
  have h2 : Sum.inl i0 ∈ ({Sum.inl j0, Sum.inr j0} : Set (Fin ℓ ⊕ Fin ℓ)) := by
    rw [h]; simp
  have h3 := Set.mem_inter h2 h1
  rw [hj0] at h3
  exact h3

private theorem case_half_pair (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    (hhalf : ∃ i : Fin ℓ,
      (Sum.inl i ∈ S ∧ Sum.inr i ∉ S) ∨ (Sum.inr i ∈ S ∧ Sum.inl i ∉ S)) :
    ∀ k ∈ K, ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ c : F,
      spEnd k (Pi.single b (1 : F)) = c • Pi.single b (1 : F) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨i, hcase | hcase⟩ := hhalf
  · exact preserves_lines_of_singleton hW hWK
      (Subgroup.mul_mem _ (sAllSp_mem_normalizer hp0)
        (spSwapSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq i))
      (isMonomial_mul isMonomial_sAllSp (isMonomial_spSwapSp i))
      (special_inl hcase.1 hcase.2) (exists_isMonomial_map_inl hp hp2 hn hpq i)
  · exact preserves_lines_of_singleton hW hWK
      (Subgroup.mul_mem _ (spSwapSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq i)
        (sAllSp_mem_normalizer hp0))
      (isMonomial_mul (isMonomial_spSwapSp i) isMonomial_sAllSp)
      (special_inr hcase.1 hcase.2) (exists_isMonomial_map_inr hp hp2 hn hpq i)

private theorem case_union_pairs (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hW : W = coordSpan (F := F) S)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    (hSne : S.Nonempty) (hSproper : S ≠ Set.univ)
    (hpair : ∀ i : Fin ℓ, (Sum.inl i ∈ S ↔ Sum.inr i ∈ S)) :
    ∀ k ∈ K, ∀ i : Fin ℓ, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ plane F i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ plane F i := by
  obtain ⟨i0, j0, hi0j0, hi0, hj0⟩ := exists_pair_support_data hSne hSproper hpair
  exact preserves_planes_of_pair hp hp2 hn hpq hW hWK
    (permSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq (Equiv.swap i0 j0))
    (isMonomial_permSp (Equiv.swap i0 j0))
    (special_pair hi0j0 hpair hi0 hj0)


theorem preserves_lines_or_planes (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1)
    {K : Subgroup ↥(StatedSp ℓ F)} {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hWV : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W)
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W) :
    (∀ k ∈ K, ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ c : F,
        spEnd k (Pi.single b (1 : F)) = c • Pi.single b (1 : F)) ∨
      (∀ k ∈ K, ∀ i : Fin ℓ, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ plane F i ∧
        spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ plane F i) := by
  classical
  have hW : W = coordSpan (F := F) (coordSupport W) :=
    eq_coordSpan_coordSupport hn hp hp2 hpq hWV
  set S := coordSupport W with hS
  have hSne : S.Nonempty := coordSupport_nonempty hn hp hp2 hpq hW0 hWV
  have hSproper : S ≠ Set.univ := coordSupport_ne_univ hn hp hp2 hpq hWtop hWV
  by_cases hhalf : ∃ i : Fin ℓ,
      (Sum.inl i ∈ S ∧ Sum.inr i ∉ S) ∨ (Sum.inr i ∈ S ∧ Sum.inl i ∉ S)
  · left
    exact case_half_pair hp hp2 hn hpq hW hWK hhalf
  · right
    push Not at hhalf
    have hpair : ∀ i : Fin ℓ, (Sum.inl i ∈ S ↔ Sum.inr i ∈ S) :=
      fun i => ⟨(hhalf i).1, (hhalf i).2⟩
    exact case_union_pairs hp hp2 hn hpq hW hWK hSne hSproper hpair

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
