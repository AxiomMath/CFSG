module

public import CFSG.ClassicalInvolution.WeakCT.WeylSigns
public import CFSG.ClassicalInvolution.WeakCT.SignedSL3

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement

@[expose] def zEdge : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

@[expose] def zNon : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

theorem zEdge_expPairs : ∀ z ∈ zEdge, ∀ w ∈ zEdge, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b →
    a • z + b • w ∈ zEdge → a = 1 ∧ b = 1 := by
  intro z hz w hw hzw a b ha hb h
  simp only [zEdge, Finset.mem_insert, Finset.mem_singleton] at hz hw h
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Prod.ext_iff] at hzw h ⊢ <;> omega

theorem zNon_expPairs : ∀ z ∈ zNon, ∀ w ∈ zNon, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b →
    a • z + b • w ∈ zNon → a = 1 ∧ b = 1 := by
  intro z hz w hw hzw a b ha hb h
  simp only [zNon, Finset.mem_insert, Finset.mem_singleton] at hz hw h
  rcases hz with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [Prod.ext_iff] at hzw h ⊢ <;> omega

@[expose] def Nz {r : ℕ} (F : Type) [Field F] (C : (Fin r → ℤ) → (Fin r → ℤ) → ℕ × ℕ → ℤ)
    (i j : Fin r) (z w : ℤ × ℤ) : F :=
  ((C (pair i j z) (pair i j w) (1, 1) : ℤ) : F)

@[expose] def rL (z : ℤ × ℤ) : ℤ × ℤ := (-z.1 + z.2, z.2)

@[expose] def rR (z : ℤ × ℤ) : ℤ × ℤ := (z.1, -z.2 + z.1)

section Pair

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

theorem reflection_pair_rL (hcij : D.cartan i j = -1) (z : ℤ × ℤ) :
    reflection D.cartan i (pair i j z) = pair i j (rL z) := by
  rw [reflection_pair_left j (D.isFiniteType.apply_self i), hcij]
  congr 1
  simp [rL]

theorem reflection_pair_rR (hcji : D.cartan j i = -1) (z : ℤ × ℤ) :
    reflection D.cartan j (pair i j z) = pair i j (rR z) := by
  rw [reflection_pair_right i (D.isFiniteType.apply_self j), hcji]
  congr 1
  simp [rR]

theorem sum_cartan_pair_left (hcij : D.cartan i j = -1) (z : ℤ × ℤ) :
    ∑ m, D.cartan i m * pair i j z m = 2 * z.1 - z.2 := by
  rw [← coroot_apply, pair_apply, map_add, map_zsmul, map_zsmul, coroot_single, coroot_single,
    D.isFiniteType.apply_self i, hcij]
  simp only [smul_eq_mul]
  ring

theorem sum_cartan_pair_right (hcji : D.cartan j i = -1) (z : ℤ × ℤ) :
    ∑ m, D.cartan j m * pair i j z m = 2 * z.2 - z.1 := by
  rw [← coroot_apply, pair_apply, map_add, map_zsmul, map_zsmul, coroot_single, coroot_single,
    D.isFiniteType.apply_self j, hcji]
  simp only [smul_eq_mul]
  ring

theorem pair_mem_roots_zEdge (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1) :
    ∀ z ∈ zEdge, pair i j z ∈ D.roots := by
  have h10 : pair i j (1, 0) ∈ D.roots := by rw [pair_one_zero]; exact single_mem_roots i
  have h01 : pair i j (0, 1) ∈ D.roots := by rw [pair_zero_one]; exact single_mem_roots j
  have hLi : ∀ z, pair i j z ∈ D.roots → pair i j (-z.1 + z.2, z.2) ∈ D.roots := fun z h => by
    have := reflection_mem_roots i h
    rwa [reflection_pair_left j (D.isFiniteType.apply_self i), hcij, neg_one_mul, sub_neg_eq_add]
      at this
  have hLj : ∀ z, pair i j z ∈ D.roots → pair i j (z.1, -z.2 + z.1) ∈ D.roots := fun z h => by
    have := reflection_mem_roots j h
    rwa [reflection_pair_right i (D.isFiniteType.apply_self j), hcji, neg_one_mul,
      sub_neg_eq_add] at this
  simp only [zEdge, Finset.mem_insert, Finset.mem_singleton]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact h10
  · simpa using hLi _ h10
  · exact h01
  · simpa using hLj _ h01
  · simpa using hLj _ h10
  · simpa using hLi _ (hLj _ h01)

theorem pair_mem_roots_zNon : ∀ z ∈ zNon, pair i j z ∈ D.roots := by
  simp only [zNon, Finset.mem_insert, Finset.mem_singleton]
  rintro z (rfl | rfl | rfl | rfl)
  · rw [pair_one_zero]; exact single_mem_roots i
  · rw [pair_neg_one_zero]; exact neg_mem_roots (single_mem_roots i)
  · rw [pair_zero_one]; exact single_mem_roots j
  · rw [pair_zero_neg_one]; exact neg_mem_roots (single_mem_roots j)

theorem commutator_pair' (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j)
    {Z : Finset (ℤ × ℤ)} (hsub : pairRoots D i j ⊆ pair i j '' Z)
    (hroot : ∀ z ∈ Z, pair i j z ∈ D.roots)
    (hZ : ∀ z ∈ Z, ∀ w ∈ Z, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b → a • z + b • w ∈ Z →
      a = 1 ∧ b = 1)
    {z w : ℤ × ℤ} (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z + w ≠ 0) (c d : F) :
    (z + w ∈ Z → ⁅x (pair i j z) c, x (pair i j w) d⁆ =
      x (pair i j (z + w)) (Nz F C i j z w * c * d)) ∧
      (z + w ∉ Z → ⁅x (pair i j z) c, x (pair i j w) d⁆ = 1) := by
  have hne : pair i j z + pair i j w ≠ 0 := by
    rw [← map_add, ← map_zero (pair i j)]
    exact fun h => hzw (pair_injective hij h)
  have hexp : ∀ a b : ℕ, 0 < a → 0 < b → a • pair i j z + b • pair i j w ∈ D.roots →
      a = 1 ∧ b = 1 := by
    intro a b ha hb h
    rw [← map_nsmul, ← map_nsmul, ← map_add] at h
    exact hZ z hz w hw hzw a b ha hb (mem_of_pair_mem hij hsub h)
  obtain ⟨h1, h2⟩ := commutator_eq hE (hroot z hz) (hroot w hw) hne hexp c d
  rw [← map_add] at h1 h2
  exact ⟨fun hs => h1 (hroot _ hs), fun hs => h2 fun h => hs (mem_of_pair_mem hij hsub h)⟩

end Pair

section A2

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) (hij : i ≠ j)
  (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1)

include hdiv hcij hcji in
theorem rel_A2 (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) {z w u : ℤ × ℤ}
    (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w = u) (hu : u ∈ zEdge) (s t : F) :
    ⁅x (pair i j z) s, x (pair i j w) t⁆ = x (pair i j u) (Nz F C i j z w * s * t) := by
  have hsub : pairRoots D i j ⊆ pair i j '' zEdge :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  subst hzw
  exact (commutator_pair' hE hij hsub (pair_mem_roots_zEdge hcij hcji) zEdge_expPairs hz hw
    (fun h => by rw [h] at hu; exact absurd hu (by decide)) s t).1 hu

include hdiv hcij hcji in
theorem commute_A2 (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) {z w : ℤ × ℤ}
    (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ≠ 0) (hu : z + w ∉ zEdge) (s t : F) :
    Commute (x (pair i j z) s) (x (pair i j w) t) := by
  have hsub : pairRoots D i j ⊆ pair i j '' zEdge :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  exact commutatorElement_eq_one_iff_commute.1
    ((commutator_pair' hE hij hsub (pair_mem_roots_zEdge hcij hcji) zEdge_expPairs hz hw hzw s
      t).2 hu)

include hdiv hcij hcji in
theorem Nz_swap (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) {z w u : ℤ × ℤ}
    (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w = u) (hu : u ∈ zEdge) :
    Nz F C i j w z = -Nz F C i j z w := by
  have hur : pair i j u ∈ D.roots := pair_mem_roots_zEdge hcij hcji u hu
  have h1 := rel_A2 hdiv hcij hcji hE hij hz hw hzw hu 1 1
  have h2 := rel_A2 hdiv hcij hcji hE hij hw hz (by rw [add_comm]; exact hzw) hu 1 1
  have h3 : ⁅x (pair i j w) 1, x (pair i j z) 1⁆ = (⁅x (pair i j z) 1, x (pair i j w) 1⁆)⁻¹ :=
    (commutatorElement_inv _ _).symm
  rw [h3, h1, ← map_neg_of_add (hE.param _ hur).2.1] at h2
  have h4 := (hE.param _ hur).2.2 h2
  linear_combination -h4

include hdiv hcij hcji in
theorem wsign_comm_left (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) {z w : ℤ × ℤ}
    (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ∈ zEdge) (hz' : rL z ∈ zEdge)
    (hw' : rL w ∈ zEdge) (hzw' : rL z + rL w ∈ zEdge) :
    Nz F C i j (rL z) (rL w) * wsign hE i (pair i j z) * wsign hE i (pair i j w) =
      wsign hE i (pair i j (z + w)) * Nz F C i j z w := by
  have hr := pair_mem_roots_zEdge hcij hcji
  have h := wsign_comm hE (k := i) (z := pair i j z) (w := pair i j w) (hr z hz) (hr w hw)
    (by rw [← map_add]; exact hr _ hzw) (N := Nz F C i j z w) (N' := Nz F C i j (rL z) (rL w))
    (fun c d => by
      rw [← map_add]
      exact rel_A2 hdiv hcij hcji hE hij hz hw rfl hzw c d)
    (fun c d => by
      rw [reflection_pair_rL hcij, reflection_pair_rL hcij, ← map_add]
      exact rel_A2 hdiv hcij hcji hE hij hz' hw' rfl hzw' c d)
  rwa [← map_add] at h

include hdiv hcij hcji in
theorem wsign_comm_right (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) {z w : ℤ × ℤ}
    (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ∈ zEdge) (hz' : rR z ∈ zEdge)
    (hw' : rR w ∈ zEdge) (hzw' : rR z + rR w ∈ zEdge) :
    Nz F C i j (rR z) (rR w) * wsign hE j (pair i j z) * wsign hE j (pair i j w) =
      wsign hE j (pair i j (z + w)) * Nz F C i j z w := by
  have hr := pair_mem_roots_zEdge hcij hcji
  have h := wsign_comm hE (k := j) (z := pair i j z) (w := pair i j w) (hr z hz) (hr w hw)
    (by rw [← map_add]; exact hr _ hzw) (N := Nz F C i j z w) (N' := Nz F C i j (rR z) (rR w))
    (fun c d => by
      rw [← map_add]
      exact rel_A2 hdiv hcij hcji hE hij hz hw rfl hzw c d)
    (fun c d => by
      rw [reflection_pair_rR hcji, reflection_pair_rR hcji, ← map_add]
      exact rel_A2 hdiv hcij hcji hE hij hz' hw' rfl hzw' c d)
  rwa [← map_add] at h

include hcij hcji in
theorem wsign_rL (hE : Steinberg.ChevalleyExtras D F x C O) {z : ℤ × ℤ} (hz : z ∈ zEdge)
    (hodd : Odd (2 * z.1 - z.2)) :
    wsign hE i (pair i j (rL z)) = -wsign hE i (pair i j z) := by
  have h := wsign_reflection hE (k := i) (pair_mem_roots_zEdge hcij hcji z hz)
    (by rw [sum_cartan_pair_left hcij]; exact hodd)
  rwa [reflection_pair_rL hcij] at h

include hcij hcji in
theorem wsign_rR (hE : Steinberg.ChevalleyExtras D F x C O) {z : ℤ × ℤ} (hz : z ∈ zEdge)
    (hodd : Odd (2 * z.2 - z.1)) :
    wsign hE j (pair i j (rR z)) = -wsign hE j (pair i j z) := by
  have h := wsign_reflection hE (k := j) (pair_mem_roots_zEdge hcij hcji z hz)
    (by rw [sum_cartan_pair_right hcji]; exact hodd)
  rwa [reflection_pair_rR hcji] at h

theorem wsign_left_one_zero (hE : Steinberg.ChevalleyExtras D F x C O) :
    wsign hE i (pair i j (1, 0)) = -1 := by
  rw [pair_one_zero]
  exact wsign_single_self hE i

theorem wsign_right_zero_one (hE : Steinberg.ChevalleyExtras D F x C O) :
    wsign hE j (pair i j (0, 1)) = -1 := by
  rw [pair_zero_one]
  exact wsign_single_self hE j

include hdiv hcij hcji in
theorem sign_A (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) :
    Nz F C i j (-1, 0) (1, 1) = Nz F C i j (1, 0) (0, 1) := by
  have h := wsign_comm_left hdiv hcij hcji hE hij (z := (1, 0)) (w := (0, 1)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : rL (1, 0) = (-1, 0) := by decide
  have e2 : rL (0, 1) = (1, 1) := by decide
  have e3 : ((1 : ℤ), (0 : ℤ)) + (0, 1) = (1, 1) := by decide
  rw [e1, e2, e3] at h
  have hc : wsign hE i (pair i j (1, 1)) = -wsign hE i (pair i j (0, 1)) := by
    have h' := wsign_rL hcij hcji hE (z := (0, 1)) (by decide) ⟨-1, by norm_num⟩
    rwa [e2] at h'
  rw [wsign_left_one_zero hE, hc] at h
  have hb := wsign_ne_zero hE (k := i) (pair_mem_roots_zEdge hcij hcji (0, 1) (by decide))
  apply mul_left_cancel₀ hb
  linear_combination -h

include hdiv hcij hcji in
theorem sign_B (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) :
    Nz F C i j (1, 0) (-1, -1) = Nz F C i j (-1, 0) (0, -1) := by
  have h := wsign_comm_left hdiv hcij hcji hE hij (z := (1, 0)) (w := (-1, -1)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : rL (1, 0) = (-1, 0) := by decide
  have e2 : rL (-1, -1) = (0, -1) := by decide
  have e3 : ((1 : ℤ), (0 : ℤ)) + (-1, -1) = (0, -1) := by decide
  have e4 : rL (0, -1) = (-1, -1) := by decide
  rw [e1, e2, e3] at h
  have hc : wsign hE i (pair i j (-1, -1)) = -wsign hE i (pair i j (0, -1)) := by
    have h' := wsign_rL hcij hcji hE (z := (0, -1)) (by decide) ⟨0, by norm_num⟩
    rwa [e4] at h'
  rw [wsign_left_one_zero hE, hc] at h
  have hb := wsign_ne_zero hE (k := i) (pair_mem_roots_zEdge hcij hcji (0, -1) (by decide))
  apply mul_left_cancel₀ hb
  linear_combination -h

include hdiv hcij hcji in
theorem sign_C (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) :
    Nz F C i j (0, 1) (-1, -1) = -Nz F C i j (-1, 0) (0, -1) := by
  have h := wsign_comm_right hdiv hcij hcji hE hij (z := (0, 1)) (w := (-1, -1)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : rR (0, 1) = (0, -1) := by decide
  have e2 : rR (-1, -1) = (-1, 0) := by decide
  have e3 : ((0 : ℤ), (1 : ℤ)) + (-1, -1) = (-1, 0) := by decide
  have e4 : rR (-1, 0) = (-1, -1) := by decide
  rw [e1, e2, e3] at h
  have hc : wsign hE j (pair i j (-1, -1)) = -wsign hE j (pair i j (-1, 0)) := by
    have h' := wsign_rR hcij hcji hE (z := (-1, 0)) (by decide) ⟨0, by norm_num⟩
    rwa [e4] at h'
  rw [wsign_right_zero_one hE, hc] at h
  have hb := wsign_ne_zero hE (k := j) (pair_mem_roots_zEdge hcij hcji (-1, 0) (by decide))
  have h5 : Nz F C i j (0, -1) (-1, 0) = Nz F C i j (0, 1) (-1, -1) := by
    apply mul_left_cancel₀ hb
    linear_combination h
  have h6 := Nz_swap hdiv hcij hcji hE hij (z := (-1, 0)) (w := (0, -1)) (u := (-1, -1))
    (by decide) (by decide) (by decide) (by decide)
  rw [h6] at h5
  linear_combination -h5

include hdiv hcij hcji in
theorem sign_D (hE : Steinberg.ChevalleyExtras D F x C O) (hij : i ≠ j) :
    Nz F C i j (0, -1) (1, 1) = -Nz F C i j (1, 0) (0, 1) := by
  have h := wsign_comm_right hdiv hcij hcji hE hij (z := (1, 0)) (w := (0, 1)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : rR (1, 0) = (1, 1) := by decide
  have e2 : rR (0, 1) = (0, -1) := by decide
  have e3 : ((1 : ℤ), (0 : ℤ)) + (0, 1) = (1, 1) := by decide
  rw [e1, e2, e3] at h
  have hc : wsign hE j (pair i j (1, 1)) = -wsign hE j (pair i j (1, 0)) := by
    have h' := wsign_rR hcij hcji hE (z := (1, 0)) (by decide) ⟨-1, by norm_num⟩
    rwa [e1] at h'
  rw [wsign_right_zero_one hE, hc] at h
  have hb := wsign_ne_zero hE (k := j) (pair_mem_roots_zEdge hcij hcji (1, 0) (by decide))
  have h5 : Nz F C i j (1, 1) (0, -1) = Nz F C i j (1, 0) (0, 1) := by
    apply mul_left_cancel₀ hb
    linear_combination -h
  have h6 := Nz_swap hdiv hcij hcji hE hij (z := (0, -1)) (w := (1, 1)) (u := (1, 0))
    (by decide) (by decide) (by decide) (by decide)
  linear_combination h6 - h5

end A2

end CFSG.ClassicalInvolution.WeakCT
