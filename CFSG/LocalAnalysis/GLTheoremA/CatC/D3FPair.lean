module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCoord

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def rA (i : D4Idx) : D4Vec := Pi.single i 1

@[expose] def rB (o : D4Idx) : D4Vec := rA o + rA 2

@[expose] def rC (o o' : D4Idx) : D4Vec := rA o + rA o' + rA 2

@[expose] def rT4 : D4Vec := ![1, 1, 1, 1]

@[expose] def rT5 : D4Vec := ![1, 1, 2, 1]

@[expose] def d4Pairs (h k : ℤ) (β : D4Vec) : Finset (D4Vec × D4Vec) :=
  ((d4RootsAt h) ×ˢ (d4RootsAt k)).filter fun p => p.1 + p.2 = β

theorem d4Pairs_11_B0 : d4Pairs 1 1 (rB 0) = {(rA 0, rA 2), (rA 2, rA 0)} := by decide +kernel
theorem d4Pairs_11_B1 : d4Pairs 1 1 (rB 1) = {(rA 1, rA 2), (rA 2, rA 1)} := by decide +kernel
theorem d4Pairs_11_B3 : d4Pairs 1 1 (rB 3) = {(rA 3, rA 2), (rA 2, rA 3)} := by decide +kernel

theorem d4Pairs_12_C01 : d4Pairs 1 2 (rC 0 1) = {(rA 0, rB 1), (rA 1, rB 0)} := by decide +kernel
theorem d4Pairs_12_C03 : d4Pairs 1 2 (rC 0 3) = {(rA 0, rB 3), (rA 3, rB 0)} := by decide +kernel
theorem d4Pairs_12_C13 : d4Pairs 1 2 (rC 1 3) = {(rA 1, rB 3), (rA 3, rB 1)} := by decide +kernel
theorem d4Pairs_21_C01 : d4Pairs 2 1 (rC 0 1) = {(rB 1, rA 0), (rB 0, rA 1)} := by decide +kernel
theorem d4Pairs_21_C03 : d4Pairs 2 1 (rC 0 3) = {(rB 3, rA 0), (rB 0, rA 3)} := by decide +kernel
theorem d4Pairs_21_C13 : d4Pairs 2 1 (rC 1 3) = {(rB 3, rA 1), (rB 1, rA 3)} := by decide +kernel
theorem d4Pairs_14_T5 : d4Pairs 1 4 rT5 = {(rA 2, rT4)} := by decide +kernel

section Evals

variable {K : Type} [Field K]


set_option linter.unusedSectionVars false

theorem isPos_rA (i : D4Idx) : IsRoot Tag.D4 (rA i) ∧ 0 < height (rA i) := by
  refine ⟨isRoot_single Tag.D4 i, ?_⟩
  have h := height_single (τ := Tag.D4) i
  exact lt_of_lt_of_eq one_pos h.symm

theorem isPos_rB : ∀ o ∈ ({0, 1, 3} : Finset (D4Idx)), IsRoot Tag.D4 (rB o) ∧ height (rB o) = 2 := by
  intro o ho
  refine ⟨mem_rootFinset.1 ?_, ?_⟩ <;> revert o <;> decide +kernel

theorem isPos_rC : ∀ o ∈ ({0, 1, 3} : Finset (D4Idx)), ∀ o' ∈ ({0, 1, 3} : Finset (D4Idx)),
    o ≠ o' → IsRoot Tag.D4 (rC o o') ∧ height (rC o o') = 3 := by
  intro o ho o' ho' hne
  refine ⟨mem_rootFinset.1 ?_, ?_⟩ <;> revert o o' <;> decide +kernel

theorem isPos_rT4 : IsRoot Tag.D4 rT4 ∧ height rT4 = 4 :=
  ⟨mem_rootFinset.1 (by decide +kernel), by decide +kernel⟩

theorem isPos_rT5 : IsRoot Tag.D4 rT5 ∧ height rT5 = 5 :=
  ⟨mem_rootFinset.1 (by decide +kernel), by decide +kernel⟩

@[expose] noncomputable def cc (γ δ : D4Vec) : K := (commConst Tag.D4 γ δ (1, 1) : K)

theorem mem_hs_pinnedX {h : ℤ} {γ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ ∧ h ≤ height γ)
    (c : K) : pinnedX Tag.D4 K γ c ∈ heightSeries Tag.D4 K h :=
  pinnedX_mem_rootSpan (S := {β | IsRoot Tag.D4 β ∧ 0 < height β ∧ h ≤ height β}) hγ c

theorem pc_pinnedX_same [Finite K] {γ δ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ) (hh : height γ = height δ) (c : K) :
    pc γ (pinnedX Tag.D4 K δ c) = if δ = γ then c else 0 := by
  rw [pc_of_pos hγ]
  split_ifs with h
  · subst h
    exact rootCoord_self hγ c
  · exact rootCoord_pinnedX_of_ne hγ hδ hh.le h c

theorem rootCoord_inv_d4 [Finite K] {γ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    {g : ModGL Tag.D4 K} (hg : g ∈ heightSeries Tag.D4 K (height γ)) :
    rootCoord hγ g⁻¹ = - rootCoord hγ g := by
  have h := rootCoord_mul hγ hg (inv_mem hg)
  rw [mul_inv_cancel, rootCoord_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem cc_antisymm [Finite K] {γ δ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ) (hne : γ ≠ δ) (hr : IsRoot Tag.D4 (γ + δ)) :
    cc (K := K) δ γ = - cc γ δ := by
  have hβ : IsRoot Tag.D4 (γ + δ) ∧ 0 < height (γ + δ) :=
    ⟨hr, by rw [d4_height_add]; omega⟩
  have hβ' : IsRoot Tag.D4 (δ + γ) ∧ 0 < height (δ + γ) := by
    rw [add_comm]; exact hβ
  have h1 : rootCoord hβ ⁅pinnedX Tag.D4 K γ 1, pinnedX Tag.D4 K δ 1⁆ = cc γ δ := by
    rw [rootCoord_commutator_pinnedX_d4 hγ hδ hβ (by rw [d4_height_add]) 1 1, if_pos rfl]
    simp [cc]
  have h2 : rootCoord hβ ⁅pinnedX Tag.D4 K δ 1, pinnedX Tag.D4 K γ 1⁆ = cc δ γ := by
    have := rootCoord_commutator_pinnedX_d4 (K := K) hδ hγ hβ (by rw [d4_height_add]; omega) 1 1
    rw [if_pos (add_comm δ γ)] at this
    rw [this]
    simp [cc]
  have hmem : ⁅pinnedX Tag.D4 K γ 1, pinnedX Tag.D4 K δ 1⁆ ∈
      heightSeries Tag.D4 K (height (γ + δ)) := by
    rw [d4_height_add]
    exact commutator_heightSeries_le K (height γ) (height δ)
      (Subgroup.commutator_mem_commutator (mem_hs_pinnedX ⟨hγ.1, hγ.2, le_rfl⟩ 1)
        (mem_hs_pinnedX ⟨hδ.1, hδ.2, le_rfl⟩ 1))
  have h3 : ⁅pinnedX Tag.D4 K δ 1, pinnedX Tag.D4 K γ 1⁆ =
      ⁅pinnedX Tag.D4 K γ 1, pinnedX Tag.D4 K δ 1⁆⁻¹ := (commutatorElement_inv _ _).symm
  rw [h3, rootCoord_inv_d4 hβ hmem, h1] at h2
  exact h2.symm

theorem cc_eq_one_or_neg_one {γ δ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ) (hne : γ ≠ δ) (hr : IsRoot Tag.D4 (γ + δ)) :
    cc (K := K) γ δ = 1 ∨ cc (K := K) γ δ = -1 := by
  have hτ : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
  have hneg : γ ≠ -δ := fun h => by
    have h1 := hγ.2
    have h2 := hδ.2
    rw [h, height_neg] at h1
    omega
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.D4 hτ hγ.1 hδ.1 hne hneg
  obtain ⟨hC, -⟩ := h1 hr
  rcases hC with h | h
  · left
    simp [cc, h]
  · right
    simp [cc, h]

theorem cc_ne_zero {γ δ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ) (hne : γ ≠ δ) (hr : IsRoot Tag.D4 (γ + δ)) :
    cc (K := K) γ δ ≠ 0 := by
  rcases cc_eq_one_or_neg_one (K := K) hγ hδ hne hr with h | h <;> rw [h]
  · exact one_ne_zero
  · exact neg_ne_zero.2 one_ne_zero

theorem cc_mul_self {γ δ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ) (hne : γ ≠ δ) (hr : IsRoot Tag.D4 (γ + δ)) :
    cc (K := K) γ δ * cc γ δ = 1 := by
  rcases cc_eq_one_or_neg_one (K := K) hγ hδ hne hr with h | h <;> rw [h] <;> ring

theorem rootCoord_commutator_pairs [Finite K] {h k : ℤ} (hh : 0 < h) (hk : 0 < k)
    {z w : ModGL Tag.D4 K} (hz : z ∈ heightSeries Tag.D4 K h) (hw : w ∈ heightSeries Tag.D4 K k)
    {β : D4Vec} (hβ : IsRoot Tag.D4 β ∧ 0 < height β) (hβh : height β = h + k) :
    rootCoord hβ ⁅z, w⁆ = ∑ p ∈ d4Pairs h k β, cc (K := K) p.1 p.2 * pc p.1 z * pc p.2 w := by
  rw [rootCoord_commutator_pair hh hk hz hw hβ hβh, d4Pairs, Finset.sum_filter,
    Finset.sum_product]
  rfl

theorem rootCoord_pairs_two [Finite K] {h k : ℤ} (hh : 0 < h) (hk : 0 < k)
    {z w : ModGL Tag.D4 K} (hz : z ∈ heightSeries Tag.D4 K h) (hw : w ∈ heightSeries Tag.D4 K k)
    {β : D4Vec} (hβ : IsRoot Tag.D4 β ∧ 0 < height β) (hβh : height β = h + k)
    {p₁ p₂ : D4Vec × D4Vec} (hP : d4Pairs h k β = {p₁, p₂}) (hne : p₁ ≠ p₂) :
    rootCoord hβ ⁅z, w⁆ = cc (K := K) p₁.1 p₁.2 * pc p₁.1 z * pc p₁.2 w +
      cc (K := K) p₂.1 p₂.2 * pc p₂.1 z * pc p₂.2 w := by
  rw [rootCoord_commutator_pairs hh hk hz hw hβ hβh, hP, Finset.sum_pair hne]

theorem rootCoord_pairs_one [Finite K] {h k : ℤ} (hh : 0 < h) (hk : 0 < k)
    {z w : ModGL Tag.D4 K} (hz : z ∈ heightSeries Tag.D4 K h) (hw : w ∈ heightSeries Tag.D4 K k)
    {β : D4Vec} (hβ : IsRoot Tag.D4 β ∧ 0 < height β) (hβh : height β = h + k)
    {p : D4Vec × D4Vec} (hP : d4Pairs h k β = {p}) :
    rootCoord hβ ⁅z, w⁆ = cc (K := K) p.1 p.2 * pc p.1 z * pc p.2 w := by
  rw [rootCoord_commutator_pairs hh hk hz hw hβ hβh, hP, Finset.sum_singleton]

theorem rA_inj : ∀ a b : D4Idx, rA a = rA b ↔ a = b := by decide +kernel

theorem height_rA (a : D4Idx) : height (rA a) = 1 := height_single (τ := Tag.D4) a

theorem pc_rA_pinnedX [Finite K] (a b : D4Idx) (c : K) :
    pc (rA a) (pinnedX Tag.D4 K (rA b) c) = if b = a then c else 0 := by
  rw [pc_pinnedX_same (isPos_rA a) (isPos_rA b) (by rw [height_rA, height_rA]) c]
  simp only [rA_inj]

theorem cc_jacobi [Finite K] {i j : D4Idx} (hi2 : i ≠ 2) (hj2 : j ≠ 2) (hij : i ≠ j)
    (hP11i : d4Pairs 1 1 (rB i) = {(rA i, rA 2), (rA 2, rA i)})
    (hP11j : d4Pairs 1 1 (rB j) = {(rA j, rA 2), (rA 2, rA j)})
    (hP21 : d4Pairs 2 1 (rC i j) = {(rB j, rA i), (rB i, rA j)})
    (hBi : IsRoot Tag.D4 (rB i) ∧ height (rB i) = 2)
    (hBj : IsRoot Tag.D4 (rB j) ∧ height (rB j) = 2)
    (hC : IsRoot Tag.D4 (rC i j) ∧ height (rC i j) = 3)
    (hcomm : Commute (pinnedX Tag.D4 K (rA i) 1) (pinnedX Tag.D4 K (rA j) 1)) :
    cc (K := K) (rB j) (rA i) * cc (rA j) (rA 2) = cc (rB i) (rA j) * cc (rA i) (rA 2) := by
  classical
  set x : ModGL Tag.D4 K := pinnedX Tag.D4 K (rA i) 1 with hx
  set y : ModGL Tag.D4 K := pinnedX Tag.D4 K (rA j) 1 with hy
  set z : ModGL Tag.D4 K := pinnedX Tag.D4 K (rA 2) 1 with hz
  have hxi : x⁻¹ = pinnedX Tag.D4 K (rA i) (-1) := pinnedX_neg Tag.D4 K _ _
  have hyi : y⁻¹ = pinnedX Tag.D4 K (rA j) (-1) := pinnedX_neg Tag.D4 K _ _
  have hzi : z⁻¹ = pinnedX Tag.D4 K (rA 2) (-1) := pinnedX_neg Tag.D4 K _ _
  have h1 : ∀ a : D4Idx, ∀ c : K, pinnedX Tag.D4 K (rA a) c ∈ heightSeries Tag.D4 K 1 :=
    fun a c => mem_hs_pinnedX ⟨(isPos_rA a).1, (isPos_rA a).2, by rw [height_rA]⟩ c
  have hU : ∀ a : D4Idx, ∀ c : K, pinnedX Tag.D4 K (rA a) c ∈ posUnipotent Tag.D4 K :=
    fun a c => heightSeries_le_posUnipotent 1 (h1 a c)
  have hcomm2 : ∀ a b : D4Idx, ∀ c d : K,
      ⁅pinnedX Tag.D4 K (rA a) c, pinnedX Tag.D4 K (rA b) d⁆ ∈ heightSeries Tag.D4 K 2 :=
    fun a b c d => commutator_heightSeries_le K 1 1
      (Subgroup.commutator_mem_commutator (h1 a c) (h1 b d))
  have hBi' : IsRoot Tag.D4 (rB i) ∧ 0 < height (rB i) := ⟨hBi.1, by omega⟩
  have hBj' : IsRoot Tag.D4 (rB j) ∧ 0 < height (rB j) := ⟨hBj.1, by omega⟩
  have hC' : IsRoot Tag.D4 (rC i j) ∧ 0 < height (rC i j) := ⟨hC.1, by omega⟩
  set W₂ : ModGL Tag.D4 K := ⁅z⁻¹, x⁻¹⁆ with hW₂
  have hW₂U : W₂ ∈ heightSeries Tag.D4 K 2 := by
    rw [hW₂, hzi, hxi]; exact hcomm2 _ _ _ _
  have hne1 : ((rA i, rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA i) := by
    intro h
    exact hi2 ((rA_inj _ _).1 (congrArg Prod.fst h))
  have hne2 : ((rA j, rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA j) := by
    intro h
    exact hj2 ((rA_inj _ _).1 (congrArg Prod.fst h))
  have hroot_i : IsRoot Tag.D4 (rA i + rA 2) := hBi.1
  have hroot_j : IsRoot Tag.D4 (rA j + rA 2) := hBj.1
  have hanti_i : cc (K := K) (rA 2) (rA i) = - cc (rA i) (rA 2) :=
    cc_antisymm (isPos_rA i) (isPos_rA 2) (fun h => hi2 ((rA_inj _ _).1 h)) hroot_i
  have hW₂i : pc (rB i) W₂ = cc (K := K) (rA 2) (rA i) := by
    rw [pc_of_pos hBi', hW₂, hzi, hxi,
      rootCoord_pairs_two (by norm_num) (by norm_num) (h1 2 _) (h1 i _) hBi'
        (by rw [hBi.2]; norm_num) hP11i hne1]
    simp [pc_rA_pinnedX, hi2, Ne.symm hi2]
  have hW₂j : pc (rB j) W₂ = 0 := by
    rw [pc_of_pos hBj', hW₂, hzi, hxi,
      rootCoord_pairs_two (by norm_num) (by norm_num) (h1 2 _) (h1 i _) hBj'
        (by rw [hBj.2]; norm_num) hP11j hne2]
    simp [pc_rA_pinnedX, hi2, Ne.symm hi2, hj2, Ne.symm hj2, hij, Ne.symm hij]
  set W₃ : ModGL Tag.D4 K := ⁅y⁻¹, z⁆ with hW₃
  have hW₃U : W₃ ∈ heightSeries Tag.D4 K 2 := by
    rw [hW₃, hyi, hz]; exact hcomm2 _ _ _ _
  have hW₃j : pc (rB j) W₃ = - cc (K := K) (rA j) (rA 2) := by
    rw [pc_of_pos hBj', hW₃, hyi, hz,
      rootCoord_pairs_two (by norm_num) (by norm_num) (h1 j _) (h1 2 _) hBj'
        (by rw [hBj.2]; norm_num) hP11j hne2]
    simp [pc_rA_pinnedX, hi2, Ne.symm hi2, hj2, Ne.symm hj2, hij, Ne.symm hij]
  have hW₃i : pc (rB i) W₃ = 0 := by
    rw [pc_of_pos hBi', hW₃, hyi, hz,
      rootCoord_pairs_two (by norm_num) (by norm_num) (h1 j _) (h1 2 _) hBi'
        (by rw [hBi.2]; norm_num) hP11i hne1]
    simp [pc_rA_pinnedX, hi2, Ne.symm hi2, hj2, Ne.symm hj2, hij, Ne.symm hij]
  have hne3 : ((rB j, rA i) : D4Vec × D4Vec) ≠ (rB i, rA j) := by
    intro h
    exact hij ((rA_inj _ _).1 (congrArg Prod.snd h))
  set T₂ : ModGL Tag.D4 K := ⁅W₂, y⁆ with hT₂
  set T₃ : ModGL Tag.D4 K := ⁅W₃, x⁻¹⁆ with hT₃
  have hT₂U : T₂ ∈ heightSeries Tag.D4 K (height (rC i j)) := by
    rw [hC.2]
    exact commutator_heightSeries_le K 2 1 (Subgroup.commutator_mem_commutator hW₂U (h1 j 1))
  have hT₃U : T₃ ∈ heightSeries Tag.D4 K (height (rC i j)) := by
    rw [hC.2]
    show ⁅W₃, x⁻¹⁆ ∈ heightSeries Tag.D4 K 3
    rw [hxi]
    exact commutator_heightSeries_le K 2 1
      (Subgroup.commutator_mem_commutator hW₃U (h1 i (-1)))
  have hT₂c : rootCoord hC' T₂ = cc (K := K) (rB i) (rA j) * cc (rA 2) (rA i) := by
    rw [hT₂, rootCoord_pairs_two (by norm_num) (by norm_num) hW₂U (h1 j 1) hC'
      (by rw [hC.2]; norm_num) hP21 hne3]
    simp only [pc_rA_pinnedX, hW₂i, hW₂j, hy]
    simp [hi2, Ne.symm hij, hij]
  have hT₃c : rootCoord hC' T₃ = cc (K := K) (rB j) (rA i) * cc (rA j) (rA 2) := by
    rw [hT₃, hxi, rootCoord_pairs_two (by norm_num) (by norm_num) hW₃U (h1 i (-1)) hC'
      (by rw [hC.2]; norm_num) hP21 hne3]
    simp only [pc_rA_pinnedX, hW₃i, hW₃j]
    simp [hij, Ne.symm hij]
  have hxy : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq
  have hHW := conj_commutatorElement_left_commutatorElement_mul x⁻¹ y z
  rw [inv_inv] at hHW
  have hHW2 : (z * T₂ * z⁻¹) * (y * T₃ * y⁻¹) = 1 := by
    have e : x⁻¹ * ⁅⁅x, y⁆, z⁆ * x * z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹ * y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹ =
        (z * T₂ * z⁻¹) * (y * T₃ * y⁻¹) := by
      rw [hxy, commutatorElement_one_left]
      simp only [hT₂, hT₃, hW₂, hW₃]
      group
    rw [← e]
    exact hHW
  have hzU : z ∈ posUnipotent Tag.D4 K := hU 2 1
  have hyU : y ∈ posUnipotent Tag.D4 K := hU j 1
  have hz₂ : z * T₂ * z⁻¹ ∈ heightSeries Tag.D4 K (height (rC i j)) :=
    (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hzU) T₂).1 hT₂U
  have hy₃ : y * T₃ * y⁻¹ ∈ heightSeries Tag.D4 K (height (rC i j)) :=
    (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hyU) T₃).1 hT₃U
  have hsum := congrArg (rootCoord hC') hHW2
  rw [rootCoord_mul hC' hz₂ hy₃, rootCoord_conj hC' hzU hT₂U, rootCoord_conj hC' hyU hT₃U,
    rootCoord_one, hT₂c, hT₃c, hanti_i] at hsum
  linear_combination hsum

theorem d4Pairs_11_gen : ∀ o : D4Idx, (o = 0 ∨ o = 1 ∨ o = 3) →
    d4Pairs 1 1 (rB o) = {(rA o, rA 2), (rA 2, rA o)} := by decide +kernel

theorem d4Pairs_12_gen : ∀ o' : D4Idx, (o' = 1 ∨ o' = 3) →
    d4Pairs 1 2 (rC 0 o') = {(rA 0, rB o'), (rA o', rB 0)} := by decide +kernel

theorem d4Pairs_21_gen : ∀ o' : D4Idx, (o' = 1 ∨ o' = 3) →
    d4Pairs 2 1 (rC 0 o') = {(rB o', rA 0), (rB 0, rA o')} := by decide +kernel

theorem not_isRoot_rA_add : ∀ i ∈ ({0, 1, 3} : Finset (D4Idx)), ∀ j ∈ ({0, 1, 3} : Finset (D4Idx)),
    i ≠ j → rA i + rA j ∉ rootFinset Tag.D4 := by decide +kernel

theorem commute_rA {i j : D4Idx} (hi : i = 0 ∨ i = 1 ∨ i = 3) (hj : j = 0 ∨ j = 1 ∨ j = 3)
    (hij : i ≠ j) : Commute (pinnedX Tag.D4 K (rA i) 1) (pinnedX Tag.D4 K (rA j) 1) := by
  have hτ : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
  have hne : rA i ≠ rA j := fun h => hij ((rA_inj _ _).1 h)
  have hneg : rA i ≠ -rA j := fun h => by
    have h1 := (isPos_rA i).2
    have h2 := (isPos_rA j).2
    rw [h, height_neg] at h1
    omega
  obtain ⟨-, h2⟩ := simply_laced_root_commutator_unit.{0} Tag.D4 hτ (isPos_rA i).1 (isPos_rA j).1
    hne hneg
  have hi' : i ∈ ({0, 1, 3} : Finset (D4Idx)) := by rcases hi with rfl | rfl | rfl <;> simp
  have hj' : j ∈ ({0, 1, 3} : Finset (D4Idx)) := by rcases hj with rfl | rfl | rfl <;> simp
  exact h2 (fun h => not_isRoot_rA_add i hi' j hj' hij (mem_rootFinset.2 h)) K _
    (mem_rootSubgroup.2 ⟨1, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)

theorem cc_jacobi_gen [Finite K] {o' : D4Idx} (ho' : o' = 1 ∨ o' = 3) :
    cc (K := K) (rB o') (rA 0) * cc (rA o') (rA 2) = cc (rB 0) (rA o') * cc (rA 0) (rA 2) := by
  have hne : (0 : D4Idx) ≠ o' := by rcases ho' with rfl | rfl <;> decide
  have h2 : o' ≠ 2 := by rcases ho' with rfl | rfl <;> decide
  exact cc_jacobi (by decide) h2 hne (d4Pairs_11_gen 0 (Or.inl rfl))
    (d4Pairs_11_gen o' (by rcases ho' with rfl | rfl <;> simp)) (d4Pairs_21_gen o' ho')
    (isPos_rB 0 (by simp)) (isPos_rB o' (by rcases ho' with rfl | rfl <;> simp))
    (isPos_rC 0 (by simp) o' (by rcases ho' with rfl | rfl <;> simp) hne)
    (commute_rA (Or.inl rfl) (by rcases ho' with rfl | rfl <;> simp) hne)

end Evals

end CFSG.LocalAnalysis.GLTheoremA
