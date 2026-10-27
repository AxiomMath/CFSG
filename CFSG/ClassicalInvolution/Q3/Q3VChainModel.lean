module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem spIncl_swap_symplectic (a b : Fin n) :
    (spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ * gram K n * spIncl (K := K) (⇑(Equiv.swap a b)) =
      gram K n := by
  have hσ : Function.Injective (⇑(Equiv.swap a b)) := (Equiv.swap a b).injective
  rw [Matrix.mul_assoc, gram_mul_spIncl, ← Matrix.mul_assoc, spIncl_transpose_mul hσ,
    Matrix.one_mul]

variable (K) in
@[expose] noncomputable def swapElt (a b : Fin n) : StatedSp n K :=
  ofSymplecticMat (spIncl (K := K) (⇑(Equiv.swap a b))) (spIncl_swap_symplectic a b)

theorem mat_swapElt (a b : Fin n) :
    mat n K (swapElt K a b) = spIncl (K := K) (⇑(Equiv.swap a b)) := rfl

theorem mat_swapElt_inv (a b : Fin n) :
    mat n K (swapElt K a b)⁻¹ = (spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ := by
  have h1 : mat n K (swapElt K a b) * mat n K (swapElt K a b)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [mat_swapElt] at h1
  have hP := spIncl_transpose_mul (K := K) (Equiv.swap a b).injective
  calc mat n K (swapElt K a b)⁻¹
      = ((spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ * spIncl (K := K) (⇑(Equiv.swap a b))) *
          mat n K (swapElt K a b)⁻¹ := by rw [hP, Matrix.one_mul]
    _ = (spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ *
          (spIncl (K := K) (⇑(Equiv.swap a b)) * mat n K (swapElt K a b)⁻¹) := by
        rw [Matrix.mul_assoc]
    _ = (spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ := by rw [h1, Matrix.mul_one]

theorem swapElt_mul_mul_inv (a b : Fin n) (g : StatedSp n K) :
    swapElt K a b * g * (swapElt K a b)⁻¹ =
      spEmbed (⇑(Equiv.swap a b)) (Equiv.swap a b).injective g := by
  apply mat_injective
  rw [map_mul, map_mul, mat_swapElt, mat_swapElt_inv, mat_spEmbed]
  have hPP : spIncl (K := K) (⇑(Equiv.swap a b)) * (spIncl (K := K) (⇑(Equiv.swap a b)))ᵀ = 1 :=
    mul_eq_one_comm.1 (spIncl_transpose_mul (K := K) (Equiv.swap a b).injective)
  rw [spEmbedMat]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP]
  abel

theorem swapElt_mul_longBlock_mul_inv (a b l : Fin n) (A : SL(2, K)) :
    swapElt K a b * longBlock K n l A * (swapElt K a b)⁻¹ =
      longBlock K n (Equiv.swap a b l) A := by
  rw [swapElt_mul_mul_inv, spEmbed_longBlock]

theorem swap_mem_union (a b : Fin n) {x : Fin n} (hx : x = a ∨ x = b) :
    Equiv.swap a b x = a ∨ Equiv.swap a b x = b := by
  rcases hx with rfl | rfl
  · exact Or.inr (Equiv.swap_apply_left _ _)
  · exact Or.inl (Equiv.swap_apply_right _ _)

theorem swapElt_mem_suppGroup (a b : Fin n) :
    swapElt K a b ∈ suppGroup (coords a ∪ coords b) := by
  rw [mem_suppGroup]
  intro r t hrt
  rw [mat_swapElt, spIncl_apply, Matrix.one_apply]
  by_cases ht : t ∈ coords a ∪ coords b
  · have hr : r ∉ coords a ∪ coords b := fun hr => hrt ⟨hr, ht⟩
    have h1 : Sum.map (⇑(Equiv.swap a b)) (⇑(Equiv.swap a b)) t ∈ coords a ∪ coords b := by
      rcases t with x | x
      · rw [Sum.map_inl, inl_mem_union_iff]
        exact swap_mem_union a b (inl_mem_union_iff.1 ht)
      · rw [Sum.map_inr, inr_mem_union_iff]
        exact swap_mem_union a b (inr_mem_union_iff.1 ht)
    have hne1 : r ≠ Sum.map (⇑(Equiv.swap a b)) (⇑(Equiv.swap a b)) t := fun h => hr (h ▸ h1)
    have hne2 : r ≠ t := fun h => hr (h ▸ ht)
    simp [hne1, hne2]
  · have h1 : Sum.map (⇑(Equiv.swap a b)) (⇑(Equiv.swap a b)) t = t := by
      rcases t with x | x
      · rw [Sum.map_inl]
        have hx : ¬ (x = a ∨ x = b) := fun h => ht (inl_mem_union_iff.2 h)
        rw [not_or] at hx
        rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]
      · rw [Sum.map_inr]
        have hx : ¬ (x = a ∨ x = b) := fun h => ht (inr_mem_union_iff.2 h)
        rw [not_or] at hx
        rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]
    rw [h1]

theorem commute_swapElt {a b : Fin n} {S : Set (Fin n ⊕ Fin n)} (hS : S ⊆ (coords a ∪ coords b)ᶜ)
    {x : StatedSp n K} (hx : x ∈ suppGroup S) : Commute (swapElt K a b) x :=
  commute_suppGroup_compl (swapElt_mem_suppGroup a b) (suppGroup_mono hS hx)

theorem coords_subset_compl_pair {a b k : Fin n} (hka : k ≠ a) (hkb : k ≠ b) :
    coords k ⊆ (coords a ∪ coords b)ᶜ := by
  intro t ht hmem
  rcases mem_coords.1 ht with rfl | rfl
  · rcases inl_mem_union_iff.1 hmem with h | h
    · exact hka h
    · exact hkb h
  · rcases inr_mem_union_iff.1 hmem with h | h
    · exact hka h
    · exact hkb h

theorem coords_pair_subset_compl_pair {a b c d : Fin n} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) : coords c ∪ coords d ⊆ (coords a ∪ coords b)ᶜ :=
  Set.union_subset (coords_subset_compl_pair hca hcb) (coords_subset_compl_pair hda hdb)

theorem commute_swapElt_longBlock {a b k : Fin n} (hka : k ≠ a) (hkb : k ≠ b) (A : SL(2, K)) :
    Commute (swapElt K a b) (longBlock K n k A) := by
  refine commute_swapElt (coords_subset_compl_pair hka hkb) ?_
  rw [← range_longBlock]
  exact ⟨A, rfl⟩

theorem commute_swapElt_pairEmbed_range {a b c d : Fin n} (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    ∀ x ∈ (pairEmbed K hcd).range, Commute (swapElt K a b) x := by
  intro x hx
  rw [range_pairEmbed] at hx
  exact commute_swapElt (coords_pair_subset_compl_pair hca hcb hda hdb) hx

theorem map_conj_swapElt_longBlock_left (a b : Fin n) :
    (longBlock K n a).range.map (MulAut.conj (swapElt K a b)).toMonoidHom =
      (longBlock K n b).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [swapElt_mul_longBlock_mul_inv, Equiv.swap_apply_left]
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    refine ⟨longBlock K n a A, ⟨A, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [swapElt_mul_longBlock_mul_inv, Equiv.swap_apply_left]

theorem map_conj_swapElt_longBlock_right (a b : Fin n) :
    (longBlock K n b).range.map (MulAut.conj (swapElt K a b)).toMonoidHom =
      (longBlock K n a).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [swapElt_mul_longBlock_mul_inv, Equiv.swap_apply_right]
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    refine ⟨longBlock K n b A, ⟨A, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [swapElt_mul_longBlock_mul_inv, Equiv.swap_apply_right]

theorem planeGroup_stdPlane_eq_range (k : Fin n) :
    planeGroup (stdPlane K n k) = (longBlock K n k).range :=
  planeGroup_stdPlane k

theorem map_map_conj_comm {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G)
    (S : Subgroup G) :
    (S.map (MulAut.conj g).toMonoidHom).map f = (S.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem map_map_conj_swapElt_left {G : Type*} [Group G] (C : StatedSp n K →* G) (a b : Fin n) :
    ((longBlock K n a).range.map C).map (MulAut.conj (C (swapElt K a b))).toMonoidHom =
      (longBlock K n b).range.map C := by
  rw [← map_map_conj_comm, map_conj_swapElt_longBlock_left]

theorem map_map_conj_swapElt_right {G : Type*} [Group G] (C : StatedSp n K →* G) (a b : Fin n) :
    ((longBlock K n b).range.map C).map (MulAut.conj (C (swapElt K a b))).toMonoidHom =
      (longBlock K n a).range.map C := by
  rw [← map_map_conj_comm, map_conj_swapElt_longBlock_right]

theorem commute_map_swapElt_longBlock {G : Type*} [Group G] (C : StatedSp n K →* G)
    {a b k : Fin n} (hka : k ≠ a) (hkb : k ≠ b) :
    ∀ y ∈ (longBlock K n k).range.map C, Commute (C (swapElt K a b)) y := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact (commute_swapElt_longBlock hka hkb A).map C

theorem commute_map_swapElt_pairEmbed_range {G : Type*} [Group G] (C : StatedSp n K →* G)
    {a b c d : Fin n} (hcd : c ≠ d) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    ∀ y ∈ (pairEmbed K hcd).range.map C, Commute (C (swapElt K a b)) y := by
  rintro _ ⟨x, hx, rfl⟩
  exact (commute_swapElt_pairEmbed_range hcd hca hcb hda hdb x hx).map C

variable (K) in
@[expose] noncomputable def shortSub (a b : Fin n) : Subgroup (StatedSp n K) :=
  if h : a = b then ⊥ else (shortBlock K h).range

theorem shortSub_of_ne {a b : Fin n} (h : a ≠ b) : shortSub K a b = (shortBlock K h).range :=
  dite_eq_right h

theorem shortSub_le_range_pairEmbed {a b : Fin n} (h : a ≠ b) :
    shortSub K a b ≤ (pairEmbed K h).range := by
  rw [shortSub_of_ne h, range_pairEmbed]
  exact shortBlock_range_le_suppGroup h

theorem exists_linearBlockStandardPair_shortSub {X : Type} [Group X] (Θ : StatedSp n K →* X)
    (hker : Θ.ker ≤ Subgroup.center (StatedSp n K)) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ∃ W, WeakCT.LinearBlockStandardPair K W ((shortSub K i j).map Θ) ((shortSub K j k).map Θ) := by
  rw [shortSub_of_ne hij, shortSub_of_ne hjk]
  exact (isLeviPair_shortBlock hij hjk hik).exists_linearBlockStandardPair_map Θ hker

theorem exists_symplecticBlockStandardPair_shortSub (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Type} [Group X] (Θ : StatedSp n K →* X)
    (hker : Θ.ker ≤ Subgroup.center (StatedSp n K)) :
    ∃ W, SymplecticBlockStandardPair K W ((longBlock K n b).range.map Θ)
      ((shortSub K a b).map Θ) := by
  rw [shortSub_of_ne hab]
  have hinj := injective_comp_pairEmbed hn hab Θ hker
  have e1 : (longBlock K 2 1).range.map (pairEmbed K hab) = (longBlock K n b).range := by
    rw [← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (spEmbed_comp_longBlock hab)
  have e2 : (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (pairEmbed K hab) =
      (shortBlock K hab).range := by
    rw [← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (spEmbed_comp_shortBlock hab)
  refine ⟨(Θ.comp (pairEmbed K hab)).range, Θ.comp (pairEmbed K hab), 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  · exact hinj.comp ((MulAut.conj _).injective.comp (longBlock_injective 1))
  · exact hinj.comp ((MulAut.conj _).injective.comp (shortBlock_injective _))
  · rw [map_conj_one, ← Subgroup.map_map, e1]
  · rw [map_conj_one, ← Subgroup.map_map, e2]

end CFSG.ClassicalInvolution.Q3.Q3V.Chain
