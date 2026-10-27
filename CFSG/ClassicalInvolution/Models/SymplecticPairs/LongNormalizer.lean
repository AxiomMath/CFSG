module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_elt_positiveLong mat_elt_negativeLong)
open scoped MatrixGroups

variable {K : Type} [Field K] {r : ℕ}

private theorem eq_zero_of_forall_longBlock_mulVec_eq {m : ℕ} {w : Fin m ⊕ Fin m → K}
    {j : Fin m}
    (hw : ∀ x ∈ (longBlock K m j).range, mat m K x *ᵥ w = w)
    {u : Fin m ⊕ Fin m} (hu : u ∈ coords j) : w u = 0 := by
  have hpos : w (Sum.inl j) + w (Sum.inr j) = w (Sum.inl j) := by
    have h := congrFun (hw _ ⟨sl2Upper 1, longBlock_sl2Upper j 1⟩) (Sum.inl j)
    rw [mat_elt_positiveLong, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec] at h
    simpa [Pi.add_apply] using h
  have hneg : w (Sum.inr j) + w (Sum.inl j) = w (Sum.inr j) := by
    have h := congrFun (hw _ ⟨sl2Lower 1, longBlock_sl2Lower j 1⟩) (Sum.inr j)
    rw [mat_elt_negativeLong, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec] at h
    simpa [Pi.add_apply] using h
  rcases mem_coords.1 hu with rfl | rfl
  · exact add_eq_left.1 hneg
  · exact add_eq_left.1 hpos

private theorem mat_inv_apply_eq_zero_of_normalizes {m : ℕ} {A : StatedSp m K} {j : Fin m}
    (hA : ∀ x ∈ (longBlock K m j).range,
      A * x * A⁻¹ ∈ (longBlock K m j).range)
    {u t : Fin m ⊕ Fin m} (hu : u ∈ coords j)
    (ht : t ∉ coords j) : mat m K A⁻¹ u t = 0 := by
  classical
  have hG : (longBlock K m j).range =
      fixing {v : Fin m ⊕ Fin m → K | ∀ s ∈ coords j, v s = 0} := by
    rw [range_longBlock, fixing_supported_eq (parClosed_coords j)]
  have he : (Pi.single t 1 : Fin m ⊕ Fin m → K) ∈
      {v : Fin m ⊕ Fin m → K | ∀ s ∈ coords j, v s = 0} := by
    intro s hs
    exact Pi.single_eq_of_ne (x := 1) (show s ≠ t from fun h => ht (h ▸ hs))
  have hfix : ∀ x ∈ (longBlock K m j).range,
      mat m K x *ᵥ (mat m K A⁻¹ *ᵥ Pi.single t 1) =
        mat m K A⁻¹ *ᵥ Pi.single t 1 := by
    intro x hx
    have h1 : (mat m K A * mat m K x * mat m K A⁻¹) *ᵥ Pi.single t 1 =
        Pi.single t 1 := by
      rw [← map_mul, ← map_mul]
      exact (mem_fixing.1 (hG ▸ hA x hx)) _ he
    have h2 : mat m K A *ᵥ (mat m K x *ᵥ
          (mat m K A⁻¹ *ᵥ Pi.single t 1)) =
        mat m K A *ᵥ (mat m K A⁻¹ *ᵥ Pi.single t 1) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, mulVec_mulVec_inv]
    have h2' := congrArg (fun z => mat m K A⁻¹ *ᵥ z) h2
    simpa only [mulVec_inv_mulVec] using h2'
  have hw := eq_zero_of_forall_longBlock_mulVec_eq hfix hu
  rwa [mulVec_single_one_apply] at hw

private theorem last_coords_not_mem_range_castSucc :
    ((Sum.inl (Fin.last (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2)) ∉
        Set.range (Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
          (Fin.castSucc : Fin (r + 1) → Fin (r + 2)))) ∧
      ((Sum.inr (Fin.last (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2)) ∉
        Set.range (Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
          (Fin.castSucc : Fin (r + 1) → Fin (r + 2)))) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases x with y | y
    · rw [Sum.map_inl] at hx
      have h := congrArg Fin.val (Sum.inl_injective hx)
      simp only [Fin.val_castSucc, Fin.val_last] at h
      omega
    · rw [Sum.map_inr] at hx
      exact Sum.inr_ne_inl hx
  · rintro ⟨x, hx⟩
    rcases x with y | y
    · rw [Sum.map_inl] at hx
      exact Sum.inl_ne_inr hx
    · rw [Sum.map_inr] at hx
      have h := congrArg Fin.val (Sum.inr_injective hx)
      simp only [Fin.val_castSucc, Fin.val_last] at h
      omega

private theorem exists_castSucc_of_notMem_range {t : Fin (r + 2) ⊕ Fin (r + 2)}
    (ht : t ∉ Set.range (Sum.map (Fin.natAdd r) (Fin.natAdd r))) :
    ∃ t' : Fin (r + 1) ⊕ Fin (r + 1), t' ∉ coords (Fin.last r) ∧
      Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
        (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) t' = t := by
  rcases t with a | a
  · have ha : a ∉ Set.range (Fin.natAdd r) := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact ht ⟨Sum.inl i, by rw [Sum.map_inl, hi]⟩
    rw [Fin.range_natAdd] at ha
    simp only [Set.mem_setOf_eq, not_le] at ha
    refine ⟨Sum.inl ⟨a.val, by omega⟩, ?_, ?_⟩
    · intro hc
      rcases mem_coords.1 hc with h | h
      · have hv' := congrArg Fin.val (Sum.inl_injective h)
        simp only [Fin.val_last] at hv'
        omega
      · exact Sum.inl_ne_inr h
    · rw [Sum.map_inl]
      exact congrArg Sum.inl (Fin.ext (by simp))
  · have ha : a ∉ Set.range (Fin.natAdd r) := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact ht ⟨Sum.inr i, by rw [Sum.map_inr, hi]⟩
    rw [Fin.range_natAdd] at ha
    simp only [Set.mem_setOf_eq, not_le] at ha
    refine ⟨Sum.inr ⟨a.val, by omega⟩, ?_, ?_⟩
    · intro hc
      rcases mem_coords.1 hc with h | h
      · exact Sum.inr_ne_inl h
      · have hv' := congrArg Fin.val (Sum.inr_injective h)
        simp only [Fin.val_last] at hv'
        omega
    · rw [Sum.map_inr]
      exact congrArg Sum.inr (Fin.ext (by simp))

private theorem inl_mem_range_natAdd {a : Fin (r + 2)}
    (h : (Sum.inl a : Fin (r + 2) ⊕ Fin (r + 2)) ∈
      Set.range (Sum.map (Fin.natAdd r) (Fin.natAdd r))) :
    a ∈ Set.range (Fin.natAdd r) := by
  obtain ⟨w, hw⟩ := h
  rcases w with i | i
  · rw [Sum.map_inl] at hw
    exact ⟨i, Sum.inl_injective hw⟩
  · rw [Sum.map_inr] at hw
    exact absurd hw (Sum.inr_ne_inl)

private theorem inr_mem_range_natAdd {a : Fin (r + 2)}
    (h : (Sum.inr a : Fin (r + 2) ⊕ Fin (r + 2)) ∈
      Set.range (Sum.map (Fin.natAdd r) (Fin.natAdd r))) :
    a ∈ Set.range (Fin.natAdd r) := by
  obtain ⟨w, hw⟩ := h
  rcases w with i | i
  · rw [Sum.map_inl] at hw
    exact absurd hw (Sum.inl_ne_inr)
  · rw [Sum.map_inr] at hw
    exact ⟨i, Sum.inr_injective hw⟩

private theorem spEmbedMat_inv_apply_eq_zero {A : StatedSp (r + 1) K}
    (hA : ∀ x ∈ (longBlock K (r + 1) (Fin.last r)).range,
      A * x * A⁻¹ ∈ (longBlock K (r + 1) (Fin.last r)).range)
    {v t : Fin (r + 2) ⊕ Fin (r + 2)}
    (hv : v ∈ Set.range (Sum.map (Fin.natAdd r) (Fin.natAdd r)))
    (ht : t ∉ Set.range (Sum.map (Fin.natAdd r) (Fin.natAdd r))) :
    spEmbedMat (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) (mat (r + 1) K A⁻¹) v t = 0 := by
  obtain ⟨hlastL, hlastR⟩ := last_coords_not_mem_range_castSucc (r := r)
  obtain ⟨t', ht', rfl⟩ := exists_castSucc_of_notMem_range ht
  rcases v with a | a
  · have ha := inl_mem_range_natAdd hv
    rw [Fin.range_natAdd] at ha
    simp only [Set.mem_setOf_eq] at ha
    rcases Nat.lt_or_ge a.val (r + 1) with hlt | hge
    · have har : a.val = r := by omega
      have haeq : a = (Fin.last r).castSucc :=
        Fin.ext (by rw [Fin.val_castSucc, Fin.val_last]; exact har)
      rw [haeq]
      rw [show (Sum.inl ((Fin.last r).castSucc) : Fin (r + 2) ⊕ Fin (r + 2)) =
          Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
            (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) (Sum.inl (Fin.last r)) from by
        rw [Sum.map_inl]]
      rw [spEmbedMat_apply_image (Fin.castSucc_injective (r + 1)) (mat (r + 1) K A⁻¹)
        (Sum.inl (Fin.last r)) t']
      exact mat_inv_apply_eq_zero_of_normalizes hA (inl_mem_coords _) ht'
    · have har : a.val = r + 1 := by omega
      have haeq : a = Fin.last (r + 1) :=
        Fin.ext (by rw [Fin.val_last]; exact har)
      rw [haeq]
      rw [spEmbedMat_apply_of_not_mem (g := mat (r + 1) K A⁻¹) (fun h => hlastL h.1)]
      exact Matrix.one_apply_ne (show (Sum.inl (Fin.last (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2)) ≠
        Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
          (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) t' from fun h => hlastL (h ▸ ⟨t', rfl⟩))
  · have ha := inr_mem_range_natAdd hv
    rw [Fin.range_natAdd] at ha
    simp only [Set.mem_setOf_eq] at ha
    rcases Nat.lt_or_ge a.val (r + 1) with hlt | hge
    · have har : a.val = r := by omega
      have haeq : a = (Fin.last r).castSucc :=
        Fin.ext (by rw [Fin.val_castSucc, Fin.val_last]; exact har)
      rw [haeq]
      rw [show (Sum.inr ((Fin.last r).castSucc) : Fin (r + 2) ⊕ Fin (r + 2)) =
          Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
            (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) (Sum.inr (Fin.last r)) from by
        rw [Sum.map_inr]]
      rw [spEmbedMat_apply_image (Fin.castSucc_injective (r + 1)) (mat (r + 1) K A⁻¹)
        (Sum.inr (Fin.last r)) t']
      exact mat_inv_apply_eq_zero_of_normalizes hA (inr_mem_coords _) ht'
    · have har : a.val = r + 1 := by omega
      have haeq : a = Fin.last (r + 1) :=
        Fin.ext (by rw [Fin.val_last]; exact har)
      rw [haeq]
      rw [spEmbedMat_apply_of_not_mem (g := mat (r + 1) K A⁻¹) (fun h => hlastR h.1)]
      exact Matrix.one_apply_ne (show (Sum.inr (Fin.last (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2)) ≠
        Sum.map (Fin.castSucc : Fin (r + 1) → Fin (r + 2))
          (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) t' from fun h => hlastR (h ▸ ⟨t', rfl⟩))

theorem spEmbed_castSucc_conj_mem_range_spEmbed_natAdd {A : StatedSp (r + 1) K}
    (hA : ∀ x ∈ (longBlock K (r + 1) (Fin.last r)).range,
      A * x * A⁻¹ ∈ (longBlock K (r + 1) (Fin.last r)).range)
    {y : StatedSp (r + 2) K}
    (hy : y ∈ (spEmbed (Fin.natAdd r : Fin 2 → Fin (r + 2)) (Fin.natAdd_injective 2 r)).range) :
    spEmbed Fin.castSucc (Fin.castSucc_injective (r + 1)) A * y *
        (spEmbed Fin.castSucc (Fin.castSucc_injective (r + 1)) A)⁻¹ ∈
      (spEmbed (Fin.natAdd r : Fin 2 → Fin (r + 2)) (Fin.natAdd_injective 2 r)).range := by
  classical
  set A' : StatedSp (r + 2) K := spEmbed Fin.castSucc (Fin.castSucc_injective (r + 1)) A with hA'
  have hA'inv : A'⁻¹ = spEmbed Fin.castSucc (Fin.castSucc_injective (r + 1)) A⁻¹ := by
    rw [hA', ← map_inv]
  have hB : mat (r + 2) K A'⁻¹ =
      spEmbedMat (Fin.castSucc : Fin (r + 1) → Fin (r + 2)) (mat (r + 1) K A⁻¹) := by
    rw [hA'inv, mat_spEmbed]
  have hrange : (spEmbed (K := K) (Fin.natAdd r : Fin 2 → Fin (r + 2))
        (Fin.natAdd_injective 2 r)).range =
      suppGroup (K := K) (Set.range (Sum.map (Fin.natAdd r : Fin 2 → Fin (r + 2))
        (Fin.natAdd r : Fin 2 → Fin (r + 2)))) :=
    range_spEmbed (Fin.natAdd_injective 2 r)
  rw [hrange] at hy ⊢
  have hS : ParClosed (Set.range (Sum.map (Fin.natAdd r : Fin 2 → Fin (r + 2))
      (Fin.natAdd r : Fin 2 → Fin (r + 2)))) := by
    rintro _ ⟨w, rfl⟩
    rcases w with w | w
    · exact ⟨Sum.inr w, rfl⟩
    · exact ⟨Sum.inl w, rfl⟩
  rw [mem_suppGroup_iff hS]
  intro t ht u
  have hkey : ∀ w, (mat (r + 2) K y * mat (r + 2) K A'⁻¹) w t = mat (r + 2) K A'⁻¹ w t := by
    intro w
    rw [Matrix.mul_apply]
    calc ∑ v, mat (r + 2) K y w v * mat (r + 2) K A'⁻¹ v t
        = ∑ v, (1 : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
            (Fin (r + 2) ⊕ Fin (r + 2)) K) w v * mat (r + 2) K A'⁻¹ v t := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases hv : v ∈ Set.range (Sum.map (Fin.natAdd r : Fin 2 → Fin (r + 2))
              (Fin.natAdd r : Fin 2 → Fin (r + 2)))
          · have h0 : mat (r + 2) K A'⁻¹ v t = 0 := by
              rw [hB]
              exact spEmbedMat_inv_apply_eq_zero hA hv ht
            rw [h0, mul_zero, mul_zero]
          · rw [(mem_suppGroup.1 hy) w v (fun h => hv h.2)]
      _ = mat (r + 2) K A'⁻¹ w t := by
          rw [← Matrix.mul_apply, Matrix.one_mul]
  calc mat (r + 2) K (A' * y * A'⁻¹) u t
      = ∑ w, mat (r + 2) K A' u w * (mat (r + 2) K y * mat (r + 2) K A'⁻¹) w t := by
          rw [map_mul, map_mul, mul_assoc, Matrix.mul_apply]
    _ = ∑ w, mat (r + 2) K A' u w * mat (r + 2) K A'⁻¹ w t :=
          Finset.sum_congr rfl fun w _ => by rw [hkey w]
    _ = (mat (r + 2) K A' * mat (r + 2) K A'⁻¹) u t := by rw [Matrix.mul_apply]
    _ = (1 : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
          (Fin (r + 2) ⊕ Fin (r + 2)) K) u t := by
          rw [← map_mul, mul_inv_cancel, map_one]

private theorem map_conj_range_spEmbed_le {m k : ℕ} {B : StatedSp m K}
    (hB : ∀ j : Fin m, ∀ x ∈ (longBlock K m j).range,
      B * x * B⁻¹ ∈ (longBlock K m j).range)
    {τ : Fin k → Fin m} (hτ : Function.Injective τ) :
    (spEmbed τ hτ).range.map (MulAut.conj B).toMonoidHom ≤ (spEmbed τ hτ).range := by
  classical
  set T : Set (Fin m ⊕ Fin m) := Set.range (Sum.map τ τ) with hT
  have hrange : (spEmbed (K := K) τ hτ).range = suppGroup (K := K) T := by
    rw [hT]
    exact range_spEmbed hτ
  have hS : ParClosed T := by
    rintro _ ⟨w, rfl⟩
    rcases w with w | w
    · exact ⟨Sum.inr w, rfl⟩
    · exact ⟨Sum.inl w, rfl⟩
  rw [hrange]
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_suppGroup_iff hS]
  intro t ht u
  have hcoords_sub : ∀ l : Fin k, coords (τ l) ⊆ T := by
    intro l a ha
    rcases mem_coords.1 ha with rfl | rfl
    · exact ⟨Sum.inl l, by rw [Sum.map_inl]⟩
    · exact ⟨Sum.inr l, by rw [Sum.map_inr]⟩
  have hkey : ∀ w, (mat m K y * mat m K B⁻¹) w t = mat m K B⁻¹ w t := by
    intro w
    rw [Matrix.mul_apply]
    calc ∑ v, mat m K y w v * mat m K B⁻¹ v t
        = ∑ v, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) w v *
            mat m K B⁻¹ v t := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases hv : v ∈ T
          · obtain ⟨w', rfl⟩ := hv
            rcases w' with l | l
            · rw [Sum.map_inl]
              have ht' : t ∉ coords (τ l) := fun h => ht (hcoords_sub l h)
              have h0 : mat m K B⁻¹ (Sum.inl (τ l)) t = 0 :=
                mat_inv_apply_eq_zero_of_normalizes (hB (τ l)) (inl_mem_coords _) ht'
              rw [h0, mul_zero, mul_zero]
            · rw [Sum.map_inr]
              have ht' : t ∉ coords (τ l) := fun h => ht (hcoords_sub l h)
              have h0 : mat m K B⁻¹ (Sum.inr (τ l)) t = 0 :=
                mat_inv_apply_eq_zero_of_normalizes (hB (τ l)) (inr_mem_coords _) ht'
              rw [h0, mul_zero, mul_zero]
          · rw [(mem_suppGroup.1 hy) w v (fun h => hv h.2)]
      _ = mat m K B⁻¹ w t := by
          rw [← Matrix.mul_apply, Matrix.one_mul]
  calc mat m K (B * y * B⁻¹) u t
      = ∑ w, mat m K B u w * (mat m K y * mat m K B⁻¹) w t := by
          rw [map_mul, map_mul, mul_assoc, Matrix.mul_apply]
    _ = ∑ w, mat m K B u w * mat m K B⁻¹ w t :=
          Finset.sum_congr rfl fun w _ => by rw [hkey w]
    _ = (mat m K B * mat m K B⁻¹) u t := by rw [Matrix.mul_apply]
    _ = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) u t := by
          rw [← map_mul, mul_inv_cancel, map_one]

theorem map_conj_range_spEmbed_of_longBlock {m k : ℕ} {A : StatedSp m K}
    (hA : ∀ j : Fin m,
      (longBlock K m j).range.map (MulAut.conj A).toMonoidHom = (longBlock K m j).range)
    {τ : Fin k → Fin m} (hτ : Function.Injective τ) :
    (spEmbed τ hτ).range.map (MulAut.conj A).toMonoidHom = (spEmbed τ hτ).range := by
  have hA' : ∀ j : Fin m, ∀ x ∈ (longBlock K m j).range,
      A * x * A⁻¹ ∈ (longBlock K m j).range := by
    intro j x hx
    have hx' : (MulAut.conj A) x ∈
        (longBlock K m j).range.map (MulAut.conj A).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rwa [hA j] at hx'
  have hAinv' : ∀ j : Fin m, ∀ x ∈ (longBlock K m j).range,
      A⁻¹ * x * (A⁻¹)⁻¹ ∈ (longBlock K m j).range := by
    intro j x hx
    have hmap := congrArg (Subgroup.map (MulAut.conj A⁻¹).toMonoidHom) (hA j)
    rw [Subgroup.map_map] at hmap
    have hcomp : (MulAut.conj A⁻¹).toMonoidHom.comp (MulAut.conj A).toMonoidHom =
        MonoidHom.id (StatedSp m K) := by
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id] at hmap
    have hx' : (MulAut.conj A⁻¹) x ∈
        (longBlock K m j).range.map (MulAut.conj A⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [← hmap] at hx'
    simpa [MulAut.conj_apply, inv_inv] using hx'
  refine le_antisymm (map_conj_range_spEmbed_le hA' hτ) ?_
  have hle := map_conj_range_spEmbed_le hAinv' hτ
  have hmono : ((spEmbed τ hτ).range.map (MulAut.conj A⁻¹).toMonoidHom).map
      (MulAut.conj A).toMonoidHom ≤
        (spEmbed τ hτ).range.map (MulAut.conj A).toMonoidHom :=
    Subgroup.map_mono hle
  rw [Subgroup.map_map] at hmono
  have hcomp : (MulAut.conj A).toMonoidHom.comp (MulAut.conj A⁻¹).toMonoidHom =
      MonoidHom.id (StatedSp m K) := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, Subgroup.map_id] at hmono
  exact hmono

end CFSG.ClassicalInvolution.Models.SymplecticPairs

end
