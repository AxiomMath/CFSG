module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabInvol

public section

namespace CFSG.AGLEmbeddingD2.ParabRealThree

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT CFSG.AGLEmbedding.ParabHub

variable {K : Type*} [Group K]

@[expose] def HasRealOrderThree (D : UniversalRootDatum K) (i : Fin D.rank) : Prop :=
  ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (-Pi.single i 1),
    x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 3 = 1 ∧ ∃ c : K, x * y * c ≠ c * (x * y)

theorem sl2Upper_one_sq {F : Type*} [Field F] [CharP F 2] :
    (sl2Upper (1 : F)) ^ 2 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2Lower_one_sq {F : Type*} [Field F] [CharP F 2] :
    (sl2Lower (1 : F)) ^ 2 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem HasSL2Node.hasRealOrderThree {D : UniversalRootDatum K} {i : Fin D.rank} {F : Type*}
    [Field F] [CharP F 2] (h : HasSL2Node D i F) : HasRealOrderThree D i := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  exact ⟨φ (sl2Upper 1), hx 1, φ (sl2Lower 1), hy 1,
    by rw [← map_pow, sl2Upper_one_sq, map_one], by rw [← map_pow, sl2Lower_one_sq, map_one],
    by rw [← map_mul, ← map_pow, sl2_upper_lower_cube, map_one],
    φ (sl2Upper 1), fun h => sl2_upper_lower_not_commute (hφ (by simpa [map_mul] using h))⟩

theorem HasRealOrderThree.of_involutions {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i : Fin D.rank} {x y : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hy : y ∈ D.rootGroup (-Pi.single i 1)) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hbraid : x * y * x = y * x * y) :
    HasRealOrderThree D i := by
  refine ⟨x, hx, y, hy, by rw [sq]; exact hx2, by rw [sq]; exact hy2,
    cube_eq_one_of_braid hx2 hy2 hbraid, x, fun h => ?_⟩
  have h1 : x * y * x = y := by rw [h, ← mul_assoc, hx2, one_mul]
  have h2 : y * x * y = y := hbraid ▸ h1
  have h3 : y * x = 1 := mul_eq_right.1 h2
  have h4 : x = y := by
    rw [eq_inv_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right hy2]
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hxU : x ∈ posUnipotent D := rootGroup_le_posUnipotent hα (ht_single_pos i) hx
  have hyU : y ∈ negUnipotent D := rootGroup_le_negUnipotent hα' (by
    rw [ht_neg]
    have := ht_single_pos (D := D) i
    omega) hy
  have hmem : x ∈ posUnipotent D ⊓ negUnipotent D := ⟨hxU, h4 ▸ hyU⟩
  rw [posUnipotent_inf_negUnipotent hext, Subgroup.mem_bot] at hmem
  exact hx1 hmem

theorem conj_mul_eq_inv_of_sq {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx])
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy])
  rw [mul_inv_rev, hx', hy', ← mul_assoc, ← sq, hx, one_mul]

section Quotient

variable {Y : Type*} [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem BorelQuotient.exists_real_three (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasRealOrderThree D i) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ g ∈ J, g ^ 3 = 1 ∧ g ≠ 1 ∧ ∃ w ∈ J, w * g * w⁻¹ = g⁻¹ := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt h.ct h.extras hBJ hne
  obtain ⟨x, hx, y, hy, hx2, hy2, h3', c, hc⟩ := h3 i
  have hxB : x ∈ borel D H := posUnipotent_le_borel (rootGroup_le_posUnipotent
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i) hx)
  have hxJ : π' x ∈ J := hBJ hxB
  have hxyJ : x * y ∈ J.comap π' := mul_mem (hBJ hxB) (hi hy)
  refine ⟨π' (x * y), hxyJ, by rw [← map_pow, h3', map_one], ?_, π' x, hxJ, ?_⟩
  · intro h1
    exact hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, conj_mul_eq_inv_of_sq hx2 hy2]

end Quotient

end CFSG.AGLEmbeddingD2.ParabRealThree
