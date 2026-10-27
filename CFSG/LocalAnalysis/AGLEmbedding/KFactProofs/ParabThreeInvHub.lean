module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabInvol
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeBasic

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Hub

variable {K : Type*} [Group K]

@[expose] def HasInvolThree (D : UniversalRootDatum K) (i : Fin D.rank) : Prop :=
  ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (-Pi.single i 1),
    x * x = 1 ∧ y * y = 1 ∧ (x * y) ^ 3 = 1 ∧ ∃ c : K, x * y * c ≠ c * (x * y)

theorem sl2Upper_one_mul_self {F : Type*} [Field F] [CharP F 2] :
    sl2Upper (1 : F) * sl2Upper 1 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2Lower_one_mul_self {F : Type*} [Field F] [CharP F 2] :
    sl2Lower (1 : F) * sl2Lower 1 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem HasSL2Node.hasInvolThree {F : Type*} [Field F] [CharP F 2] {D : UniversalRootDatum K}
    {i : Fin D.rank} (h : HasSL2Node D i F) : HasInvolThree D i := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  refine ⟨φ (sl2Upper 1), hx 1, φ (sl2Lower 1), hy 1, ?_, ?_, ?_, φ (sl2Upper 1), fun h => ?_⟩
  · rw [← map_mul, sl2Upper_one_mul_self, map_one]
  · rw [← map_mul, sl2Lower_one_mul_self, map_one]
  · rw [← map_mul, ← map_pow, sl2_upper_lower_cube, map_one]
  · exact sl2_upper_lower_not_commute (hφ (by simpa [map_mul] using h))

theorem HasInvolThree.of_involutions {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i : Fin D.rank} {x y : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hy : y ∈ D.rootGroup (-Pi.single i 1))
    (hx1 : x ≠ 1) (hx2 : x * x = 1) (hy2 : y * y = 1) (hbraid : x * y * x = y * x * y) :
    HasInvolThree D i := by
  exact ⟨x, hx, y, hy, hx2, hy2, cube_eq_one_of_braid hx2 hy2 hbraid, x, by
    intro h
    have h1 : x * y * x = y := by rw [h, ← mul_assoc, hx2, one_mul]
    have h2 : y * x * y = y := hbraid ▸ h1
    have h3' : y * x = 1 := mul_eq_right.1 h2
    have h4 : x = y := by
      rw [eq_inv_of_mul_eq_one_right h3', inv_eq_of_mul_eq_one_right hy2]
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
    exact hx1 hmem⟩

variable {Y : Type*} [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem BorelQuotient.invThree (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasInvolThree D i) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
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
  have hgJ : π' (x * y) ∈ J := mul_mem (hBJ hxB) (hi hy)
  have hne1 : π' (x * y) ≠ 1 := by
    intro h1
    exact hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨π' (x * y), hgJ, π' x, hBJ hxB, orderOf_eq_prime (by rw [← map_pow, h3', map_one])
    hne1, ?_⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have e : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hx2, one_mul]
  rw [← map_inv, ← map_mul, ← map_mul, e, map_inv]

end Hub

theorem invThree_sl_psl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {Y : Type}
    [Group Y] [Finite Y] (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J :=
  BorelQuotient.invThree (borelQuotient_sl e)
    (fun i => HasSL2Node.hasInvolThree (hasSL2Node_sl i)) T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
