module

public import CFSG.LieType.SeitzGeneration.InnerThreeUnitaryLeaves
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorPair
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorWords

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits HeisTensor HeisTensor.Words

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem eq_top_of_plane [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hn : 4 ≤ n) {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h (idGram K n)) (hy : y ∈ primeFormUnitary h (idGram K n))
    {ω α β : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hωN : h.bar ω * ω = 1)
    (hyx : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      ω • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hxα : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hyβ : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hCx : Cent H (x : Matrix (Fin n) (Fin n) K)) (hCy : Cent H (y : Matrix (Fin n) (Fin n) K))
    (hCxy : Cent H ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))
    (hCxyy : Cent H ((x : Matrix (Fin n) (Fin n) K) *
      ((y : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)))) : H = ⊤ := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hαN := NonCube.bar_mul_eq_one_of_pow_three h hn1 hx hxα
  have hβN := NonCube.bar_mul_eq_one_of_pow_three h hn1 hy hyβ
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβN
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hX3 : (x : Matrix (Fin n) (Fin n) K) * x * x = α • 1 := by
    rw [← hxα, Units.val_pow_eq_pow_val]
    simp [pow_succ]
  have hY3 : (y : Matrix (Fin n) (Fin n) K) * y * y = β • 1 := by
    rw [← hyβ, Units.val_pow_eq_pow_val]
    simp [pow_succ]
  have hω2 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hω2ne : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    linear_combination hω3 - ω * h2
  have hω2N : h.bar (ω ^ 2) * ω ^ 2 = 1 := by rw [map_pow, ← mul_pow, hωN, one_pow]
  have hq : ∀ {c : K}, h.bar c * c = 1 → c ^ (ℓ ^ f + 1) = 1 := fun {c} hc => by
    rwa [h.bar_apply, ← pow_succ] at hc
  have hxyM : ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) := Units.val_mul _ _
  have hxyyM : ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) *
        ((y : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) := by
    rw [pow_two, Units.val_mul, Units.val_mul]
  by_cases hcβ : ∃ ν : K, ν ^ 3 = β
  ·
    obtain ⟨ν, hν⟩ := hcβ
    have hν0 : ν ≠ 0 := by
      rintro rfl
      apply hβ0
      rw [← hν]
      norm_num
    have hνN := bar_mul_eq_one_of_cube h hq3 hν0 hν (hq hβN)
    exact eq_top_of_heis_pair h hn hy hx hω3 hω1 hωN hν0 hνN (by rw [hyβ, hν]) hxα hyx hCy hCx
      hCxy hCxyy
  · by_cases hcα : ∃ μ : K, μ ^ 3 = α
    ·
      obtain ⟨ν, hν⟩ := hcα
      have hν0 : ν ≠ 0 := by
        rintro rfl
        apply hα0
        rw [← hν]
        norm_num
      have hνN := bar_mul_eq_one_of_cube h hq3 hν0 hν (hq hαN)
      refine eq_top_of_heis_pair h hn hx hy hω2 hω2ne hω2N hν0 hνN (by rw [hxα, hν]) hyβ
        (idF2 hω3 hyx) hCx hCy ?_ ?_
      · rw [hyx]
        exact hCxy.smul hω0
      · exact hCxyy.of_mul_eq (mul_ne_zero hα0 hβ0) (idC hX3 hY3)
    · rcases NonCube.cube_dichotomy hα0 hβ0 hcα hcβ with ⟨ν, hν⟩ | ⟨ν, hν⟩
      ·
        have hν0 : ν ≠ 0 := by
          rintro rfl
          apply mul_ne_zero hα0 hβ0
          rw [← hν]
          norm_num
        have hαβN : h.bar (α * β) * (α * β) = 1 := by
          rw [map_mul, mul_mul_mul_comm, hαN, hβN, one_mul]
        have hνN := bar_mul_eq_one_of_cube h hq3 hν0 hν (hq hαβN)
        have hg0 : ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ 3) • 1 := by
          rw [hxyM, hν]
          exact idA hω3 hyx hX3 hY3
        have hg03 : (((x * y) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ 3) • 1 := by
          rw [Units.val_pow_eq_pow_val]
          simpa [pow_succ] using hg0
        refine eq_top_of_heis_pair h hn (mul_mem hx hy) hy hω2 hω2ne hω2N hν0 hνN hg03 hyβ
          ?_ ?_ hCy ?_ ?_
        · rw [hxyM]
          exact idF3 hω3 hyx
        · rw [hxyM]
          exact hCxy
        · rw [hxyM, idD1 hyx]
          exact hCxyy.smul hω0
        · rw [hxyM, idD2 hω3 hyx hY3]
          exact hCx.sq hα0 hX3 hβ0
      ·
        have hν0 : ν ≠ 0 := by
          rintro rfl
          apply mul_ne_zero hα0 (pow_ne_zero 2 hβ0)
          rw [← hν]
          norm_num
        have hαβN : h.bar (α * β ^ 2) * (α * β ^ 2) = 1 := by
          rw [map_mul, map_pow, mul_mul_mul_comm, hαN, ← mul_pow, hβN, one_pow, one_mul]
        have hνN := bar_mul_eq_one_of_cube h hq3 hν0 hν (hq hαβN)
        have hg0 : ((x : Matrix (Fin n) (Fin n) K) * ((y : Matrix (Fin n) (Fin n) K) * y)) *
            ((x : Matrix (Fin n) (Fin n) K) * ((y : Matrix (Fin n) (Fin n) K) * y)) *
            ((x : Matrix (Fin n) (Fin n) K) * ((y : Matrix (Fin n) (Fin n) K) * y)) =
            (ν ^ 3) • 1 := by
          rw [hν]
          exact idB hω3 hyx hX3 hY3
        have hg03 : (((x * y ^ 2) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (ν ^ 3) • 1 := by
          rw [Units.val_pow_eq_pow_val, hxyyM]
          simpa [pow_succ] using hg0
        refine eq_top_of_heis_pair h hn (mul_mem hx (pow_mem hy 2)) hy hω2 hω2ne hω2N hν0 hνN
          hg03 hyβ ?_ ?_ hCy ?_ ?_
        · rw [hxyyM]
          exact idF4 hω3 hyx hY3
        · rw [hxyyM]
          exact hCxyy
        · rw [hxyyM, idE1 hyx hY3]
          exact hCx.smul (mul_ne_zero hω0 hβ0)
        · rw [hxyyM, idE2 hω3 hyx hY3]
          exact hCxy.sq (mul_ne_zero hα0 hβ0) (idA hω3 hyx hX3 hY3) hβ0

theorem unitaryHeisTensorPlanesGU_holds :
    ∀ (ℓ f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ∣ ℓ ^ f + 1 → 6 ≤ n →
      3 ∣ n → ∀ x y : GL (Fin n) K, x ∈ primeFormUnitary h (idGram K n) →
        y ∈ primeFormUnitary h (idGram K n) → ∀ ω : K, IsPrimitiveRoot ω 3 →
          (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
            ω • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) →
          (∃ α : K, ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1) →
          (∃ β : K, ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1) →
            Subgroup.closure (planeFixUn ℓ f n K x y) = ⊤ := by
  intro ℓ f n K _ h hq3 hn6 hn3 x y hx hy ω hω hyx hα hβ
  classical
  obtain ⟨α, hxα⟩ := hα
  obtain ⟨β, hyβ⟩ := hβ
  have hfin := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hωN : h.bar ω * ω = 1 := by
    rw [h.bar_apply, ← pow_succ]
    obtain ⟨k, hk⟩ := hq3
    rw [hk, pow_mul, hω3, one_pow]
  let ε : SUid (unitaryInvolution K ℓ f) n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let H : Subgroup (SUid (unitaryInvolution K ℓ f) n) :=
    (Subgroup.closure (planeFixUn ℓ f n K x y)).comap ε.toMonoidHom
  have hxyM : ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) := Units.val_mul _ _
  have hxyyM : ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) *
        ((y : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) := by
    rw [pow_two, Units.val_mul, Units.val_mul]
  have hCx : Cent H (x : Matrix (Fin n) (Fin n) K) := fun g hg =>
    Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (mem_FixUn_of_mul_comm (g := ε g) hg))))
  have hCy : Cent H (y : Matrix (Fin n) (Fin n) K) := fun g hg =>
    Subgroup.subset_closure (Or.inl (Or.inl (Or.inr (mem_FixUn_of_mul_comm (g := ε g) hg))))
  have hCxy : Cent H ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) :=
    fun g hg => Subgroup.subset_closure (Or.inl (Or.inr (mem_FixUn_of_mul_comm (g := ε g)
      (by rw [hxyM]; exact hg))))
  have hCxyy : Cent H ((x : Matrix (Fin n) (Fin n) K) *
      ((y : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K))) :=
    fun g hg => Subgroup.subset_closure (Or.inr (mem_FixUn_of_mul_comm (g := ε g)
      (by rw [hxyyM]; exact hg)))
  have hH : H = ⊤ :=
    eq_top_of_plane h hq3 (by omega) hx hy hω3 hω1 hωN hyx hxα hyβ hCx hCy hCxy hCxyy
  rw [eq_top_iff]
  intro u _
  have hu : ε.symm u ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using hu

theorem unitaryHeisTensorPlanes_holds : UnitaryHeisTensorPlanes := by
  intro ℓ f n K _ h hq3 hn6 hn3 x y hx hy ω hω hyx hα hβ
  exact unitaryHeisTensorPlanesGU_holds ℓ f n K h hq3 hn6 hn3 x y
    (CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h hx)
    (CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h hy) ω hω hyx hα hβ

theorem seitzInnerThreeUnitaryNonabHigh : SeitzInnerThreeUnitaryNonabHigh :=
  seitzInnerThreeUnitaryNonabHigh_of_heis unitaryHeisTensorPlanes_holds

end CFSG.LieType.SeitzGeneration
