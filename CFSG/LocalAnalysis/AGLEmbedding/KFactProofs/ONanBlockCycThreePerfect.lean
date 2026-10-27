module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section Node

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.exists_perfect_three
    (h : BorelQuotient D n H π M) {F : Type} [Field F] [CharP F 2]
    (hF : ∃ s : Finset F, s.card = 4) (hsl : ∀ i, HasSL2Node D i F) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ P : Subgroup Y, P ≤ J ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
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
  obtain ⟨φ, hφ, hx, hy⟩ := hsl i
  have hφJ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, φ A ∈ J.comap π' := by
    intro A
    have hA := Sp.mem_closure_sl2 A
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (J.comap π').comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hBJ (posUnipotent_le_borel (rootGroup_le_posUnipotent
          ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i)
          (hx c)))
      · exact hi (hy c)
    exact hle hA
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hF
  set f : Matrix.SpecialLinearGroup (Fin 2) F →* Y := π'.comp φ with hf
  refine ⟨f.range, ?_, Subgroup.commutator_eq_self (H := f.range)
    (hH := Group.IsPerfect.range f), ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact hφJ A
  ·
    set z : Matrix.SpecialLinearGroup (Fin 2) F := sl2Upper 1 * sl2Lower 1 with hz
    have hz3 : f z ^ 3 = 1 := by
      rw [← map_pow, hz, sl2_upper_lower_cube, map_one]
    have hz1 : f z ≠ 1 := by
      intro h1
      have hc := Subgroup.mem_center_iff.1 (hQ.ker_central (φ z) h1) (φ (sl2Upper 1))
      apply sl2_upper_lower_not_commute (F := F)
      apply hφ
      simp only [hz, map_mul] at hc ⊢
      exact hc.symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (f z) = 3 := orderOf_eq_prime hz3 hz1
    have h1 := orderOf_dvd_natCard (⟨f z, z, rfl⟩ : f.range)
    rw [← Subgroup.orderOf_coe] at h1
    change orderOf (f z) ∣ _ at h1
    rwa [hord] at h1

end Node

theorem exists_perfect_psl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : ∃ s : Finset F, s.card = 4) {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ P : Subgroup Y, P ≤ J ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P :=
  (borelQuotient_sl e).exists_perfect_three hF (fun i => hasSL2Node_sl i) T J hNJ hJ

end CFSG.AGLEmbedding.BlockCyc
