module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lWeilSp
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Cover

variable {G L : Type} [Group G] [Group L]

theorem a2l_map_eq_of_center_pair (hP : Group.IsPerfect G) (ψ : G →* L)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center G) {g : G}
    (hcen : ∀ s ∈ center G, s = 1 ∨ s = g) {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1) :
    ψ g = z := by
  obtain ⟨s, rfl⟩ := hψ z
  have hsc : s ∈ center G := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP ψ hψ hker]
    exact hz
  rcases hcen s hsc with h | h
  · exact absurd (by rw [h, map_one]) hz1
  · rw [← h]

theorem a2l_injective_of_center_pair (ψ : G →* L) (hker : ψ.ker ≤ center G) {g : G}
    (hcen : ∀ s ∈ center G, s = 1 ∨ s = g) (h1 : ψ g ≠ 1) : Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rcases hcen x (hker (MonoidHom.mem_ker.2 hx)) with h | h
  · exact h
  · rw [h] at hx
    exact absurd hx h1

theorem a2l_isPGroup_two_center_of_center_pair (hP : Group.IsPerfect G) (ψ : G →* L)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center G) {g : G}
    (hcen : ∀ s ∈ center G, s = 1 ∨ s = g) (hg : g * g = 1) : IsPGroup 2 ↥(center L) := by
  intro y
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨s, hs⟩ := hψ (y : L)
  have hsc : s ∈ center G := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP ψ hψ hker, mem_comap, hs]
    exact y.2
  have h : s * s = 1 := by
    rcases hcen s hsc with h | h
    · rw [h, one_mul]
    · rw [h, hg]
  rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, ← hs, ← map_mul, h, map_one]

end Cover

section SL

variable {K : Type} [Field K] [Finite K]

theorem a2l_center_sl_cases (hK : Nat.card K = 3) {n : ℕ} (hn : n ≠ 0) {s : SL(n, K)}
    (hs : s ∈ center SL(n, K)) :
    (s : Matrix (Fin n) (Fin n) K) = 1 ∨ (s : Matrix (Fin n) (Fin n) K) = -1 := by
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hs
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hr
    exact zero_ne_one hr
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hr2 : r * r = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [hq, show 3 - 1 = 2 from rfl, sq] at h
  rcases mul_self_eq_one_iff.1 hr2 with h | h
  · left
    rw [← hrs, h, map_one]
  · right
    rw [← hrs, h, map_neg, map_one]

theorem a2l_exists_sl2_27_sl6 [CharP K 3] (hK : Nat.card K = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ι : SL(2, F) →* SL(6, K)),
      Nat.card F = 27 ∧ Function.Injective ι ∧
        ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) = -1 →
          (ι g : Matrix (Fin 6) (Fin 6) K) = -1 := by
  obtain ⟨F, hF, hFin, φ, hcard, hinj, hneg⟩ := a2l_exists_weil_sl2_27 K hK
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let R : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K ≃ₐ[K] Matrix (Fin 6) (Fin 6) K :=
    Matrix.reindexAlgEquiv K K e
  let ρ : SL(2, F) →* GL (Fin 6) K :=
    (Units.map R.toMonoidHom).comp ((StatedSp 3 K).subtype.comp φ)
  have hdet : ∀ g, (ρ g : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    intro g
    have hperf : Group.IsPerfect SL(2, F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F (by rw [hcard]; norm_num)
    have hker := Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp ρ)
    rw [hperf.commutator_eq_top] at hker
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hker (Subgroup.mem_top g)))
    simpa using h1
  let ι : SL(2, F) →* SL(6, K) :=
    { toFun := fun g => (⟨(ρ g : Matrix (Fin 6) (Fin 6) K), hdet g⟩ : SL(6, K))
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => by
        apply Subtype.ext
        change ((ρ (g * h) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          (ρ g : Matrix (Fin 6) (Fin 6) K) * (ρ h : Matrix (Fin 6) (Fin 6) K)
        rw [map_mul, Units.val_mul] }
  refine ⟨F, hF, hFin, ι, hcard, ?_, fun g hg => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ρ g = 1 := Units.ext (congrArg Subtype.val hg)
    have h2 : (StatedSp 3 K).subtype (φ g) = 1 :=
      Units.map_injective R.injective (by rw [map_one]; exact h1)
    exact hinj (by rw [map_one]; exact Subtype.ext h2)
  · have h1 := hneg g hg
    show (((Units.map R.toMonoidHom) ((φ g : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = -1
    rw [h1]
    simp [map_neg]

end SL

end CFSG.OddStandard.SmallF3.HypA2Leaves
