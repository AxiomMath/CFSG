module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPlane
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne

theorem fixPlane_of_hom {X P : Type*} [Group X] [Group P] {p : ℕ} (φ : X →* P)
    (hφ : Function.Injective φ) (hX : PlaneCentGen X p) {A : Subgroup P} (hAφ : A ≤ φ.range)
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    φ.range ≤ Subgroup.closure {k | k ∈ φ.range ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} := by
  set A₂ : Subgroup X := A.comap φ with hA₂
  have hmap : A₂.map φ = A := Subgroup.map_comap_eq_self hAφ
  have hcardA₂ : Nat.card A₂ = p ^ 2 := by
    rw [← hAc, ← hmap, Subgroup.card_map_of_injective hφ]
  have hel : IsElemAbelian p A₂ := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      apply hφ
      have := hA.1.is_comm.comm ⟨φ a, hmap ▸ Subgroup.mem_map_of_mem φ a.2⟩
        ⟨φ b, hmap ▸ Subgroup.mem_map_of_mem φ b.2⟩
      simpa using congrArg Subtype.val this
    · intro g hg
      apply hφ
      rw [map_pow, map_one]
      exact hA.2 (φ g) (hmap ▸ Subgroup.mem_map_of_mem φ hg)
  have h := hX A₂ hel hcardA₂
  have h1 : (⊤ : Subgroup X).map φ ≤ Subgroup.closure {k | k ∈ φ.range ∧
      ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} := by
    rw [← h, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, ⟨b, hb, hb1, hxb⟩, rfl⟩
    refine Subgroup.subset_closure ⟨⟨x, rfl⟩, φ b, hmap ▸ Subgroup.mem_map_of_mem φ hb,
      fun h => hb1 (hφ (by rw [h, map_one])), ?_⟩
    rw [← map_mul, ← map_mul, hxb]
  rwa [← MonoidHom.range_eq_map] at h1

theorem planeCentGen_L3_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : PlaneCentGen (projectiveSL 3 k) p := by
  intro A hA hAc
  exfalso
  have h1 : p ^ 2 ∣ Nat.card (projectiveSL 3 k) := hAc ▸ Subgroup.card_subgroup_dvd_card A
  have h2 : Nat.card (projectiveSL 3 k) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) :=
    Subgroup.card_dvd_of_surjective (proj_surjective 3 k)
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) = 168 := by
    rw [card_SL_eq (by norm_num), hk]
    decide +kernel
  have h4 : p ^ 2 ∣ 168 := h3 ▸ h1.trans h2
  have h5 : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h4
  have h6 : p ≤ 12 := by nlinarith
  have key : ∀ q : ℕ, q ≤ 12 → q.Prime → q ≠ 2 → ¬ q ^ 2 ∣ 168 := by decide
  exact key p h6 hp hp2 h4

@[expose] def L4TwoPlanes : Prop :=
  ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    PlaneCentGen (projectiveSL 4 k) p

theorem fixPlaneGen_projectiveSL
    (hL4 : L4TwoPlanes) {m : ℕ}
    (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card K - 1)))
    (hno : ¬ ∃ E : Subgroup (projectiveSL (m + 1) K), IsElemAbelian p E ∧ Nat.card E = p ^ 3) :
    FixPlaneGen (projectiveSL (m + 1) K) p := by
  have hn3 : 3 ≤ m + 1 := by omega
  intro σ hσ A hA hAa hAc
  obtain ⟨d, -, g, ⟨τ, hτ, rfl⟩, rfl⟩ := outer_descent_gen hn3 hp hp2 hℓ hpℓ hf hK hcop σ hσ
  set k := semilinearFixedSubfield τ with hk
  have hpf : p ∣ f ∧ Nat.card k = ℓ ^ (f / p) := card_semilinearFixedSubfield hℓ hf hK hτ
  have he : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf.1) hp.pos
  let j := linearSubfieldInclusion (m + 1) k
  have hj : Function.Injective j := linearSubfieldInclusion_injective (by omega) k
  let φ : projectiveSL (m + 1) k →* projectiveSL (m + 1) K := (d : projectiveSL (m + 1) K →* _).comp j
  have hφ : Function.Injective φ := d.injective.comp hj
  have hrange : φ.range = fixedSubgroup (d * fieldAut (m + 1) K τ * d⁻¹) := by
    rw [fixedSubgroup_conj, fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hτ,
      MonoidHom.range_comp]
    rfl
  have hrk : RankLE2 p (projectiveSL (m + 1) k) := by
    intro F hF
    have h1 := rankLE2_of_not_exists_cube hp hno (F.map φ)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _)
    rwa [Subgroup.card_map_of_injective hφ] at h1
  have hX : PlaneCentGen (projectiveSL (m + 1) k) p := by
    by_cases h2 : Nat.card k = 2
    · rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
      · exact planeCentGen_L3_two h2 hp hp2
      · exact hL4 k h2 p hp hp2
      · refine planeCentGen_projectiveSL hm hℓ he hpf.2 hp hp2 hpℓ ?_ ?_ hrk
        · rintro ⟨-, h | h⟩ <;> omega
        · rintro ⟨-, -, -, h⟩
          omega
    · refine planeCentGen_projectiveSL hm hℓ he hpf.2 hp hp2 hpℓ ?_ ?_ hrk
      · rintro ⟨h, -⟩
        exact h2 (hpf.2.trans h)
      · rintro ⟨hp3, hℓ2, he2, hm2⟩
        subst hm2 hp3 hℓ2
        have hf6 : f = 3 * 2 := by
          rw [← he2]
          exact (Nat.mul_div_cancel' hpf.1).symm
        rw [hf6] at hK
        have h63 : Nat.card K - 1 = 63 := by rw [hK]; norm_num
        rw [h63] at hcop
        norm_num at hcop
  rw [← hrange]
  exact fixPlane_of_hom φ hφ hX (hrange ▸ hA) hAa hAc

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
