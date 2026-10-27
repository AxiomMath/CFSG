module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT2Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem t1Gens_getD_zero : t1Gens.getD 0 0 = 3 := rfl

theorem t1Gens_length : t1Gens.length = 10 := rfl

theorem t1Gens_getD_lt {i : ℕ}
    (hi : i < 10) : t1Gens.getD i 0 < 131072 := by
  rw [List.getD_eq_getElem _ _ (by rw [t1Gens_length]; exact hi)]
  exact t1Gens_lt _ (List.getElem_mem _)

theorem mem_s2V {T₁ : Subgroup G}
    {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0)
    (hinv : ∀ c, c < 131072 → inv c < 131072 ∧ mul c (inv c) = 0) {y₀ : G}
    (hy : y₀ ∈ normalizer (T₁ : Set G)) (hy2 : y₀ * y₀ ∈ T₁) {B : ℕ → ℕ}
    (hB : ∀ g : T₁, Φ.f (conjEquiv hy g) = B (Φ.f g)) :
    Φ.f ⟨y₀ * y₀, hy2⟩ ∈ s2V mul inv (s2Cj0 mul inv) B := by
  set Y : T₁ := ⟨y₀ * y₀, hy2⟩
  have hconj : ∀ g : T₁, Φ.f (Y * g * Y⁻¹) = B (B (Φ.f g)) := by
    intro g
    have e1 : Y * g * Y⁻¹ = conjEquiv hy (conjEquiv hy g) := by
      apply Subtype.ext
      simp only [Y, conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, hB, hB]
  have hgi : ∀ i, i < 10 → cconj mul inv (Φ.f Y) (t1Gens.getD i 0) = B (B (t1Gens.getD i 0)) := by
    intro i hi
    have hlt := t1Gens_getD_lt hi
    rw [← Φ.f_g hlt, ← Φ.f_conj h0 hinv, hconj]
  have hBv : B (Φ.f Y) = Φ.f Y := by
    rw [← hB]
    congr 1
    apply Subtype.ext
    simp only [Y, conjEquiv_apply]
    group
  unfold s2V
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 (Φ.lt _), ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  have hbb : ∀ i, i < 10 → (t1Gens.map fun g => B (B g)).getD i 0 = B (B (t1Gens.getD i 0)) :=
    fun i hi => getD_map_lt (by rw [t1Gens_length]; exact hi) 0 0
  refine ⟨⟨?_, fun i hi => ?_⟩, hBv⟩
  · unfold s2Cj0
    rw [getElem!_pos _ _ (by simpa using Φ.lt Y), Array.getElem_map]
    simp only [List.getElem_toArray, List.getElem_range]
    rw [hbb 0 (by norm_num), ← hgi 0 (by norm_num), t1Gens_getD_zero]
  · rw [hbb i hi, hgi i hi]

section Act

variable {S T₁ : Subgroup G}
  (e : S ≃* SModel) {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T₁ 131072 mul) (hST : S ≤ T₁) {x : G} (hxT : x ∈ T₁)
  (hΦS : ∀ (g : T₁) (hg : (g : G) ∈ S), Φ.f g = (e ⟨g, hg⟩).code)
  {y : G} (hy : y ∈ normalizer (T₁ : Set G)) {ι : Array ℕ} {F : ℕ → ℕ}
  (hyS : ∀ s : S, Φ.f (conjEquiv hy ⟨s, hST s.2⟩) = ι[F (e s).code]!)

include hΦS hyS in
theorem act_eq_s2B (hΦx : ∀ (g : T₁), (g : G) ∉ S → ∀ hg : (g : G) * x⁻¹ ∈ S,
      Φ.f g = (e ⟨g * x⁻¹, hg⟩).code + 65536)
    (hT : ∀ g : T₁, (g : G) ∈ S ∨ (g : G) * x⁻¹ ∈ S) (g : T₁) :
    Φ.f (conjEquiv hy g) = s2B mul ι F (Φ.f (conjEquiv hy ⟨x, hxT⟩)) (Φ.f g) := by
  unfold s2B
  by_cases hg : (g : G) ∈ S
  · have h1 := hΦS g hg
    have hlt : Φ.f g < 65536 := by rw [h1]; exact (e _).lt
    rw [ite_eq_left hlt, h1, ← hyS ⟨g, hg⟩]
  · have hg' := (hT g).resolve_left hg
    have h1 := hΦx g hg hg'
    rw [ite_eq_right (by omega), h1, Nat.add_sub_cancel, ← hyS ⟨_, hg'⟩, ← Φ.map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp

end Act

end CFSG.EvenSmallLie.OmegaEight.SpBranch
