module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeights
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open Subgroup

section Lines

variable {A : Type*} [CommGroup A] [Finite A]

omit [Finite A] in
theorem card_zpowers_of_pow_five {g : A} (hg : g ^ 5 = 1) (hg1 : g ≠ 1) :
    Nat.card (zpowers g) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hg hg1

omit [Finite A] in
theorem index_eq_five_of_card {F : Subgroup A} (hAcard : Nat.card A = 5 ^ 2)
    (hF : Nat.card F = 5) : F.index = 5 := by
  have h := F.card_mul_index
  rw [hF, hAcard] at h
  omega

end Lines

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open Subgroup

section Lines2

variable {A : Type*} [CommGroup A] [Finite A]

theorem exists_not_mem_of_card {S : Finset (Subgroup A)} (hS : ∀ F ∈ S, Nat.card F ≤ 5)
    (hcard : 5 * S.card < Nat.card A) : ∃ g : A, ∀ F ∈ S, g ∉ F := by
  by_contra hall
  push Not at hall
  have hcov : (Set.univ : Set A) ⊆ ⋃ F ∈ S, (F : Set A) := by
    intro g _
    obtain ⟨F, hF, hgF⟩ := hall g
    exact Set.mem_biUnion hF hgF
  have h1 : Nat.card A ≤ (⋃ F ∈ S, (F : Set A)).ncard := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard hcov (Set.toFinite _)
  have h2 : (⋃ F ∈ S, (F : Set A)).ncard ≤ ∑ F ∈ S, (F : Set A).ncard :=
    Finset.set_ncard_biUnion_le S (fun F => (F : Set A))
  have h3 : ∑ F ∈ S, (F : Set A).ncard ≤ ∑ _F ∈ S, 5 := by
    refine Finset.sum_le_sum fun F hF => ?_
    have := hS F hF
    rwa [← Nat.card_coe_set_eq]
  rw [Finset.sum_const, smul_eq_mul, mul_comm] at h3
  omega

end Lines2

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open Subgroup

section Lines3

variable {A : Type*} [CommGroup A] [Finite A]

open Classical in
theorem exists_four_lines (hA : ∀ a : A, a ^ 5 = 1) (hAcard : Nat.card A = 5 ^ 2) :
    ∃ F : Fin 4 → Subgroup A, Function.Injective F ∧ ∀ j, (F j).index = 5 := by
  have hc : ∀ g : A, Nat.card (zpowers g) ≤ 5 := fun g => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA g))
  have hbot : Nat.card (⊥ : Subgroup A) ≤ 5 := by rw [card_bot]; norm_num
  obtain ⟨g₀, hg₀⟩ := exists_not_mem_of_card (S := {⊥})
    (fun F hF => by rw [Finset.mem_singleton.mp hF]; exact hbot) (by rw [hAcard]; simp)
  have h₀ : g₀ ≠ 1 := fun h => hg₀ ⊥ (by simp) (h ▸ one_mem _)
  obtain ⟨g₁, hg₁⟩ := exists_not_mem_of_card (S := {zpowers g₀})
    (fun F hF => by rw [Finset.mem_singleton.mp hF]; exact hc g₀) (by rw [hAcard]; simp)
  obtain ⟨g₂, hg₂⟩ := exists_not_mem_of_card (S := {zpowers g₀, zpowers g₁})
    (fun F hF => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl <;> exact hc _)
    (by
      have h2 := (Finset.card_le_two : ({zpowers g₀, zpowers g₁} : Finset _).card ≤ 2)
      rw [hAcard]
      omega)
  obtain ⟨g₃, hg₃⟩ := exists_not_mem_of_card (S := {zpowers g₀, zpowers g₁, zpowers g₂})
    (fun F hF => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl | rfl <;> exact hc _)
    (by
      have h3 := (Finset.card_le_three :
        ({zpowers g₀, zpowers g₁, zpowers g₂} : Finset _).card ≤ 3)
      rw [hAcard]
      omega)
  have n1 : g₁ ∉ zpowers g₀ := hg₁ _ (Finset.mem_singleton_self _)
  have n20 : g₂ ∉ zpowers g₀ := hg₂ _ (by simp)
  have n21 : g₂ ∉ zpowers g₁ := hg₂ _ (by simp)
  have n30 : g₃ ∉ zpowers g₀ := hg₃ _ (by simp)
  have n31 : g₃ ∉ zpowers g₁ := hg₃ _ (by simp)
  have n32 : g₃ ∉ zpowers g₂ := hg₃ _ (by simp)
  have hne : ∀ {x y : A}, y ∉ zpowers x → zpowers x ≠ zpowers y := fun hy hxy =>
    hy (hxy ▸ mem_zpowers _)
  have hne1 : ∀ {x : A}, x ∉ zpowers g₀ → x ≠ 1 := fun hx h => hx (h ▸ one_mem _)
  set g : Fin 4 → A := ![g₀, g₁, g₂, g₃] with hg
  have hlt : ∀ i j : Fin 4, i < j → g j ∉ zpowers (g i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | assumption
  refine ⟨fun j => zpowers (g j), fun i j hij => ?_, fun j => ?_⟩
  · have hij' : zpowers (g i) = zpowers (g j) := hij
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hlt i j h (hij' ▸ mem_zpowers _)
    · exact hlt j i h (hij'.symm ▸ mem_zpowers _)
  · refine index_eq_five_of_card hAcard (card_zpowers_of_pow_five (hA _) ?_)
    fin_cases j
    · exact h₀
    · exact hne1 n1
    · exact hne1 n20
    · exact hne1 n30

end Lines3

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open Subgroup

section Transitive

variable {A : Type*} [CommGroup A] [Finite A] {V : Type*} [CommGroup V] [Finite V]
  [MulDistribMulAction A V]

theorem exists_four_lines_fixedPiece {s : ℕ} [Fact s.Prime] (hs5 : s ≠ 5)
    (hA : ∀ a : A, a ^ 5 = 1) (hAcard : Nat.card A = 5 ^ 2) (hV : ∀ v : V, v ^ s = 1)
    (Γ : Set (MulAut A × MulAut V)) (hΓ : ∀ g ∈ Γ, ∀ (a : A) (v : V), g.2 (a • v) = g.1 a • g.2 v)
    (htrans : ∀ F F' : Subgroup A, F.index = 5 → F'.index = 5 →
      ∃ g ∈ Γ, F.map g.1.toMonoidHom = F')
    (hnt : ∃ (a : A) (v : V), a • v ≠ v) :
    ∃ F : Fin 4 → Subgroup A, Function.Injective F ∧ (∀ j, (F j).index = 5) ∧
      ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5V : ¬ 5 ∣ Nat.card V := fun h => by
    have hcop := coprime_card_of_exponent hs5 hA hV
    rw [hAcard] at hcop
    have hc5 : Nat.Coprime 5 (Nat.card V) :=
      Nat.Coprime.coprime_dvd_left (dvd_pow_self 5 (by norm_num)) hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hc5 h) (by norm_num)
  obtain ⟨F₀, hF₀, hne₀⟩ := exists_fixedPiece_ne_bot hA h5V hnt
  obtain ⟨F, hFinj, hFidx⟩ := exists_four_lines hA hAcard
  refine ⟨F, hFinj, hFidx, fun j => ?_⟩
  obtain ⟨g, hg, hgF⟩ := htrans F₀ (F j) hF₀ (hFidx j)
  rw [← hgF]
  exact fixedPiece_map_ne_bot (hΓ g hg) hne₀

end Transitive

end CFSG.AGLEmbedding
