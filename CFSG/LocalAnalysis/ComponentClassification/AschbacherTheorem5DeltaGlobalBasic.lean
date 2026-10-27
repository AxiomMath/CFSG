module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveStrong

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem twoElt_conj {t : G} (ht : ∃ k : ℕ, t ^ (2 ^ k) = 1) (g : G) :
    ∃ k : ℕ, (g * t * g⁻¹) ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨k, ?_⟩
  rw [conj_pow, hk]
  group

omit [Finite G] in
theorem twoElt_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {t : G} (ht : t ∈ P) :
    ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_other (hC : Counterexample G D r Abar) (i : Fin r) : ∃ j : Fin r, j ≠ i :=
  Strong.exists_ne_index (two_le hC) i

theorem centralizer_le_conj_of_centralizes (hC : Counterexample G D r Abar) (k : Fin r) (g : G)
    {t : G} (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (hcent : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar k)) (g * t * g⁻¹)) :
    Subgroup.centralizer {t} ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  have hs1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hC' := centralizer_le hC k (twoElt_conj ht2 g) hs1 hcent
  intro x hx
  rw [mem_rightConjugate_iff]
  apply hC'
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
    _ = g * (t * x) * g⁻¹ := by rw [hx]
    _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group

theorem centralizer_le_conj (hC : Counterexample G D r Abar) (i : Fin r) (g : G) {t : G}
    (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htA : t ∈ rightConjugate (aschbacherThm5Preimage D (Abar i)) g) :
    Subgroup.centralizer {t} ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  obtain ⟨j, hji⟩ := exists_other hC i
  rw [mem_rightConjugate_iff] at htA
  exact centralizer_le_conj_of_centralizes hC j g ht2 ht1
    (cross_factor_centralizes D Abar hC.hyp.hcomm j i hji _ htA)

theorem eq_one_of_mem_inf_conj (hC : Counterexample G D r Abar) {i j : Fin r} {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) {t : G} (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (hti : t ∈ aschbacherThm5Preimage D (Abar i))
    (htj : t ∈ rightConjugate (aschbacherThm5Preimage D (Abar j)) x) : t = 1 := by
  by_contra ht1
  obtain ⟨i', hi'⟩ := exists_other hC i
  obtain ⟨j', hj'⟩ := exists_other hC j
  rw [mem_rightConjugate_iff] at htj
  have hs1 : x * t * x⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  apply hx
  apply mem_normalizer_of_fusion hC j' i' (twoElt_conj ht2 x) hs1
    (cross_factor_centralizes D Abar hC.hyp.hcomm j' j hj' _ htj)
  have heq : x⁻¹ * (x * t * x⁻¹) * x = t := by group
  rw [heq]
  exact cross_factor_centralizes D Abar hC.hyp.hcomm i' i hi' _ hti

theorem eq_bot_of_le_inf_conj (hC : Counterexample G D r Abar) {i j : Fin r} {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPi : P ≤ aschbacherThm5Preimage D (Abar i))
    (hPj : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar j)) x) : P = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_inf_conj hC hx (twoElt_of_mem hP ht) (hPi ht) (hPj ht)

theorem not_centralizes_of_mem_conj (hC : Counterexample G D r Abar) {i : Fin r} (k : Fin r)
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {t : G}
    (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htA : t ∈ rightConjugate (aschbacherThm5Preimage D (Abar i)) g) :
    ¬ aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k)) t := by
  intro hcent
  obtain ⟨i', hi'⟩ := exists_other hC i
  rw [mem_rightConjugate_iff] at htA
  have hs1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  apply hg
  apply mem_normalizer_of_fusion hC i' k (twoElt_conj ht2 g) hs1
    (cross_factor_centralizes D Abar hC.hyp.hcomm i' i hi' _ htA)
  have heq : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  rwa [heq]

theorem not_centralizes_conj (hC : Counterexample G D r Abar) {i : Fin r} (k : Fin r)
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {t : G}
    (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htA : t ∈ aschbacherThm5Preimage D (Abar i)) :
    ¬ aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k))
      (g * t * g⁻¹) := by
  intro hcent
  obtain ⟨i', hi'⟩ := exists_other hC i
  apply hg
  have hmem := mem_normalizer_of_fusion hC i' k (t := t) (g := g⁻¹) ht2 ht1
    (cross_factor_centralizes D Abar hC.hyp.hcomm i' i hi' _ htA) (by rwa [inv_inv])
  simpa using (Subgroup.normalizer (D : Set G)).inv_mem hmem

theorem commute_of_normalizers (hC : Counterexample G D r Abar) {a : Fin r} {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T W P : Subgroup G}
    (hT : T ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hW : W ≤ aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G))
    (hP : IsPGroup 2 P) (hTWP : ∀ t ∈ T, ∀ w ∈ W, t⁻¹ * w⁻¹ * t * w ∈ P) :
    ∀ t ∈ T, ∀ w ∈ W, t * w = w * t := by
  intro t ht w hw
  set A := aschbacherThm5Preimage D (Abar a)
  set L := rightConjugate A g
  have hcA : t⁻¹ * w⁻¹ * t * w ∈ A := by
    have h1 : t⁻¹ * w⁻¹ * t ∈ A := by
      have h2 : w⁻¹ ∈ A := A.inv_mem (hW hw).1
      have h3 := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hT ht).2) (w⁻¹)).mp h2
      simpa [mul_assoc] using h3
    exact A.mul_mem h1 (hW hw).1
  have hcL : t⁻¹ * w⁻¹ * t * w ∈ L := by
    have h1 : w⁻¹ * t * w ∈ L := by
      have h3 := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hW hw).2) t).mp (hT ht).1
      simpa [mul_assoc] using h3
    have h2 : t⁻¹ * (w⁻¹ * t * w) ∈ L := L.mul_mem (L.inv_mem (hT ht).1) h1
    simpa [mul_assoc] using h2
  have h1 := eq_one_of_mem_inf_conj hC hg (twoElt_of_mem hP (hTWP t ht w hw)) hcA hcL
  have h2 : t⁻¹ * w⁻¹ * t * w = (w * t)⁻¹ * (t * w) := by group
  rw [h2, inv_mul_eq_one] at h1
  exact h1.symm

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
