module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalDefs

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
theorem le_normalizer_bot (T : Subgroup G) :
    T ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  intro t _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro h
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group

theorem exists_invariant_sylow {K T P : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hP : IsPGroup 2 P) (hPK : P ≤ K)
    (hTP : T ≤ Subgroup.normalizer (P : Set G)) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ P ≤ S ∧ T ≤ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (P ⊔ T : Subgroup G) := IsPGroup.to_sup_of_normal_left' hP hT hTP
  obtain ⟨Q, hQ, hle⟩ := AschbacherTheorem3.exists_isSylowOf_le h2
    (sup_le_sup_right hPK T : P ⊔ T ≤ K ⊔ T)
  refine ⟨Q ⊓ K, hQ.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTK),
    le_inf (le_sup_left.trans hle) hPK, fun t ht => ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (hle (Subgroup.mem_sup_right ht)), hTK ht⟩

theorem normalizer_conj_le (hC : Counterexample G D r Abar) (i : Fin r) (g : G) :
    Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar i)) g : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  rw [← AschbacherTheorem3.rightConjugate_normalizer]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate
    (factor_normalizer_le D r Abar hC.hyp.hii i) g

omit [Finite G] in
theorem conj_factor_le (i : Fin r) (g : G) :
    rightConjugate (aschbacherThm5Preimage D (Abar i)) g ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g :=
  AschbacherTheorem3.rightConjugate_le_rightConjugate
    ((preimage_le D _).trans Subgroup.le_normalizer) g

theorem exists_sylow_datum (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) :
    ∃ d : DeltaDatum D Abar a, d.g = g ∧
      IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G))
        (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set L := rightConjugate A g with hLdef
  set Hg := rightConjugate H g with hHgdef
  obtain ⟨-, -, hne', U, hU'⟩ := hΔ
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (L ⊓ Subgroup.normalizer (A : Set G))
  have hTL : T ≤ L := hT.le.trans inf_le_left
  have hTA : T ≤ Subgroup.normalizer (A : Set G) := hT.le.trans inf_le_right
  have hTHg : T ≤ Hg := hTL.trans (conj_factor_le a g)
  have hTNL : T ≤ Subgroup.normalizer (L : Set G) := hTL.trans Subgroup.le_normalizer
  have hNLHg : Subgroup.normalizer (L : Set G) ≤ Hg := normalizer_conj_le hC a g
  have hTN : T ≤ Subgroup.normalizer
      ((A ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTA ht, Subgroup.le_normalizer (hTNL ht)⟩
  obtain ⟨P₀, hP₀, -, hTP₀⟩ := exists_invariant_sylow hT.isPGroup hTN
    (IsPGroup.of_card (n := 0) (by simp) : IsPGroup 2 (⊥ : Subgroup G)) bot_le
    (le_normalizer_bot T)
  have hTAHg : T ≤ Subgroup.normalizer ((A ⊓ Hg : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTA ht, Subgroup.le_normalizer (hTHg ht)⟩
  obtain ⟨P₁, hP₁, hP₀P₁, hTP₁⟩ := exists_invariant_sylow hT.isPGroup hTAHg hP₀.isPGroup
    (hP₀.le.trans (inf_le_inf_left A hNLHg)) hTP₀
  obtain ⟨S, hS, hP₁S, hTS⟩ := exists_invariant_sylow hT.isPGroup hTA hP₁.isPGroup
    (hP₁.le.trans inf_le_left) hTP₁
  have hSHg : IsSylowOf 2 (S ⊓ Hg) (A ⊓ Hg) := by
    have heq := hP₁.eq_of_le (le_inf hP₁S (hP₁.le.trans inf_le_right))
      (inf_le_inf_right Hg hS.le) (hS.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hP₁
  have hSN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (L : Set G))
      (A ⊓ Subgroup.normalizer (L : Set G)) := by
    have heq := hP₀.eq_of_le (le_inf (hP₀P₁.trans hP₁S) (hP₀.le.trans inf_le_right))
      (inf_le_inf_right _ hS.le) (hS.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hP₀
  exact ⟨⟨g, hne', U, hU', T, hT, S, hS, hTS, hSHg⟩, rfl, hSN⟩

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
