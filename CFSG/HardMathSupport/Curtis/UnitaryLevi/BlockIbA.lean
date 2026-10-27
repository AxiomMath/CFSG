module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinThree
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinVoidA

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem isClassicalTwoOrG2_of_isLieOf_A {X : Type} [Group X] (h : IsLieOf IdxA X) :
    IsClassicalTwoOrG2 X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | A r q => exact Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩
  | _ => exact hd.elim

section Core

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIbA_core (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hA : IsLieOf IdxA (↥Lb ⧸ Subgroup.center ↥Lb))
    (U : Subgroup Y) (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hUD : U ≤ Subgroup.centralizer (D : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∃ (X : Type) (_ : Group X) (φ : ↥U →* MulAut X), IsCyclic φ.range ∧
      ∀ a : ↥U, φ a = 1 → (a : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
  have hT := isClassicalTwoOrG2_of_isLieOf_A hA
  obtain ⟨n, f, hn2, hf1, hn2f, hn3f, hn4f, ⟨e⟩⟩ := exists_model_A hA
  have hperf : Group.IsPerfect ↥Lb := ⟨hP.comp.2.2.1⟩
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
    · exact (blockIb_false_of_two hP hD hT e).elim
    · refine ⟨_, inferInstance, (descendHom e).comp (Subgroup.inclusion hUL),
        blockIb_cyclic_three hP hD hT (hn3f rfl) e U hUL hUP hUD hU3, ?_⟩
      intro a ha
      exact mem_centralizer_of_descendAut_eq_one e (hUL a.2) ha
  · exact (blockIb_false_of_four_le hP hD h4 hf1 hn4f e).elim

end Core

section Fam

theorem blockIbAbFam_A : BlockIbAbFam (IsLieOf IdxA) := by
  intro Y _ _ Lb Pb D x hP hA hD U hUL hUP hUD hU3
  obtain ⟨X, _, φ, hcyc, hker⟩ := blockIbA_core hP hD hA U hUL hUP hUD hU3
  intro a ha b hb
  have hcomm : ∀ u v : φ.range, u * v = v * u := by
    letI := hcyc.commGroup
    intro u v; exact mul_comm u v
  have h1 := hcomm ⟨φ ⟨a, ha⟩, ⟨_, rfl⟩⟩ ⟨φ ⟨b, hb⟩, ⟨_, rfl⟩⟩
  have h2 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := congrArg Subtype.val h1
  have h3 : φ (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  exact hker _ h3

theorem blockIbRankFam_A : BlockIbRankFam (IsLieOf IdxA) := by
  intro Y _ _ Lb Pb D x hP hA hD E hEL hEP hED hEab hE9 t ht htE htF
  by_contra hcon
  have hE3 : IsPGroup 3 E := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 2) (by rw [hE9])
  obtain ⟨X, _, φ, hcyc, hker⟩ := blockIbA_core hP hD hA E hEL hEP hED hE3
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hC := hker a ha
    have : (a : Y) ∈ E ⊓ Subgroup.centralizer (Lb : Set Y) := ⟨a.2, hC⟩
    rw [hcon, Subgroup.mem_bot] at this
    exact Subtype.ext this
  haveI : IsCyclic ↥E := by
    have e : ↥E ≃* φ.range := MonoidHom.ofInjective hinj
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have hgo : orderOf g = 3 ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hE9]
  have h3 : (g : Y) ^ 3 = 1 := hEab.2 _ g.2
  have : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  rw [hgo] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

end Fam

end CFSG.HardMathSupport.Curtis.UnitaryLevi
