module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIInner

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ S : Subgroup G}

theorem Sec3.exists_t_conj_normalizes [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hS : Sec3 T T₁) (hcard : Nat.card T = Nat.card (normIn T T₁) * 2)
    (hL8 : 8 ≤ Nat.card (normIn T T₁)) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (T : Set G))
    (hSL : S ≤ Subgroup.normalizer (normIn T T₁ : Set G)) (hL₁S : normIn T₁ T ≤ S) {x u : G}
    (hxS : x ∈ S) (hxx : x * x = 1) (hu : u ∈ normIn T T₁)
    (hvals : ∀ t ∈ T, ⁅t, x⁆ = 1 ∨ ⁅t, x⁆ = u) :
    ∃ t ∈ T, conjSubgroup (t⁻¹ * x) T₁ = T₁ := by
  by_cases hT₁x : conjSubgroup x T₁ = T₁
  · exact ⟨1, T.one_mem, by rw [inv_one, one_mul]; exact hT₁x⟩
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := hSN hxS
  have hxL : x ∈ Subgroup.normalizer (normIn T T₁ : Set G) := hSL hxS
  have h38 := section3Eight h214 hInv hSz hnab hS hS2 hSN hSL hL₁S
  have hcomm : ∀ e ∈ normIn T₁ T, ∀ f ∈ conjSubgroup x (normIn T₁ T), e * f = f * e := by
    intro e he f hf
    have heK : e ∈ ⨆ s : S, conjSubgroup (s : G) (normIn T₁ T) :=
      Subgroup.mem_iSup_of_mem (⟨1, S.one_mem⟩ : S) (by
        show e ∈ conjSubgroup 1 (normIn T₁ T)
        rw [conjSubgroup_one]
        exact he)
    have hfK : f ∈ ⨆ s : S, conjSubgroup (s : G) (normIn T₁ T) :=
      Subgroup.mem_iSup_of_mem (⟨x, hxS⟩ : S) hf
    exact elemAbelian_mul_comm h38 heK hfK
  have hB6 : SecB6 T T₁ S x := ⟨hS, hS2, hL₁S, hxS, hxx, hxN, hxL, hT₁x, hcomm, hcard⟩
  have hS₂ := hB6.sec₂ h214 hInv
  have hNorm := hS₂.normal_cfgM_subgroupOf
  have hpair := Sec3.sylowInner_map h214 hSz hnab hS₂
  exact hB6.exists_t_normalizes h214 hInv hu hvals hL8 hpair

end CFSG.CGT.Timmesfeld75
