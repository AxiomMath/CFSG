module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmMain
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmNA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEGlue
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5DempwolffMin

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.GMS78.RuPi7

theorem orderOf_ruZ0 :
    orderOf ruZ0 = 2 := by
  have hz : ruZ0 = ruA0Elt 1 := by rw [ruA0Elt, show ruA0PowWord 1 = ruZ0Word by decide]; rfl
  have h2 : ruZ0 ^ 2 = 1 := by
    rw [sq, hz, ruA0Elt_mul (by norm_num) (by norm_num), Nat.xor_self, ruA0Elt_zero]
  exact orderOf_eq_prime h2 ruZ0_ne_one

variable {G : Type} [Group G] {z : G} {A : Subgroup G}

theorem orderOf_eq_two_of_isNormCz
    {f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))}
    (h : IsNormCz f₁ A) : orderOf z = 2 := by
  have hz0 : ruZ0 ∈ ruM1 := pi7Word_mem_letterSub (by decide)
  rw [← h.1 ⟨ruZ0, hz0⟩ rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact orderOf_ruZ0

theorem nonempty_mulEquiv_ru_of_pi7b
    [Finite G] {e : G}
    {f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))} (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hf₁ : IsNormCz f₁ A) (hag : RuEdgeAgree f₁ f₂ (MonoidHom.id _))
    (hzc : 2 ^ 9 ∣ Nat.card (centralizer ({z} : Set G)))
    (he : e ∈ normalizer (A : Set G)) (he2 : orderOf e = 2)
    (hec : Nat.card (centralizer ({e} : Set G)) = 116480) :
    Nonempty (G ≃* Blueprint.NativeSporadic.Ru) :=
  nonempty_mulEquiv_ru_of_edgeAgree RuNE.pi7bEquivRu RuNE.pi7bRels_cases f₁ f₂ hag
    (RuNE.ruLetterImg_w_pow_seven hf₁ hag) (orderOf_eq_two_of_isNormCz hf₁) hzc he he2 hec

@[expose] def RuEdgeData (G : Type) [Group G] : Prop :=
  ∃ (z e : G) (A : Subgroup G) (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G)))
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G))),
    IsNormCz f₁ A ∧ RuEdgeAgree f₁ f₂ (MonoidHom.id _) ∧
      2 ^ 9 ∣ Nat.card (centralizer ({z} : Set G)) ∧ e ∈ normalizer (A : Set G) ∧
        orderOf e = 2 ∧ Nat.card (centralizer ({e} : Set G)) = 116480

theorem nonempty_mulEquiv_ru_of_edgeData
    [Finite G] (h : RuEdgeData G) :
    Nonempty (G ≃* Blueprint.NativeSporadic.Ru) := by
  obtain ⟨z, e, A, f₁, f₂, hf₁, hag, hzc, he, he2, hec⟩ := h
  exact nonempty_mulEquiv_ru_of_pi7b f₂ hf₁ hag hzc he he2 hec

theorem dempwolffRuMin_of_edgeData
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SzMinCounter G L 1 →
      ∀ T₀ : Subgroup G, IsSylowOf 2 T₀ (centralizer (L : Set G)) → Nat.card T₀ = 4 →
        RuEdgeData G) :
    DempwolffRuMin := by
  intro G _ _ L hM T₀ hT₀ h4
  obtain ⟨eG⟩ := nonempty_mulEquiv_ru_of_edgeData (h G L hM T₀ hT₀ h4)
  exact hM.false_of_mulEquiv_ru eG

end CFSG.ComponentClassification.GMS78.RuAsm
