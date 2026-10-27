module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortAux
public import CFSG.HardMathSupport.RichardWeiss.Proving.NoCharNormal
public import CFSG.Quasithin.H13.GoldschmidtI51Elem

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem false_of_caseI {X S L Q : Subgroup G} (hA : CFSG.AGLEmbedding.Asc81bHyp X S) (hL : L ≤ X)
    (hLS : ¬ L ≤ Subgroup.normalizer (S : Set G)) (hQS : Q ≤ S)
    (hQL : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q)
    (hCQ : S ⊓ Subgroup.centralizer ((⁅S, S⁆ : Subgroup G) : Set G) ≤ Q)
    (hI : ⁅L, Q⁆ ≤ Subgroup.centralizer ((⁅S, S⁆ : Subgroup G) : Set G)) : False := by
  set S' : Subgroup G := ⁅S, S⁆ with hS'
  set C : Subgroup G := S ⊓ Subgroup.centralizer (S' : Set G) with hC
  have hS' : S' ≤ S := Subgroup.commutator_le.2 fun a ha b hb => by
    simpa [commutatorElement_def, mul_assoc] using
      S.mul_mem (S.mul_mem ha hb) (S.mul_mem (S.inv_mem ha) (S.inv_mem hb))
  have hchar : (C.subgroupOf S).Characteristic :=
    centralizer_characteristic (Y := S') hS' (by
      have := commutator_characteristic (Y := S) le_rfl (by
        rw [Subgroup.subgroupOf_self]; infer_instance)
      exact this)
  have hCS : C ≤ S := inf_le_left
  have hSp : IsPGroup 2 S := by
    have := hA.twoRadical.2.2
    rw [this]
    exact CFSG.Quasithin.H13.I51.isPGroup_pCoreOf _
  have hC1 : C ≠ ⊥ := by
    have hS1 : S ≠ ⊥ := hA.twoRadical.2.1
    haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hS1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hbot := hSp.bot_lt_center
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Subgroup.center S)).1
      (bot_lt_iff_ne_bot.1 hbot)
    intro hCb
    have hzC : ((z : S) : G) ∈ C := by
      refine ⟨(z : S).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have hh' : h ∈ S := hS' hh
      have := Subgroup.mem_center_iff.1 (z.2) ⟨h, hh'⟩
      exact congrArg Subtype.val this
    rw [hCb] at hzC
    apply hz1
    exact Subtype.ext (Subtype.ext (by simpa using hzC))
  have hnorm : ∀ l ∈ L, ∀ c ∈ C, l * c * l⁻¹ ∈ C := by
    intro l hl c hc
    have hcQ : c ∈ Q := hCQ hc
    have hlcQ : l * c * l⁻¹ ∈ Q := hQL l hl c hcQ
    have hcomm : (l * c * l⁻¹) * c⁻¹ ∈ Subgroup.centralizer (S' : Set G) := by
      apply hI
      have : ⁅l, c⁆ ∈ ⁅L, Q⁆ := Subgroup.commutator_mem_commutator hl hcQ
      simpa [commutatorElement_def, mul_assoc] using this
    refine ⟨hQS hlcQ, ?_⟩
    have := Subgroup.mul_mem _ hcomm hc.2
    simpa [mul_assoc] using this
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hnorm l hl h hh, fun hh => ?_⟩
    have := hnorm l⁻¹ (L.inv_mem hl) _ hh
    simpa [mul_assoc] using this
  exact noCharNormal_of_asc81bHyp hA hL (R₀ := C) hCS hchar hLS C le_rfl hC1
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hLC

end CFSG.HardMathSupport.RichardWeiss.Proving
