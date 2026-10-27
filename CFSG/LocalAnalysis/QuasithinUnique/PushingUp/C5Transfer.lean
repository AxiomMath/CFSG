module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Open Subgroup

section Separate

variable {E : Type*} [Group E] [Finite E]

theorem exists_hom_units_of_notMem (hcomm : ∀ a b : E, a * b = b * a) (hE : ∀ e : E, e * e = 1)
    {A : Subgroup E} {z : E} (hz : z ∉ A) :
    ∃ f : E →* ℤˣ, (∀ a ∈ A, f a = 1) ∧ f z = -1 := by
  classical
  have : Finite (Subgroup E) :=
    Finite.of_injective (SetLike.coe : Subgroup E → Set E) SetLike.coe_injective
  have : Fintype (Subgroup E) := Fintype.ofFinite _
  obtain ⟨H₀, hH₀, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun H : Subgroup E => A ≤ H ∧ z ∉ H)
    (fun H : Subgroup E => Nat.card H) ⟨A, by simp [hz]⟩
  obtain ⟨hAH, hzH⟩ := (Finset.mem_filter.mp hH₀).2
  have hzz : z * z = 1 := hE z
  have key : ∀ y : E, y ∈ H₀ ∨ y * z ∈ H₀ := by
    intro y
    by_cases hy : y ∈ H₀
    · exact Or.inl hy
    · right
      set H₁ := H₀ ⊔ zpowers y with hH₁
      have hAH₁ : A ≤ H₁ := hAH.trans le_sup_left
      have hlt : H₀ < H₁ := by
        refine lt_of_le_of_ne le_sup_left fun h => hy ?_
        have : y ∈ H₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
        rwa [← h] at this
      have hcard : Nat.card H₀ < Nat.card H₁ := Subgroup.card_lt_of_lt hlt
      have hzH₁ : z ∈ H₁ := by
        by_contra hz₁
        have := hmax H₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAH₁, hz₁⟩)
        omega
      obtain ⟨h, hh, w, hw, hhw⟩ := mem_sup_of_commute (fun a _ b _ => hcomm a b) hzH₁
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hy2 : y * y = 1 := hE y
      have hyk : y ^ k = 1 ∨ y ^ k = y := by
        have h2 : y ^ (2 * (k / 2)) = 1 := by
          rw [zpow_mul]
          have : y ^ (2 : ℤ) = 1 := by simpa [pow_two] using hy2
          rw [this, one_zpow]
        have hk' : k = 2 * (k / 2) + k % 2 := by omega
        have hk : y ^ k = y ^ (k % 2) := by
          conv_lhs => rw [hk']
          rw [zpow_add, h2, one_mul]
        rw [hk]
        rcases Int.emod_two_eq_zero_or_one k with h0 | h0
        · left; rw [h0]; simp
        · right; rw [h0]; simp
      rcases hyk with h1 | h1
      · exfalso
        rw [h1, mul_one] at hhw
        exact hzH (hhw ▸ hh)
      · rw [h1] at hhw
        have : y * z = h := by
          rw [hhw, ← mul_assoc, hcomm y h, mul_assoc, hy2, mul_one]
        rw [this]; exact hh
  refine ⟨{ toFun := fun e => if e ∈ H₀ then 1 else -1, map_one' := by simp, map_mul' := ?_ },
    ?_, ?_⟩
  · intro e₁ e₂
    by_cases h₁ : e₁ ∈ H₀ <;> by_cases h₂ : e₂ ∈ H₀
    · simp [h₁, h₂, mul_mem h₁ h₂]
    · have : e₁ * e₂ ∉ H₀ := fun h => h₂ (by simpa using mul_mem (inv_mem h₁) h)
      simp [h₁, h₂, this]
    · have : e₁ * e₂ ∉ H₀ := fun h => h₁ (by simpa using mul_mem h (inv_mem h₂))
      simp [h₁, h₂, this]
    · have h₁' : e₁ * z ∈ H₀ := (key e₁).resolve_left h₁
      have h₂' : e₂ * z ∈ H₀ := (key e₂).resolve_left h₂
      have : e₁ * e₂ ∈ H₀ := by
        have e : e₁ * e₂ = (e₁ * z) * (e₂ * z) := by
          calc e₁ * e₂ = e₁ * e₂ * (z * z) := by rw [hzz, mul_one]
            _ = e₁ * (e₂ * z) * z := by group
            _ = e₁ * (z * e₂) * z := by rw [hcomm e₂ z]
            _ = (e₁ * z) * (e₂ * z) := by rw [← mul_assoc e₁ z e₂, mul_assoc (e₁ * z) e₂ z]
        rw [e]; exact mul_mem h₁' h₂'
      simp [h₁, h₂, this]
  · intro a ha
    simp [hAH ha]
  · simp [hzH]

end Separate

section Norm

variable {L E : Type*} [Group L] [Group E]

theorem exists_invariant_hom [Finite L] (act : L →* MulAut E) (T : Subgroup L) (f : E →* ℤˣ)
    (hf : ∀ t ∈ T, ∀ e, f (act t e) = f e) :
    ∃ F : E →* ℤˣ, (∀ h e, F (act h e) = F e) ∧
      ∀ z, (∀ h, act h z = z) → F z = f z ^ T.index := by
  classical
  have : Fintype (L ⧸ T) := Fintype.ofFinite _
  let φ : (L ⧸ T) → E →* ℤˣ := fun x => f.comp (act (Quotient.out x)⁻¹).toMonoidHom
  refine ⟨∏ x, φ x, ?_, ?_⟩
  · intro h e
    rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply]
    refine Fintype.prod_equiv (MulAction.toPerm h⁻¹) _ _ fun x => ?_
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (h⁻¹ * Quotient.out x)
    have hx : (QuotientGroup.mk (Quotient.out x) : L ⧸ T) = x := Quotient.out_eq' x
    have hsm : (MulAction.toPerm h⁻¹ : Equiv.Perm (L ⧸ T)) x =
        (QuotientGroup.mk (h⁻¹ * Quotient.out x) : L ⧸ T) := by
      conv_lhs => rw [← hx]
      rfl
    rw [hsm, ht]
    have e1 : (act ((h⁻¹ * Quotient.out x * (t : L))⁻¹)) e =
        act (t : L)⁻¹ (act (Quotient.out x)⁻¹ (act h e)) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e1, hf _ (inv_mem t.2)]
  · intro z hz
    rw [MonoidHom.finsetProd_apply]
    have : ∀ x : L ⧸ T, φ x z = f z := by
      intro x
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hz]
    simp only [this, Finset.prod_const, Finset.card_univ]
    rw [Subgroup.index, Nat.card_eq_fintype_card]

end Norm

end CFSG.QuasithinUnique.C5

namespace CFSG.QuasithinUnique.C1

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem blockZ_le_commutator_sylow (hL : IsShort2 L) {T : Subgroup G} (hT : IsSylowTwoOf T L) :
    blockZ L ≤ ⁅blockU L, T⁆ := by
  classical
  intro z hz
  by_contra hzA
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (elemAb2_blockU hL).1
  have hUL : blockU L ≤ L := (blockU_le_blockQ hL).trans (blockQ_le L)
  have hLN : L ≤ normalizer (blockU L : Set G) := le_normalizer_blockU L
  have hnorm : ((blockU L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr hLN
  let act : ↥L →* MulAut ↥((blockU L).subgroupOf L) := MulAut.conjNormal
  let f₀ : ↥((blockU L).subgroupOf L) →* G := L.subtype.comp ((blockU L).subgroupOf L).subtype
  have hf₀ : Function.Injective f₀ := Subtype.val_injective.comp Subtype.val_injective
  have hf₀val : ∀ e : ↥((blockU L).subgroupOf L), f₀ e = ((e : L) : G) := fun _ => rfl
  have hcomm : ∀ a b : ↥((blockU L).subgroupOf L), a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (hUab _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))
  let A' : Subgroup ↥((blockU L).subgroupOf L) := (⁅blockU L, T⁆).comap f₀
  let z' : ↥((blockU L).subgroupOf L) :=
    ⟨⟨z, hUL hz.1⟩, Subgroup.mem_subgroupOf.mpr hz.1⟩
  have hz'A : z' ∉ A' := hzA
  have hE : ∀ e : ↥((blockU L).subgroupOf L), e * e = 1 := by
    intro e
    have h := blockU_sq hL _ (Subgroup.mem_subgroupOf.mp e.2)
    apply Subtype.ext; apply Subtype.ext
    simpa [pow_two] using h
  obtain ⟨f, hfA, hfz⟩ := C5.exists_hom_units_of_notMem hcomm hE hz'A
  have hT' : ∀ t ∈ T.subgroupOf L, ∀ e, f (act t e) = f e := by
    intro t ht e
    have hmem : act t e * e⁻¹ ∈ A' := by
      show f₀ (act t e * e⁻¹) ∈ ⁅blockU L, T⁆
      have hte : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      have heU : f₀ e ∈ blockU L := Subgroup.mem_subgroupOf.mp e.2
      have : f₀ (act t e * e⁻¹) = ⁅(t : G), f₀ e⁆ := by
        rw [map_mul, map_inv, commutatorElement_def]
        simp [hf₀val, act]
      rw [this, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hte heU
    calc f (act t e) = f (act t e * e⁻¹) * f e := by rw [← map_mul]; group
      _ = f e := by rw [hfA _ hmem, one_mul]
  obtain ⟨F, hFinv, hFz⟩ := C5.exists_invariant_hom act (T.subgroupOf L) f hT'
  have hodd : Odd (T.subgroupOf L).index := by
    have := hT.2.2
    exact Nat.odd_iff.mpr (by omega)
  have hFz' : F z' = -1 := by
    rw [hFz z' ?_, hfz, hodd.neg_one_pow]
    intro l
    apply Subtype.ext; apply Subtype.ext
    show (l : G) * z * (l : G)⁻¹ = z
    have := Subgroup.mem_centralizer_iff.mp hz.2 (l : G) l.2
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have hUK : blockU L ≤ (F.ker).map f₀ := by
    refine (commutator_blockU hL).symm.le.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu l hl
    set u' : ↥((blockU L).subgroupOf L) := ⟨⟨u, hUL hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ with hu'
    refine ⟨u' * (act ⟨l, hl⟩ u')⁻¹, ?_, ?_⟩
    · show F (u' * (act ⟨l, hl⟩ u')⁻¹) = 1
      rw [map_mul, map_inv, hFinv, mul_inv_cancel]
    · rw [map_mul, map_inv, commutatorElement_def]
      simp [hf₀val, act, u', mul_assoc]
  obtain ⟨w, hw, hwz⟩ := hUK hz.1
  have hwz' : w = z' := hf₀ (by rw [hwz]; rfl)
  have hFw : F w = 1 := hw
  rw [hwz', hFz'] at hFw
  exact absurd hFw (by decide)

end CFSG.QuasithinUnique.C1
