module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeP
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4L2Inv

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CatalogueSchreierLinearTwo (semilinearAction semilinearAction_inr semilinearEquivAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {F : Type} [Field F] [Finite F]

theorem psl2_facts_of_perfect (hpp : IsOddPrimePower (Nat.card F))
    (h25 : Nat.card F = 25) {α : MulAut (PSL2 F)} (hα2 : α * α = 1)
    (hr : ((semilinearEquivAut F).symm α).right ≠ 1) {L : Subgroup (PSL2 F)}
    (hL : L ≤ fixedSubgroup α) (hLp : ⁅L, L⁆ = L) (h60 : 60 ≤ Nat.card L) :
    Nat.card L = 60 ∧ (∀ φ : MulAut (PSL2 F), (∀ y ∈ L, φ y = y) → φ = 1 ∨ φ = α) ∧
      60 < Nat.card (fixedSubgroup α) := by
  classical
  have hfixL : ∀ y ∈ L, α y = y := fun y hy => hL hy
  set g := (semilinearEquivAut F).symm α with hgdef
  have hgα' : semilinearAction F g = α := (semilinearEquivAut F).apply_symm_apply α
  have hgg : g * g = 1 := by rw [hgdef, ← map_mul, hα2, map_one]
  have hg1 : g ≠ 1 := fun h => hr (by rw [h]; rfl)
  have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hpp g hgo hr
  have hσσ' : g.right * g.right = 1 := by
    have := congrArg SemidirectProduct.right hgg
    simpa using this
  have hσ : orderOf g.right = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ') hr
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield g.right hσ
  have hσσ : ∀ x, g.right (g.right x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσσ'
    simpa using this
  set c : MulAut (PSL2 F) := semilinearAction F (SemidirectProduct.inl C) with hc
  have hgC : g = SemidirectProduct.inl C * SemidirectProduct.inr g.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hαc : α = c * psl2FieldAut F g.right * c⁻¹ := by
    rw [← hgα', hc]
    conv_lhs => rw [hgC]
    rw [map_mul, map_mul, map_inv, semilinearAction_inr]
  have hL₁p : ⁅(L.map (c⁻¹).toMonoidHom).map (incl F), (L.map (c⁻¹).toMonoidHom).map (incl F)⁆ =
      (L.map (c⁻¹).toMonoidHom).map (incl F) := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hLp]
  have hL₁σ : ∀ x ∈ (L.map (c⁻¹).toMonoidHom).map (incl F),
      x * SemidirectProduct.inr g.right = SemidirectProduct.inr g.right * x := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    symm
    rw [commute_incl_iff, semilinearAction_inr]
    have h1 := hfixL y hy
    rw [hαc] at h1
    have h3 := congrArg (c⁻¹ : MulAut (PSL2 F)) h1
    simpa [MulAut.mul_apply] using h3
  have hL₁le := CatFactsSp4.perfect_centralizer_inr_le hK₀ h90 hσσ hL₁σ hL₁p
  set N' := ((psl2Sub K₀).range).map c.toMonoidHom with hN'def
  have hLN' : L ≤ N' := by
    intro y hy
    obtain ⟨w, hw⟩ := hL₁le ⟨(c⁻¹ : MulAut (PSL2 F)) y, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨psl2Sub K₀ w, ⟨w, rfl⟩, ?_⟩
    have hw' : psl2Sub K₀ w = (c⁻¹ : MulAut (PSL2 F)) y := incl_injective F hw
    change c (psl2Sub K₀ w) = y
    rw [hw']
    simp
  let e₁ : PSL2 K₀ ≃* (psl2Sub K₀).range := MonoidHom.ofInjective (psl2Sub_injective K₀)
  let e₂ : (psl2Sub K₀).range ≃* N' :=
    ((psl2Sub K₀).range).equivMapOfInjective c.toMonoidHom c.injective
  have hK₀5 : Nat.card K₀ = 5 := by
    have h1 : Nat.card K₀ ^ 2 = 5 ^ 2 := by rw [← hcard, h25]; norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1
  have hodd₀ : IsOddPrimePower (Nat.card K₀) :=
    isOddPrimePower_of_odd_card K₀ (by rw [hK₀5]; exact ⟨2, rfl⟩)
  have hN'card : Nat.card N' = 60 := by
    rw [← Nat.card_congr (e₁.trans e₂).toEquiv, psl2_card_formula K₀ hodd₀, hK₀5]
    norm_num
  have hLeq : L = N' :=
    Subgroup.eq_of_le_of_card_ge hLN' (by rw [hN'card]; exact h60)
  refine ⟨by rw [hLeq, hN'card], ?_, ?_⟩
  ·
    intro φ hφ
    set x := (semilinearEquivAut F).symm (c⁻¹ * φ * c) with hxdef
    have hx' : semilinearAction F x = c⁻¹ * φ * c := (semilinearEquivAut F).apply_symm_apply _
    have hx : ∀ w : PSL2 K₀, semilinearAction F x (psl2Sub K₀ w) = psl2Sub K₀ w := by
      intro w
      have hmem : c (psl2Sub K₀ w) ∈ L := by
        rw [hLeq]
        exact ⟨psl2Sub K₀ w, ⟨w, rfl⟩, rfl⟩
      rw [hx', MulAut.mul_apply, MulAut.mul_apply, hφ _ hmem]
      simp
    rcases eq_of_fixes_psl2Sub hr hK₀ hcard x hx with h | h
    · left
      have h1 : c⁻¹ * φ * c = 1 := by rw [← hx', h, map_one]
      calc φ = c * (c⁻¹ * φ * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      have h1 : c⁻¹ * φ * c = psl2FieldAut F g.right := by rw [← hx', h, semilinearAction_inr]
      calc φ = c * (c⁻¹ * φ * c) * c⁻¹ := by group
        _ = α := by rw [h1, hαc]
  ·
    have hfix : (fieldCent g.right).map c.toMonoidHom = fixedSubgroup α := by
      rw [hαc]
      exact FiveFL2.map_fixedSubgroup_mulAutConj c (psl2FieldAut F g.right)
    rw [← hfix, card_map_of_injective c.injective,
      card_fieldCent_eq hK₀ h90 hσσ hcard hpp, BenderSuzuki.External.huppertXI13_card_pgl2,
      hK₀5]
    norm_num

variable {Y : Type} [Group Y]

theorem mbar_facts_psl2 (hpp : IsOddPrimePower (Nat.card F))
    (h25 : Nat.card F = 25) (e : Y ≃* PSL2 F) {s : MulAut Y} (hs2 : s * s = 1)
    (hr : ((semilinearEquivAut F).symm (MulAut.congr e s)).right ≠ 1) {L : Subgroup Y}
    (hL : L ≤ fixedSubgroup s) (hLp : ⁅L, L⁆ = L) (h60 : 60 ≤ Nat.card L) :
    Nat.card L = 60 ∧ (∀ φ : MulAut Y, (∀ y ∈ L, φ y = y) → φ = 1 ∨ φ = s) ∧
      (∀ g : Y, (∀ y ∈ L, g * y * g⁻¹ = y) → g = 1) ∧ 60 < Nat.card (fixedSubgroup s) := by
  classical
  set α := MulAut.congr e s with hαdef
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hs2, map_one]
  have hfixα : (fixedSubgroup s).map e.toMonoidHom = fixedSubgroup α :=
    FiveFHe.map_fixedSubgroup_congr e s
  set L' := L.map e.toMonoidHom with hL'def
  have hL' : L' ≤ fixedSubgroup α := by
    rw [← hfixα]
    exact map_mono hL
  have hL'p : ⁅L', L'⁆ = L' := by rw [hL'def, ← map_commutator, hLp]
  have hcardL' : Nat.card L' = Nat.card L := card_map_of_injective e.injective
  obtain ⟨h1, h2, h3⟩ := psl2_facts_of_perfect hpp h25 hα2 hr hL' hL'p (by rw [hcardL']; exact h60)
  have hcongr : ∀ φ : MulAut Y, (∀ y ∈ L, φ y = y) → φ = 1 ∨ φ = s := by
    intro φ hφ
    have hφ' : ∀ y ∈ L', MulAut.congr e φ y = y := by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulAut.congr_apply]
      simp [hφ y hy]
    rcases h2 _ hφ' with h | h
    · left
      apply (MulAut.congr e).injective
      rw [h, map_one]
    · right
      exact (MulAut.congr e).injective h
  refine ⟨by rw [← hcardL']; exact h1, hcongr, ?_, ?_⟩
  ·
    intro g hg
    rcases hcongr (MulAut.conj g) fun y hy => by rw [MulAut.conj_apply]; exact hg y hy with h | h
    · exact FiveFL2.conj_injective_psl2 e (show MulAut.conj g = MulAut.conj 1 by rw [h, map_one])
    · exfalso
      apply hr
      change (autEquiv e s).right = 1
      rw [← h, autEquiv_conj, incl_apply]
      rfl
  · rw [← hfixα, card_map_of_injective e.injective] at h3
    exact h3

end CFSG.ComponentClassification.SolMax.L32
