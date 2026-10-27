module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4L2Inv
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab

public section

namespace CFSG.ComponentClassification.SolMax.FiveFL2

open CFSG Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.SolMax.FiveFHe (HasOddA card_eq_card_ker_mul)
open CatalogueSchreierLinearTwo (semilinearAction semilinearAction_inr semilinearEquivAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {F : Type} [Field F] [Finite F]

theorem eq_five_of_half_mul_sq_sub {r : ℕ} (h4 : 4 ≤ r) (h : r * (r ^ 2 - 1) / 2 = 60) :
    r = 5 := by
  rcases Nat.lt_or_ge r 6 with h6 | h6
  · obtain rfl | rfl : r = 4 ∨ r = 5 := by omega
    · norm_num at h
    · rfl
  · exfalso
    have h1 : 6 * (6 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul h6 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h6 2) 1)
    have h2 : 6 * (6 ^ 2 - 1) / 2 ≤ r * (r ^ 2 - 1) / 2 := Nat.div_le_div_right h1
    norm_num at h2
    omega

theorem card_eq_25_of_hasOddA (hpp : IsOddPrimePower (Nat.card F))
    {α : MulAut (PSL2 F)} (hα2 : α * α = 1) (hα1 : α ≠ 1) {A : Type*} [Group A]
    (hA : Nat.card A = 60) (h : HasOddA (fixedSubgroup α) A) :
    Nat.card F = 25 ∧ ((semilinearEquivAut F).symm α).right ≠ 1 := by
  classical
  obtain ⟨S, hS, hSp, ρ, hρ, hodd⟩ := h
  set L := S.map (fixedSubgroup α).subtype with hLdef
  have hL : L ≤ fixedSubgroup α := map_subtype_le S
  have hLS : L.subgroupOf (fixedSubgroup α) = S :=
    comap_map_eq_self_of_injective (fixedSubgroup α).subtype_injective S
  let eLS : S ≃* L := S.equivMapOfInjective _ (fixedSubgroup α).subtype_injective
  have hLp : ⁅L, L⁆ = L := by rw [hLdef, ← map_commutator, hSp]
  have hLcard : Nat.card L = Nat.card ρ.ker * 60 := by
    rw [← Nat.card_congr eLS.toEquiv, card_eq_card_ker_mul hρ, hA]
  have hLb : L ≠ ⊥ := by
    intro h0
    rw [h0, card_bot] at hLcard
    have : 0 < Nat.card ρ.ker := Nat.card_pos
    omega
  have hfixL : ∀ y ∈ L, α y = y := fun y hy => hL hy
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hpp
  obtain ⟨g, hgα⟩ := (semilinearEquivAut F).surjective α
  have hgα' : semilinearAction F g = α := hgα
  have hgs : (semilinearEquivAut F).symm α = g := by
    rw [← hgα]
    exact (semilinearEquivAut F).symm_apply_apply g
  rw [hgs]
  have hgg : g * g = 1 := (semilinearEquivAut F).injective (by rw [map_mul, hgα, hα2, map_one])
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hgα', map_one])
  by_cases hr : g.right = 1
  ·
    exfalso
    have hgt : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hr
    have ht2 : g.left * g.left = 1 := by
      have := congrArg SemidirectProduct.left hgg
      simpa [hr] using this
    have ht1 : g.left ≠ 1 := by
      intro h
      apply hg1
      rw [hgt, h, map_one]
    have hTp : ⁅L.map (incl F), L.map (incl F)⁆ = L.map (incl F) := by
      rw [← Subgroup.map_commutator, hLp]
    have hTg : ∀ x ∈ L.map (incl F), x * SemidirectProduct.inl g.left =
        SemidirectProduct.inl g.left * x := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hgt]
      exact ((commute_incl_iff g y).mpr (by rw [hgα']; exact hfixL y hy)).symm
    have hTb := CatFactsSp4.perfect_centralizer_inl_eq_bot h2 ht2 ht1 hTg hTp
    apply hLb
    rw [eq_bot_iff]
    intro y hy
    have : incl F y ∈ L.map (incl F) := ⟨y, hy, rfl⟩
    rw [hTb, mem_bot] at this
    rw [mem_bot]
    exact incl_injective F (this.trans (map_one _).symm)
  refine ⟨?_, hr⟩
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
  obtain ⟨c, hc⟩ : ∃ c : MulAut (PSL2 F), c = semilinearAction F (SemidirectProduct.inl C) :=
    ⟨_, rfl⟩
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
  have hN'fix : N' ≤ fixedSubgroup α := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    change α (c (psl2Sub K₀ w)) = c (psl2Sub K₀ w)
    have hw : psl2FieldAut F g.right (psl2Sub K₀ w) = psl2Sub K₀ w :=
      psl2Sub_mem_fieldCent hK₀ w
    rw [hαc]
    simp [MulAut.mul_apply, hw]
  let e₁ : PSL2 K₀ ≃* (psl2Sub K₀).range := MonoidHom.ofInjective (psl2Sub_injective K₀)
  let e₂ : (psl2Sub K₀).range ≃* N' :=
    ((psl2Sub K₀).range).equivMapOfInjective c.toMonoidHom c.injective
  have hodd₀ : Odd (Nat.card K₀) := by
    obtain ⟨p, n, -, hpo, -, hpn⟩ := hpp
    have : Odd (Nat.card K₀ ^ 2) := by rw [← hcard, hpn]; exact hpo.pow
    exact (Nat.odd_pow_iff two_ne_zero).mp this
  have hN'card : Nat.card N' = Nat.card K₀ * (Nat.card K₀ ^ 2 - 1) / 2 := by
    rw [← Nat.card_congr (e₁.trans e₂).toEquiv,
      psl2_card_formula K₀ (isOddPrimePower_of_odd_card K₀ hodd₀)]
  have hK₀3 : 3 ≤ Nat.card K₀ := by
    have h1 : 1 < Nat.card K₀ := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd₀
    omega
  have hLle : Nat.card L ≤ Nat.card N' := Subgroup.card_le_of_le hLN'
  rcases Nat.lt_or_ge (Nat.card K₀) 4 with hK₀4 | hK₀4
  ·
    exfalso
    have h3 : Nat.card K₀ = 3 := by omega
    rw [hN'card, h3] at hLle
    have : 0 < Nat.card ρ.ker := Nat.card_pos
    norm_num at hLle
    omega
  have hs0 : IsSimpleGroup (PSL2 K₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK₀4
  have hsN' : IsSimpleGroup N' := (e₁.trans e₂).isSimpleGroup_congr.mp hs0
  have hLsn : (L.subgroupOf (fixedSubgroup α)).IsSubnormal := by
    rw [hLS]
    exact hS
  have hsn' := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hN'fix hLsn
  have hLeq : L = N' := by
    rcases hsn'.eq_bot_or_top_of_isSimpleGroup hsN' with h | h
    · exfalso
      apply hLb
      rw [subgroupOf_eq_bot] at h
      exact le_bot_iff.mp (fun y hy => h.le_bot ⟨hy, hLN' hy⟩)
    · rw [subgroupOf_eq_top] at h
      exact le_antisymm hLN' h
  have hsS : IsSimpleGroup S := (eLS.trans (MulEquiv.subgroupCongr hLeq)).isSimpleGroup
  have hker : Nat.card ρ.ker = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · rw [h, card_bot]
    · exfalso
      have h1 := card_eq_card_ker_mul hρ
      rw [h, card_top, hA] at h1
      have : 0 < Nat.card S := Nat.card_pos
      omega
  have h60 : Nat.card K₀ * (Nat.card K₀ ^ 2 - 1) / 2 = 60 := by
    rw [← hN'card, ← hLeq, hLcard, hker, one_mul]
  have h5 := eq_five_of_half_mul_sq_sub hK₀4 h60
  rw [hcard, h5]
  norm_num

end CFSG.ComponentClassification.SolMax.FiveFL2
