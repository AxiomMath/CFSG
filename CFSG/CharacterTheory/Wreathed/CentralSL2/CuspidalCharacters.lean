module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalGamma

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section InnerProduct

variable {K : Type} [Group K] [Fintype K]

theorem blocksInnerProduct_sub_left' (f g h : K → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, sub_mul]

theorem blocksInnerProduct_sub_right' (f g h : K → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, map_sub, mul_sub]

theorem blocksInnerProduct_conj_symm (f g : K → ℂ) :
    BlocksInnerProduct g f = starRingEnd ℂ (BlocksInnerProduct f g) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem inducedFunction_classFunction (H : Subgroup K) (ρ : H → ℂ) :
    BlocksIsClassFunction (inducedFunction H ρ) := fun g h => inducedFunction_conjugate H ρ g h

theorem sum_units_hom_mul_conj (χ χ' : K →* ℂˣ) :
    (∑ g : K, (χ g : ℂ) * starRingEnd ℂ (χ' g : ℂ)) =
      (Nat.card K : ℂ) * (if χ = χ' then 1 else 0) := by
  have h := blocksInnerProduct_units_hom χ χ'
  unfold BlocksInnerProduct at h
  have hcard : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

end InnerProduct

section Cuspidal

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

@[expose] noncomputable def restrictA (hb : ¬ IsSquare b)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ :=
  lam.comp (Subgroup.inclusion (zpowers_le_nonsplitTorus hb))

omit [Fintype F] in
theorem restrictA_apply (hb : ¬ IsSquare b) (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    restrictA hb lam α = lam ⟨α, zpowers_le_nonsplitTorus hb α.2⟩ := rfl

@[expose] noncomputable def minusWeylConj (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) :
    nonsplitTorus F b m hm heven E basis →* nonsplitTorus F b m hm heven E basis where
  toFun g := ⟨(nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
      nonsplitWeyl F b m hm heven E basis h2 y hy, by
    obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
    exact nonsplitWeyl_inv_conj_mem z hz y hy h2 g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem minusWeylConj_apply (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (g : nonsplitTorus F b m hm heven E basis) :
    (minusWeylConj h2 y hy g : CentralExtension F b m hm heven) =
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
        nonsplitWeyl F b m hm heven E basis h2 y hy := rfl

theorem minusWeylConj_eq (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) :
    minusWeylConj (b := b) (m := m) (hm := hm) (heven := heven) (basis := basis) h2 y hy =
      nonsplitWeylConj F b m hm heven E basis h2 z hz y hy :=
  MonoidHom.ext fun _ => Subtype.ext rfl

theorem minusWeylConj_apply' (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (g : nonsplitTorus F b m hm heven E basis) :
    (minusWeylConj h2 y hy g : CentralExtension F b m hm heven) =
      nonsplitWeyl F b m hm heven E basis h2 y hy * g *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ :=
  nonsplitWeyl_inv_conj y hy h2 _

theorem minusWeylConj_central (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) {g : nonsplitTorus F b m hm heven E basis}
    (hg : (g : CentralExtension F b m hm heven) ∈
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    minusWeylConj h2 y hy g = g := by
  apply Subtype.ext
  rw [minusWeylConj_apply, ← cyclicGenerator_sq_zpowers_comm hg, inv_mul_cancel_right]

@[expose] noncomputable def cuspidalCharacter (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) : CentralExtension F b m hm heven → ℂ :=
  gammaCharacter hb (restrictA hb lam) ψ - torusInduction lam

theorem cuspidalCharacter_classFunction (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    BlocksIsClassFunction (cuspidalCharacter hb ψ lam) := by
  intro g h
  simp only [cuspidalCharacter, Pi.sub_apply, gammaCharacter, torusInduction,
    inducedFunction_conjugate]

theorem cuspidalCharacter_central (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    cuspidalCharacter hb ψ lam α = ((Nat.card F : ℂ) - 1) * (restrictA hb lam α : ℂ) := by
  rw [cuspidalCharacter, Pi.sub_apply, gammaCharacter_central, torusInduction_central hb lam α.2,
    restrictA_apply]
  ring

theorem cuspidalCharacter_unipotent {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) {t : F} (ht : t ≠ 0) :
    cuspidalCharacter hb ψ lam (α * unipotentElement F b m hm heven t) =
      -(restrictA hb lam α : ℂ) := by
  rw [cuspidalCharacter, Pi.sub_apply, gammaCharacter_unipotent hpodd hb hψ _ α ht,
    torusInduction_eq_zero hb lam (Or.inl (card_fixed_unipotent α.2 ht)), sub_zero]

theorem cuspidalCharacter_split (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    cuspidalCharacter hb ψ lam t = 0 := by
  have h2 := card_fixed_splitTorus hb ht htA
  rw [cuspidalCharacter, Pi.sub_apply, gammaCharacter_eq_zero hb _ ψ (Or.inr h2),
    torusInduction_eq_zero hb lam (Or.inr h2), sub_zero]

theorem torusInduction_nonsplit' (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) {t : nonsplitTorus F b m hm heven E basis}
    (htA : (t : CentralExtension F b m hm heven) ∉
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    torusInduction lam t = (lam t : ℂ) + (lam (minusWeylConj h2 y hy t) : ℂ) := by
  rw [torusInduction_nonsplit hb y hy h2 lam t.2 htA]
  congr 3
  exact Subtype.ext (minusWeylConj_apply' h2 y hy t).symm

theorem cuspidalCharacter_nonsplit (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) {t : nonsplitTorus F b m hm heven E basis}
    (htA : (t : CentralExtension F b m hm heven) ∉
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    cuspidalCharacter hb ψ lam t = -(lam t : ℂ) - (lam (minusWeylConj h2 y hy t) : ℂ) := by
  rw [cuspidalCharacter, Pi.sub_apply,
    gammaCharacter_eq_zero hb _ ψ (Or.inl (card_fixed_nonsplitTorus hb t.2 htA)),
    torusInduction_nonsplit' hb y hy h2 lam htA]
  ring

end Cuspidal

section Inner

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

theorem sum_ite_mem_of_le {G : Type} [Group G] [Fintype G] {H K : Subgroup G} (hle : H ≤ K)
    (f : K → ℂ) :
    (∑ k : K, if (k : G) ∈ H then f k else 0) = ∑ h : H, f (Subgroup.inclusion hle h) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun k hk => ⟨k, (Finset.mem_filter.mp hk).2⟩)
    (fun h _ => Subgroup.inclusion hle h) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro h _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h.2
  · intro k _
    rfl
  · intro h _
    rfl
  · intro k _
    rfl

theorem sum_ite_eq_zero_add (c : ℂ) (g : F → ℂ) :
    (∑ s : F, if s = 0 then c else g s) = c + ∑ s : F, if s = 0 then 0 else g s := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ite_eq_left rfl,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ite_eq_left rfl, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun s hs => by
    rw [ite_eq_right (Finset.ne_of_mem_erase hs), ite_eq_right (Finset.ne_of_mem_erase hs)]

theorem gammaCharacter_classFunction (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ) :
    BlocksIsClassFunction (gammaCharacter hb ξ ψ) :=
  inducedFunction_classFunction _ _

theorem torusInduction_classFunction (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    BlocksIsClassFunction (torusInduction lam) :=
  inducedFunction_classFunction _ _

theorem card_zpowers_A (hb : ¬ IsSquare b) :
    Nat.card (Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) = m := by
  rw [Nat.card_zpowers, orderOf_cyclicGenerator_sq F b m hm heven (two_ne_zero_of_not_isSquare hb)]

theorem inner_gamma_gamma {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (ξ η : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) :
    BlocksInnerProduct (gammaCharacter hb ξ ψ) (gammaCharacter hb η ψ) =
      (Nat.card F : ℂ) * (if ξ = η then 1 else 0) := by
  have hq : 2 ≤ Nat.card F := two_le_card F
  rw [gammaCharacter, blocksInnerProduct_inducedFunction_left _ _ _
    (gammaCharacter_classFunction hb η ψ)]
  unfold BlocksInnerProduct
  rw [card_auSubgroup hb, sum_auSubgroup hb]
  have hval : ∀ (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (s : F),
      auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (gammaCharacter hb η ψ (α * unipotentElement F b m hm heven s)) =
      ((ξ α : ℂ) * starRingEnd ℂ (η α : ℂ)) *
        (if s = 0 then ((Nat.card F : ℂ) ^ 2 - 1) else -ψ s) := by
    intro α s
    rw [auCharacter_apply]
    by_cases hs : s = 0
    · subst hs
      rw [ite_eq_left rfl, unipotentElement_zero, mul_one, gammaCharacter_central,
        AddChar.map_zero_eq_one, mul_one, map_mul, map_sub, map_pow, Complex.conj_natCast,
        map_one]
      ring
    · rw [ite_eq_right hs, gammaCharacter_unipotent hpodd hb hψ η α hs, map_neg]
      ring
  have hsum : ∀ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
      (∑ s : F, auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (gammaCharacter hb η ψ (α * unipotentElement F b m hm heven s))) =
      ((ξ α : ℂ) * starRingEnd ℂ (η α : ℂ)) * (Nat.card F : ℂ) ^ 2 := by
    intro α
    rw [Finset.sum_congr rfl fun s _ => hval α s, ← Finset.mul_sum, sum_ite_eq_zero_add]
    have h1 : (∑ s : F, if s = 0 then (0 : ℂ) else -ψ s) = 1 := by
      have h := sum_addChar_ne_zero hψ
      rw [show (∑ s : F, if s = 0 then (0 : ℂ) else -ψ s) =
          -∑ s : F, if s = 0 then 0 else ψ s by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp, h, neg_neg]
    rw [h1]
    ring
  have htotal : (∑ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), ∑ s : F,
      auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (gammaCharacter hb η ψ (α * unipotentElement F b m hm heven s))) =
      (m : ℂ) * (if ξ = η then 1 else 0) * (Nat.card F : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl fun α _ => hsum α, ← Finset.sum_mul, sum_units_hom_mul_conj,
      card_zpowers_A hb]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hq0 : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc ((m * Nat.card F : ℕ) : ℂ)⁻¹ * (∑ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
        ∑ s : F, auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (gammaCharacter hb η ψ (α * unipotentElement F b m hm heven s)))
      = ((m * Nat.card F : ℕ) : ℂ)⁻¹ * ((m : ℂ) * (if ξ = η then 1 else 0) *
          (Nat.card F : ℂ) ^ 2) := by rw [htotal]
    _ = _ := by
      push_cast
      field_simp

theorem inner_gamma_torus (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ)
    (μ : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    BlocksInnerProduct (gammaCharacter hb ξ ψ) (torusInduction μ) =
      ((Nat.card F : ℂ) - 1) * (if ξ = restrictA hb μ then 1 else 0) := by
  have hq : 2 ≤ Nat.card F := two_le_card F
  rw [gammaCharacter, blocksInnerProduct_inducedFunction_left _ _ _
    (torusInduction_classFunction μ)]
  unfold BlocksInnerProduct
  rw [card_auSubgroup hb, sum_auSubgroup hb]
  have hval : ∀ (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (s : F),
      auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (torusInduction μ (α * unipotentElement F b m hm heven s)) =
      if s = 0 then (Nat.card F : ℂ) * (Nat.card F - 1) *
        ((ξ α : ℂ) * starRingEnd ℂ (restrictA hb μ α : ℂ)) else 0 := by
    intro α s
    rw [auCharacter_apply]
    by_cases hs : s = 0
    · subst hs
      rw [ite_eq_left rfl, AddChar.map_zero_eq_one, mul_one, unipotentElement_zero, mul_one,
        torusInduction_central hb μ α.2, restrictA_apply, map_mul, map_mul, map_sub,
        Complex.conj_natCast, map_one]
      ring
    · rw [ite_eq_right hs, torusInduction_eq_zero hb μ (Or.inl (card_fixed_unipotent α.2 hs)),
        map_zero, mul_zero]
  have htotal : (∑ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), ∑ s : F,
      auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (torusInduction μ (α * unipotentElement F b m hm heven s))) =
      (Nat.card F : ℂ) * (Nat.card F - 1) * ((m : ℂ) * (if ξ = restrictA hb μ then 1 else 0)) := by
    rw [Finset.sum_congr rfl fun α _ => (Finset.sum_congr rfl fun s _ => hval α s).trans
      (Fintype.sum_ite_eq' 0 _), ← Finset.mul_sum, sum_units_hom_mul_conj, card_zpowers_A hb]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hq0 : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc ((m * Nat.card F : ℕ) : ℂ)⁻¹ * (∑ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
        ∑ s : F, auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
          alpha_mul_unipotent_mem_au α.2 s⟩ *
        starRingEnd ℂ (torusInduction μ (α * unipotentElement F b m hm heven s)))
      = ((m * Nat.card F : ℕ) : ℂ)⁻¹ * ((Nat.card F : ℂ) * (Nat.card F - 1) *
          ((m : ℂ) * (if ξ = restrictA hb μ then 1 else 0))) := by rw [htotal]
    _ = _ := by
      push_cast
      field_simp

theorem inner_torus_gamma (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (η : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) :
    BlocksInnerProduct (torusInduction lam) (gammaCharacter hb η ψ) =
      ((Nat.card F : ℂ) - 1) * (if restrictA hb lam = η then 1 else 0) := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  have hq : 2 ≤ Nat.card F := two_le_card F
  rw [torusInduction, blocksInnerProduct_inducedFunction_left _ _ _
    (gammaCharacter_classFunction hb η ψ)]
  unfold BlocksInnerProduct
  rw [card_nonsplitTorus z hz]
  have hpt : ∀ t : nonsplitTorus F b m hm heven E basis,
      (lam t : ℂ) * starRingEnd ℂ (gammaCharacter hb η ψ t) =
        if (t : CentralExtension F b m hm heven) ∈
            Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) then
          (lam t : ℂ) * starRingEnd ℂ (gammaCharacter hb η ψ t) else 0 := by
    intro t
    split_ifs with ht
    · rfl
    · rw [gammaCharacter_eq_zero hb η ψ (Or.inl (card_fixed_nonsplitTorus hb t.2 ht)),
        map_zero, mul_zero]
  have hval : ∀ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
      (lam (Subgroup.inclusion (zpowers_le_nonsplitTorus hb) α) : ℂ) *
        starRingEnd ℂ (gammaCharacter hb η ψ
          (Subgroup.inclusion (zpowers_le_nonsplitTorus hb) α :
            nonsplitTorus F b m hm heven E basis)) =
      ((Nat.card F : ℂ) ^ 2 - 1) * ((restrictA hb lam α : ℂ) * starRingEnd ℂ (η α : ℂ)) := by
    intro α
    change (restrictA hb lam α : ℂ) * starRingEnd ℂ (gammaCharacter hb η ψ α) = _
    rw [gammaCharacter_central, map_mul, map_sub, map_pow, Complex.conj_natCast, map_one]
    ring
  have htotal : (∑ t : nonsplitTorus F b m hm heven E basis,
      (lam t : ℂ) * starRingEnd ℂ (gammaCharacter hb η ψ t)) =
      ((Nat.card F : ℂ) ^ 2 - 1) * ((m : ℂ) * (if restrictA hb lam = η then 1 else 0)) := by
    rw [Finset.sum_congr rfl fun t _ => hpt t, sum_ite_mem_of_le (zpowers_le_nonsplitTorus hb),
      Finset.sum_congr rfl fun α _ => hval α, ← Finset.mul_sum, sum_units_hom_mul_conj,
      card_zpowers_A hb]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hq0 : (Nat.card F : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [htotal]
  push_cast
  field_simp
  ring

theorem torusInduction_restrict (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)
    (μ : nonsplitTorus F b m hm heven E basis →* ℂˣ) (t : nonsplitTorus F b m hm heven E basis) :
    torusInduction μ t = (μ t : ℂ) + (μ (minusWeylConj h2 y hy t) : ℂ) +
      if (t : CentralExtension F b m hm heven) ∈
          Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) then
        ((Nat.card F : ℂ) * (Nat.card F - 1) - 2) * (μ t : ℂ) else 0 := by
  split_ifs with ht
  · rw [torusInduction_central hb μ ht, minusWeylConj_central h2 y hy ht]
    ring
  · rw [torusInduction_nonsplit' hb y hy h2 μ ht, add_zero]

theorem inner_torus_torus (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)
    (lam μ : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    BlocksInnerProduct (torusInduction lam) (torusInduction μ) =
      (if lam = μ then 1 else 0) + (if lam = μ.comp (minusWeylConj h2 y hy) then 1 else 0) +
        ((Nat.card F : ℂ) - 2) * (if restrictA hb lam = restrictA hb μ then 1 else 0) := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  have hq : 2 ≤ Nat.card F := two_le_card F
  rw [torusInduction, blocksInnerProduct_inducedFunction_left _ _ _
    (torusInduction_classFunction μ)]
  unfold BlocksInnerProduct
  rw [card_nonsplitTorus z hz]
  have hpt : ∀ t : nonsplitTorus F b m hm heven E basis,
      (lam t : ℂ) * starRingEnd ℂ (torusInduction μ t) =
        ((lam t : ℂ) * starRingEnd ℂ (μ t : ℂ) +
          (lam t : ℂ) * starRingEnd ℂ (μ.comp (minusWeylConj h2 y hy) t : ℂ)) +
        if (t : CentralExtension F b m hm heven) ∈
            Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) then
          ((Nat.card F : ℂ) * (Nat.card F - 1) - 2) *
            ((lam t : ℂ) * starRingEnd ℂ (μ t : ℂ)) else 0 := by
    intro t
    rw [torusInduction_restrict hb y hy h2 μ t, MonoidHom.comp_apply]
    split_ifs
    · simp only [map_add, map_mul, map_sub, Complex.conj_natCast, map_one, map_ofNat]
      ring
    · rw [add_zero, add_zero, map_add, mul_add]
  have hval : ∀ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
      ((Nat.card F : ℂ) * (Nat.card F - 1) - 2) *
        ((lam (Subgroup.inclusion (zpowers_le_nonsplitTorus hb) α) : ℂ) *
          starRingEnd ℂ (μ (Subgroup.inclusion (zpowers_le_nonsplitTorus hb) α) : ℂ)) =
      ((Nat.card F : ℂ) * (Nat.card F - 1) - 2) *
        ((restrictA hb lam α : ℂ) * starRingEnd ℂ (restrictA hb μ α : ℂ)) := fun _ => rfl
  have htotal : (∑ t : nonsplitTorus F b m hm heven E basis,
      (lam t : ℂ) * starRingEnd ℂ (torusInduction μ t)) =
      ((m * (Nat.card F + 1) : ℕ) : ℂ) * (if lam = μ then 1 else 0) +
        ((m * (Nat.card F + 1) : ℕ) : ℂ) *
          (if lam = μ.comp (minusWeylConj h2 y hy) then 1 else 0) +
        ((Nat.card F : ℂ) * (Nat.card F - 1) - 2) *
          ((m : ℂ) * (if restrictA hb lam = restrictA hb μ then 1 else 0)) := by
    rw [Finset.sum_congr rfl fun t _ => hpt t, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_ite_mem_of_le (zpowers_le_nonsplitTorus hb), Finset.sum_congr rfl fun α _ => hval α,
      ← Finset.mul_sum, sum_units_hom_mul_conj, sum_units_hom_mul_conj, sum_units_hom_mul_conj,
      card_zpowers_A hb, card_nonsplitTorus z hz]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hq0 : (Nat.card F : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [htotal]
  push_cast
  field_simp
  ring

theorem inner_cuspidal {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) (lam μ : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    BlocksInnerProduct (cuspidalCharacter hb ψ lam) (cuspidalCharacter hb ψ μ) =
      (if lam = μ then 1 else 0) + (if lam = μ.comp (minusWeylConj h2 y hy) then 1 else 0) := by
  rw [cuspidalCharacter, cuspidalCharacter, blocksInnerProduct_sub_left',
    blocksInnerProduct_sub_right', blocksInnerProduct_sub_right', inner_gamma_gamma hpodd hb hψ,
    inner_gamma_torus, inner_torus_gamma, inner_torus_torus hb y hy h2]
  split_ifs <;> ring

end Inner

end CFSG.Wreathed.CentralSL2
