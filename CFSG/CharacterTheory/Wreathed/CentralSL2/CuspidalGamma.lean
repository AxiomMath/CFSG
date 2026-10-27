module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyClasses

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section AU

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def auSubgroup : Subgroup (CentralExtension F b m hm heven) :=
  Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ⊔ unipotentSubgroup F b m hm heven

variable {F b m hm heven}

theorem mem_auSubgroup_iff (hb : ¬ IsSquare b) (g : CentralExtension F b m hm heven) :
    g ∈ auSubgroup F b m hm heven ↔
      ∃ α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), ∃ t : F,
        g = α * unipotentElement F b m hm heven t := by
  constructor
  · intro hg
    have hle : auSubgroup F b m hm heven ≤
        Subgroup.centralizer {unipotentElement F b m hm heven 1} := by
      refine sup_le ?_ ?_
      · intro α hα
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact cyclicGenerator_sq_zpowers_comm hα _
      · intro n hn
        obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven n).mp hn
        rw [Subgroup.mem_centralizer_singleton_iff, ← unipotentElement_add,
          ← unipotentElement_add, add_comm]
    exact (mem_centralizer_unipotent_iff hb g).mp (hle hg)
  · rintro ⟨α, hα, t, rfl⟩
    exact (auSubgroup F b m hm heven).mul_mem (Subgroup.mem_sup_left hα)
      (Subgroup.mem_sup_right ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨t, rfl⟩))

theorem alpha_mul_unipotent_mem_au {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (t : F) :
    α * unipotentElement F b m hm heven t ∈ auSubgroup F b m hm heven :=
  (auSubgroup F b m hm heven).mul_mem (Subgroup.mem_sup_left hα)
    (Subgroup.mem_sup_right ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨t, rfl⟩))

@[expose] noncomputable def auHom :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) × Multiplicative F →*
      auSubgroup F b m hm heven where
  toFun p := ⟨p.1 * unipotentElement F b m hm heven p.2.toAdd,
    alpha_mul_unipotent_mem_au p.1.2 _⟩
  map_one' := Subtype.ext (by simp [unipotentElement_zero])
  map_mul' p q := Subtype.ext (by
    have hc := cyclicGenerator_sq_zpowers_comm q.1.2
      (unipotentElement F b m hm heven p.2.toAdd)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, toAdd_mul, unipotentElement_add]
    rw [mul_assoc, ← mul_assoc (q.1 : CentralExtension F b m hm heven), hc]
    simp only [mul_assoc])

theorem auHom_apply (p : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) × Multiplicative F) :
    ((auHom p : auSubgroup F b m hm heven) : CentralExtension F b m hm heven) =
      p.1 * unipotentElement F b m hm heven p.2.toAdd := rfl

theorem auHom_bijective (hb : ¬ IsSquare b) :
    Function.Bijective (auHom (F := F) (b := b) (m := m) (hm := hm) (heven := heven)) := by
  constructor
  · rintro ⟨α, t⟩ ⟨α', t'⟩ h
    obtain ⟨h1, h2⟩ := alpha_unipotent_injective α.2 α'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) h2
  · rintro ⟨g, hg⟩
    obtain ⟨α, hα, t, rfl⟩ := (mem_auSubgroup_iff hb g).mp hg
    exact ⟨(⟨α, hα⟩, Multiplicative.ofAdd t), rfl⟩

@[expose] noncomputable def auEquiv (hb : ¬ IsSquare b) :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) × Multiplicative F ≃*
      auSubgroup F b m hm heven :=
  MulEquiv.ofBijective auHom (auHom_bijective hb)

@[expose] noncomputable def auCharacter (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ) :
    auSubgroup F b m hm heven →* ℂ :=
  (((Units.coeHom ℂ).comp ξ).coprod ψ.toMonoidHom).comp (auEquiv hb).symm.toMonoidHom

theorem auCharacter_apply (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (t : F) :
    auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven t, alpha_mul_unipotent_mem_au α.2 t⟩ =
      (ξ α : ℂ) * ψ t := by
  have h : (⟨α * unipotentElement F b m hm heven t, alpha_mul_unipotent_mem_au α.2 t⟩ :
      auSubgroup F b m hm heven) = auEquiv hb (α, Multiplicative.ofAdd t) := rfl
  rw [h, auCharacter, MonoidHom.comp_apply]
  simp

end AU

section Values

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

@[expose] noncomputable def gammaCharacter (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ) :
    CentralExtension F b m hm heven → ℂ :=
  inducedFunction (auSubgroup F b m hm heven) fun g => auCharacter hb ξ ψ g

theorem card_auSubgroup (hb : ¬ IsSquare b) :
    Nat.card (auSubgroup F b m hm heven) = m * Nat.card F := by
  have h2 := two_ne_zero_of_not_isSquare hb
  rw [← Nat.card_congr (auEquiv hb).toEquiv, Nat.card_prod, Nat.card_zpowers,
    orderOf_cyclicGenerator_sq F b m hm heven h2]
  rfl

theorem sum_auSubgroup (hb : ¬ IsSquare b) (f : auSubgroup F b m hm heven → ℂ) :
    ∑ g : auSubgroup F b m hm heven, f g =
      ∑ α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), ∑ t : F,
        f ⟨α * unipotentElement F b m hm heven t, alpha_mul_unipotent_mem_au α.2 t⟩ := by
  rw [← (auEquiv hb).toEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact Fintype.sum_equiv Multiplicative.toAdd _ _ fun t => rfl

omit [Fintype F] in
theorem isConj_central_iff {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (g : CentralExtension F b m hm heven) : IsConj α g ↔ g = α := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := isConj_iff.mp h
    rw [← cyclicGenerator_sq_zpowers_comm hα k, mul_inv_cancel_right]
  · rintro rfl
    exact IsConj.refl _

omit [Fintype F] in
theorem centralizer_central {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Subgroup.centralizer {α} = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_singleton_iff]
  exact (cyclicGenerator_sq_zpowers_comm hα g).symm

theorem gammaCharacter_central (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    gammaCharacter hb ξ ψ α = ((Nat.card F : ℂ) ^ 2 - 1) * (ξ α : ℂ) := by
  rw [gammaCharacter, inducedFunction_eq_sum_isConj, centralizer_central α.2,
    Subgroup.card_top, card_centralExtension_eq, card_auSubgroup hb]
  have hαAU : (α : CentralExtension F b m hm heven) ∈ auSubgroup F b m hm heven :=
    Subgroup.mem_sup_left α.2
  rw [Finset.sum_eq_single ⟨α, hαAU⟩]
  · rw [ite_eq_left (IsConj.refl _)]
    have h1 : (⟨α, hαAU⟩ : auSubgroup F b m hm heven) =
        ⟨α * unipotentElement F b m hm heven 0, alpha_mul_unipotent_mem_au α.2 0⟩ :=
      Subtype.ext (by
        show (α : CentralExtension F b m hm heven) = α * unipotentElement F b m hm heven 0
        rw [unipotentElement_zero, mul_one])
    rw [h1, auCharacter_apply, AddChar.map_zero_eq_one, mul_one]
    have hq : 2 ≤ Nat.card F := two_le_card F
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hq0 : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ Nat.card F ^ 2)]
    field_simp
  · intro h _ hne
    rw [ite_eq_right]
    intro hc
    exact hne (Subtype.ext ((isConj_central_iff α.2 _).mp hc))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_au_isConj_unipotent {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    (∑ h : auSubgroup F b m hm heven,
      if IsConj ((α : CentralExtension F b m hm heven) * unipotentElement F b m hm heven 1)
        (h : CentralExtension F b m hm heven) then auCharacter hb ξ ψ h else 0) =
      (ξ α : ℂ) * ∑ s : F, (if s = 0 then 0 else ψ s) := by
  rw [sum_auSubgroup hb, Finset.sum_eq_single α]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    show (if IsConj ((α : CentralExtension F b m hm heven) * unipotentElement F b m hm heven 1)
        ((α : CentralExtension F b m hm heven) * unipotentElement F b m hm heven s) then
      auCharacter hb ξ ψ ⟨α * unipotentElement F b m hm heven s,
        alpha_mul_unipotent_mem_au α.2 s⟩ else 0) = _
    rw [auCharacter_apply]
    by_cases hs : s = 0
    · rw [ite_eq_right, ite_eq_left hs, mul_zero]
      intro hc
      exact ((isConj_alpha_unipotent_iff hpodd hb α.2 α.2 s).mp hc).2 hs
    · rw [ite_eq_left ((isConj_alpha_unipotent_iff hpodd hb α.2 α.2 s).mpr ⟨rfl, hs⟩),
        ite_eq_right hs]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun s _ => ?_
    show (if IsConj ((α : CentralExtension F b m hm heven) * unipotentElement F b m hm heven 1)
        ((α' : CentralExtension F b m hm heven) * unipotentElement F b m hm heven s) then
      auCharacter hb ξ ψ ⟨α' * unipotentElement F b m hm heven s,
        alpha_mul_unipotent_mem_au α'.2 s⟩ else 0) = 0
    rw [ite_eq_right]
    intro hc
    exact hne (Subtype.ext ((isConj_alpha_unipotent_iff hpodd hb α.2 α'.2 s).mp hc).1)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem gammaCharacter_unipotent {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ)
    (α : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) {t : F} (ht : t ≠ 0) :
    gammaCharacter hb ξ ψ (α * unipotentElement F b m hm heven t) = -(ξ α : ℂ) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp (isConj_mul_central α.2
    (isConj_unipotent (hm := hm) (heven := heven) hb ht))
  rw [← hk, gammaCharacter, inducedFunction_conjugate, inducedFunction_eq_sum_isConj,
    centralizer_alpha_unipotent α.2, card_centralizer_unipotent hb, card_auSubgroup hb,
    div_self (by
      have hq : 2 ≤ Nat.card F := two_le_card F
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hm.ne' (by omega))), one_mul]
  have h := sum_au_isConj_unipotent hpodd hb ξ ψ α
  rw [sum_addChar_ne_zero hψ, mul_neg_one] at h
  convert h using 3

theorem card_fixed_auSubgroup {g : CentralExtension F b m hm heven}
    (hg : g ∈ auSubgroup F b m hm heven) (hb : ¬ IsSquare b) :
    Nat.card {p : Omega F // g • p = p} = Nat.card F + 1 ∨
      Nat.card {p : Omega F // g • p = p} = 1 := by
  obtain ⟨α, hα, t, rfl⟩ := (mem_auSubgroup_iff hb g).mp hg
  by_cases ht : t = 0
  · left
    rw [ht, unipotentElement_zero, mul_one]
    exact card_fixed_of_mem_zpowers hα
  · right
    exact card_fixed_unipotent hα ht

theorem gammaCharacter_eq_zero (hb : ¬ IsSquare b)
    (ξ : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) →* ℂˣ) (ψ : AddChar F ℂ)
    {g : CentralExtension F b m hm heven}
    (hg : Nat.card {p : Omega F // g • p = p} = 0 ∨ Nat.card {p : Omega F // g • p = p} = 2) :
    gammaCharacter hb ξ ψ g = 0 := by
  rw [gammaCharacter, inducedFunction_eq_sum_isConj]
  rw [Finset.sum_eq_zero, mul_zero]
  intro h _
  rw [ite_eq_right]
  intro hc
  have h1 := card_fixed_of_isConj (Ω := Omega F) hc
  have hq : 2 ≤ Nat.card F := two_le_card F
  rcases card_fixed_auSubgroup h.2 hb with h2 | h2 <;> rcases hg with h3 | h3 <;> omega

@[expose] noncomputable def torusInduction {E : Type} [Field E] [Algebra F E]
    {basis : Module.Basis (Fin 2) F E} (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    CentralExtension F b m hm heven → ℂ :=
  inducedFunction (nonsplitTorus F b m hm heven E basis) fun t => (lam t : ℂ)

variable {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

theorem torusInduction_central (hb : ¬ IsSquare b)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    torusInduction lam α = (Nat.card F : ℂ) * (Nat.card F - 1) *
      (lam ⟨α, zpowers_le_nonsplitTorus hb hα⟩ : ℂ) := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  rw [torusInduction, inducedFunction_eq_sum_isConj, centralizer_central hα,
    Subgroup.card_top, card_centralExtension_eq, card_nonsplitTorus z hz]
  rw [Finset.sum_eq_single ⟨α, zpowers_le_nonsplitTorus hb hα⟩]
  · rw [ite_eq_left (IsConj.refl _)]
    have hq : 2 ≤ Nat.card F := two_le_card F
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hq0 : (Nat.card F : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ Nat.card F ^ 2)]
    field_simp
    ring
  · intro h _ hne
    rw [ite_eq_right]
    intro hc
    exact hne (Subtype.ext ((isConj_central_iff hα _).mp hc))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem torusInduction_nonsplit (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    torusInduction lam t = (lam ⟨t, ht⟩ : ℂ) +
      (lam ⟨nonsplitWeyl F b m hm heven E basis h2 y hy * t *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹, by
          obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
          exact nonsplitWeyl_conj_mem z hz y hy h2 ht⟩ : ℂ) := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  set w := nonsplitWeyl F b m hm heven E basis h2 y hy with hw
  have hwt : w * t * w⁻¹ ∈ nonsplitTorus F b m hm heven E basis :=
    nonsplitWeyl_conj_mem z hz y hy h2 ht
  have hne : (⟨t, ht⟩ : nonsplitTorus F b m hm heven E basis) ≠ ⟨w * t * w⁻¹, hwt⟩ :=
    fun h => nonsplitWeyl_conj_ne y hy h2 hb ht htA (congrArg Subtype.val h).symm
  rw [torusInduction, inducedFunction_eq_sum_isConj, centralizer_nonsplitTorus y hy h2 hb ht htA,
    div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  have hfil : (Finset.univ.filter fun h : nonsplitTorus F b m hm heven E basis =>
      IsConj t (h : CentralExtension F b m hm heven)) = {⟨t, ht⟩, ⟨w * t * w⁻¹, hwt⟩} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [isConj_nonsplitTorus_iff y hy h2 hb ht htA h.2]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hsum : (∑ h : nonsplitTorus F b m hm heven E basis,
      if IsConj t (h : CentralExtension F b m hm heven) then (lam h : ℂ) else 0) =
        (lam ⟨t, ht⟩ : ℂ) + lam ⟨w * t * w⁻¹, hwt⟩ := by
    rw [← Finset.sum_filter, hfil, Finset.sum_pair hne]
  convert hsum using 3

theorem torusInduction_eq_zero (hb : ¬ IsSquare b)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) {g : CentralExtension F b m hm heven}
    (hg : Nat.card {p : Omega F // g • p = p} = 1 ∨ Nat.card {p : Omega F // g • p = p} = 2) :
    torusInduction lam g = 0 := by
  rw [torusInduction, inducedFunction_eq_sum_isConj]
  rw [Finset.sum_eq_zero, mul_zero]
  intro h _
  rw [ite_eq_right]
  intro hc
  have h1 := card_fixed_of_isConj (Ω := Omega F) hc
  have hq : 2 ≤ Nat.card F := two_le_card F
  by_cases hA : (h : CentralExtension F b m hm heven) ∈
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)
  · have h2 := card_fixed_of_mem_zpowers hA
    rcases hg with h3 | h3 <;> omega
  · have h2 := card_fixed_nonsplitTorus hb h.2 hA
    rcases hg with h3 | h3 <;> omega

end Values

end CFSG.Wreathed.CentralSL2
