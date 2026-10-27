module

public import CFSG.CharacterTheory.Blocks.InnerProduct

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open TwoRankLowerBound.Helpers

section Linear

variable {K : Type} [Group K] [Fintype K]

theorem conj_units_hom (χ : K →* ℂˣ) (g : K) :
    starRingEnd ℂ (χ g : ℂ) = (χ g⁻¹ : ℂ) := by
  have hfin : (χ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hnorm : ‖(χ g : ℂ)‖ = 1 := by
    have h1 : ‖(χ g : ℂ)‖ ^ orderOf g = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (orderOf_pos g).ne').mp h1
  rw [map_inv, Units.val_inv_eq_inv_val, Complex.inv_eq_conj hnorm]

theorem blocksInnerProduct_units_hom (χ χ' : K →* ℂˣ) :
    BlocksInnerProduct (fun g => (χ g : ℂ)) (fun g => (χ' g : ℂ)) = if χ = χ' then 1 else 0 := by
  let ψ : K →* ℂ := (Units.coeHom ℂ).comp (χ * χ'⁻¹)
  have hψ : ∀ g, (χ g : ℂ) * starRingEnd ℂ (χ' g : ℂ) = ψ g := by
    intro g
    rw [conj_units_hom]
    simp [ψ, map_inv]
  have hiff : ψ = 1 ↔ χ = χ' := by
    constructor
    · intro h
      ext g
      have h1 : (χ g : ℂ) * starRingEnd ℂ (χ' g : ℂ) = 1 := by
        rw [hψ, h, MonoidHom.one_apply]
      rw [conj_units_hom, map_inv, Units.val_inv_eq_inv_val] at h1
      exact (mul_inv_eq_one₀ (Units.ne_zero _)).mp h1
    · rintro rfl
      ext g
      simp [ψ]
  unfold BlocksInnerProduct
  rw [Finset.sum_congr rfl fun g _ => hψ g, sum_hom_units ψ, Nat.card_eq_fintype_card]
  by_cases h : χ = χ'
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    have hcard : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact inv_mul_cancel₀ hcard
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, Nat.cast_zero, mul_zero]

end Linear

section ExtendByZero

variable {K : Type} [Group K]

@[expose] noncomputable def extendByZero (H : Subgroup K) (μ : H → ℂ) (x : K) : ℂ :=
  if hx : x ∈ H then μ ⟨x, hx⟩ else 0

theorem extendByZero_of_mem (H : Subgroup K) (μ : H → ℂ) {x : K} (hx : x ∈ H) :
    extendByZero H μ x = μ ⟨x, hx⟩ := dite_eq_left hx

theorem extendByZero_of_not_mem (H : Subgroup K) (μ : H → ℂ) {x : K} (hx : x ∉ H) :
    extendByZero H μ x = 0 := dite_eq_right hx

theorem extendByZero_coe (H : Subgroup K) (μ : H → ℂ) (h : H) :
    extendByZero H μ h = μ h := extendByZero_of_mem H μ h.2

theorem extendByZero_conj (H : Subgroup K) (μ : H → ℂ) (hμ : ∀ s t : H, μ (s * t * s⁻¹) = μ t)
    (s : H) (y : K) : extendByZero H μ ((s : K) * y * (s : K)⁻¹) = extendByZero H μ y := by
  by_cases hy : y ∈ H
  · have hmem : (s : K) * y * (s : K)⁻¹ ∈ H := H.mul_mem (H.mul_mem s.2 hy) (H.inv_mem s.2)
    rw [extendByZero_of_mem H μ hmem, extendByZero_of_mem H μ hy, ← hμ s ⟨y, hy⟩]
    rfl
  · have hmem : (s : K) * y * (s : K)⁻¹ ∉ H := by
      intro h
      apply hy
      have := H.mul_mem (H.mul_mem (H.inv_mem s.2) h) s.2
      simpa [mul_assoc] using this
    rw [extendByZero_of_not_mem H μ hmem, extendByZero_of_not_mem H μ hy]

theorem inducedFunction_eq_extendByZero [Fintype K] (H : Subgroup K) (μ : H → ℂ) (g : K) :
    inducedFunction H μ g = (Nat.card H : ℂ)⁻¹ * ∑ x : K, extendByZero H μ (x⁻¹ * g * x) := rfl

theorem sum_subgroup_eq [Fintype K] (L : Subgroup K) (f : K → ℂ) :
    ∑ l : L, f l = ∑ x : K, if x ∈ L then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun x => by simp) f).symm

end ExtendByZero

section Stabilizer

variable {K Ω : Type} [Group K] [MulAction K Ω]

theorem conj_mem_iff_of_stabilizer {ω : Ω} {H : Subgroup K} (hH : ∀ x, x ∈ H ↔ x • ω = ω)
    (x g : K) : x⁻¹ * g * x ∈ H ↔ g • x • ω = x • ω := by
  rw [hH, mul_smul, mul_smul, inv_smul_eq_iff]

theorem conj_mem_of_stabilizer {ω : Ω} {H : Subgroup K} (hH : ∀ x, x ∈ H ↔ x • ω = ω)
    {p : Ω} {x g : K} (hx : x • ω = p) (hg : g • p = p) : x⁻¹ * g * x ∈ H := by
  rw [conj_mem_iff_of_stabilizer hH, hx, hg]

theorem conj_mem_of_mem_inf {ω ω' : Ω} {H : Subgroup K} (hH : ∀ x, x ∈ H ↔ x • ω = ω)
    {w : K} (hw : w • ω = ω') {l : K} (hl : l ∈ H ⊓ MulAction.stabilizer K ω') :
    w⁻¹ * l * w ∈ H :=
  conj_mem_of_stabilizer hH hw (Subgroup.mem_inf.mp hl).2

@[expose] noncomputable def stabilizerProdEquiv {ω : Ω} {H : Subgroup K}
    (hH : ∀ x, x ∈ H ↔ x • ω = ω) (rep : Ω → K) (hrep : ∀ p, rep p • ω = p) :
    Ω × H ≃ K where
  toFun x := rep x.1 * (x.2 : K)
  invFun x := (x • ω, ⟨(rep (x • ω))⁻¹ * x, by
    rw [hH, mul_smul, inv_smul_eq_iff, hrep]⟩)
  left_inv := by
    rintro ⟨p, s⟩
    have hp : (rep p * (s : K)) • ω = p := by
      rw [mul_smul, (hH s).mp s.2, hrep]
    refine Prod.ext hp (Subtype.ext ?_)
    change (rep ((rep p * (s : K)) • ω))⁻¹ * (rep p * s) = s
    rw [hp, inv_mul_cancel_left]
  right_inv x := by
    change rep (x • ω) * ((rep (x • ω))⁻¹ * x) = x
    rw [mul_inv_cancel_left]

theorem stabilizerProdEquiv_apply {ω : Ω} {H : Subgroup K} (hH : ∀ x, x ∈ H ↔ x • ω = ω)
    (rep : Ω → K) (hrep : ∀ p, rep p • ω = p) (x : Ω × H) :
    stabilizerProdEquiv hH rep hrep x = rep x.1 * (x.2 : K) := rfl

variable [Fintype Ω]

theorem inducedFunction_stabilizer [Fintype K] {ω : Ω} {H : Subgroup K}
    (hH : ∀ x, x ∈ H ↔ x • ω = ω) (μ : H → ℂ) (hμ : ∀ s t : H, μ (s * t * s⁻¹) = μ t)
    (rep : Ω → K) (hrep : ∀ p, rep p • ω = p) (g : K) :
    inducedFunction H μ g = ∑ p : Ω, extendByZero H μ ((rep p)⁻¹ * g * rep p) := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [inducedFunction_eq_extendByZero, ← (stabilizerProdEquiv hH rep hrep).sum_comp,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hterm : ∀ s : H, extendByZero H μ
      ((stabilizerProdEquiv hH rep hrep (p, s))⁻¹ * g * stabilizerProdEquiv hH rep hrep (p, s)) =
        extendByZero H μ ((rep p)⁻¹ * g * rep p) := by
    intro s
    have heq : (stabilizerProdEquiv hH rep hrep (p, s))⁻¹ * g *
        stabilizerProdEquiv hH rep hrep (p, s) =
          ((s⁻¹ : H) : K) * ((rep p)⁻¹ * g * rep p) * ((s⁻¹ : H) : K)⁻¹ := by
      rw [stabilizerProdEquiv_apply]
      simp only [Subgroup.coe_inv, inv_inv, _root_.mul_inv_rev, mul_assoc]
    rw [heq, extendByZero_conj H μ hμ s⁻¹]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem card_stabilizer_eq_mul {ω : Ω} {H : Subgroup K} (hH : ∀ x, x ∈ H ↔ x • ω = ω)
    (ω' : Ω) (hne : ω' ≠ ω) (k : Ω → K) (hk : ∀ p, p ≠ ω → k p ∈ H ∧ k p • ω' = p) :
    Nat.card H = (Fintype.card Ω - 1) * Nat.card (H ⊓ MulAction.stabilizer K ω' : Subgroup K) := by
  have horbit : MulAction.orbit H ω' = {p | p ≠ ω} := by
    ext p
    constructor
    · rintro ⟨h, rfl⟩ hp
      apply hne
      have h1 : (h : K) • ω' = (h : K) • ω := by
        rw [(hH h).mp h.2]
        exact hp
      exact smul_left_cancel _ h1
    · intro hp
      exact ⟨⟨k p, (hk p hp).1⟩, (hk p hp).2⟩
  have hcardorbit : (MulAction.orbit H ω').ncard = Fintype.card Ω - 1 := by
    rw [horbit, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    rw [Finset.filter_ne' Finset.univ ω, Finset.card_erase_of_mem (Finset.mem_univ ω),
      Finset.card_univ]
  let e : MulAction.stabilizer H ω' ≃ (H ⊓ MulAction.stabilizer K ω' : Subgroup K) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, (Subgroup.mem_inf.mp x.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, ← hcardorbit, ← MulAction.index_stabilizer,
    Subgroup.index_mul_card]

theorem blocksInnerProduct_inducedFunction_twoPoint [Fintype K] {ω : Ω} {H : Subgroup K}
    (hH : ∀ x, x ∈ H ↔ x • ω = ω) (ω' : Ω) (w : K) (hw : w • ω = ω') (hne : ω' ≠ ω)
    (k : Ω → K) (hk : ∀ p, p ≠ ω → k p ∈ H ∧ k p • ω' = p) (lam μ : H → ℂ)
    (hlam : ∀ s t : H, lam (s * t * s⁻¹) = lam t) (hμ : ∀ s t : H, μ (s * t * s⁻¹) = μ t) :
    BlocksInnerProduct (inducedFunction H lam) (inducedFunction H μ) =
      BlocksInnerProduct lam μ +
        BlocksInnerProduct
          (fun l : (H ⊓ MulAction.stabilizer K ω' : Subgroup K) =>
            lam ⟨l, (Subgroup.mem_inf.mp l.2).1⟩)
          (fun l => μ ⟨w⁻¹ * l * w, conj_mem_of_mem_inf hH hw l.2⟩) := by
  have hclass : BlocksIsClassFunction (inducedFunction H μ) := fun g h =>
    inducedFunction_conjugate H μ g h
  rw [blocksInnerProduct_inducedFunction_left H lam _ hclass]
  let rep : Ω → K := fun p => if p = ω then 1 else k p * w
  have hrep : ∀ p, rep p • ω = p := by
    intro p
    by_cases hp : p = ω
    · subst hp
      simp [rep]
    · simp only [rep, ite_eq_right hp]
      rw [mul_smul, hw, (hk p hp).2]
  have hres : ∀ h : H, inducedFunction H μ h = μ h +
      ∑ p ∈ Finset.univ.erase ω, extendByZero H μ (w⁻¹ * ((k p)⁻¹ * h * k p) * w) := by
    intro h
    rw [inducedFunction_stabilizer hH μ hμ rep hrep,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ω)]
    congr 1
    · simp only [rep, ite_eq_left (rfl : ω = ω), inv_one, one_mul, mul_one]
      exact extendByZero_coe H μ h
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p ≠ ω := Finset.ne_of_mem_erase hp
      simp only [rep, ite_eq_right hp']
      congr 1
      group
  have hS : ∀ p ∈ Finset.univ.erase ω,
      ∑ h : H, lam h * starRingEnd ℂ (extendByZero H μ (w⁻¹ * ((k p)⁻¹ * h * k p) * w)) =
        ∑ h : H, lam h * starRingEnd ℂ (extendByZero H μ (w⁻¹ * h * w)) := by
    intro p hp
    have hp' : p ≠ ω := Finset.ne_of_mem_erase hp
    let kp : H := ⟨k p, (hk p hp').1⟩
    refine Fintype.sum_equiv (MulAut.conj kp⁻¹).toEquiv _ _ fun h => ?_
    have hconj : (((MulAut.conj kp⁻¹).toEquiv h : H) : K) = (k p)⁻¹ * h * k p := by
      change ((kp⁻¹ * h * kp⁻¹⁻¹ : H) : K) = _
      rw [inv_inv]
      rfl
    rw [hconj]
    congr 1
    exact (hlam kp⁻¹ h).symm
  have hL : ∑ h : H, lam h * starRingEnd ℂ (extendByZero H μ (w⁻¹ * h * w)) =
      ∑ l : (H ⊓ MulAction.stabilizer K ω' : Subgroup K), lam ⟨l, (Subgroup.mem_inf.mp l.2).1⟩ *
        starRingEnd ℂ (μ ⟨w⁻¹ * l * w, conj_mem_of_mem_inf hH hw l.2⟩) := by
    let f : K → ℂ := fun x =>
      extendByZero H lam x * starRingEnd ℂ (extendByZero H μ (w⁻¹ * x * w))
    have h1 : ∑ h : H, lam h * starRingEnd ℂ (extendByZero H μ (w⁻¹ * h * w)) =
        ∑ h : H, f h := by
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [f, extendByZero_coe]
    have h2 : ∑ l : (H ⊓ MulAction.stabilizer K ω' : Subgroup K),
        lam ⟨l, (Subgroup.mem_inf.mp l.2).1⟩ *
          starRingEnd ℂ (μ ⟨w⁻¹ * l * w, conj_mem_of_mem_inf hH hw l.2⟩) =
          ∑ l : (H ⊓ MulAction.stabilizer K ω' : Subgroup K), f l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [f]
      rw [extendByZero_of_mem H lam (Subgroup.mem_inf.mp l.2).1,
        extendByZero_of_mem H μ (conj_mem_of_mem_inf hH hw l.2)]
    rw [h1, h2, sum_subgroup_eq H f, sum_subgroup_eq _ f]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hxH : x ∈ H
    · by_cases hx' : x ∈ MulAction.stabilizer K ω'
      · rw [ite_eq_left hxH, ite_eq_left (Subgroup.mem_inf.mpr ⟨hxH, hx'⟩)]
      · have hxL : x ∉ H ⊓ MulAction.stabilizer K ω' := fun h => hx' (Subgroup.mem_inf.mp h).2
        rw [ite_eq_left hxH, ite_eq_right hxL]
        have hnot : w⁻¹ * x * w ∉ H := by
          rw [conj_mem_iff_of_stabilizer hH, hw]
          exact hx'
        simp only [f, extendByZero_of_not_mem H μ hnot, map_zero, mul_zero]
    · have hxL : x ∉ H ⊓ MulAction.stabilizer K ω' := fun h => hxH (Subgroup.mem_inf.mp h).1
      rw [ite_eq_right hxH, ite_eq_right hxL]
  have hcardH := card_stabilizer_eq_mul hH ω' hne k hk
  have hLpos : (Nat.card (H ⊓ MulAction.stabilizer K ω' : Subgroup K) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hΩ : ((Finset.univ.erase ω).card : ℂ) = ((Fintype.card Ω - 1 : ℕ) : ℂ) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ]
  have hΩpos : ((Fintype.card Ω - 1 : ℕ) : ℂ) ≠ 0 := by
    have : 2 ≤ Fintype.card Ω := by
      rw [← Finset.card_univ]
      exact Finset.one_lt_card.mpr ⟨ω, Finset.mem_univ _, ω', Finset.mem_univ _, hne.symm⟩
    exact Nat.cast_ne_zero.mpr (by omega)
  have hsum : ∑ h : H, lam h * starRingEnd ℂ (inducedFunction H μ h) =
      ∑ h : H, lam h * starRingEnd ℂ (μ h) + ((Fintype.card Ω - 1 : ℕ) : ℂ) *
        ∑ l : (H ⊓ MulAction.stabilizer K ω' : Subgroup K), lam ⟨l, (Subgroup.mem_inf.mp l.2).1⟩ *
          starRingEnd ℂ (μ ⟨w⁻¹ * l * w, conj_mem_of_mem_inf hH hw l.2⟩) := by
    simp_rw [hres, map_add, map_sum, mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr rfl hS, Finset.sum_const,
      nsmul_eq_mul, hΩ, hL, Finset.mul_sum]
  unfold BlocksInnerProduct
  rw [hsum, mul_add, hcardH]
  push_cast
  field_simp

theorem blocksInnerProduct_inducedFunction_twoPoint' [Fintype K] {ω : Ω} {H : Subgroup K}
    (hH : ∀ x, x ∈ H ↔ x • ω = ω) (ω' : Ω) (w : K) (hw : w • ω = ω') (hne : ω' ≠ ω)
    (k : Ω → K) (hk : ∀ p, p ≠ ω → k p ∈ H ∧ k p • ω' = p) {L : Subgroup K}
    (hL : ∀ x, x ∈ L ↔ x ∈ H ∧ x • ω' = ω') (lam μ : H → ℂ)
    (hlam : ∀ s t : H, lam (s * t * s⁻¹) = lam t) (hμ : ∀ s t : H, μ (s * t * s⁻¹) = μ t) :
    BlocksInnerProduct (inducedFunction H lam) (inducedFunction H μ) =
      BlocksInnerProduct lam μ +
        BlocksInnerProduct (fun l : L => lam ⟨l, ((hL l).mp l.2).1⟩)
          (fun l => μ ⟨w⁻¹ * l * w, conj_mem_of_stabilizer hH hw ((hL l).mp l.2).2⟩) := by
  have hLeq : L = H ⊓ MulAction.stabilizer K ω' := by
    ext x
    rw [hL, Subgroup.mem_inf]
    rfl
  subst hLeq
  exact blocksInnerProduct_inducedFunction_twoPoint hH ω' w hw hne k hk lam μ hlam hμ

end Stabilizer

end CFSG.Wreathed.CentralSL2
