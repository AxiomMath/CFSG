module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSol
public import CFSG.LocalAnalysis.ComponentClassification.Sol78GenAltIso
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.Sol78

section Small

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem four_le_card_support_of_mul_self_eq_one {σ : Perm α} (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (hs : sign σ = 1) : 4 ≤ σ.support.card := by
  by_contra h
  push Not at h
  have h0 : σ.support.card ≠ 0 := fun h0 =>
    h1 (support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0))
  have hne1 := card_support_ne_one σ
  interval_cases hc : σ.support.card
  · exact h0 rfl
  · exact hne1 rfl
  · have := (card_support_eq_two.mp hc).sign_eq
    rw [hs] at this
    exact absurd this (by decide)
  · have h3 := card_support_eq_three_iff.mp hc
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
    rw [h3.orderOf] at hdvd
    norm_num at hdvd

theorem isThreeCycle_of_card_support_le_five {σ : Perm α} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (h5 : σ.support.card ≤ 5) : σ.IsThreeCycle := by
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  have hall : ∀ x ∈ σ.cycleType, x = 3 := by
    intro x hx
    have hdvd := dvd_of_mem_cycleType hx
    rw [hord] at hdvd
    have h2 := two_le_of_mem_cycleType hx
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum := sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hne : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    rw [Multiset.card_eq_zero, cycleType_eq_zero] at h0
    exact h1 h0
  rw [← card_support_eq_three_iff]
  omega

theorem card_support_permCongr {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (σ : Perm α) : (e.permCongr σ).support.card = σ.support.card := by
  have h : (e.permCongr σ).support = σ.support.map e.toEmbedding := by
    ext y
    rw [mem_support, Finset.mem_map_equiv, mem_support, permCongr_apply]
    constructor
    · intro hy hσ
      apply hy
      rw [hσ, apply_symm_apply]
    · intro hy hσ
      apply hy
      calc σ (e.symm y) = e.symm (e (σ (e.symm y))) := (e.symm_apply_apply _).symm
        _ = e.symm y := by rw [hσ]
  rw [h, Finset.card_map]

omit [Fintype α] in
theorem swap_mul_swap_mul_swap_mul_swap_eq {x y u v : α} (hxu : x ≠ u) (hyu : y ≠ u) :
    swap x y * swap y u * (swap x y * swap y v) = swap x u * swap y v := by
  have h := swap_apply_apply (swap x y) x u
  rw [swap_apply_left, swap_apply_of_ne_of_ne hxu.symm hyu.symm, swap_inv] at h
  rw [h]
  simp only [mul_assoc, swap_mul_self_mul]

end Small

section Moved

variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (f : alternatingGroup α →* Perm (Fin N))

open Classical in
@[expose] noncomputable def movedSet : Finset (Fin N) :=
  Finset.univ.filter fun y => ∃ x, f x y ≠ y

theorem mem_movedSet {y : Fin N} : y ∈ movedSet f ↔ ∃ x, f x y ≠ y := by
  classical
  simp [movedSet]

theorem apply_of_not_mem_movedSet {y : Fin N} (hy : y ∉ movedSet f) (x : alternatingGroup α) :
    f x y = y := by
  by_contra h
  exact hy ((mem_movedSet f).mpr ⟨x, h⟩)

variable {f} (hf : Function.Injective f)

@[expose] noncomputable def rangeEquiv : f.range ≃* alternatingGroup (Fin (Fintype.card α)) :=
  (MonoidHom.ofInjective hf).symm.trans (altCongrHom (Fintype.equivFin α))

theorem stabilizer_ne_top_of_mem_movedSet {y : Fin N} (hy : y ∈ movedSet f) :
    MulAction.stabilizer f.range y ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := (mem_movedSet f).mp hy
  have hmem : (⟨f x, x, rfl⟩ : f.range) ∈ MulAction.stabilizer f.range y := htop ▸ mem_top _
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def] at hmem
  exact hx hmem

include hf in
theorem fix_of_commute_movedSet (hm : 5 ≤ Fintype.card α) (hNm : N < 2 * Fintype.card α)
    {σ : Perm (Fin N)} (hσ : ∀ x, f x * σ = σ * f x) {y : Fin N} (hy : y ∈ movedSet f) :
    σ y = y := by
  refine fix_of_commute hm hNm (rangeEquiv hf) (fun h hh => ?_)
    (stabilizer_ne_top_of_mem_movedSet hy)
  obtain ⟨x, rfl⟩ := hh
  exact hσ x

include hf in
theorem card_movedSet (hm : 5 ≤ Fintype.card α) (hN4 : N ≤ Fintype.card α + 4)
    (hNm : N < 2 * Fintype.card α) {r : Perm (Fin N)} (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hrs : sign r = 1) (hrc : ∀ x, f x * r = r * f x) :
    (movedSet f).card = Fintype.card α ∧ N = Fintype.card α + 4 := by
  obtain ⟨ω₀, hω₀⟩ := exists_stabilizer_ne_top hm (rangeEquiv hf)
  have horb : MulAction.orbit f.range ω₀ ⊆ ((movedSet f : Finset (Fin N)) : Set (Fin N)) := by
    rintro y ⟨h, rfl⟩
    rw [Finset.mem_coe]
    by_contra hy
    apply hω₀
    refine eq_top_iff.mpr fun k _ => ?_
    rw [MulAction.mem_stabilizer_iff]
    have hfix : ∀ z : f.range, z • (h • ω₀) = h • ω₀ := fun z => by
      obtain ⟨x, hx⟩ := z.2
      rw [Subgroup.smul_def, Perm.smul_def, ← hx]
      exact apply_of_not_mem_movedSet f hy x
    have := hfix (h * k * h⁻¹)
    rw [mul_smul, mul_smul, inv_smul_smul] at this
    exact smul_left_cancel h this
  have h1 := le_ncard_orbit hm (rangeEquiv hf) hω₀
  have h2 : (MulAction.orbit f.range ω₀).ncard ≤ (movedSet f).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard horb (Finset.finite_toSet _)
  have h3 : r.support ⊆ Finset.univ \ movedSet f := by
    intro y hy
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ y, fun hyM => ?_⟩
    exact (mem_support.mp hy) (fix_of_commute_movedSet hf hm hNm hrc hyM)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin] at h4
  have h5 := four_le_card_support_of_mul_self_eq_one hr1 hr2 hrs
  have h6 : (movedSet f).card ≤ N := by
    calc (movedSet f).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
      _ = N := by rw [Finset.card_univ, Fintype.card_fin]
  omega

theorem sign_apply_eq_one (hm : 5 ≤ Fintype.card α) (x : alternatingGroup α) : sign (f x) = 1 := by
  have : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; exact hm)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sign.comp f).ker with h | h
  · exfalso
    have hinj : Function.Injective (sign.comp f) := (MonoidHom.ker_eq_bot_iff _).mp h
    have h1 := Nat.card_le_card_of_injective _ hinj
    have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := α),
      Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at h1
    have h2 : (5 : ℕ).factorial ≤ (Fintype.card α).factorial := Nat.factorial_le hm
    have h3 : (5 : ℕ).factorial = 120 := rfl
    omega
  · have hx : x ∈ (sign.comp f).ker := h ▸ mem_top x
    exact hx

include hf in
theorem exists_mulEquiv_movedSet (hm : 5 ≤ Fintype.card α) (hcard : (movedSet f).card =
    Fintype.card α) : ∃ g : alternatingGroup α ≃* alternatingGroup {y // y ∈ movedSet f},
      ∀ x, ofSubtype ((g x : alternatingGroup {y // y ∈ movedSet f}) :
        Perm {y // y ∈ movedSet f}) = f x := by
  set M := movedSet f with hMdef
  set K : Subgroup (Perm (Fin N)) := (alternatingGroup {y // y ∈ M}).map ofSubtype with hKdef
  have hle : f.range ≤ K := by
    rintro _ ⟨x, rfl⟩
    rw [hKdef, SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
    exact ⟨fun y hy => apply_of_not_mem_movedSet f hy x, sign_apply_eq_one hm x⟩
  have hMcard : Fintype.card {y // y ∈ M} = Fintype.card α := by
    rw [Fintype.card_coe, hcard]
  have hcardK : Nat.card K = Nat.card f.range := by
    rw [hKdef, SymmetricLocal.card_map_ofSubtype_alternatingGroup,
      ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have : Nontrivial {y // y ∈ M} := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := α),
      Nat.card_eq_fintype_card (α := {y // y ∈ M}), hMcard]
  have heq : f.range = K := Subgroup.eq_of_le_of_card_ge hle hcardK.le
  set E := (alternatingGroup {y // y ∈ M}).equivMapOfInjective ofSubtype ofSubtype_injective
    with hEdef
  refine ⟨(MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr heq).trans E.symm),
    fun x => ?_⟩
  set z : K := (MulEquiv.subgroupCongr heq) (MonoidHom.ofInjective hf x) with hz
  have h1 : ((E (E.symm z) : K) : Perm (Fin N)) = (z : Perm (Fin N)) := by
    rw [MulEquiv.apply_symm_apply]
  exact h1

theorem exists_equiv_of_mulEquiv_alternating_six {β : Type*} [Fintype β] [DecidableEq β]
    (hα : Fintype.card α = 6) (hβ : Fintype.card β = 6)
    (θ : alternatingGroup α ≃* alternatingGroup β) {c : alternatingGroup α}
    (hc : (c : Perm α).IsThreeCycle)
    (hθc : ((θ c : alternatingGroup β) : Perm β).IsThreeCycle) :
    ∃ τ : α ≃ β, ∀ x : alternatingGroup α, ((θ x : alternatingGroup β) : Perm β) =
      τ.permCongr x := by
  let eα₀ : α ≃ Fin 6 := Fintype.equivFinOfCardEq hα
  let eβ : β ≃ Fin 6 := Fintype.equivFinOfCardEq hβ
  have hc₀ : (eα₀.permCongr (c : Perm α)).IsThreeCycle := by
    rw [← card_support_eq_three_iff, card_support_permCongr, card_support_eq_three_iff]
    exact hc
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : Perm (Fin 6),
      π₁ * eα₀.permCongr (c : Perm α) * π₁⁻¹ = (a6c012 : Perm (Fin 6)) :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr (by rw [hc₀, isThreeCycle_a6c012]))
  let eα : α ≃ Fin 6 := eα₀.trans π₁
  have heα : ∀ σ : Perm α, eα.permCongr σ = π₁ * eα₀.permCongr σ * π₁⁻¹ := fun σ =>
    Equiv.ext fun _ => rfl
  have hcα : altCongr eα c = a6c012 := Subtype.ext (by rw [altCongr_apply_coe, heα, hπ₁])
  let κ : MulAut (alternatingGroup (Fin 6)) := ((altCongr eα).symm.trans θ).trans (altCongr eβ)
  have hκ : ∀ y, κ y = altCongr eβ (θ ((altCongr eα).symm y)) := fun _ => rfl
  have hκc : ((κ a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)).IsThreeCycle := by
    rw [hκ, ← hcα, MulEquiv.symm_apply_apply, altCongr_apply_coe, ← card_support_eq_three_iff,
      card_support_permCongr, card_support_eq_three_iff]
    exact hθc
  obtain ⟨σ, hσ⟩ := exists_perm_of_isThreeCycle κ hκc
  refine ⟨(eα.trans σ).trans eβ.symm, fun x => ?_⟩
  have h1 := hσ (altCongr eα x)
  rw [hκ, MulEquiv.symm_apply_apply, altCongr_apply_coe, altCongr_apply_coe] at h1
  have h2 : ((θ x : alternatingGroup β) : Perm β) =
      eβ.symm.permCongr (σ * eα.permCongr (x : Perm α) * σ⁻¹) := by
    rw [← h1]
    ext b
    simp [permCongr_apply]
  rw [h2]
  ext b
  simp [permCongr_apply, Perm.mul_apply]

include hf in
theorem exists_equiv_movedSet (hm : 5 ≤ Fintype.card α) (hcard : (movedSet f).card =
    Fintype.card α) (h6 : Fintype.card α ≠ 6 ∨
      ∃ c : alternatingGroup α, (c : Perm α).IsThreeCycle ∧ (f c).IsThreeCycle) :
    ∃ τ : α ≃ {y // y ∈ movedSet f}, ∀ x : alternatingGroup α,
      f x = ofSubtype (τ.permCongr (x : Perm α)) := by
  obtain ⟨g, hg⟩ := exists_mulEquiv_movedSet hf hm hcard
  have hMcard : Fintype.card α = Fintype.card {y // y ∈ movedSet f} := by
    rw [Fintype.card_coe, hcard]
  obtain ⟨τ, hτ⟩ : ∃ τ : α ≃ {y // y ∈ movedSet f}, ∀ x : alternatingGroup α,
      ((g x : alternatingGroup {y // y ∈ movedSet f}) : Perm {y // y ∈ movedSet f}) =
        τ.permCongr x := by
    by_cases h66 : Fintype.card α = 6
    · rcases h6 with h6 | ⟨c, hc, hfc⟩
      · exact absurd h66 h6
      · refine exists_equiv_of_mulEquiv_alternating_six h66 (by omega) g hc ?_
        rw [IsThreeCycle, ← cycleType_ofSubtype, hg c]
        exact hfc
    · exact exists_equiv_of_mulEquiv_alternating hm h66 hMcard g
  exact ⟨τ, fun x => by rw [← hg x, hτ x]⟩

end Moved

end CFSG.ComponentClassification.RankTwoAlt
