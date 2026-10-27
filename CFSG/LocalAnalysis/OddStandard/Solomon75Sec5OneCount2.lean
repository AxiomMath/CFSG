module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneCount
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard.Solomon75

open scoped commutatorElement

theorem exists_hom_range_of_ker_le {T G S : Type*} [Group T] [Group G] [Group S]
    (φ : T →* G) (f : T →* S) (hf : Function.Surjective f) (hk : ∀ t, φ t = 1 → f t = 1) :
    ∃ f' : φ.range →* S, Function.Surjective f' ∧ ∀ t, f' ⟨φ t, t, rfl⟩ = f t := by
  have hker : φ.ker ≤ f.ker := fun t ht => hk t ht
  let g : T ⧸ φ.ker →* S := QuotientGroup.lift φ.ker f hker
  let e := QuotientGroup.quotientKerEquivRange φ
  let f' : φ.range →* S := g.comp e.symm.toMonoidHom
  have key : ∀ t, f' ⟨φ t, t, rfl⟩ = f t := by
    intro t
    have h1 : e.symm ⟨φ t, t, rfl⟩ = QuotientGroup.mk t := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show g (e.symm ⟨φ t, t, rfl⟩) = f t
    rw [h1]
    rfl
  refine ⟨f', fun s => ?_, key⟩
  obtain ⟨t, rfl⟩ := hf s
  exact ⟨⟨φ t, t, rfl⟩, key t⟩

theorem not_isSolvable_alternatingGroup' {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : 5 ≤ Fintype.card α) : ¬ Group.IsSolvable (alternatingGroup α) := by
  intro h
  refine Equiv.Perm.not_isSolvable α ?_ (Group.isSolvable_of_ker_le_range
    (alternatingGroup α).subtype (Equiv.Perm.sign (α := α)) fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩)
  rw [Cardinal.mk_fintype]
  exact_mod_cast h5

theorem card_alternatingGroup_eq {α : Type*} [Fintype α] [DecidableEq α]
    (h2 : 2 ≤ Fintype.card α) :
    Nat.card (alternatingGroup α) = (Fintype.card α).factorial / 2 := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]

theorem even_card_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (h4 : 4 ≤ Fintype.card α) : Even (Nat.card (alternatingGroup α)) := by
  rw [card_alternatingGroup_eq (by omega)]
  obtain ⟨c, hc⟩ : 4 ∣ (Fintype.card α).factorial := by
    have h := Nat.factorial_dvd_factorial h4
    exact (by decide : 4 ∣ (4 : ℕ).factorial).trans h
  rw [hc]
  exact ⟨c, by omega⟩

theorem card_mul_le_factorial_of_hom {G : Type*} [Group G] [Finite G]
    {β : Type*} [Fintype β] [DecidableEq β]
    (Φ : G →* Equiv.Perm β) (hΦ : Group.IsSolvable Φ.ker)
    (L : Subgroup G) [L.Normal] (hL : Odd (Nat.card L))
    {T₁ T₂ : Type*} [Group T₁] [Group T₂] (φ₁ : T₁ →* G) (φ₂ : T₂ →* G)
    (hcomm : ∀ a b, ⁅φ₁ a, φ₂ b⁆ ∈ L)
    {S₁ S₂ : Type*} [Group S₁] [Group S₂] [Finite S₁] [Finite S₂]
    [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hns₁ : ¬ Group.IsSolvable S₁) (hns₂ : ¬ Group.IsSolvable S₂)
    (he₁ : Even (Nat.card S₁)) (he₂ : Even (Nat.card S₂))
    (f₁ : T₁ →* S₁) (f₂ : T₂ →* S₂)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (hk₁ : ∀ t, φ₁ t = 1 → f₁ t = 1) (hk₂ : ∀ t, φ₂ t = 1 → f₂ t = 1) :
    Nat.card S₁ * Nat.card S₂ ≤ (Fintype.card β).factorial := by
  obtain ⟨f₁', hf₁', -⟩ := exists_hom_range_of_ker_le φ₁ f₁ hf₁ hk₁
  obtain ⟨f₂', hf₂', -⟩ := exists_hom_range_of_ker_le φ₂ f₂ hf₂ hk₂
  exact card_mul_le_factorial_of_solvable_ker Φ hΦ L hL φ₁.range φ₂.range (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hcomm a b) hns₁ hns₂ he₁ he₂ f₁' f₂' hf₁' hf₂'

theorem odd_card_ker_restrict {T Γ U' : Type*} [Group T] [Finite T] [Group Γ] [Group U']
    (ψ : T →* Γ) (T' : Subgroup T) (φ : T' →* U') (ι : U' →* Γ)
    (hφ : ∀ t, ι (φ t) = ψ t) (hodd : Odd (Nat.card ψ.ker)) : Odd (Nat.card φ.ker) := by
  let g : φ.ker →* ψ.ker :=
    ⟨⟨fun t => ⟨(t.1 : T), by
      have h1 : φ t.1 = 1 := t.2
      have := hφ t.1
      rw [h1, map_one] at this
      exact this.symm⟩, rfl⟩, fun a b => rfl⟩
  have hg : Function.Injective g := fun a b h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ψ.ker => (w : T)) h
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective g hg)

theorem exists_alt_restriction {T : Type*} [Group T] {C : Type*} [Fintype C]
    [DecidableEq C] (π : T →* Equiv.Perm C) (hπ : alternatingGroup C ≤ π.range) :
    ∃ (T' : Subgroup T) (f : T' →* alternatingGroup C), Function.Surjective f ∧
      ∀ t : T', (f t : Equiv.Perm C) = π t := by
  refine ⟨(alternatingGroup C).comap π,
    (π.comp ((alternatingGroup C).comap π).subtype).codRestrict _ (fun t => t.2), ?_,
    fun t => rfl⟩
  rintro ⟨a, ha⟩
  obtain ⟨t, ht⟩ := hπ ha
  exact ⟨⟨t, by show π t ∈ alternatingGroup C; rw [ht]; exact ha⟩, Subtype.ext ht⟩

theorem card_alt_mul_le_factorial {Γ : Type*} [Group Γ] [Finite Γ]
    {β : Type*} [Fintype β] [DecidableEq β]
    (U : Subgroup Γ) (Φ : ↥U →* Equiv.Perm β) (hΦ : Group.IsSolvable Φ.ker)
    (Lp : Subgroup Γ) (hLn : ∀ u ∈ U, ∀ l ∈ Lp, u * l * u⁻¹ ∈ Lp) (hLp : Odd (Nat.card Lp))
    {T₁ T₂ : Type*} [Group T₁] [Group T₂] [Finite T₁] [Finite T₂]
    (ψ₁ : T₁ →* Γ) (ψ₂ : T₂ →* Γ)
    (hU₁ : ∀ t, ψ₁ t ∈ U) (hU₂ : ∀ t, ψ₂ t ∈ U)
    (hcomm : ∀ a b, ⁅ψ₁ a, ψ₂ b⁆ ∈ Lp)
    {C₁ C₂ : Type*} [Fintype C₁] [DecidableEq C₁] [Fintype C₂] [DecidableEq C₂]
    (h5₁ : 5 ≤ Fintype.card C₁) (h5₂ : 5 ≤ Fintype.card C₂)
    (π₁ : T₁ →* Equiv.Perm C₁) (π₂ : T₂ →* Equiv.Perm C₂)
    (hπ₁ : alternatingGroup C₁ ≤ π₁.range) (hπ₂ : alternatingGroup C₂ ≤ π₂.range)
    (hodd₁ : Odd (Nat.card ψ₁.ker)) (hodd₂ : Odd (Nat.card ψ₂.ker)) :
    (Fintype.card C₁).factorial / 2 * ((Fintype.card C₂).factorial / 2) ≤
      (Fintype.card β).factorial := by
  classical
  have : IsSimpleGroup (alternatingGroup C₁) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; exact h5₁)
  have : IsSimpleGroup (alternatingGroup C₂) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; exact h5₂)
  obtain ⟨T₁', f₁, hf₁, -⟩ := exists_alt_restriction π₁ hπ₁
  obtain ⟨T₂', f₂, hf₂, -⟩ := exists_alt_restriction π₂ hπ₂
  have he₁ := even_card_alternatingGroup (α := C₁) (by omega)
  have he₂ := even_card_alternatingGroup (α := C₂) (by omega)
  let φ₁ : T₁' →* ↥U := (ψ₁.comp T₁'.subtype).codRestrict U (fun t => hU₁ t)
  let φ₂ : T₂' →* ↥U := (ψ₂.comp T₂'.subtype).codRestrict U (fun t => hU₂ t)
  have hk₁ : ∀ t, φ₁ t = 1 → f₁ t = 1 := by
    intro t ht
    have : φ₁.ker ≤ f₁.ker :=
      le_ker_of_odd_card he₁ f₁ hf₁ φ₁.ker
        (odd_card_ker_restrict ψ₁ T₁' φ₁ U.subtype (fun t => rfl) hodd₁)
    exact this ht
  have hk₂ : ∀ t, φ₂ t = 1 → f₂ t = 1 := by
    intro t ht
    have : φ₂.ker ≤ f₂.ker :=
      le_ker_of_odd_card he₂ f₂ hf₂ φ₂.ker
        (odd_card_ker_restrict ψ₂ T₂' φ₂ U.subtype (fun t => rfl) hodd₂)
    exact this ht
  let L : Subgroup ↥U := Lp.subgroupOf U
  have : L.Normal := ⟨fun l hl u => by
    have h1 : (l : Γ) ∈ Lp := hl
    show ((u * l * u⁻¹ : ↥U) : Γ) ∈ Lp
    simpa using hLn u u.2 l h1⟩
  have hLodd : Odd (Nat.card L) := by
    let g : L →* Lp :=
      ⟨⟨fun x => ⟨((x : ↥U) : Γ), x.2⟩, rfl⟩, fun a b => rfl⟩
    have hg : Function.Injective g := fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥Lp => (w : Γ)) h
    exact Odd.of_dvd_nat hLp (Subgroup.card_dvd_of_injective g hg)
  have hcommL : ∀ a b, ⁅φ₁ a, φ₂ b⁆ ∈ L := by
    intro a b
    show ((⁅φ₁ a, φ₂ b⁆ : ↥U) : Γ) ∈ Lp
    have h1 := hcomm (a : T₁) (b : T₂)
    have e1 : ((φ₁ a : ↥U) : Γ) = ψ₁ (a : T₁) := rfl
    have e2 : ((φ₂ b : ↥U) : Γ) = ψ₂ (b : T₂) := rfl
    have e3 : ((⁅φ₁ a, φ₂ b⁆ : ↥U) : Γ) = ⁅ψ₁ (a : T₁), ψ₂ (b : T₂)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, e1, e2]
    rw [e3]
    exact h1
  have h := card_mul_le_factorial_of_hom Φ hΦ L hLodd φ₁ φ₂ hcommL
    (not_isSolvable_alternatingGroup' h5₁) (not_isSolvable_alternatingGroup' h5₂) he₁ he₂
    f₁ f₂ hf₁ hf₂ hk₁ hk₂
  rwa [card_alternatingGroup_eq (by omega), card_alternatingGroup_eq (by omega)] at h

theorem false_of_alt_counts {a b c : ℕ} (hb : 5 ≤ b) (hab : b ≤ a) (hc : c ≤ b + 1)
    (h : a.factorial / 2 * (b.factorial / 2) ≤ c.factorial) : False := by
  have h1 := factorial_succ_lt_sq hb
  have h2 : b.factorial / 2 * (b.factorial / 2) ≤ a.factorial / 2 * (b.factorial / 2) :=
    Nat.mul_le_mul_right _ (Nat.div_le_div_right (Nat.factorial_le hab))
  have h3 : c.factorial ≤ (b + 1).factorial := Nat.factorial_le hc
  omega

end CFSG.OddStandard.Solomon75
