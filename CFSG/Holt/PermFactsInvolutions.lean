module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.Holt

open Equiv Equiv.Perm Finset

open scoped Nat

section Parity

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem cycleType_eq_replicate_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    π.cycleType = Multiset.replicate (#π.support / 2) 2 := by
  have h := cycleType_of_pow_prime_eq_one hπ
  have hs : #π.support = Multiset.card π.cycleType * 2 := by
    rw [← sum_cycleType, h]
    simp
  rw [hs, Nat.mul_div_cancel _ two_pos]
  exact h

theorem card_support_add_card_fixedPoints (π : Perm Ψ) :
    #π.support + Fintype.card (Function.fixedPoints π) = Fintype.card Ψ := by
  rw [card_fixedPoints, sum_cycleType, Nat.add_sub_cancel' (card_le_univ _)]

theorem sign_eq_neg_one_pow_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = (-1) ^ (#π.support / 2) := by
  rw [sign_of_pow_two_eq_one hπ, ← card_support_add_card_fixedPoints π, Nat.add_sub_cancel]

theorem sign_eq_one_iff_four_dvd_card_support {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = 1 ↔ 4 ∣ #π.support := by
  obtain ⟨m, hm⟩ := two_dvd_card_support hπ
  rw [sign_eq_neg_one_pow_of_sq_eq_one hπ, hm, Nat.mul_div_cancel_left _ two_pos,
    neg_one_pow_eq_one_iff_even (by decide)]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

theorem sign_eq_one_iff_four_dvd_card_sub {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = 1 ↔ 4 ∣ Nat.card Ψ - Nat.card (Function.fixedPoints π) := by
  rw [sign_eq_one_iff_four_dvd_card_support hπ, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← card_support_add_card_fixedPoints π, Nat.add_sub_cancel]

theorem card_support_eq_of_existsUnique {π : Perm Ψ} (h : ∃! x, π x = x) :
    #π.support + 1 = Nat.card Ψ := by
  obtain ⟨a, ha, huniq⟩ := h
  have hfix : Fintype.card (Function.fixedPoints π) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨a, ha⟩, fun ⟨y, hy⟩ => Subtype.ext (huniq y hy)⟩
  rw [Nat.card_eq_fintype_card, ← card_support_add_card_fixedPoints π, hfix]

theorem existsUnique_of_card_support_add_one {π : Perm Ψ} (h : #π.support + 1 = Nat.card Ψ) :
    ∃! x, π x = x := by
  have hfix : Fintype.card (Function.fixedPoints π) = 1 := by
    have := card_support_add_card_fixedPoints π
    rw [Nat.card_eq_fintype_card] at h
    omega
  obtain ⟨⟨a, ha⟩, hu⟩ := Fintype.card_eq_one_iff.mp hfix
  exact ⟨a, ha, fun y hy => congrArg Subtype.val (hu ⟨y, hy⟩)⟩

theorem sign_eq_one_iff_of_existsUnique {π : Perm Ψ} (hπ : π ^ 2 = 1) (h : ∃! x, π x = x) :
    sign π = 1 ↔ Nat.card Ψ % 4 = 1 := by
  rw [sign_eq_one_iff_four_dvd_card_support hπ, ← card_support_eq_of_existsUnique h]
  omega

end Parity

section Conjugacy

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_mem_alternatingGroup_conj_eq {π τ : Perm Ψ} (hτ : sign τ = -1)
    (hπτ : Commute π τ) (g : Perm Ψ) :
    ∃ h ∈ alternatingGroup Ψ, h * π * h⁻¹ = g * π * g⁻¹ := by
  rcases Int.units_eq_one_or (sign g) with hg | hg
  · exact ⟨g, hg, rfl⟩
  · refine ⟨g * τ, by simp [mem_alternatingGroup, hg, hτ], ?_⟩
    rw [mul_inv_rev, mul_assoc g τ π, ← hπτ.eq]
    group

omit [Fintype Ψ] in
theorem commute_swap_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) (a : Ψ) :
    Commute π (swap a (π a)) := by
  have h2 : π (π a) = a := by
    simpa [sq] using congrArg (fun f : Perm Ψ => f a) hπ
  rw [Commute, SemiconjBy, mul_swap_eq_swap_mul, h2, swap_comm]

theorem exists_mem_alternatingGroup_conj_eq_of_card_support_eq {π σ : Perm Ψ} (hπ : π ^ 2 = 1)
    (hσ : σ ^ 2 = 1) (h : #π.support = #σ.support) :
    ∃ g ∈ alternatingGroup Ψ, g * π * g⁻¹ = σ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((isConj_iff_cycleType_eq (σ := π) (τ := σ)).mpr (by
    rw [cycleType_eq_replicate_of_sq_eq_one hπ, cycleType_eq_replicate_of_sq_eq_one hσ, h]))
  by_cases h1 : π = 1
  · exact ⟨1, one_mem _, by simp [h1]⟩
  · obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
      by_contra! h'
      exact h1 (Equiv.ext h')
    exact exists_mem_alternatingGroup_conj_eq (sign_swap ha.symm)
      (commute_swap_of_sq_eq_one hπ a) g

theorem exists_mem_alternatingGroup_conj_eq_of_card_fixedPoints_eq {π σ : Perm Ψ}
    (hπ : π ^ 2 = 1) (hσ : σ ^ 2 = 1)
    (h : Nat.card (Function.fixedPoints π) = Nat.card (Function.fixedPoints σ)) :
    ∃ g ∈ alternatingGroup Ψ, g * π * g⁻¹ = σ := by
  refine exists_mem_alternatingGroup_conj_eq_of_card_support_eq hπ hσ ?_
  have hπ' := card_support_add_card_fixedPoints π
  have hσ' := card_support_add_card_fixedPoints σ
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  omega

theorem exists_mem_alternatingGroup_conj_eq_of_existsUnique {π σ : Perm Ψ} (hπ : π ^ 2 = 1)
    (hσ : σ ^ 2 = 1) (hπ1 : ∃! x, π x = x) (hσ1 : ∃! x, σ x = x) :
    ∃ g ∈ alternatingGroup Ψ, g * π * g⁻¹ = σ := by
  refine exists_mem_alternatingGroup_conj_eq_of_card_support_eq hπ hσ ?_
  have := card_support_eq_of_existsUnique hπ1
  have := card_support_eq_of_existsUnique hσ1
  omega

end Conjugacy

section Lifting

variable {G H : Type*} [Group G] [Group H]

theorem orderOf_pow_card_eq_two (ρ : G →* H) {O : Subgroup G} (hO : Odd (Nat.card O)) {x : G}
    (hx : x ^ 2 ∈ O) (hρ : orderOf (ρ x) = 2) :
    orderOf (x ^ Nat.card O) = 2 ∧ ρ (x ^ Nat.card O) = ρ x := by
  obtain ⟨k, hk⟩ := hO
  have hO1 : (x ^ 2) ^ Nat.card O = 1 := by
    have := pow_card_eq_one' (G := O) (x := ⟨x ^ 2, hx⟩)
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val this
  have hρ1 : ρ x ^ 2 = 1 := by
    rw [← hρ]
    exact pow_orderOf_eq_one _
  have hρy : ρ (x ^ Nat.card O) = ρ x := by
    rw [map_pow, hk, pow_succ, pow_mul, hρ1, one_pow, one_mul]
  refine ⟨orderOf_eq_prime ?_ ?_, hρy⟩
  · rw [← pow_mul, mul_comm, pow_mul, hO1]
  · intro h1
    have : ρ x = 1 := by rw [← hρy, h1, map_one]
    rw [this, orderOf_one] at hρ
    exact absurd hρ (by decide)

theorem exists_isPGroup_le_map_eq [Finite G] {p : ℕ} [Fact p.Prime] (ρ : G →* H)
    {K : Subgroup G} {R : Subgroup H} (hR : IsPGroup p R) (hRK : R ≤ K.map ρ) :
    ∃ P ≤ K, IsPGroup p P ∧ P.map ρ = R := by
  set L : Subgroup G := K ⊓ R.comap ρ
  let g : L →* R := (ρ.comp L.subtype).codRestrict R fun x => x.2.2
  have hf : Function.Surjective g := by
    rintro ⟨r, hr⟩
    obtain ⟨k, hk, rfl⟩ := hRK hr
    exact ⟨⟨k, hk, hr⟩, rfl⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p L))
  have htop : (T : Subgroup L).map g = ⊤ :=
    (T.mapSurjective hf).is_maximal' (hR.to_subgroup ⊤) le_top |>.symm
  refine ⟨(T : Subgroup L).map L.subtype, ?_, T.isPGroup'.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  · rw [Subgroup.map_map]
    have : ρ.comp L.subtype = R.subtype.comp g := rfl
    rw [this, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Lifting

section Centralizer

theorem padicValNat_two_factorial_two_mul (r : ℕ) :
    padicValNat 2 (2 * r)! = r + padicValNat 2 r ! := by
  rw [padicValNat_factorial_mul, add_comm]

theorem add_two_lt_two_pow_padicValNat_factorial {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    n + 2 < 2 ^ padicValNat 2 n ! := by
  obtain ⟨r, rfl⟩ := heven
  have hr : 2 ≤ r := by omega
  have h2 : ∀ k, 2 ≤ k → k + 1 < 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k _ ih => rw [pow_succ]; omega
  have h1 : 1 ≤ padicValNat 2 r ! :=
    one_le_padicValNat_of_dvd (Nat.factorial_pos r).ne' (Nat.dvd_factorial two_pos hr)
  have h2 := h2 r hr
  rw [← two_mul, padicValNat_two_factorial_two_mul]
  calc 2 * r + 2 < 2 ^ (r + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ (r + padicValNat 2 r !) := Nat.pow_le_pow_right two_pos (by omega)

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

theorem nat_card_centralizer_of_sq_eq_one {s : Perm Γ} (hs : s ^ 2 = 1) (hfree : ∀ x, s x ≠ x) :
    Nat.card (Subgroup.centralizer {s}) = 2 ^ (Nat.card Γ / 2) * (Nat.card Γ / 2)! := by
  have hsupp : #s.support = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Finset.card_eq_iff_eq_univ]
    ext x
    simp [hfree x]
  obtain ⟨r, hr⟩ := hsupp ▸ two_dvd_card_support hs
  have hct := cycleType_eq_replicate_of_sq_eq_one hs
  rw [hsupp, hr, Nat.mul_div_cancel_left _ two_pos] at hct
  have hc : Fintype.card Γ = 2 * r := by rw [← Nat.card_eq_fintype_card, hr]
  rw [hr, Nat.mul_div_cancel_left _ two_pos, nat_card_centralizer, hct, Multiset.sum_replicate,
    Multiset.prod_replicate, smul_eq_mul, hc, mul_comm r 2, Nat.sub_self, Nat.factorial_zero,
    one_mul, Multiset.toFinset_replicate]
  split_ifs with h0
  · simp [h0]
  · simp

theorem exists_isPGroup_le_centralizer_card_eq {s : Perm Γ} (hs : s ^ 2 = 1)
    (hfree : ∀ x, s x ≠ x) :
    ∃ P ≤ Subgroup.centralizer {s}, IsPGroup 2 P ∧
      Nat.card P = 2 ^ padicValNat 2 (Nat.card Γ)! := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (Subgroup.centralizer {s})))
  refine ⟨(T : Subgroup _).map (Subgroup.centralizer {s}).subtype, Subgroup.map_subtype_le _,
    T.isPGroup'.map _, ?_⟩
  have hsupp : #s.support = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Finset.card_eq_iff_eq_univ]
    ext x
    simp [hfree x]
  obtain ⟨r, hr⟩ := hsupp ▸ two_dvd_card_support hs
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), T.card_eq_multiplicity,
    nat_card_centralizer_of_sq_eq_one hs hfree, hr, Nat.mul_div_cancel_left _ two_pos,
    padicValNat_two_factorial_two_mul, Nat.factorization_def _ Nat.prime_two,
    padicValNat.mul (by positivity) (Nat.factorial_pos r).ne', padicValNat.prime_pow]

end Centralizer

section BlockTranslation

variable {Γ ι A : Type*} [AddCommGroup A] (e : Γ ≃ ι × A)

@[expose] def blockTranslate (f : ι → A) : Perm Γ where
  toFun γ := e.symm ((e γ).1, (e γ).2 + f (e γ).1)
  invFun γ := e.symm ((e γ).1, (e γ).2 - f (e γ).1)
  left_inv γ := by simp
  right_inv γ := by simp

@[simp]
theorem apply_blockTranslate (f : ι → A) (γ : Γ) :
    e (blockTranslate e f γ) = ((e γ).1, (e γ).2 + f (e γ).1) := by
  simp [blockTranslate]

theorem blockTranslate_add (f g : ι → A) :
    blockTranslate e (f + g) = blockTranslate e f * blockTranslate e g := by
  ext γ
  apply e.injective
  simp only [apply_blockTranslate, Perm.mul_apply, Pi.add_apply, Prod.mk.injEq, true_and]
  rw [add_comm (f _), add_assoc]

@[simp]
theorem blockTranslate_zero : blockTranslate e (0 : ι → A) = 1 := by
  ext γ
  apply e.injective
  simp

@[expose] def blockTranslateHom : Multiplicative (ι → A) →* Perm Γ where
  toFun f := blockTranslate e f.toAdd
  map_one' := blockTranslate_zero e
  map_mul' f g := blockTranslate_add e f.toAdd g.toAdd

@[expose] def blockTranslations : Subgroup (Perm Γ) := (blockTranslateHom e).range

theorem mem_blockTranslations {x : Perm Γ} :
    x ∈ blockTranslations e ↔ ∃ f, blockTranslate e f = x :=
  ⟨fun ⟨f, hf⟩ => ⟨f.toAdd, hf⟩, fun ⟨f, hf⟩ => ⟨Multiplicative.ofAdd f, hf⟩⟩

theorem blockTranslate_mem (f : ι → A) : blockTranslate e f ∈ blockTranslations e :=
  (mem_blockTranslations e).2 ⟨f, rfl⟩

theorem blockTranslate_apply_eq_self_iff (f : ι → A) (γ : Γ) :
    blockTranslate e f γ = γ ↔ f (e γ).1 = 0 := by
  rw [← e.injective.eq_iff, apply_blockTranslate]
  simp [Prod.ext_iff]

theorem blockTranslate_commute (f g : ι → A) :
    Commute (blockTranslate e f) (blockTranslate e g) := by
  rw [Commute, SemiconjBy, ← blockTranslate_add, ← blockTranslate_add, add_comm]

theorem blockTranslate_sq (hA : ∀ a : A, a + a = 0) (f : ι → A) :
    blockTranslate e f ^ 2 = 1 := by
  rw [sq, ← blockTranslate_add, show f + f = 0 from funext fun i => hA (f i),
    blockTranslate_zero]

theorem isPGroup_blockTranslations (hA : ∀ a : A, a + a = 0) :
    IsPGroup 2 (blockTranslations e) := by
  rintro ⟨x, hx⟩
  obtain ⟨f, rfl⟩ := (mem_blockTranslations e).1 hx
  exact ⟨1, Subtype.ext (by simpa using blockTranslate_sq e hA f)⟩

theorem exists_blockTranslate_apply_ne [Nontrivial A] (γ : Γ) :
    ∃ f : ι → A, blockTranslate e f γ ≠ γ := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact ⟨fun _ => a, by rw [Ne, blockTranslate_apply_eq_self_iff]; exact ha⟩

theorem card_support_blockTranslate [Fintype Γ] [DecidableEq Γ] [Fintype ι] [Fintype A]
    [DecidableEq A] (f : ι → A) :
    #(blockTranslate e f).support = #{i | f i ≠ 0} * Fintype.card A := by
  have h1 : (blockTranslate e f).support = univ.filter (fun γ => f (e γ).1 ≠ 0) := by
    ext γ
    simp [mem_support, blockTranslate_apply_eq_self_iff]
  have h2 : #(univ.filter (fun γ => f (e γ).1 ≠ 0)) =
      #((univ : Finset (ι × A)).filter (fun q => f q.1 ≠ 0)) := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  rw [h1, h2, ← univ_product_univ, filter_product_left (fun i => f i ≠ 0), card_product,
    card_univ]

theorem mem_blockTranslations_of_forall_commute [DecidableEq ι] [Nontrivial A] {c : Perm Γ}
    (hc : ∀ f : ι → A, Commute c (blockTranslate e f)) : c ∈ blockTranslations e := by
  have hcomm : ∀ (f : ι → A) (γ : Γ), c (blockTranslate e f γ) = blockTranslate e f (c γ) :=
    fun f γ => congrArg (fun g : Perm Γ => g γ) (hc f).eq
  have hblock : ∀ γ, (e (c γ)).1 = (e γ).1 := by
    intro γ
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    by_contra hne
    have h1 : blockTranslate e (Pi.single (e γ).1 a) (c γ) = c γ := by
      rw [blockTranslate_apply_eq_self_iff, Pi.single_eq_of_ne hne]
    have h2 : blockTranslate e (Pi.single (e γ).1 a) γ ≠ γ := by
      rw [Ne, blockTranslate_apply_eq_self_iff, Pi.single_eq_same]
      exact ha
    exact h2 (c.injective (by rw [hcomm, h1]))
  have key : ∀ i a, e (c (e.symm (i, a))) = (i, (e (c (e.symm (i, 0)))).2 + a) := by
    intro i a
    have hγ : e.symm (i, a) = blockTranslate e (Pi.single i a) (e.symm (i, 0)) := by
      apply e.injective
      simp
    rw [hγ, hcomm, apply_blockTranslate, hblock]
    simp
  refine (mem_blockTranslations e).2 ⟨fun i => (e (c (e.symm (i, 0)))).2, ?_⟩
  ext γ
  apply e.injective
  have h := key (e γ).1 (e γ).2
  rw [Prod.mk.eta, e.symm_apply_apply] at h
  rw [apply_blockTranslate, h, add_comm]

theorem nonempty_equiv_fin_prod {Γ A : Type*} [Fintype Γ] [Fintype A] {k : ℕ}
    (h : Nat.card Γ = k * Fintype.card A) : Nonempty (Γ ≃ Fin k × A) :=
  ⟨Fintype.equivOfCardEq (by rw [← Nat.card_eq_fintype_card, h, Fintype.card_prod,
    Fintype.card_fin])⟩

end BlockTranslation

section FourGroup

@[expose] def fourRot (v : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (v.2, v.1 + v.2)

theorem fourRot_add (v w : ZMod 2 × ZMod 2) : fourRot (v + w) = fourRot v + fourRot w := by
  revert v w
  unfold fourRot
  decide

theorem fourRot_fourRot_fourRot (v : ZMod 2 × ZMod 2) : fourRot (fourRot (fourRot v)) = v := by
  revert v
  unfold fourRot
  decide

theorem fourRot_ne_zero_and {v : ZMod 2 × ZMod 2} (hv : v ≠ 0) :
    fourRot v ≠ 0 ∧ v + fourRot v ≠ 0 := by
  revert v
  unfold fourRot
  decide

theorem four_add_self (v : ZMod 2 × ZMod 2) : v + v = 0 := by
  revert v
  decide

variable {Γ ι : Type*} (e : Γ ≃ ι × (ZMod 2 × ZMod 2))

@[expose] def blockRotate : Perm Γ where
  toFun γ := e.symm ((e γ).1, fourRot (e γ).2)
  invFun γ := e.symm ((e γ).1, fourRot (fourRot (e γ).2))
  left_inv γ := by simp [fourRot_fourRot_fourRot]
  right_inv γ := by simp [fourRot_fourRot_fourRot]

@[simp]
theorem apply_blockRotate (γ : Γ) : e (blockRotate e γ) = ((e γ).1, fourRot (e γ).2) := by
  simp [blockRotate]

theorem blockRotate_mul_blockTranslate (f : ι → ZMod 2 × ZMod 2) :
    blockRotate e * blockTranslate e f = blockTranslate e (fourRot ∘ f) * blockRotate e := by
  ext γ
  apply e.injective
  simp [fourRot_add]

theorem blockRotate_pow_three : blockRotate e ^ 3 = 1 := by
  ext γ
  apply e.injective
  simp [pow_succ, fourRot_fourRot_fourRot]

theorem centralizer_blockTranslations [DecidableEq ι] :
    Subgroup.centralizer (blockTranslations e : Set (Perm Γ)) = blockTranslations e := by
  ext c
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    exact mem_blockTranslations_of_forall_commute e fun f => (hc _ (blockTranslate_mem e f)).symm
  · intro hc x hx
    obtain ⟨f, rfl⟩ := (mem_blockTranslations e).1 hc
    obtain ⟨g, rfl⟩ := (mem_blockTranslations e).1 hx
    exact (blockTranslate_commute e g f).eq

variable [Fintype Γ] [DecidableEq Γ]

theorem blockRotate_mem_alternatingGroup : blockRotate e ∈ alternatingGroup Γ := by
  have h := congrArg sign (blockRotate_pow_three e)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (sign (blockRotate e)) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem blockTranslations_le_alternatingGroup [Fintype ι] :
    blockTranslations e ≤ alternatingGroup Γ := by
  intro x hx
  obtain ⟨f, rfl⟩ := (mem_blockTranslations e).1 hx
  rw [mem_alternatingGroup, sign_eq_one_iff_four_dvd_card_support
    (blockTranslate_sq e four_add_self f), card_support_blockTranslate]
  exact Dvd.intro_left _ rfl

theorem exists_conj_eq_blockTranslate {x : Perm Γ} (hx : x ∈ blockTranslations e)
    (hfree : ∀ γ, x γ ≠ γ) :
    ∃ w ∈ blockTranslations e, ∃ h ∈ alternatingGroup Γ,
      (∀ γ, w γ ≠ γ) ∧ (∀ γ, (x * w) γ ≠ γ) ∧ h * x * h⁻¹ = w := by
  obtain ⟨f, rfl⟩ := (mem_blockTranslations e).1 hx
  have hf : ∀ γ, f (e γ).1 ≠ 0 := fun γ => by
    simpa [blockTranslate_apply_eq_self_iff] using hfree γ
  refine ⟨blockTranslate e (fourRot ∘ f), blockTranslate_mem e _, blockRotate e,
    blockRotate_mem_alternatingGroup e, fun γ => ?_, fun γ => ?_, ?_⟩
  · rw [Ne, blockTranslate_apply_eq_self_iff]
    exact (fourRot_ne_zero_and (hf γ)).1
  · rw [← blockTranslate_add, Ne, blockTranslate_apply_eq_self_iff]
    exact (fourRot_ne_zero_and (hf γ)).2
  · rw [mul_inv_eq_iff_eq_mul, blockRotate_mul_blockTranslate]

omit [DecidableEq Γ] in
theorem nonempty_equiv_fin_prod_four (h : 4 ∣ Nat.card Γ) :
    Nonempty (Γ ≃ Fin (Nat.card Γ / 4) × (ZMod 2 × ZMod 2)) :=
  nonempty_equiv_fin_prod (by
    rw [Fintype.card_prod, ZMod.card, Nat.div_mul_cancel h])

end FourGroup

section FixedPointFree

variable {Λ : Type*}

theorem exists_mem_sylow_smul_ne {G : Type*} [Group G] [Finite G] [MulAction G Λ] {p : ℕ}
    [Fact p.Prime] {R : Subgroup G} (hR : IsPGroup p R) (hfree : ∀ x : Λ, ∃ r ∈ R, r • x ≠ x)
    (P : Sylow p G) (x : Λ) : ∃ g ∈ (P : Subgroup G), g • x ≠ x := by
  obtain ⟨Q, hQ⟩ := hR.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  obtain ⟨r, hr, hrx⟩ := hfree (g • x)
  have hmem : r ∈ ((g • P : Sylow p G) : Subgroup G) := hQ hr
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv] at hmem
  refine ⟨_, hmem, fun h => hrx ?_⟩
  rwa [mul_smul, mul_smul, inv_smul_eq_iff] at h

variable [Fintype Λ] [DecidableEq Λ]

theorem exists_isPGroup_le_alternatingGroup_forall_exists_ne (h4 : 4 ≤ Nat.card Λ)
    (heven : Even (Nat.card Λ)) :
    ∃ R ≤ alternatingGroup Λ, IsPGroup 2 R ∧ ∀ x : Λ, ∃ r ∈ R, r x ≠ x := by
  obtain ⟨m, hm⟩ := heven
  obtain ⟨e⟩ := nonempty_equiv_fin_prod (Γ := Λ) (A := ZMod 2) (k := m) (by
    rw [hm, ZMod.card]
    ring)
  have hA : ∀ a : ZMod 2, a + a = 0 := by decide
  refine ⟨blockTranslations e ⊓ alternatingGroup Λ, inf_le_right,
    (isPGroup_blockTranslations e hA).to_le inf_le_left, fun x => ?_⟩
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) (e x).1
  set f : Fin m → ZMod 2 := Pi.single (e x).1 1 + Pi.single j 1
  have hsupp : ∀ l, f l ≠ 0 ↔ l = (e x).1 ∨ l = j := by
    intro l
    by_cases h1 : l = (e x).1
    · subst h1
      simp [f, Pi.single_eq_of_ne' hj]
    · by_cases h2 : l = j
      · subst h2
        simp [f, h1]
      · simp [f, h1, h2]
  have hcard : #{l | f l ≠ 0} = 2 := by
    rw [show (univ.filter fun l => f l ≠ 0) = {(e x).1, j} by ext l; simp [hsupp]]
    exact card_pair hj.symm
  refine ⟨blockTranslate e f, Subgroup.mem_inf.2 ⟨blockTranslate_mem e f, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, sign_eq_one_iff_four_dvd_card_support (blockTranslate_sq e hA f),
      card_support_blockTranslate, hcard]
    decide
  · rw [Ne, blockTranslate_apply_eq_self_iff]
    exact (hsupp _).2 (Or.inl rfl)

theorem exists_mem_sylow_alternatingGroup_apply_ne (h4 : 4 ≤ Nat.card Λ)
    (heven : Even (Nat.card Λ)) (P : Sylow 2 (alternatingGroup Λ)) (x : Λ) :
    ∃ r ∈ (P : Subgroup (alternatingGroup Λ)), (r : Perm Λ) x ≠ x := by
  obtain ⟨R, hRA, hR, hfree⟩ := exists_isPGroup_le_alternatingGroup_forall_exists_ne h4 heven
  refine exists_mem_sylow_smul_ne (hR.comap_of_injective _ (Subgroup.subtype_injective _))
    (fun y => ?_) P x
  obtain ⟨r, hr, hry⟩ := hfree y
  exact ⟨⟨r, hRA hr⟩, hr, hry⟩

theorem exists_mem_sylow_perm_apply_ne (h4 : 4 ≤ Nat.card Λ) (heven : Even (Nat.card Λ))
    (P : Sylow 2 (Perm Λ)) (x : Λ) : ∃ r ∈ (P : Subgroup (Perm Λ)), r x ≠ x := by
  obtain ⟨R, -, hR, hfree⟩ := exists_isPGroup_le_alternatingGroup_forall_exists_ne h4 heven
  exact exists_mem_sylow_smul_ne hR hfree P x

end FixedPointFree

end CFSG.Holt
