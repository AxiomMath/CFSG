module

public import CFSG.Holt.PermFactsInvolutions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Holt

open Equiv Equiv.Perm Finset

theorem closure_normal_of_conj_mem {G : Type*} [Group G] {s : Set G}
    (hs : ∀ g, ∀ x ∈ s, g * x * g⁻¹ ∈ s) : (Subgroup.closure s).Normal := by
  constructor
  intro n hn g
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hs g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

section Generation

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_longInvolution (h : Odd (Nat.card Ψ)) (h3 : 3 ≤ Nat.card Ψ) :
    ∃ π : Perm Ψ, orderOf π = 2 ∧ ∃! x, π x = x := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨π, hπ⟩ := (exists_with_cycleType_iff (α := Ψ)
    (m := Multiset.replicate k 2)).2 ⟨by simp [← Nat.card_eq_fintype_card, hk]; omega,
      fun a ha => (Multiset.eq_of_mem_replicate ha).ge⟩
  have hsq : π ^ 2 = 1 := pow_prime_eq_one_iff.2 fun c hc => by
    rw [hπ] at hc
    exact Multiset.eq_of_mem_replicate hc
  have hne : π ≠ 1 := by
    rintro rfl
    rw [cycleType_one] at hπ
    have := congrArg Multiset.card hπ
    simp at this
    omega
  refine ⟨π, orderOf_eq_prime hsq hne, existsUnique_of_card_support_add_one ?_⟩
  rw [← sum_cycleType, hπ, hk]
  simp
  ring

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem closure_longInvolutions_perm_normal :
    (Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x}).Normal := by
  refine closure_normal_of_conj_mem fun g π ⟨h2, h1⟩ => ⟨?_, ?_⟩
  · rw [← h2, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · obtain ⟨a, ha, hu⟩ := h1
    refine ⟨g a, by simp [ha], fun y hy => ?_⟩
    have : π (g⁻¹ y) = g⁻¹ y := by
      simpa [Perm.mul_apply, eq_inv_iff_mul_eq_one, ← Perm.eq_inv_iff_eq] using hy
    rw [← hu _ this]
    simp

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem sq_eq_one_of_orderOf_eq_two {π : Perm Ψ} (h : orderOf π = 2) : π ^ 2 = 1 :=
  h ▸ pow_orderOf_eq_one π

theorem eq_top_of_alternatingGroup_le {H : Subgroup (Perm Ψ)} (hA : alternatingGroup Ψ ≤ H)
    {τ : Perm Ψ} (hτH : τ ∈ H) (hτ : sign τ = -1) : H = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rcases Int.units_eq_one_or (sign σ) with hσ | hσ
  · exact hA hσ
  · rw [show σ = σ * τ⁻¹ * τ by group]
    exact mul_mem (hA (by simp [mem_alternatingGroup, hσ, hτ])) hτH

theorem closure_longInvolutions_eq_alternatingGroup (h : Nat.card Ψ % 4 = 1) :
    Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} = alternatingGroup Ψ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro π ⟨hπ2, hπ1⟩
    exact (sign_eq_one_iff_of_existsUnique (sq_eq_one_of_orderOf_eq_two hπ2) hπ1).2 h
  · rcases (by omega : Nat.card Ψ = 1 ∨ 5 ≤ Nat.card Ψ) with h1 | h5
    · rw [alternatingGroup.eq_bot_of_card_le_two (by omega)]
      exact bot_le
    · have := closure_longInvolutions_perm_normal (Ψ := Ψ)
      obtain ⟨π, hπ⟩ := exists_longInvolution (Ψ := Ψ) (Nat.odd_iff.2 (by omega)) (by omega)
      refine Equiv.Perm.alternatingGroup_le_of_normal h5 ⟨⟨π, Subgroup.subset_closure hπ⟩, 1,
        fun h1 => ?_⟩
      have : π = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at hπ
      exact absurd hπ.1 (by decide)

theorem closure_longInvolutions_eq_top (h : Nat.card Ψ % 4 = 3) :
    Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} = ⊤ := by
  rcases (by omega : Nat.card Ψ = 3 ∨ 7 ≤ Nat.card Ψ) with h3 | h7
  · rw [eq_top_iff, ← closure_isSwap]
    apply Subgroup.closure_mono
    rintro σ ⟨a, b, hab, rfl⟩
    refine ⟨orderOf_eq_prime (by rw [sq, swap_mul_self]) 
      (fun h1 => hab (by simpa using (congrArg (fun f : Perm Ψ => f a) h1).symm)),
      existsUnique_of_card_support_add_one ?_⟩
    rw [card_support_swap hab, h3]
  · have := closure_longInvolutions_perm_normal (Ψ := Ψ)
    obtain ⟨π, hπ⟩ := exists_longInvolution (Ψ := Ψ) (Nat.odd_iff.2 (by omega)) (by omega)
    have hπ1 : π ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hπ
      exact absurd hπ.1 (by decide)
    have hA : alternatingGroup Ψ ≤ Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} :=
      Equiv.Perm.alternatingGroup_le_of_normal (by omega) ⟨⟨π, Subgroup.subset_closure hπ⟩, 1,
        fun h1 => hπ1 (congrArg Subtype.val h1)⟩
    have hodd : sign π = -1 := by
      rcases Int.units_eq_one_or (sign π) with h1 | h1
      · have := (sign_eq_one_iff_of_existsUnique (sq_eq_one_of_orderOf_eq_two hπ.1) hπ.2).1 h1
        omega
      · exact h1
    exact eq_top_of_alternatingGroup_le hA (Subgroup.subset_closure hπ) hodd

theorem alternatingGroup_le_closure_longInvolutions (h : Odd (Nat.card Ψ)) :
    alternatingGroup Ψ ≤ Subgroup.closure {π : Perm Ψ | orderOf π = 2 ∧ ∃! x, π x = x} := by
  rcases (by rw [Nat.odd_iff] at h; omega : Nat.card Ψ % 4 = 1 ∨ Nat.card Ψ % 4 = 3) with h1 | h3
  · rw [closure_longInvolutions_eq_alternatingGroup h1]
  · rw [closure_longInvolutions_eq_top h3]
    exact le_top

end Generation

section Normal

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem eq_one_of_forall_commute_alternatingGroup (h4 : 4 ≤ Nat.card Λ) {c : Perm Λ}
    (hc : ∀ a ∈ alternatingGroup Λ, Commute c a) : c = 1 := by
  ext x
  by_contra hx
  rw [Perm.one_apply] at hx
  have hcard : 1 < #(univ \ {x, c x}) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair (Ne.symm hx),
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.1 hcard
  simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hy hz
  set σ := swap x y * swap x z
  have hσ : IsThreeCycle σ := isThreeCycle_swap_mul_swap_same (Ne.symm hy.1) (Ne.symm hz.1) hyz
  have h1 : σ x = z := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hz.1 (Ne.symm hyz)]
  have h2 : σ (c x) = c x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx (Ne.symm hz.2),
      swap_apply_of_ne_of_ne hx (Ne.symm hy.2)]
  have hcomm : c (σ x) = σ (c x) :=
    congrArg (fun f : Perm Λ => f x) (hc σ hσ.mem_alternatingGroup).eq
  rw [h1, h2] at hcomm
  exact hz.1 (c.injective hcomm)

theorem eq_bot_or_alternatingGroup_le (h5 : 5 ≤ Nat.card Λ) {N : Subgroup (Perm Λ)}
    (hN : alternatingGroup Λ ≤ Subgroup.normalizer (N : Set (Perm Λ))) :
    N = ⊥ ∨ alternatingGroup Λ ≤ N := by
  set A := alternatingGroup Λ
  have hM : ((N ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun m hm a => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN a.2) m).1 hm.1,
      mul_mem (mul_mem a.2 hm.2) (inv_mem a.2)⟩
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h5 (N := (N ⊓ A).subgroupOf A)
    with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_commute_alternatingGroup (by omega) fun a ha => ?_
    have hk : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ A := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
        exact mul_mem hn ((Subgroup.mem_normalizer_iff.1 (hN ha) _).1 (inv_mem hn))
      · exact mul_mem ((alternatingGroup.normal).conj_mem a ha n) (inv_mem ha)
    have hk1 : (⟨_, hk.2⟩ : A) ∈ (N ⊓ A).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    rw [h, Subgroup.mem_bot] at hk1
    have := congrArg Subtype.val hk1
    simp only [OneMemClass.coe_one] at this
    rw [Commute, SemiconjBy, ← mul_inv_eq_one, mul_inv_rev, ← mul_assoc]
    exact this
  · right
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ (N ⊓ A).subgroupOf A := by
      rw [h]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1

theorem eq_bot_or_eq_alternatingGroup_or_eq_top_of_normal (h5 : 5 ≤ Nat.card Λ)
    {N : Subgroup (Perm Λ)} [N.Normal] : N = ⊥ ∨ N = alternatingGroup Λ ∨ N = ⊤ := by
  rcases eq_bot_or_alternatingGroup_le h5 (N := N) (by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top) with h | h
  · exact Or.inl h
  · right
    by_cases hN : ∃ τ ∈ N, sign τ = -1
    · obtain ⟨τ, hτN, hτ⟩ := hN
      exact Or.inr (eq_top_of_alternatingGroup_le h hτN hτ)
    · push Not at hN
      refine Or.inl (le_antisymm (fun τ hτ => ?_) h)
      rcases Int.units_eq_one_or (sign τ) with h1 | h1
      · exact h1
      · exact absurd h1 (hN τ hτ)

theorem eq_bot_of_odd_card (h5 : 5 ≤ Nat.card Λ) {N : Subgroup (Perm Λ)}
    (hN : alternatingGroup Λ ≤ Subgroup.normalizer (N : Set (Perm Λ)))
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  refine (eq_bot_or_alternatingGroup_le h5 hN).resolve_right fun hA => ?_
  have : Nontrivial Λ := Fintype.one_lt_card_iff_nontrivial.1 (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  have h2 : 2 ∣ Nat.card (alternatingGroup Λ) := by
    rw [nat_card_alternatingGroup]
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial (show 4 ≤ Nat.card Λ by omega)
    rw [hk, show Nat.factorial 4 = 2 * 12 from rfl, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    exact Dvd.intro (6 * k) (by ring)
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2
    (h2.trans (Subgroup.card_dvd_of_le hA)))

theorem eq_bot_of_odd_card_of_normal (h5 : 5 ≤ Nat.card Λ) {Y N : Subgroup (Perm Λ)}
    (hAY : alternatingGroup Λ ≤ Y) (hNY : N ≤ Y) [(N.subgroupOf Y).Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ :=
  eq_bot_of_odd_card h5 (hAY.trans (Subgroup.le_normalizer_of_normal_subgroupOf hNY)) hodd

end Normal

section Semiregular

variable {G Λ : Type*} [Group G] [MulAction G Λ]

theorem card_le_card_of_semiregular [Finite Λ] (h : ∀ g : G, ∀ x : Λ, g • x = x → g = 1)
    (x : Λ) : Nat.card G ≤ Nat.card Λ := by
  refine Nat.card_le_card_of_injective (fun g => g • x) fun g g' hgg => ?_
  have : (g'⁻¹ * g) • x = x := by
    simp only at hgg
    rw [mul_smul, hgg, inv_smul_smul]
  exact (inv_mul_eq_one.1 (h _ _ this)).symm

theorem card_dvd_card_of_semiregular [Finite G] [Finite Λ]
    (h : ∀ g : G, ∀ x : Λ, g • x = x → g = 1) : Nat.card G ∣ Nat.card Λ := by
  have horb : ∀ y : Λ, Nat.card (MulAction.orbit G y) = Nat.card G := by
    intro y
    have hstab : MulAction.stabilizer G y = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact h g y hg
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G y), hstab,
      Nat.card_congr (QuotientGroup.quotientBot.toEquiv)]
  have : Fintype (MulAction.orbitRel.Quotient G Λ) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G Λ), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => (horb _).symm.dvd

end Semiregular

section Product

variable {A B : Type*} [Fintype A] [DecidableEq A]

theorem prod_bot_le_of_card_le_four [Finite B] (hA : 5 ≤ Nat.card A) (hB : Nat.card B ≤ 4)
    {Y : Subgroup (Perm A × Perm B)} (hY : alternatingGroup A ≤ Y.map (MonoidHom.fst _ _)) :
    (alternatingGroup A).prod ⊥ ≤ Y := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).1 (Equiv.Perm.isSolvable hB)
  set f₁ : Y →* Perm A := (MonoidHom.fst _ _).comp Y.subtype
  set f₂ : Y →* Perm B := (MonoidHom.snd _ _).comp Y.subtype
  have h1 : ∀ k, alternatingGroup A ≤ (derivedSeries Y k).map f₁ := by
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
        Subgroup.range_subtype]
      exact hY
    | succ k ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ← commutator_alternatingGroup_eq_self hA]
      exact Subgroup.commutator_mono ih ih
  have h2 : (derivedSeries Y n).map f₂ = ⊥ := by
    rw [eq_bot_iff, ← hn]
    exact map_derivedSeries_le_derivedSeries f₂ n
  rintro ⟨a, b⟩ hab
  rw [Subgroup.mem_prod, Subgroup.mem_bot] at hab
  obtain ⟨y, hy, hya⟩ := h1 n hab.1
  have hyb : f₂ y = 1 := by
    have : f₂ y ∈ (derivedSeries Y n).map f₂ := ⟨y, hy, rfl⟩
    rwa [h2, Subgroup.mem_bot] at this
  have : (y : Perm A × Perm B) = (a, b) := Prod.ext hya (hyb.trans hab.2.symm)
  rw [← this]
  exact y.2

theorem prod_bot_le_of_card_lt [Fintype B] (hA : 5 ≤ Nat.card A) (hB : Nat.card B < Nat.card A)
    {Y : Subgroup (Perm A × Perm B)} (hY : alternatingGroup A ≤ Y.map (MonoidHom.fst _ _)) :
    (alternatingGroup A).prod ⊥ ≤ Y := by
  set Alt := alternatingGroup A
  set N : Subgroup (Perm A) := Y.comap (MonoidHom.inl _ _) ⊓ Alt
  have hlift : ∀ a ∈ Alt, ∃ b, (a, b) ∈ Y := fun a ha => by
    obtain ⟨⟨a', b⟩, hy, rfl⟩ := hY ha
    exact ⟨b, hy⟩
  have hN : (N.subgroupOf Alt).Normal := by
    refine ⟨fun m hm a => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm ⊢
    obtain ⟨b, hb⟩ := hlift a a.2
    refine ⟨?_, mul_mem (mul_mem a.2 hm.2) (inv_mem a.2)⟩
    have := mul_mem (mul_mem hb hm.1) (inv_mem hb)
    simpa [Subgroup.mem_comap] using this
  suffices hAN : Alt ≤ N by
    rintro ⟨a, b⟩ hab
    rw [Subgroup.mem_prod, Subgroup.mem_bot] at hab
    obtain rfl := hab.2
    exact (hAN hab.1).1
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top hA (N := N.subgroupOf Alt) with h | h
  · exfalso
    choose! g hg using hlift
    have hinj : Function.Injective fun a : Alt => g a := by
      intro a a' haa
      have hmem : (a * a'⁻¹ : Alt) ∈ N.subgroupOf Alt := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨?_, (a * a'⁻¹).2⟩
        have := mul_mem (hg a a.2) (inv_mem (hg a' a'.2))
        simp only at haa
        simpa [Subgroup.mem_comap, haa] using this
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    have h1 := Nat.card_le_card_of_injective _ hinj
    have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by
      rw [← Nat.card_eq_fintype_card]
      omega)
    rw [nat_card_alternatingGroup, Nat.card_perm] at h1
    obtain ⟨k, hk⟩ : ∃ k, Nat.card A = k + 1 := ⟨Nat.card A - 1, by omega⟩
    rw [hk, Nat.factorial_succ] at h1
    have h2 : (Nat.card B).factorial ≤ k.factorial := Nat.factorial_le (by omega)
    have h3 := Nat.factorial_pos k
    have h4 : 2 * k.factorial < (k + 1) * k.factorial :=
      Nat.mul_lt_mul_of_pos_right (by omega) h3
    have h5 := Nat.div_mul_cancel (show 2 ∣ (k + 1) * k.factorial by
      rw [← Nat.factorial_succ, ← hk]
      exact Nat.dvd_factorial two_pos (by omega))
    nlinarith
  · intro a ha
    have : (⟨a, ha⟩ : Alt) ∈ N.subgroupOf Alt := by
      rw [h]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at this

end Product

section Subset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {Δ : Set Ω} [DecidablePred (· ∈ Δ)]

omit [Fintype Ω] [DecidableEq Ω] in
theorem exists_subtypeCongr_eq_of_forall_apply_eq {y : Perm Ω} {σ : Perm Δ}
    (h : ∀ δ : Δ, y δ = σ δ) : ∃ τ : Perm {x // x ∉ Δ}, σ.subtypeCongr τ = y := by
  have hstab : ∀ x, y x ∉ Δ ↔ x ∉ Δ := by
    intro x
    constructor
    · intro hyx hx
      apply hyx
      rw [show x = ((⟨x, hx⟩ : Δ) : Ω) from rfl, h]
      exact (σ ⟨x, hx⟩).2
    · intro hx hyx
      apply hx
      have : y x = y (σ⁻¹ ⟨y x, hyx⟩) := by
        rw [h]
        simp
      rw [y.injective this]
      exact (σ⁻¹ ⟨y x, hyx⟩).2
  refine ⟨y.subtypePerm hstab, ?_⟩
  ext x
  by_cases hx : x ∈ Δ
  · rw [Perm.subtypeCongr.left_apply _ _ hx]
    exact (h ⟨x, hx⟩).symm
  · rw [Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem alternatingGroup_le_map_fst_comap {Y : Subgroup (Perm Ω)}
    (hY : ∀ σ ∈ alternatingGroup Δ, ∃ y ∈ Y, ∀ δ : Δ, y δ = σ δ) :
    alternatingGroup Δ ≤ (Y.comap (subtypeCongrHom (· ∈ Δ))).map (MonoidHom.fst _ _) := by
  intro σ hσ
  obtain ⟨y, hy, hyσ⟩ := hY σ hσ
  obtain ⟨τ, hτ⟩ := exists_subtypeCongr_eq_of_forall_apply_eq hyσ
  exact ⟨(σ, τ), by simpa [Subgroup.mem_comap, hτ] using hy, rfl⟩

theorem ofSubtype_mem_of_prod_bot_le {Y : Subgroup (Perm Ω)}
    (h : (alternatingGroup Δ).prod ⊥ ≤ Y.comap (subtypeCongrHom (· ∈ Δ))) {σ : Perm Δ}
    (hσ : σ ∈ alternatingGroup Δ) : ofSubtype σ ∈ Y := by
  have := h (x := (σ, 1)) (Subgroup.mem_prod.2 ⟨hσ, Subgroup.one_mem _⟩)
  rw [Subgroup.mem_comap, subtypeCongrHom_apply] at this
  convert this using 1
  ext x
  by_cases hx : x ∈ Δ
  · rw [ofSubtype_apply_of_mem _ hx, Perm.subtypeCongr.left_apply _ _ hx]
  · rw [ofSubtype_apply_of_not_mem _ hx, Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem ofSubtype_mem_of_card_compl_le_four {Y : Subgroup (Perm Ω)} (h5 : 5 ≤ Nat.card Δ)
    (h4 : Nat.card ↥Δᶜ ≤ 4) (hY : ∀ σ ∈ alternatingGroup Δ, ∃ y ∈ Y, ∀ δ : Δ, y δ = σ δ)
    {σ : Perm Δ} (hσ : σ ∈ alternatingGroup Δ) : ofSubtype σ ∈ Y :=
  ofSubtype_mem_of_prod_bot_le
    (prod_bot_le_of_card_le_four (B := {x // x ∉ Δ}) h5 h4 (alternatingGroup_le_map_fst_comap hY))
    hσ

theorem ofSubtype_mem_of_card_compl_lt {Y : Subgroup (Perm Ω)} (h5 : 5 ≤ Nat.card Δ)
    (hlt : Nat.card ↥Δᶜ < Nat.card Δ)
    (hY : ∀ σ ∈ alternatingGroup Δ, ∃ y ∈ Y, ∀ δ : Δ, y δ = σ δ)
    {σ : Perm Δ} (hσ : σ ∈ alternatingGroup Δ) : ofSubtype σ ∈ Y :=
  ofSubtype_mem_of_prod_bot_le
    (prod_bot_le_of_card_lt (B := {x // x ∉ Δ}) h5 hlt (alternatingGroup_le_map_fst_comap hY))
    hσ

omit [DecidablePred (· ∈ Δ)] in
theorem exists_isThreeCycle_ofSubtype {p : Ω → Prop} [DecidablePred p]
    (h3 : 3 ≤ Nat.card {x // p x}) :
    ∃ σ : Perm {x // p x}, σ.IsThreeCycle ∧ (ofSubtype σ).IsThreeCycle := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1
    (by rw [← Nat.card_eq_fintype_card]; omega : 2 < Fintype.card {x // p x})
  have h := isThreeCycle_swap_mul_swap_same hab hac hbc
  refine ⟨_, h, ?_⟩
  unfold IsThreeCycle
  rw [cycleType_ofSubtype]
  exact h

theorem exists_isThreeCycle_mem_of_card_compl_lt {X : Subgroup (Perm Ω)} (h5 : 5 ≤ Nat.card Δ)
    (hlt : Nat.card ↥Δᶜ < Nat.card Δ)
    (hX : ∀ σ ∈ alternatingGroup Δ, ∃ x ∈ X, ∀ δ : Δ, x δ = σ δ) :
    ∃ g ∈ X, g.IsThreeCycle := by
  obtain ⟨σ, hσ, h3⟩ := exists_isThreeCycle_ofSubtype (p := (· ∈ Δ))
    (show 3 ≤ Nat.card Δ by omega)
  exact ⟨_, ofSubtype_mem_of_card_compl_lt h5 hlt hX hσ.mem_alternatingGroup, h3⟩

theorem alternatingGroup_le_of_isPreprimitive_of_card_compl_lt {X : Subgroup (Perm Ω)}
    (hprim : MulAction.IsPreprimitive X Ω) (h5 : 5 ≤ Nat.card Δ) (hlt : Nat.card ↥Δᶜ < Nat.card Δ)
    (hX : ∀ σ ∈ alternatingGroup Δ, ∃ x ∈ X, ∀ δ : Δ, x δ = σ δ) : alternatingGroup Ω ≤ X := by
  obtain ⟨g, hg, h3⟩ := exists_isThreeCycle_mem_of_card_compl_lt h5 hlt hX
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hg

theorem alternatingGroup_le_range_toPermHom_of_card_compl_lt {G : Type*} [Group G]
    [MulAction G Ω] [hprim : MulAction.IsPreprimitive G Ω] (h5 : 5 ≤ Nat.card Δ)
    (hlt : Nat.card ↥Δᶜ < Nat.card Δ)
    (hG : ∀ σ ∈ alternatingGroup Δ, ∃ g : G, ∀ δ : Δ, g • (δ : Ω) = σ δ) :
    (∃ g : G, (MulAction.toPerm g : Perm Ω).IsThreeCycle) ∧
      alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
  have hX : ∀ σ ∈ alternatingGroup Δ, ∃ x ∈ (MulAction.toPermHom G Ω).range,
      ∀ δ : Δ, x δ = σ δ := fun σ hσ => by
    obtain ⟨g, hg⟩ := hG σ hσ
    exact ⟨MulAction.toPerm g, ⟨g, rfl⟩, hg⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨_, ⟨g, rfl⟩, h3⟩ := exists_isThreeCycle_mem_of_card_compl_lt h5 hlt hX
    exact ⟨g, h3⟩
  · let φ : G → (MulAction.toPermHom G Ω).range := fun g => ⟨MulAction.toPerm g, g, rfl⟩
    let f : Ω →ₑ[φ] Ω := ⟨id, fun _ _ => rfl⟩
    have : MulAction.IsPreprimitive (MulAction.toPermHom G Ω).range Ω :=
      MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id
    exact alternatingGroup_le_of_isPreprimitive_of_card_compl_lt this h5 hlt hX

end Subset

section TransitiveExtension

open scoped Pointwise

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem alternatingGroup_le_of_isPretransitive {K : Subgroup (Perm C)}
    [MulAction.IsPretransitive K C] (h4 : 4 ≤ Nat.card C) (c : C)
    (hK : ∀ σ ∈ alternatingGroup {x // x ≠ c}, ∃ k ∈ K, ∀ x : {x // x ≠ c}, k x = σ x) :
    alternatingGroup C ≤ K := by
  have hlift : ∀ σ ∈ alternatingGroup {x // x ≠ c}, ofSubtype σ ∈ K := by
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := hK σ hσ
    convert hk using 1
    ext x
    by_cases hx : x = c
    · subst hx
      rw [ofSubtype_apply_of_not_mem (p := fun y => y ≠ x) _ (not_not.2 rfl)]
      by_contra hkc
      have h1 := hkσ (σ⁻¹ ⟨k x, Ne.symm hkc⟩)
      rw [show σ (σ⁻¹ ⟨k x, Ne.symm hkc⟩) = ⟨k x, Ne.symm hkc⟩ from
        (Equiv.eq_symm_apply σ).mp rfl] at h1
      exact (σ⁻¹ ⟨k x, Ne.symm hkc⟩).2 (k.injective h1)
    · rw [ofSubtype_apply_of_mem (p := fun y => y ≠ c) _ hx]
      exact (hkσ ⟨x, hx⟩).symm
  have hcard : 3 ≤ Nat.card {x // x ≠ c} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card]
    omega
  have hprim : MulAction.IsPreprimitive K C := by
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base c fun {B} hcB hB => ?_
    by_cases hsub : B.Subsingleton
    · exact Or.inl hsub
    right
    obtain ⟨y, hyB, hyc⟩ : ∃ y ∈ B, y ≠ c := by
      by_contra! h
      exact hsub fun a ha b hb => (h a ha).trans (h b hb).symm
    ext z
    simp only [Set.mem_univ, iff_true]
    by_cases hzc : z = c
    · rw [hzc]
      exact hcB
    have := alternatingGroup.isPretransitive_of_three_le_card {x // x ≠ c} hcard
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup {x // x ≠ c})
      (⟨y, hyc⟩ : {x // x ≠ c}) ⟨z, hzc⟩
    let k : K := ⟨ofSubtype (σ : Perm {x // x ≠ c}), hlift σ σ.2⟩
    have hkc : k • c = c := ofSubtype_apply_of_not_mem (p := fun y => y ≠ c) _ (not_not.2 rfl)
    have hkB : k • B = B := hB.smul_eq_of_mem hcB (by rw [hkc]; exact hcB)
    have hky : k • y = z := by
      change ofSubtype (σ : Perm {x // x ≠ c}) y = z
      rw [ofSubtype_apply_of_mem (p := fun y => y ≠ c) _ hyc]
      exact congrArg Subtype.val hσ
    rw [← hky, ← hkB]
    exact Set.smul_mem_smul_set hyB
  obtain ⟨σ, hσ, h3⟩ := exists_isThreeCycle_ofSubtype (p := fun x => x ≠ c) hcard
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3
    (hlift σ hσ.mem_alternatingGroup)

end TransitiveExtension

end CFSG.Holt
