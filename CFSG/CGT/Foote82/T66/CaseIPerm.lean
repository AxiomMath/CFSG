module

public import CFSG.CGT.Foote82.T66.Perm310
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent

public section

namespace CFSG.CGT.Foote82

namespace CaseIPerm

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem perm_apply_inv (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x := σ.apply_symm_apply x

theorem perm_inv_apply (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x := σ.symm_apply_apply x

theorem mem_altOn_iff {m : ℕ} {F : Set (Fin m)} {σ : Perm (Fin m)} :
    σ ∈ altOn F ↔ σ ∈ alternatingGroup (Fin m) ∧ ∀ x, x ∉ F → σ x = x := by
  rw [altOn, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  exact and_congr_right fun _ => ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

theorem altOn_eq_ghInv {m : ℕ} (F : Set (Fin m)) [DecidablePred (· ∈ F)] :
    altOn F = CFSG.GH74.GLS.IVK.GHInv.altOn (Finset.univ.filter (· ∈ F)) := by
  ext g
  rw [CFSG.GH74.GLS.IVK.GHInv.mem_altOn, mem_altOn_iff, Equiv.Perm.mem_alternatingGroup,
    and_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem fixes_of_commute_altOn {m : ℕ} {F : Set (Fin m)} (hF : 5 ≤ Nat.card F)
    {g : Perm (Fin m)} (hg : ∀ k ∈ altOn F, g * k = k * g) {x : Fin m} (hx : x ∈ F) : g x = x := by
  classical
  have hcard : (Finset.univ.filter (· ∈ F)).card = Nat.card F := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine CFSG.GH74.GLS.IVK.GHInv.fixes_of_commute_altOn (F := Finset.univ.filter (· ∈ F))
    (by rw [hcard]; exact hF) (fun k hk => hg k ?_) (by simpa using hx)
  rw [altOn_eq_ghInv]
  exact hk

theorem eq_one_or_eq_swap_of_commute_altOn {m : ℕ} (hm : 7 ≤ m) {a b : Fin m} (hab : a ≠ b)
    {g : Perm (Fin m)} (hg : ∀ k ∈ altOn {i | i ≠ a ∧ i ≠ b}, g * k = k * g) :
    g = 1 ∨ g = swap a b := by
  classical
  have hcard : 5 ≤ Nat.card {i : Fin m | i ≠ a ∧ i ≠ b} := by
    have h1 : Nat.card {i : Fin m | i ≠ a ∧ i ≠ b} =
        (Finset.univ.filter (fun i : Fin m => i ≠ a ∧ i ≠ b)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    have h2 : (Finset.univ.filter (fun i : Fin m => i ≠ a ∧ i ≠ b)) =
        (Finset.univ.erase a).erase b := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h1, h2, Finset.card_erase_of_mem (by simp [Ne.symm hab]),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  have hfix : ∀ x, x ≠ a → x ≠ b → g x = x := fun x hxa hxb =>
    fixes_of_commute_altOn hcard hg ⟨hxa, hxb⟩
  have hga : g a = a ∨ g a = b := by
    by_contra h
    push Not at h
    have := hfix (g a) h.1 h.2
    exact h.1 (g.injective this)
  rcases hga with hga | hga
  · left
    have hgb : g b = b := by
      by_contra h
      have h' : g b ≠ a := fun h' => hab.symm (g.injective (h'.trans hga.symm))
      exact h (g.injective (hfix (g b) h' h))
    ext x
    by_cases hxa : x = a
    · rw [hxa, hga]; rfl
    by_cases hxb : x = b
    · rw [hxb, hgb]; rfl
    · rw [hfix x hxa hxb]; rfl
  · right
    have hgb : g b = a := by
      by_contra h
      have h' : g b ≠ b := fun h' => hab (g.injective (hga.trans h'.symm))
      exact h' (g.injective (hfix (g b) h h'))
    ext x
    by_cases hxa : x = a
    · rw [hxa, hga, swap_apply_left]
    by_cases hxb : x = b
    · rw [hxb, hgb, swap_apply_right]
    · rw [hfix x hxa hxb, swap_apply_of_ne_of_ne hxa hxb]

theorem exists_two_not_mem {m : ℕ} (X : Finset (Fin m)) (hX : X.card + 2 ≤ m) :
    ∃ p q : Fin m, p ∉ X ∧ q ∉ X ∧ p ≠ q := by
  have h1 : (Finset.univ \ X).card = m - X.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_univ, Fintype.card_fin]
  have h2 : 1 < (Finset.univ \ X).card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 h2
  exact ⟨p, q, (Finset.mem_sdiff.1 hp).2, (Finset.mem_sdiff.1 hq).2, hpq⟩

theorem alternatingGroup_le_sup_altOn {m : ℕ} (hm : 8 ≤ m) {a b c d : Fin m} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    alternatingGroup (Fin m) ≤ altOn {i | i ≠ a ∧ i ≠ b} ⊔ altOn {i | i ≠ c ∧ i ≠ d} := by
  classical
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  have hσA : σ ∈ alternatingGroup (Fin m) := hσ3.mem_alternatingGroup
  by_cases hσab : σ a = a ∧ σ b = b
  · refine Subgroup.mem_sup_left (mem_altOn_iff.2 ⟨hσA, fun x hx => ?_⟩)
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
    rcases hx with rfl | rfl
    · exact hσab.1
    · exact hσab.2
  set X : Finset (Fin m) := {a, b, c, d} ∪ σ.support with hX
  have hXcard : X.card + 2 ≤ m := by
    have h1 : X.card ≤ ({a, b, c, d} : Finset (Fin m)).card + σ.support.card :=
      Finset.card_union_le _ _
    have h2 : ({a, b, c, d} : Finset (Fin m)).card ≤ 4 := Finset.card_le_four
    have h3 : σ.support.card = 3 := hσ3.card_support
    have h4 : X.card ≤ 6 := by
      have hmem : a ∈ σ.support ∨ b ∈ σ.support := by
        by_contra h
        push Not at h
        exact hσab ⟨Equiv.Perm.notMem_support.1 h.1, Equiv.Perm.notMem_support.1 h.2⟩
      have hsub : X ⊆ (({a, b, c, d} : Finset (Fin m)).erase
          (if a ∈ σ.support then a else b)) ∪ σ.support := by
        intro x hx
        rw [hX, Finset.mem_union] at hx
        rw [Finset.mem_union]
        by_cases hxs : x ∈ σ.support
        · exact Or.inr hxs
        · left
          rcases hx with hx | hx
          · refine Finset.mem_erase.2 ⟨?_, hx⟩
            split_ifs with h
            · exact fun hxa => hxs (hxa ▸ h)
            · rcases hmem with h' | h'
              · exact absurd h' h
              · exact fun hxb => hxs (hxb ▸ h')
          · exact absurd hx hxs
      have hcard := Finset.card_le_card hsub
      have h5 := Finset.card_union_le ((({a, b, c, d} : Finset (Fin m)).erase
          (if a ∈ σ.support then a else b))) σ.support
      have h6 : (({a, b, c, d} : Finset (Fin m)).erase (if a ∈ σ.support then a else b)).card ≤ 3 := by
        have hm : (if a ∈ σ.support then a else b) ∈ ({a, b, c, d} : Finset (Fin m)) := by
          split_ifs <;> simp
        rw [Finset.card_erase_of_mem hm]
        omega
      omega
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_two_not_mem X hXcard
  simp only [hX, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or,
    Equiv.Perm.mem_support, not_not] at hp hq
  obtain ⟨⟨hpa, hpb, hpc, hpd⟩, hσp⟩ := hp
  obtain ⟨⟨hqa, hqb, hqc, hqd⟩, hσq⟩ := hq
  set τ : Perm (Fin m) := swap a p * swap b q with hτ
  have hτB : τ ∈ altOn {i | i ≠ c ∧ i ≠ d} := by
    refine mem_altOn_iff.2 ⟨?_, fun x hx => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, hτ, map_mul, sign_swap (Ne.symm hpa),
        sign_swap (Ne.symm hqb)]
      rfl
    · simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
      rcases hx with rfl | rfl
      · rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne hbc.symm (Ne.symm hqc),
          swap_apply_of_ne_of_ne hac.symm (Ne.symm hpc)]
      · rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne hbd.symm (Ne.symm hqd),
          swap_apply_of_ne_of_ne had.symm (Ne.symm hpd)]
  have hτinv : τ⁻¹ = swap b q * swap a p := by
    rw [hτ, mul_inv_rev, swap_inv, swap_inv]
  have hτA : τ ∈ alternatingGroup (Fin m) := (mem_altOn_iff.1 hτB).1
  have hτia : τ⁻¹ a = p := by
    rw [hτinv, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpb hpq]
  have hτib : τ⁻¹ b = q := by
    rw [hτinv, Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm (Ne.symm hpb), swap_apply_left]
  have hτp : τ p = a := by
    rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne hpb hpq, swap_apply_right]
  have hτq : τ q = b := by
    rw [hτ, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hab.symm (Ne.symm hpb)]
  have hconjA : τ * σ * τ⁻¹ ∈ altOn {i | i ≠ a ∧ i ≠ b} := by
    refine mem_altOn_iff.2 ⟨?_, fun x hx => ?_⟩
    · exact (alternatingGroup (Fin m)).mul_mem ((alternatingGroup (Fin m)).mul_mem hτA hσA)
        ((alternatingGroup (Fin m)).inv_mem hτA)
    · simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
      rcases hx with rfl | rfl
      · rw [Perm.mul_apply, Perm.mul_apply, hτia, hσp, hτp]
      · rw [Perm.mul_apply, Perm.mul_apply, hτib, hσq, hτq]
  have hσeq : σ = τ⁻¹ * (τ * σ * τ⁻¹) * τ := by group
  rw [hσeq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hτB))
    (Subgroup.mem_sup_left hconjA)) (Subgroup.mem_sup_right hτB)

theorem cycleType_eq_replicate_of_mul_self {σ : Perm α} (hσ : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  refine Multiset.eq_replicate.2 ⟨rfl, fun c hc => ?_⟩
  have h1 : c ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hc
  have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hσ])
  have h3 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
  have h4 : c ∣ 2 := h1.trans h2
  have h5 : c ≤ 2 := Nat.le_of_dvd (by norm_num) h4
  omega

theorem card_support_of_mul_self {σ : Perm α} (hσ : σ * σ = 1) :
    σ.support.card = 2 * Multiset.card σ.cycleType ∧
      sign σ = (-1) ^ Multiset.card σ.cycleType := by
  have h := cycleType_eq_replicate_of_mul_self hσ
  refine ⟨?_, ?_⟩
  · rw [← Equiv.Perm.sum_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul, mul_comm]
  · rw [Equiv.Perm.sign_of_cycleType]
    set c := Multiset.card σ.cycleType with hc
    rw [h, Multiset.sum_replicate, smul_eq_mul,
      show c * 2 + c = 2 * c + c by ring, pow_add, pow_mul]
    simp

private theorem swap_mul_of_mul_self {σ : Perm α} (hσ : σ * σ = 1) {a : α} :
    (swap a (σ a) * σ) a = a ∧ (swap a (σ a) * σ) (σ a) = σ a ∧
      (∀ x, x ≠ a → x ≠ σ a → (swap a (σ a) * σ) x = σ x) ∧
      (swap a (σ a) * σ) * (swap a (σ a) * σ) = 1 := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Perm α => f x) hσ
    simpa using this
  have hoff : ∀ x, x ≠ a → x ≠ σ a → σ x ≠ a ∧ σ x ≠ σ a := fun x hxa hxb =>
    ⟨fun h => hxb (by rw [← h, hσσ]), fun h => hxa (σ.injective h)⟩
  refine ⟨?_, ?_, fun x hxa hxb => ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_right]
  · rw [Perm.mul_apply, hσσ, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hoff x hxa hxb).1 (hoff x hxa hxb).2]
  · ext x
    simp only [Perm.mul_apply, Perm.one_apply]
    by_cases hxa : x = a
    · subst hxa; rw [swap_apply_right, swap_apply_right]
    by_cases hxb : x = σ a
    · subst hxb; rw [hσσ, swap_apply_left, hσσ, swap_apply_left]
    · rw [swap_apply_of_ne_of_ne (hoff x hxa hxb).1 (hoff x hxa hxb).2,
        swap_apply_of_ne_of_ne (hoff (σ x) (hoff x hxa hxb).1 (hoff x hxa hxb).2).1
          (hoff (σ x) (hoff x hxa hxb).1 (hoff x hxa hxb).2).2, hσσ]

private theorem four_cycle_sq {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a d * swap a b * swap a c) * (swap a d * swap a b * swap a c) = swap a b * swap c d := by
  set ρ := swap a d * swap a b * swap a c with hρ
  have hρa : ρ a = c := by
    rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm,
      swap_apply_of_ne_of_ne hac.symm hcd]
  have hρb : ρ b = d := by
    rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm hbc, swap_apply_right,
      swap_apply_left]
  have hρc : ρ c = b := by
    rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_right, swap_apply_left,
      swap_apply_of_ne_of_ne hab.symm hbd]
  have hρd : ρ d = a := by
    rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne had.symm hcd.symm,
      swap_apply_of_ne_of_ne had.symm hbd.symm, swap_apply_right]
  ext x
  rw [show (ρ * ρ) x = ρ (ρ x) from rfl,
    show (swap a b * swap c d) x = swap a b (swap c d x) from rfl]
  by_cases hxa : x = a
  · rw [hxa, hρa, hρc, swap_apply_of_ne_of_ne hac had, swap_apply_left]
  by_cases hxb : x = b
  · rw [hxb, hρb, hρd, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
  by_cases hxc : x = c
  · rw [hxc, hρc, hρb, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
  by_cases hxd : x = d
  · rw [hxd, hρd, hρa, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hρx : ρ x = x := by
    rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxc,
      swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxa hxd]
  rw [hρx, hρx, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

theorem exists_mul_self_eq_aux : ∀ k : ℕ, ∀ σ : Perm α, σ.support.card = k → σ * σ = 1 →
    sign σ = 1 → ∃ τ : Perm α, τ * τ = σ ∧ ∀ x, σ x = x → τ x = x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro σ hk hσ hsign
  by_cases h1 : σ = 1
  · exact ⟨1, by rw [h1, one_mul], fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact h1 (Perm.ext h)
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Perm α => f x) hσ
    simpa using this
  have hab : a ≠ σ a := fun h => ha h.symm
  obtain ⟨hσ₁a, hσ₁b, hσ₁x, hσ₁⟩ := swap_mul_of_mul_self (a := a) hσ
  have hsign₁ : sign (swap a (σ a) * σ) = -1 := by
    rw [map_mul, sign_swap hab, hsign]; rfl
  have h1' : swap a (σ a) * σ ≠ 1 := fun h => by
    rw [h, Equiv.Perm.sign_one] at hsign₁
    exact absurd hsign₁ (by decide)
  obtain ⟨c, hc⟩ : ∃ c, (swap a (σ a) * σ) c ≠ c := by
    by_contra h
    push Not at h
    exact h1' (Perm.ext h)
  have hca : c ≠ a := fun h => hc (by rw [h]; exact hσ₁a)
  have hcb : c ≠ σ a := fun h => hc (by rw [h]; exact hσ₁b)
  have hσc : σ c = (swap a (σ a) * σ) c := (hσ₁x c hca hcb).symm
  have hcd : c ≠ σ c := fun h => hc (by rw [← hσc]; exact h.symm)
  have hda : σ c ≠ a := fun h => hcb (by rw [← h, hσσ])
  have hdb : σ c ≠ σ a := fun h => hca (σ.injective h)
  obtain ⟨hσ₂c, hσ₂d, hσ₂x, hσ₂⟩ := swap_mul_of_mul_self (a := c) hσ₁
  rw [← hσc] at hσ₂c hσ₂d hσ₂x hσ₂
  set σ₂ := swap c (σ c) * (swap a (σ a) * σ) with hσ₂def
  have hσ₂a : σ₂ a = a := by
    rw [hσ₂x a hca.symm hda.symm, hσ₁a]
  have hσ₂b : σ₂ (σ a) = σ a := by
    rw [hσ₂x (σ a) hcb.symm hdb.symm, hσ₁b]
  have hσ₂off : ∀ x, x ≠ a → x ≠ σ a → x ≠ c → x ≠ σ c → σ₂ x = σ x :=
    fun x hxa hxb hxc hxd => by rw [hσ₂x x hxc hxd, hσ₁x x hxa hxb]
  have hsign₂ : sign σ₂ = 1 := by
    rw [hσ₂def, map_mul, sign_swap hcd, hsign₁]; rfl
  have hsupp : σ₂.support.card < k := by
    rw [← hk]
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
    · rw [Equiv.Perm.mem_support] at hx ⊢
      by_cases hxa : x = a
      · exact absurd (hxa ▸ hσ₂a) hx
      by_cases hxb : x = σ a
      · exact absurd (hxb ▸ hσ₂b) hx
      by_cases hxc : x = c
      · exact absurd (hxc ▸ hσ₂c) hx
      by_cases hxd : x = σ c
      · exact absurd (hxd ▸ hσ₂d) hx
      rwa [← hσ₂off x hxa hxb hxc hxd]
    · have := h (Equiv.Perm.mem_support.2 ha)
      exact (Equiv.Perm.mem_support.1 this) hσ₂a
  obtain ⟨τ₂, hτ₂, hτ₂fix⟩ := ih _ hsupp σ₂ rfl hσ₂ hsign₂
  set ρ := swap a (σ c) * swap a (σ a) * swap a c with hρ
  have hρfix : ∀ x, x ≠ a → x ≠ σ a → x ≠ c → x ≠ σ c → ρ x = x :=
    fun x hxa hxb hxc hxd => by
      rw [hρ, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxc,
        swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxa hxd]
  have hdisj : Equiv.Perm.Disjoint ρ τ₂ := by
    intro x
    by_cases hxa : x = a
    · right; rw [hxa]; exact hτ₂fix a hσ₂a
    by_cases hxb : x = σ a
    · right; rw [hxb]; exact hτ₂fix (σ a) hσ₂b
    by_cases hxc : x = c
    · right; rw [hxc]; exact hτ₂fix c hσ₂c
    by_cases hxd : x = σ c
    · right; rw [hxd]; exact hτ₂fix (σ c) hσ₂d
    · left; exact hρfix x hxa hxb hxc hxd
  refine ⟨ρ * τ₂, ?_, fun x hx => ?_⟩
  · have hcomm : τ₂ * ρ = ρ * τ₂ := (hdisj.commute).eq.symm
    calc ρ * τ₂ * (ρ * τ₂) = ρ * ρ * (τ₂ * τ₂) := by
          rw [mul_assoc, ← mul_assoc τ₂, hcomm]; group
      _ = swap a (σ a) * swap c (σ c) * σ₂ := by
          rw [hτ₂, hρ, four_cycle_sq hab hca.symm hda.symm hcb.symm hdb.symm hcd]
      _ = σ := by
          rw [hσ₂def, ← mul_assoc, mul_assoc (swap a (σ a)), swap_mul_self, mul_one,
            ← mul_assoc, swap_mul_self, one_mul]
  · have hxa : x ≠ a := fun h => ha (h ▸ hx)
    have hxb : x ≠ σ a := fun h => by
      have h2 : σ (σ a) = σ a := h ▸ hx
      rw [hσσ] at h2
      exact hab h2
    have hxc : x ≠ c := fun h => hcd (h ▸ hx).symm
    have hxd : x ≠ σ c := fun h => by
      have h2 : σ (σ c) = σ c := h ▸ hx
      rw [hσσ] at h2
      exact hcd h2
    rw [Perm.mul_apply, hτ₂fix x (by rw [hσ₂off x hxa hxb hxc hxd, hx]),
      hρfix x hxa hxb hxc hxd]

theorem exists_mul_self_eq {σ : Perm α} (hσ : σ * σ = 1) (hsign : sign σ = 1) :
    ∃ τ : Perm α, τ * τ = σ := by
  obtain ⟨τ, hτ, -⟩ := exists_mul_self_eq_aux _ σ rfl hσ hsign
  exact ⟨τ, hτ⟩

theorem exists_regular_of_unique_involution {Q : Subgroup (Perm α)} (hQ : IsPGroup 2 Q)
    {j : Perm α} (hj : orderOf j = 2) (huniq : ∀ x ∈ Q, orderOf x = 2 → x = j) :
    ∃ p : α, ∀ q ∈ Q, q p = p → q = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  have hfix : ∀ p, j p = p := by
    intro p
    obtain ⟨q, hqQ, hqp, hq1⟩ := h p
    let St : Subgroup (Perm α) := Q ⊓ MulAction.stabilizer (Perm α) p
    have hSt2 : IsPGroup 2 St := hQ.to_le inf_le_left
    have hqSt : q ∈ St := ⟨hqQ, hqp⟩
    have hnt : Nontrivial St := ⟨⟨⟨q, hqSt⟩, 1, fun h => hq1 (congrArg Subtype.val h)⟩⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hSt2
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : Nat.card St = 1 := by rw [hk, pow_zero]
      rw [Nat.card_eq_one_iff_unique] at this
      exact (not_subsingleton St) this.1
    have h2 : 2 ∣ Nat.card St := by rw [hk]; exact dvd_pow_self 2 hk0
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := St) 2 h2
    have ht' : orderOf (t : Perm α) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have := huniq t t.2.1 ht'
    rw [← this]
    exact t.2.2
  have : j = 1 := Perm.ext hfix
  rw [this, orderOf_one] at hj
  exact absurd hj (by norm_num)

theorem card_le_of_unique_involution {Q : Subgroup (Perm α)} (hQ : IsPGroup 2 Q)
    {j : Perm α} (hj : orderOf j = 2) (huniq : ∀ x ∈ Q, orderOf x = 2 → x = j) :
    Nat.card Q ≤ Fintype.card α := by
  obtain ⟨p, hp⟩ := exists_regular_of_unique_involution hQ hj huniq
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective (fun q : Q => (q : Perm α) p) fun q₁ q₂ h => ?_
  have h' : ((q₂ : Perm α)⁻¹ * q₁) p = p := by
    simp only [Perm.mul_apply]
    rw [show (q₁ : Perm α) p = (q₂ : Perm α) p from h]
    exact (q₂ : Perm α).symm_apply_apply p
  have := hp _ (Q.mul_mem (Q.inv_mem q₂.2) q₁.2) h'
  exact Subtype.ext (inv_mul_eq_one.1 this).symm

theorem sign_eq_neg_one_of_orderOf_eq_four {s : Perm α} (hs : orderOf s = 4)
    (hsupp : s.support.card ≤ 4) : sign s = -1 := by
  have h4 : 4 ∈ s.cycleType := by
    by_contra h4
    have hdvd : s.cycleType.lcm ∣ 2 := by
      refine Multiset.lcm_dvd.2 fun c hc => ?_
      have h1 : c ∣ 4 := hs ▸ Equiv.Perm.dvd_of_mem_cycleType hc
      have h2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
      have h3 : c ≤ 4 := Nat.le_of_dvd (by norm_num) h1
      have h5 : c ≠ 4 := fun h => h4 (h ▸ hc)
      interval_cases c
      · exact dvd_refl 2
      · exact absurd h1 (by norm_num)
      · exact absurd rfl h5
    rw [Equiv.Perm.lcm_cycleType, hs] at hdvd
    exact absurd hdvd (by norm_num)
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h4
  have hsum : s.cycleType.sum = s.support.card := Equiv.Perm.sum_cycleType s
  rw [ht, Multiset.sum_cons] at hsum
  have ht0 : t = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hne
    have hc' : c ∈ s.cycleType := by rw [ht]; exact Multiset.mem_cons_of_mem hc
    have h2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc'
    have : c ≤ t.sum := Multiset.le_sum_of_mem hc
    omega
  rw [Equiv.Perm.sign_of_cycleType, ht, ht0]
  rfl

theorem fixes_support_of_commute_isThreeCycle {γ s : Perm α} (hγ : γ.IsThreeCycle)
    (hc : s * γ = γ * s) {k : ℕ} (hs : s ^ (2 ^ k) = 1) {x : α} (hx : x ∈ γ.support) :
    s x = x := by
  have hγx : γ x ≠ x := Equiv.Perm.mem_support.1 hx
  have hsupp : γ.support = {x, γ x, γ (γ x)} := (hγ.support_eq_iff_mem_support).2 hx
  have hcomm : ∀ m : ℕ, ∀ y, s ((γ ^ m) y) = (γ ^ m) (s y) := fun m y => by
    have : s * γ ^ m = γ ^ m * s := ((Commute.pow_right (show Commute s γ from hc) m)).eq
    exact congrArg (fun f : Perm α => f y) this
  have hsx : s x ∈ γ.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    have : γ (s x) = s (γ x) := by
      have := hcomm 1 x
      simpa using this.symm
    rw [h] at this
    exact hγx (s.injective this.symm)
  rw [hsupp] at hsx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsx
  obtain ⟨r, hr, hrx⟩ : ∃ r : ℕ, r < 3 ∧ s x = (γ ^ r) x := by
    rcases hsx with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
    · exact ⟨2, by norm_num, by rw [h, sq, Perm.mul_apply]⟩
  have hpow : ∀ m : ℕ, (s ^ m) x = (γ ^ (r * m)) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Perm.mul_apply, ih, hcomm, hrx, ← Perm.mul_apply, ← pow_add,
        show r * (m + 1) = r * m + r by ring, add_comm]
  have h1 : (γ ^ (r * 2 ^ k)) x = x := by rw [← hpow, hs]; rfl
  have h2 : γ ^ (r * 2 ^ k) = 1 :=
    (hγ.isCycle.pow_eq_one_iff).2 ⟨x, hγx, h1⟩
  have h3 : 3 ∣ r * 2 ^ k := by
    rw [← hγ.orderOf]
    exact orderOf_dvd_of_pow_eq_one h2
  have hr0 : r = 0 := by
    by_contra hr0
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have := (Nat.Coprime.dvd_of_dvd_mul_right hcop h3)
    have : 3 ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) this
    omega
  rw [hrx, hr0, pow_zero]
  rfl

theorem exists_two_orbits_of_orderOf_eq_three {σ : Perm α} (h3 : orderOf σ = 3)
    (hn : ¬ σ.IsThreeCycle) {a : α} (ha : σ a ≠ a) :
    ∃ d : α, σ d ≠ d ∧ d ≠ a ∧ d ≠ σ a ∧ d ≠ σ (σ a) := by
  by_contra h
  push Not at h
  apply hn
  rw [← card_support_eq_three_iff]
  have hsub : σ.support ⊆ {a, σ a, σ (σ a)} := by
    intro d hd
    rw [Equiv.Perm.mem_support] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hd'
    push Not at hd'
    exact h d hd hd'.1 hd'.2.1 |> fun h' => hd'.2.2 h'
  have hσ3 : ∀ y, σ (σ (σ y)) = y := fun y => by
    have : σ ^ 3 = 1 := h3 ▸ pow_orderOf_eq_one σ
    have := congrArg (fun f : Perm α => f y) this
    simpa [pow_succ, Perm.mul_apply] using this
  have hab : a ≠ σ a := fun h => ha h.symm
  have hbc : σ a ≠ σ (σ a) := fun h => ha (σ.injective h).symm
  have hac : a ≠ σ (σ a) := fun h => by
    have h' := congrArg σ h
    rw [hσ3] at h'
    exact ha h'
  have hsup : ({a, σ a, σ (σ a)} : Finset α) ⊆ σ.support := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Equiv.Perm.mem_support]
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact fun h => ha (σ.injective h)
    · intro h
      rw [hσ3] at h
      exact hac h
  rw [Finset.Subset.antisymm hsub hsup]
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem
    (by simp [hbc]), Finset.card_singleton]

theorem two_mul_card_altOn {m : ℕ} (F : Set (Fin m)) (hF : 2 ≤ Nat.card F) :
    2 * Nat.card (altOn F) = (Nat.card F).factorial := by
  classical
  rw [altOn_eq_ghInv]
  have e := CFSG.GH74.GLS.IVK.GHInv.altOnEquiv (Finset.univ.filter (· ∈ F))
  rw [← Nat.card_congr e.toEquiv]
  have hcard : Nat.card {x // x ∈ Finset.univ.filter (· ∈ F)} = Nat.card F := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  haveI : Nontrivial {x // x ∈ Finset.univ.filter (· ∈ F)} := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    omega
  rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
    ← Nat.card_eq_fintype_card, hcard]

@[expose] def shift2 (k : ℕ) : Fin k ≃ {i : Fin (k + 2) // i ≠ 0 ∧ i ≠ 1} where
  toFun j := ⟨Fin.addNat j 2, by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> have := congrArg Fin.val h <;> simp at this⟩
  invFun i := ⟨i.1.val - 2, by
    have h0 : i.1.val ≠ 0 := fun h => i.2.1 (Fin.ext h)
    have h1 : i.1.val ≠ 1 := fun h => i.2.2 (Fin.ext h)
    have := i.1.2
    omega⟩
  left_inv j := Fin.ext (by simp)
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have h0 : i.1.val ≠ 0 := fun h => i.2.1 (Fin.ext h)
    have h1 : i.1.val ≠ 1 := fun h => i.2.2 (Fin.ext h)
    simp only [Fin.coe_addNat]
    omega

theorem shift2_val {k : ℕ} (j : Fin k) : ((shift2 k j : Fin (k + 2)) : ℕ) = j + 2 := rfl

@[expose] noncomputable def iota2 (k : ℕ) : Perm (Fin k) →* Perm (Fin (k + 2)) :=
  Equiv.Perm.extendDomainHom (shift2 k)

theorem iota2_injective (k : ℕ) : Function.Injective (iota2 k) :=
  Equiv.Perm.extendDomainHom_injective _

theorem iota2_apply_shift {k : ℕ} (σ : Perm (Fin k)) (j : Fin k) :
    iota2 k σ (shift2 k j) = shift2 k (σ j) :=
  Equiv.Perm.extendDomain_apply_image σ (shift2 k) j

theorem iota2_apply_zero {k : ℕ} (σ : Perm (Fin k)) : iota2 k σ 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype σ (shift2 k) (by simp)

theorem iota2_apply_one {k : ℕ} (σ : Perm (Fin k)) : iota2 k σ 1 = 1 :=
  Equiv.Perm.extendDomain_apply_not_subtype σ (shift2 k) (by simp)

theorem sign_iota2 {k : ℕ} (σ : Perm (Fin k)) : sign (iota2 k σ) = sign σ :=
  Equiv.Perm.sign_extendDomain σ (shift2 k)

theorem cycleType_iota2 {k : ℕ} (σ : Perm (Fin k)) : (iota2 k σ).cycleType = σ.cycleType :=
  Equiv.Perm.cycleType_extendDomain (shift2 k)

theorem exists_iota2_eq {k : ℕ} {τ : Perm (Fin (k + 2))} (h0 : τ 0 = 0) (h1 : τ 1 = 1) :
    ∃ σ : Perm (Fin k), iota2 k σ = τ := by
  have hτ : ∀ x, (τ x ≠ 0 ∧ τ x ≠ 1) ↔ (x ≠ 0 ∧ x ≠ 1) := by
    intro x
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨fun h => ha (by rw [h, h0]), fun h => hb (by rw [h, h1])⟩
    · rintro ⟨ha, hb⟩
      exact ⟨fun h => ha (τ.injective (h.trans h0.symm)), fun h => hb (τ.injective (h.trans h1.symm))⟩
  refine ⟨(Equiv.permCongr (shift2 k)).symm (τ.subtypePerm hτ), ?_⟩
  ext x
  by_cases hx : x ≠ 0 ∧ x ≠ 1
  · rw [iota2, Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.extendDomain_apply_subtype (p := fun i : Fin (k + 2) => i ≠ 0 ∧ i ≠ 1) _ _ hx]
    simp [Equiv.permCongr_symm_apply]
  · rw [iota2, Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.extendDomain_apply_not_subtype (p := fun i : Fin (k + 2) => i ≠ 0 ∧ i ≠ 1) _ _ hx]
    simp only [not_and_or, not_not] at hx
    rcases hx with rfl | rfl
    · rw [h0]
    · rw [h1]

theorem altOn_eq_map_iota2 (k : ℕ) :
    altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1} = (alternatingGroup (Fin k)).map (iota2 k) := by
  ext τ
  rw [mem_altOn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hA, hfix⟩
    have h0 : τ 0 = 0 := hfix 0 (by simp)
    have h1 : τ 1 = 1 := hfix 1 (by simp)
    obtain ⟨σ, rfl⟩ := exists_iota2_eq h0 h1
    refine ⟨σ, ?_, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, ← sign_iota2]
    exact hA
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨by rw [Equiv.Perm.mem_alternatingGroup, sign_iota2]; exact hσ, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
    rcases hx with rfl | rfl
    · exact iota2_apply_zero σ
    · exact iota2_apply_one σ

theorem commutator_altOn_eq_self {k : ℕ} (hk : 5 ≤ k) :
    ⁅altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1}, altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1}⁆ =
      altOn {i : Fin (k + 2) | i ≠ 0 ∧ i ≠ 1} := by
  rw [altOn_eq_map_iota2, ← Subgroup.map_commutator, commutator_alternatingGroup_eq_self]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hk

theorem orderOf_swap_mul_swap {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : orderOf (swap a b * swap c d) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Equiv.Perm.Disjoint (swap a b) (swap c d) := by
    intro x
    by_cases hxa : x = a
    · right; rw [hxa]; exact swap_apply_of_ne_of_ne hac had
    by_cases hxb : x = b
    · right; rw [hxb]; exact swap_apply_of_ne_of_ne hbc hbd
    · left; exact swap_apply_of_ne_of_ne hxa hxb
  refine orderOf_eq_prime ?_ ?_
  · rw [sq]
    calc swap a b * swap c d * (swap a b * swap c d)
        = swap a b * (swap c d * swap a b) * swap c d := by group
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hdisj.commute.eq.symm]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  · intro h
    have := congrArg (fun f : Perm α => f a) h
    simp only [Perm.mul_apply, Perm.one_apply, swap_apply_of_ne_of_ne hac had,
      swap_apply_left] at this
    exact hab this.symm

end CaseIPerm

end CFSG.CGT.Foote82
