module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.KC.PCent

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_mul_card_stab_le {α : Type*} [MulAction G α] {H : Subgroup G} [Finite H] {x : α}
    (S : Finset α) (hS : ∀ s ∈ S, ∃ g ∈ H, g • x = s) :
    S.card * Nat.card (H ⊓ MulAction.stabilizer G x : Subgroup G) ≤ Nat.card H := by
  classical
  choose! f hfH hfx using hS
  let F : S × (H ⊓ MulAction.stabilizer G x : Subgroup G) → H := fun p =>
    ⟨f p.1 * p.2, H.mul_mem (hfH _ p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨s, hs⟩, ⟨c, hc⟩⟩ ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ h
    have h' : f s * c = f t * d := congrArg Subtype.val h
    have hcx : c • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hc).2
    have hdx : d • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hd).2
    have hst : s = t := by
      have e := congrArg (· • x) h'
      simp only [mul_smul, hcx, hdx] at e
      rw [← hfx s hs, ← hfx t ht]
      exact e
    subst hst
    have hcd : c = d := mul_left_cancel h'
    subst hcd
    rfl
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle

theorem card_mul_card_centralizer_le {H : Subgroup G} [Finite H] {v : G} (S : Finset G)
    (hS : ∀ s ∈ S, ∃ g ∈ H, g * v * g⁻¹ = s) :
    S.card * Nat.card (H ⊓ Subgroup.centralizer {v} : Subgroup G) ≤ Nat.card H := by
  classical
  choose! f hfH hfx using hS
  have key : ∀ a c : G, c ∈ Subgroup.centralizer {v} → a * c * v * (a * c)⁻¹ = a * v * a⁻¹ := by
    intro a c hc
    have hcv : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v (Set.mem_singleton v)
    have e : c * v * c⁻¹ = v := by rw [← hcv, mul_inv_cancel_right]
    calc a * c * v * (a * c)⁻¹ = a * (c * v * c⁻¹) * a⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = a * v * a⁻¹ := by rw [e]
  let F : S × (H ⊓ Subgroup.centralizer {v} : Subgroup G) → H := fun p =>
    ⟨f p.1 * p.2, H.mul_mem (hfH _ p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨s, hs⟩, ⟨c, hc⟩⟩ ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ h
    have h' : f s * c = f t * d := congrArg Subtype.val h
    have hst : s = t := by
      have e := congrArg (fun y => y * v * y⁻¹) h'
      rw [key _ _ (Subgroup.mem_inf.1 hc).2, key _ _ (Subgroup.mem_inf.1 hd).2, hfx s hs,
        hfx t ht] at e
      exact e
    subst hst
    have hcd : c = d := mul_left_cancel h'
    subst hcd
    rfl
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle

@[expose] def ChainLB {α : Type*} [MulAction G α] : Subgroup G → List (α × Finset α) → Prop
  | _, [] => True
  | H, (x, S) :: L => (∀ s ∈ S, ∃ g ∈ H, g • x = s) ∧ ChainLB (H ⊓ MulAction.stabilizer G x) L

theorem prod_card_le_of_chainLB [Finite G] {α : Type*} [MulAction G α] :
    ∀ (H : Subgroup G) (L : List (α × Finset α)), ChainLB H L →
      (L.map fun p => p.2.card).prod ≤ Nat.card H
  | H, [], _ => by
    rw [List.map_nil, List.prod_nil]
    exact Nat.card_pos
  | H, (x, S) :: L, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := prod_card_le_of_chainLB _ L h2
    rw [List.map_cons, List.prod_cons]
    exact (Nat.mul_le_mul_left _ ih).trans (card_mul_card_stab_le S h1)

theorem eq_commutator_of_card_le [Finite G] {M D : Subgroup G} (hD : D ≤ ⁅M, M⁆)
    (hc : Nat.card M ≤ 2 * Nat.card D) : D = ⁅M, M⁆ := by
  have hMM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hDM : D ≤ M := hD.trans hMM
  let N : Subgroup M := D.subgroupOf M
  have hN : Nat.card N = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv
  have hmul : Nat.card N * N.index = Nat.card M := Subgroup.card_mul_index N
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hi0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hi2 : N.index ≤ 2 := by
    rw [hN] at hmul
    by_contra hlt
    have h3 : 3 ≤ N.index := by omega
    have : Nat.card D * 3 ≤ Nat.card D * N.index := Nat.mul_le_mul_left _ h3
    omega
  have hmem : ∀ a b : M, ⁅a, b⁆ ∈ N := by
    intro a b
    rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top _
    · rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
  refine le_antisymm hD (Subgroup.commutator_le.2 fun a ha b hb => ?_)
  have h := hmem ⟨a, ha⟩ ⟨b, hb⟩
  rw [Subgroup.mem_subgroupOf] at h
  exact h

theorem eq_bot_of_odd_orbit [Finite G] {α : Type*} [MulAction G α] {D Q : Subgroup G} {k : ℕ}
    (hQD : Q ≤ D) (hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hQ : Nat.card Q = 2 ^ k)
    (Ω : Finset α) (x₀ : α) (htr : ∀ y ∈ Ω, ∃ d ∈ D, d • x₀ = y)
    (hinv : ∀ d ∈ D, ∀ y ∈ Ω, d • y ∈ Ω) (hodd : Odd Ω.card)
    (hfaith : ∀ d ∈ D, (∀ y ∈ Ω, d • y = y) → d = 1) : Q = ⊥ := by
  classical
  have hp : IsPGroup 2 Q := IsPGroup.of_card hQ
  let P : SubMulAction Q α :=
    { carrier := (Ω : Set α)
      smul_mem' := fun q y hy => by
        rw [Subgroup.smul_def]
        exact hinv q (hQD q.2) y hy }
  have hfin : Finite P := by
    change Finite (Ω : Set α)
    exact Ω.finite_toSet.to_subtype
  have hcard : Nat.card P = Ω.card := by
    change Nat.card ((Ω : Set α)) = Ω.card
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hmod := hp.card_modEq_card_fixedPoints P
  obtain ⟨⟨f, hfΩ⟩, hf⟩ : (MulAction.fixedPoints Q P).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hcard, hne, Nat.card_of_isEmpty] at hmod
    have h1 := Nat.odd_iff.1 hodd
    unfold Nat.ModEq at hmod
    omega
  have hfix : ∀ q ∈ Q, (q : G) • f = f := fun q hq => by
    have e := hf ⟨q, hq⟩
    have e' := congrArg Subtype.val e
    rw [SubMulAction.val_smul, Subgroup.smul_def] at e'
    exact e'
  refine (Subgroup.eq_bot_iff_forall Q).2 fun q hq => hfaith q (hQD hq) fun y hy => ?_
  obtain ⟨d, hd, rfl⟩ := htr y hy
  obtain ⟨d', hd', hfd⟩ := htr f hfΩ
  have he : d * d'⁻¹ ∈ D := D.mul_mem hd (D.inv_mem hd')
  have hy' : d • x₀ = (d * d'⁻¹) • f := by rw [← hfd, ← mul_smul, inv_mul_cancel_right]
  have hq' : (d * d'⁻¹)⁻¹ * q * (d * d'⁻¹) ∈ Q := by
    have := hQn _ (D.inv_mem he) q hq
    rwa [inv_inv] at this
  rw [hy', ← mul_smul]
  calc (q * (d * d'⁻¹)) • f = (d * d'⁻¹) • (((d * d'⁻¹)⁻¹ * q * (d * d'⁻¹)) • f) := by
        rw [← mul_smul]
        group
    _ = (d * d'⁻¹) • f := by rw [hfix _ hq']

end CFSG.KC.PCent

end
