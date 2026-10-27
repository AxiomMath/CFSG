module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ComponentClassification.GSThmB.Catalog82A10

open Equiv Equiv.Perm Subgroup

section Perfect

theorem le_derivedSeries_of_perfect {G : Type*} [Group G] (P : Subgroup G) (hP : ⁅P, P⁆ = P) :
    ∀ n, P ≤ derivedSeries G n
  | 0 => le_top
  | n + 1 => by
    rw [derivedSeries_succ]
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ :=
        Subgroup.commutator_mono (le_derivedSeries_of_perfect P hP n)
          (le_derivedSeries_of_perfect P hP n)

theorem eq_bot_of_perfect_of_solvable {G : Type*} [Group G] [hG : Group.IsSolvable G]
    (P : Subgroup G) (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := hG.solvable
  exact eq_bot_iff.mpr (hn ▸ le_derivedSeries_of_perfect P hP n)

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem perfect_le_alternating (L : Subgroup (Perm α)) (hL : ⁅L, L⁆ = L) :
    L ≤ alternatingGroup α := by
  have h1 : ⁅L, L⁆ ≤ ⁅(⊤ : Subgroup (Perm α)), (⊤ : Subgroup (Perm α))⁆ :=
    Subgroup.commutator_mono le_top le_top
  have h2 : ⁅(⊤ : Subgroup (Perm α)), (⊤ : Subgroup (Perm α))⁆ ≤ alternatingGroup α :=
    alternatingGroup.commutator_perm_le
  calc L = ⁅L, L⁆ := hL.symm
    _ ≤ alternatingGroup α := h1.trans h2

omit [DecidableEq α] in
theorem perfect_fix_small (L : Subgroup (Perm α)) (hL : ⁅L, L⁆ = L) (S : Finset α)
    (hS : S.card ≤ 4) (hpres : ∀ g ∈ L, ∀ x, g x ∈ S ↔ x ∈ S) :
    ∀ g ∈ L, ∀ x ∈ S, g x = x := by
  let ρ : L →* Perm {x // x ∈ S} :=
    { toFun := fun g => (g : Perm α).subtypePerm (hpres g g.2)
      map_one' := by ext; rfl
      map_mul' := fun g h => by ext; rfl }
  have : Group.IsSolvable (Perm {x // x ∈ S}) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hS)
  have hLtop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = (⊤ : Subgroup L) := by
    have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hLtop]
  have hbot := eq_bot_of_perfect_of_solvable ρ.range hperf
  intro g hg x hx
  have h1 : ρ ⟨g, hg⟩ = 1 := by
    have : ρ ⟨g, hg⟩ ∈ ρ.range := ⟨_, rfl⟩
    rw [hbot, mem_bot] at this
    exact this
  have h2 := congrArg (fun π : Perm {x // x ∈ S} => (π ⟨x, hx⟩ : α)) h1
  exact h2

theorem mem_support_iff_of_commute {g σ : Perm α} (h : g * σ = σ * g) (x : α) :
    g x ∈ σ.support ↔ x ∈ σ.support := by
  simp only [Equiv.Perm.mem_support]
  have key : σ (g x) = g (σ x) := by
    change (σ * g) x = (g * σ) x
    rw [h]
  constructor
  · intro hx hx'
    apply hx
    rw [key, hx']
  · intro hx hx'
    apply hx
    apply g.injective
    rw [← key, hx']

theorem commute_of_support_subset_compl {g σ : Perm α} (h : g.support ⊆ σ.supportᶜ) :
    g * σ = σ * g := by
  have hd : Disjoint g σ := by
    intro x
    by_cases hx : x ∈ σ.support
    · left
      by_contra hgx
      have := h (Equiv.Perm.mem_support.mpr hgx)
      rw [Finset.mem_compl] at this
      exact this hx
    · right
      exact Equiv.Perm.notMem_support.mp hx
  exact hd.commute.eq

end Perfect

section AltOn

variable {α : Type*} [DecidableEq α] [Fintype α]

@[expose] def altOn (T : Finset α) : Subgroup (Perm α) :=
  ((alternatingGroup.ofSubtype T).range).map (alternatingGroup α).subtype

theorem mem_altOn {T : Finset α} {g : Perm α} :
    g ∈ altOn T ↔ g ∈ alternatingGroup α ∧ g.support ⊆ T := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (alternatingGroup.mem_range_ofSubtype_iff T k).mp hk⟩
  · rintro ⟨hA, hS⟩
    exact ⟨⟨g, hA⟩, (alternatingGroup.mem_range_ofSubtype_iff T _).mpr hS, rfl⟩

@[expose] noncomputable def altOnEquiv (T : Finset α) : alternatingGroup T ≃* altOn T :=
  (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := T))).trans
    (Subgroup.equivMapOfInjective _ _ (alternatingGroup α).subtype_injective)

theorem isSimpleGroup_altOn (T : Finset α) (hT : 5 ≤ T.card) : IsSimpleGroup (altOn T) := by
  have : IsSimpleGroup (alternatingGroup T) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hT)
  exact (altOnEquiv T).symm.isSimpleGroup

theorem card_altOn (T : Finset α) (hT : 2 ≤ T.card) :
    Nat.card (altOn T) = (T.card).factorial / 2 := by
  have : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  rw [← Nat.card_congr (altOnEquiv T).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_coe]

end AltOn

section Involution

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem cycleType_of_orderOf_two {σ : Perm α} (h : orderOf σ = 2) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 ∧
      σ.support.card = 2 * (σ.support.card / 2) ∧ 1 ≤ σ.support.card / 2 := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (h ▸ Nat.prime_two)
  rw [h] at hn
  have hsum := sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have h2 : σ.support.card / 2 = n + 1 := by omega
  refine ⟨by rw [hn, h2], by omega, by omega⟩

theorem card_centralizer_of_orderOf_two {σ : Perm (Fin 10)} (h : orderOf σ = 2) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) =
      (10 - 2 * (σ.support.card / 2)).factorial * 2 ^ (σ.support.card / 2) *
        (σ.support.card / 2).factorial := by
  obtain ⟨hct, -, hm⟩ := cycleType_of_orderOf_two h
  have hne : σ.support.card / 2 ≠ 0 := by omega
  rw [nat_card_centralizer, hct, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul,
    Fintype.card_fin, Multiset.toFinset_replicate]
  simp only [hne, ↓reduceIte, Finset.prod_singleton, Multiset.count_replicate_self,
    mul_comm (σ.support.card / 2) 2]

end Involution

section SigmaTwo

abbrev sigmaOne : Perm (Fin 10) := swap 0 1

abbrev sigmaTwo : Perm (Fin 10) := swap 0 1 * swap 2 3

abbrev fixTwo : Finset (Fin 10) := {4, 5, 6, 7, 8, 9}

theorem orderOf_sigmaOne : orderOf sigmaOne = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem orderOf_sigmaTwo : orderOf sigmaTwo = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem card_support_sigmaOne : sigmaOne.support.card = 2 := by decide

theorem card_support_sigmaTwo : sigmaTwo.support.card = 4 := by decide

theorem support_sigmaTwo_compl : sigmaTwo.supportᶜ = fixTwo := by decide

theorem mem_support_of_commute {g c : Perm (Fin 10)} (h : g * c = c * g) {x : Fin 10}
    (hx : x ∈ c.support) : g x ∈ c.support := by
  have h1 : (g * c * g⁻¹).support = c.support.map g.toEmbedding := support_conj
  rw [h, mul_inv_cancel_right] at h1
  rw [h1]
  exact Finset.mem_map_of_mem _ hx

theorem eq_of_commute_two {g c₁ c₂ : Perm (Fin 10)} {x : Fin 10} (h₁ : g * c₁ = c₁ * g)
    (h₂ : g * c₂ = c₂ * g) (hx₁ : x ∈ c₁.support) (hx₂ : x ∈ c₂.support)
    (hint : c₁.support ∩ c₂.support = {x}) : g x = x := by
  have : g x ∈ c₁.support ∩ c₂.support :=
    Finset.mem_inter.mpr ⟨mem_support_of_commute h₁ hx₁, mem_support_of_commute h₂ hx₂⟩
  rw [hint, Finset.mem_singleton] at this
  exact this

theorem threeCycle_mem (x a b : Fin 10) (hsupp : (swap x a * swap x b).support ⊆ fixTwo)
    (hxa : x ≠ a) (hxb : x ≠ b) : swap x a * swap x b ∈ altOn fixTwo := by
  refine mem_altOn.mpr ⟨?_, hsupp⟩
  rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hxa, Perm.sign_swap hxb]
  decide

theorem fix_of_commute_altOn {g : Perm (Fin 10)}
    (hg : ∀ n ∈ altOn fixTwo, g * n = n * g) : ∀ x ∈ fixTwo, g x = x := by
  have key : ∀ x a b c d : Fin 10, (swap x a * swap x b).support ⊆ fixTwo →
      (swap x c * swap x d).support ⊆ fixTwo → x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      x ∈ (swap x a * swap x b).support → x ∈ (swap x c * swap x d).support →
      (swap x a * swap x b).support ∩ (swap x c * swap x d).support = {x} → g x = x := by
    intro x a b c d hs₁ hs₂ hxa hxb hxc hxd hx₁ hx₂ hint
    exact eq_of_commute_two (hg _ (threeCycle_mem x a b hs₁ hxa hxb))
      (hg _ (threeCycle_mem x c d hs₂ hxc hxd)) hx₁ hx₂ hint
  intro x hx
  simp only [fixTwo, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 4 5 6 7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact key 5 4 6 7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact key 6 4 5 7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact key 7 4 5 6 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact key 8 4 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact key 9 4 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

abbrev pairsTwo : Finset (Fin 10 × Fin 10) :=
  Finset.univ.filter fun w => w.1.val < 4 ∧ w.2.val < 4 ∧ w.2 ≠ w.1 ∧ w.2 ≠ sigmaTwo w.1

theorem card_pairsTwo : pairsTwo.card = 8 := by decide

theorem apply_one_three {g : Perm (Fin 10)} (h : g * sigmaTwo = sigmaTwo * g) :
    g 1 = sigmaTwo (g 0) ∧ g 3 = sigmaTwo (g 2) := by
  have key : ∀ x, g (sigmaTwo x) = sigmaTwo (g x) := fun x => by
    change (g * sigmaTwo) x = (sigmaTwo * g) x
    rw [h]
  exact ⟨key 0, key 2⟩

theorem lt_four_of_fix {g : Perm (Fin 10)} (hfix : ∀ x ∈ fixTwo, g x = x) {y : Fin 10}
    (hy : y.val < 4) : (g y).val < 4 := by
  by_contra hge
  push Not at hge
  have hmem : g y ∈ fixTwo := by
    have : (g y).val < 10 := (g y).isLt
    simp only [fixTwo, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  have := g.injective ((hfix _ hmem).trans rfl : g (g y) = g y)
  rw [← this] at hmem
  simp only [fixTwo, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hmem
  omega

theorem pair_mem {g : Perm (Fin 10)} (hfix : ∀ x ∈ fixTwo, g x = x)
    (hc : g * sigmaTwo = sigmaTwo * g) : (g 0, g 2) ∈ pairsTwo := by
  obtain ⟨h1, -⟩ := apply_one_three hc
  simp only [pairsTwo, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨lt_four_of_fix hfix (by decide), lt_four_of_fix hfix (by decide), ?_, ?_⟩
  · intro h
    exact absurd (g.injective h) (by decide)
  · intro h
    rw [← h1] at h
    exact absurd (g.injective h) (by decide)

theorem eq_of_pair_eq {g h : Perm (Fin 10)} (hg : ∀ x ∈ fixTwo, g x = x)
    (hh : ∀ x ∈ fixTwo, h x = x) (hgc : g * sigmaTwo = sigmaTwo * g)
    (hhc : h * sigmaTwo = sigmaTwo * h) (h0 : g 0 = h 0) (h2 : g 2 = h 2) : g = h := by
  obtain ⟨g1, g3⟩ := apply_one_three hgc
  obtain ⟨h1, h3⟩ := apply_one_three hhc
  ext x
  fin_cases x
  · exact congrArg Fin.val h0
  · change ((g 1 : Fin 10) : ℕ) = h 1
    rw [g1, h1, h0]
  · exact congrArg Fin.val h2
  · change ((g 3 : Fin 10) : ℕ) = h 3
    rw [g3, h3, h2]
  all_goals
    rw [hg _ (by decide), hh _ (by decide)]

theorem card_le_eight_of_le_D (R : Subgroup (Perm (Fin 10)))
    (hR : ∀ g ∈ R, (∀ x ∈ fixTwo, g x = x) ∧ g * sigmaTwo = sigmaTwo * g) :
    Nat.card R ≤ 8 ∧ (Nat.card R = 8 → ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u) := by
  let κ : R → pairsTwo := fun g =>
    ⟨((g : Perm (Fin 10)) 0, (g : Perm (Fin 10)) 2), pair_mem (hR g g.2).1 (hR g g.2).2⟩
  have hκ : Function.Injective κ := by
    intro g h hgh
    have h0 := congrArg (fun w : pairsTwo => w.val.1) hgh
    have h2 := congrArg (fun w : pairsTwo => w.val.2) hgh
    exact Subtype.ext (eq_of_pair_eq (hR g g.2).1 (hR h h.2).1 (hR g g.2).2 (hR h h.2).2 h0 h2)
  have hcard : Nat.card pairsTwo = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_pairsTwo]
  have hle : Nat.card R ≤ 8 := hcard ▸ Nat.card_le_card_of_injective κ hκ
  refine ⟨hle, fun h8 => ?_⟩
  have hbij : Function.Bijective κ :=
    (Function.Injective.bijective_of_nat_card_le hκ (by rw [hcard, h8]))
  obtain ⟨u, hu⟩ := hbij.2 ⟨(1, 2), by decide⟩
  obtain ⟨v, hv⟩ := hbij.2 ⟨(2, 0), by decide⟩
  have hu0 : (u : Perm (Fin 10)) 0 = 1 := congrArg (fun w : pairsTwo => w.val.1) hu
  have hu2 : (u : Perm (Fin 10)) 2 = 2 := congrArg (fun w : pairsTwo => w.val.2) hu
  have hv0 : (v : Perm (Fin 10)) 0 = 2 := congrArg (fun w : pairsTwo => w.val.1) hv
  refine ⟨u, u.2, v, v.2, fun huv => ?_⟩
  obtain ⟨hv1, -⟩ := apply_one_three (hR v v.2).2
  have h1 := congrArg (fun π : Perm (Fin 10) => π 0) huv
  simp only [Perm.coe_mul, Function.comp_apply] at h1
  rw [hv0, hu2, hu0, hv1, hv0] at h1
  exact absurd h1 (by decide)

end SigmaTwo

end CFSG.ComponentClassification.GSThmB.Catalog82A10
