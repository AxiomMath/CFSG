module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB

public noncomputable section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.Assembly.LowTwoRank

universe u

theorem card_centralizer_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card (Subgroup.centralizer ({e g} : Set H)) := by
  have hmap : (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
    ext h
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      have := congrArg e hc
      simpa using this
    · intro hc
      apply e.injective
      simpa using hc
  rw [← hmap]
  exact Nat.card_congr (e.subgroupMap _).toEquiv

theorem card_centralizer_S (s : S) :
    Nat.card (Subgroup.centralizer ({s} : Set S)) =
      Nat.card ↥(Subgroup.centralizer {(s : Equiv.Perm (Fin 42))} ⊓ S) := by
  have hmap : (Subgroup.centralizer ({s} : Set S)).map S.subtype =
      Subgroup.centralizer {(s : Equiv.Perm (Fin 42))} ⊓ S := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa using congrArg Subtype.val hy, y.2⟩
    · rintro ⟨hx, hxS⟩
      exact ⟨⟨x, hxS⟩, Subtype.ext hx, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective S.subtype_injective]

theorem isConj_r₁_of_inner {x : R} (hxS : (x : Equiv.Perm (Fin 42)) ∈ S) (h1 : x ≠ 1)
    (h2 : x * x = 1) : IsConj x r₁R := by
  rcases (orderOf_eq_two_iff x).1 (orderOf_eq_two_of_mul_self h1 h2) with h | h | h | h
  · exact h
  · exact (not_mem_S_of_isConj h not_mem_S_r₂ hxS).elim
  · exact (not_mem_S_of_isConj h not_mem_S_r₃ hxS).elim
  · exact (not_mem_S_of_isConj h not_mem_S_r₄ hxS).elim

theorem card_centralizer_involution_S (s : S) (hs : orderOf s = 2) :
    Nat.card (Subgroup.centralizer ({s} : Set S)) = 64 := by
  let x : R := ⟨s, S_le_R s.2⟩
  have h1 : x ≠ 1 := by
    intro h
    have hs1 : (s : Equiv.Perm (Fin 42)) = 1 := congrArg Subtype.val h
    have : s = 1 := Subtype.ext hs1
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have h2 : x * x = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs, pow_two] at this
    have hss : (s : Equiv.Perm (Fin 42)) * s = 1 := congrArg Subtype.val this
    exact Subtype.ext hss
  obtain ⟨e⟩ := fixed_of_isConj (isConj_r₁_of_inner (x := x) s.2 h1 h2)
  rw [card_centralizer_S, Nat.card_congr e.toEquiv]
  exact card_C₁

@[expose] def altInvolution : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[expose] def altThree : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 5 6, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem orderOf_altInvolution : orderOf altInvolution = 2 := by
  apply orderOf_eq_prime
  · exact Subtype.ext (by decide)
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem altThree_mem : altThree ∈ Subgroup.centralizer ({altInvolution} : Set _) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (by decide)

theorem three_dvd_card_centralizer :
    3 ∣ Nat.card (Subgroup.centralizer ({altInvolution} : Set (alternatingGroup (Fin 8)))) := by
  have h : orderOf (⟨altThree, altThree_mem⟩ :
      Subgroup.centralizer ({altInvolution} : Set (alternatingGroup (Fin 8)))) = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (Subtype.ext (by decide))
    · intro h
      have := congrArg (fun y => ((y.1 : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8))) h
      revert this
      decide
  rw [← h]
  exact orderOf_dvd_natCard _

theorem eq_eight_of_factorial {m : ℕ} (hm : 5 ≤ m) (h : m.factorial = 40320) : m = 8 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have : m.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
    rw [h] at this
    exact absurd this (by decide)
  · have : (9 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hgt
    rw [h] at this
    exact absurd this (by decide)

theorem facts_of_equiv_S {X : Type*} [Group X] (θ : X ≃* S) :
    Nat.card X = 20160 ∧
      (∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) = 64) ∧
      ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
        IsEmpty (X ≃* alternatingGroup Ω) := by
  have hcard : Nat.card X = 20160 := by rw [Nat.card_congr θ.toEquiv, card_S]
  have hcent : ∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) = 64 := by
    intro t ht
    rw [card_centralizer_of_equiv θ t]
    exact card_centralizer_involution_S (θ t) (by rw [MulEquiv.orderOf_eq]; exact ht)
  refine ⟨hcard, hcent, fun Ω _ _ hΩ => ⟨fun φ => ?_⟩⟩
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Ω)
  rw [← Nat.card_congr φ.toEquiv, hcard, Nat.card_perm, Nat.card_eq_fintype_card] at h2
  have h8 : Fintype.card Ω = 8 := eq_eight_of_factorial hΩ (by omega)
  let ξ : X ≃* alternatingGroup (Fin 8) :=
    φ.trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq h8))
  have ht : orderOf (ξ.symm altInvolution) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_altInvolution
  have h64 := hcent _ ht
  rw [card_centralizer_of_equiv ξ, MulEquiv.apply_symm_apply] at h64
  have h3 := three_dvd_card_centralizer
  rw [h64] at h3
  exact absurd h3 (by decide)


theorem excludes_alternating_models (X : Type) [Group X]
    (hX : Assembly.ComponentType.ClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 ∧
      (∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) = 64) ∧
      ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
        IsEmpty (X ≃* alternatingGroup Ω) := by
  obtain ⟨θ⟩ := exact_model.2.2.2.2.2 X hX
  exact facts_of_equiv_S θ

theorem excludes_alternating_models_stated (X : Type) [Group X]
    (hX : StatedClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 ∧
      (∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) = 64) ∧
      ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
        IsEmpty (X ≃* alternatingGroup Ω) := by
  obtain ⟨θ⟩ := nonempty_equiv_of_stated X hX
  exact facts_of_equiv_S θ

end CFSG.ComponentClassification.PSL3Four
