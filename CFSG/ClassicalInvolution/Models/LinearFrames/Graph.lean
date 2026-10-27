module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic

section CommGraph

variable {G : Type*} [Group G]

@[expose] def commGraph (S : Set (Subgroup G)) : SimpleGraph ↥S :=
  SimpleGraph.fromRel fun K L => K ≠ L ∧ Commutes (K : Subgroup G) (L : Subgroup G)

theorem commGraph_adj {S : Set (Subgroup G)} {K L : ↥S} :
    (commGraph S).Adj K L ↔ K ≠ L ∧ Commutes (K : Subgroup G) (L : Subgroup G) := by
  simp only [commGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h2 | h2⟩
    · exact h2
    · exact ⟨h2.1.symm, h2.2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl ⟨h1, h2⟩⟩

theorem nonCommGraph_eq_compl (S : Set (Subgroup G)) : nonCommGraph S = (commGraph S)ᶜ := by
  ext K L
  rw [nonCommGraph_adj, SimpleGraph.compl_adj, commGraph_adj]
  tauto

end CommGraph

section WeylConnected

variable {n : ℕ}

theorem weylGraph_compl_adj {T T' : Pair n} :
    (weylGraph n)ᶜ.Adj T T' ↔ T ≠ T' ∧ ¬ Disjoint T.1 T'.1 := by
  rw [SimpleGraph.compl_adj, weylGraph_adj]
  tauto

theorem natCard_pair (n : ℕ) : Nat.card (Pair n) = n.choose 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter fun T : Finset (Fin n) => T.card = 2) =
      Finset.powersetCard 2 Finset.univ := by
    ext T
    simp [Finset.mem_powersetCard]
  rw [e, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem exists_mem_pair (T : Pair n) : ∃ a, a ∈ T.1 :=
  Finset.card_pos.mp (by rw [T.2]; omega)

theorem nonempty_pair (hn : 2 ≤ n) : Nonempty (Pair n) :=
  ⟨⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩⟩

theorem weylGraph_compl_connected (hn : 2 ≤ n) : (weylGraph n)ᶜ.Connected := by
  have := nonempty_pair hn
  refine ⟨fun T T' => ?_⟩
  by_cases hTT : T = T'
  · subst hTT
    exact SimpleGraph.Reachable.refl _
  by_cases hd : Disjoint T.1 T'.1
  · obtain ⟨a, ha⟩ := exists_mem_pair T
    obtain ⟨c, hc⟩ := exists_mem_pair T'
    have hac : a ≠ c := fun h => Finset.disjoint_left.mp hd ha (h ▸ hc)
    let U : Pair n := ⟨{a, c}, Finset.card_pair hac⟩
    have hTU : (weylGraph n)ᶜ.Adj T U := by
      rw [weylGraph_compl_adj]
      refine ⟨fun h => ?_, ?_⟩
      · have hcU : c ∈ U.1 := by simp [U]
        rw [← h] at hcU
        exact Finset.disjoint_left.mp hd hcU hc
      · rw [Finset.not_disjoint_iff]
        exact ⟨a, ha, by simp [U]⟩
    have hUT : (weylGraph n)ᶜ.Adj U T' := by
      rw [weylGraph_compl_adj]
      refine ⟨fun h => ?_, ?_⟩
      · have haU : a ∈ U.1 := by simp [U]
        rw [h] at haU
        exact Finset.disjoint_left.mp hd ha haU
      · rw [Finset.not_disjoint_iff]
        exact ⟨c, by simp [U], hc⟩
    exact hTU.reachable.trans hUT.reachable
  · exact (weylGraph_compl_adj.mpr ⟨hTT, hd⟩).reachable

end WeylConnected

section PairFamily

variable {n : ℕ} {G : Type*} [Group G]

structure IsPairFamily (L : Pair n → Subgroup G) : Prop where
  inj : Function.Injective L
  commutes_iff : ∀ T T' : Pair n, T ≠ T' → (Commutes (L T) (L T') ↔ Disjoint T.1 T'.1)

variable {L : Pair n → Subgroup G}

@[expose] noncomputable def IsPairFamily.equiv (h : IsPairFamily L) : Pair n ≃ ↥(Set.range L) :=
  Equiv.ofInjective L h.inj

theorem IsPairFamily.coe_equiv (h : IsPairFamily L) (T : Pair n) :
    ((h.equiv T : ↥(Set.range L)) : Subgroup G) = L T := rfl

@[expose] noncomputable def IsPairFamily.iso (h : IsPairFamily L) :
    weylGraph n ≃g commGraph (Set.range L) where
  toEquiv := h.equiv
  map_rel_iff' := by
    intro T T'
    rw [commGraph_adj, weylGraph_adj, ne_eq, h.equiv.injective.eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h.commutes_iff T T' h1).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h.commutes_iff T T' h1).mpr h2⟩

@[expose] def complIso {V W : Type*} {G₁ : SimpleGraph V} {G₂ : SimpleGraph W} (e : G₁ ≃g G₂) :
    G₁ᶜ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.compl_adj, ne_eq, RelIso.coe_fn_toEquiv, e.map_adj_iff,
      e.injective.eq_iff]

theorem IsPairFamily.nonCommConnected (h : IsPairFamily L) (hn : 2 ≤ n) :
    NonCommConnected (Set.range L) := by
  unfold NonCommConnected
  rw [nonCommGraph_eq_compl]
  exact (complIso h.iso).symm.connected_iff.mpr (weylGraph_compl_connected hn)

theorem IsPairFamily.ncard_range (h : IsPairFamily L) : (Set.range L).ncard = n.choose 2 := by
  rw [Set.ncard_range_of_injective h.inj, natCard_pair]

end PairFamily

section Swaps

variable {n : ℕ}

abbrev Swaps (n : ℕ) := {t : Equiv.Perm (Fin n) // t.IsSwap}

@[expose] def swapGraph (n : ℕ) : SimpleGraph (Swaps n) :=
  SimpleGraph.fromRel fun s t => s ≠ t ∧ Commute s.1 t.1

theorem swapGraph_adj {s t : Swaps n} :
    (swapGraph n).Adj s t ↔ s ≠ t ∧ Commute s.1 t.1 := by
  simp only [swapGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h2 | h2⟩
    · exact h2
    · exact ⟨h2.1.symm, h2.2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl ⟨h1, h2⟩⟩

theorem isSwap_iff_exists {t : Equiv.Perm (Fin n)} :
    t.IsSwap ↔ ∃ x y, x ≠ y ∧ t = Equiv.swap x y :=
  Iff.rfl

@[expose] def swapsElt {i j : Fin n} (hij : i ≠ j) : Swaps n :=
  ⟨Equiv.swap i j, i, j, hij, rfl⟩

theorem swap_support_eq_iff {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ({i, j} : Finset (Fin n)) = {k, l}) : Equiv.swap i j = Equiv.swap k l := by
  have hi : i ∈ ({k, l} : Finset (Fin n)) := h ▸ by simp
  have hj : j ∈ ({k, l} : Finset (Fin n)) := h ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · subst hi
    subst hj
    rfl
  · subst hi
    subst hj
    exact Equiv.swap_comm _ _
  · exact absurd (hi.trans hj.symm) hij

@[expose] noncomputable def swapPairEquiv (n : ℕ) : Swaps n ≃ Pair n :=
  Equiv.ofBijective (fun t => ⟨t.1.support, Equiv.Perm.card_support_eq_two.mpr t.2⟩)
    ⟨by
      rintro ⟨s, x, y, hxy, rfl⟩ ⟨t, z, w, hzw, rfl⟩ h
      have h' := congrArg Subtype.val h
      simp only [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzw] at h'
      exact Subtype.ext (swap_support_eq_iff hxy hzw h'),
    by
      rintro ⟨T, hT⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
      exact ⟨swapsElt hxy, Subtype.ext (Equiv.Perm.support_swap hxy)⟩⟩

theorem swapPairEquiv_apply (t : Swaps n) : ((swapPairEquiv n t : Pair n) : Finset (Fin n)) =
    t.1.support := rfl

theorem swapPairEquiv_swapsElt {i j : Fin n} (hij : i ≠ j) :
    ((swapPairEquiv n (swapsElt hij) : Pair n) : Finset (Fin n)) = {i, j} :=
  Equiv.Perm.support_swap hij

theorem swap_commute_iff_disjoint {s t : Swaps n} (hne : s ≠ t) :
    Commute s.1 t.1 ↔ Disjoint s.1.support t.1.support := by
  constructor
  · intro hc
    by_contra hnd
    obtain ⟨s, x, y, hxy, rfl⟩ := s
    obtain ⟨t, z, w, hzw, rfl⟩ := t
    simp only [Equiv.Perm.support_swap hxy, Equiv.Perm.support_swap hzw] at hnd
    have hne' : ({x, y} : Finset (Fin n)) ≠ {z, w} := fun h =>
      hne (Subtype.ext (swap_support_eq_iff hxy hzw h))
    rcases pair_disjoint_or_share_one (Finset.card_pair hxy) (Finset.card_pair hzw) hne' with
      hd | ⟨a, b, c, hab, hbc, hac, h1, h2⟩
    · exact hnd hd
    · have e1 : Equiv.swap x y = Equiv.swap a b := swap_support_eq_iff hxy hab h1
      have e2 : Equiv.swap z w = Equiv.swap b c := swap_support_eq_iff hzw hbc h2
      have hc' : Commute (Equiv.swap x y) (Equiv.swap z w) := hc
      rw [e1, e2] at hc'
      have h3 := congrArg (fun p : Equiv.Perm (Fin n) => p a) hc'.eq
      simp only [Equiv.Perm.mul_apply] at h3
      rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left,
        Equiv.swap_apply_left] at h3
      exact hbc h3
  · intro hd
    obtain ⟨s, x, y, hxy, rfl⟩ := s
    obtain ⟨t, z, w, hzw, rfl⟩ := t
    exact Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_iff_disjoint_support.mpr hd)

@[expose] def Swaps.conj (σ : Equiv.Perm (Fin n)) (t : Swaps n) : Swaps n :=
  ⟨σ * t.1 * σ⁻¹, Equiv.Perm.card_support_eq_two.mp (by
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr t.2)⟩

theorem swapPairEquiv_conj (σ : Equiv.Perm (Fin n)) (t : Swaps n) :
    swapPairEquiv n (Swaps.conj σ t) = Pair.map σ (swapPairEquiv n t) :=
  Subtype.ext Equiv.Perm.support_conj

theorem swapPairEquiv_symm_map (σ : Equiv.Perm (Fin n)) (T : Pair n) :
    ((swapPairEquiv n).symm (Pair.map σ T)).1 = σ * ((swapPairEquiv n).symm T).1 * σ⁻¹ := by
  have h := swapPairEquiv_conj σ ((swapPairEquiv n).symm T)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]
  rfl

@[expose] noncomputable def swapGraphIso (n : ℕ) : swapGraph n ≃g weylGraph n where
  toEquiv := swapPairEquiv n
  map_rel_iff' := by
    intro s t
    rw [weylGraph_adj, swapGraph_adj, ne_eq, (swapPairEquiv n).injective.eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (swap_commute_iff_disjoint h1).mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (swap_commute_iff_disjoint h1).mp h2⟩

end Swaps

section WeylDatum

variable {n : ℕ} {G : Type*} [Group G] {L : Pair n → Subgroup G}

@[expose] noncomputable def IsPairFamily.swapEquiv (h : IsPairFamily L) :
    ↥(Set.range L) ≃ Swaps n :=
  h.equiv.symm.trans (swapPairEquiv n).symm

theorem IsPairFamily.swapEquiv_equiv (h : IsPairFamily L) (T : Pair n) :
    h.swapEquiv (h.equiv T) = (swapPairEquiv n).symm T := by
  simp [IsPairFamily.swapEquiv]

theorem support_swapPairEquiv_symm (T : Pair n) :
    ((swapPairEquiv n).symm T).1.support = T.1 := by
  have h := swapPairEquiv_apply (n := n) ((swapPairEquiv n).symm T)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem IsPairFamily.commutes_iff_disjoint_swap (h : IsPairFamily L) {K K' : ↥(Set.range L)}
    (hne : K ≠ K') :
    Commutes (K : Subgroup G) K' ↔
      Disjoint (h.swapEquiv K).1.support (h.swapEquiv K').1.support := by
  obtain ⟨T, rfl⟩ := h.equiv.surjective K
  obtain ⟨T', rfl⟩ := h.equiv.surjective K'
  have hTT' : T ≠ T' := fun e => hne (by rw [e])
  rw [h.swapEquiv_equiv, h.swapEquiv_equiv, support_swapPairEquiv_symm,
    support_swapPairEquiv_symm]
  exact h.commutes_iff T T' hTT'

theorem IsPairFamily.commutes_iff_disjoint_perm (h : IsPairFamily L) {K K' : ↥(Set.range L)}
    (hne : K ≠ K') :
    Commutes (K : Subgroup G) K' ↔ (h.swapEquiv K).1.Disjoint (h.swapEquiv K').1 := by
  rw [h.commutes_iff_disjoint_swap hne, Equiv.Perm.disjoint_iff_disjoint_support]

end WeylDatum

end CFSG.ClassicalInvolution.Models
