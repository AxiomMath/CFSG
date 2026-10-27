module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup MulAction CFSG.EvenSporadicStandard.Solomon78

section Sylow

variable {Γ : Type} [Group Γ] {Ω : Type} [MulAction Γ Ω]

theorem fi24in_exists_odd_index_stabilizer [Finite Γ] [Finite Ω] (hΩ : Odd (Nat.card Ω)) :
    ∃ ω : Ω, Odd (stabilizer Γ ω).index := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 Γ) := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := P.isPGroup'
  have hmod := hP.card_modEq_card_fixedPoints (α := Ω)
  have hodd : Odd (Nat.card (fixedPoints P Ω)) := by
    have h1 : Nat.card Ω % 2 = Nat.card (fixedPoints P Ω) % 2 := hmod
    rw [Nat.odd_iff] at hΩ ⊢
    omega
  have hne : Nonempty (fixedPoints P Ω) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Nat.card_of_isEmpty] at hodd
  obtain ⟨⟨ω, hω⟩⟩ := hne
  refine ⟨ω, ?_⟩
  have hle : (P : Subgroup Γ) ≤ stabilizer Γ ω := fun g hg => by
    rw [mem_stabilizer_iff]
    exact (mem_fixedPoints.1 hω) ⟨g, hg⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  have hnd : ¬ 2 ∣ (P : Subgroup Γ).index := P.not_dvd_index
  rw [Nat.odd_iff]
  by_contra h
  apply hnd
  exact dvd_trans (by omega : 2 ∣ (stabilizer Γ ω).index) hdvd

theorem fi24in_even_index_stabilizer_of_transitive [IsPretransitive Γ Ω]
    (hΩ : Even (Nat.card Ω)) (ω : Ω) : Even (stabilizer Γ ω).index := by
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
  simpa [Nat.card_univ] using hΩ

end Sylow

section Edges

variable {Γ V : Type} [Group Γ] [MulAction Γ V] (r : V → V → Prop)

abbrev fi24inGraph : SimpleGraph V := SimpleGraph.fromRel r

variable {r}

theorem fi24in_adj_iff (hsymm : ∀ p q, r p q → r q p) {p q : V} :
    (fi24inGraph r).Adj p q ↔ p ≠ q ∧ r p q := by
  rw [SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => ⟨fun h => h.elim id (hsymm _ _), Or.inl⟩

theorem fi24in_smul_mem_edgeSet (hinv : ∀ (g : Γ) p q, r (g • p) (g • q) ↔ r p q)
    (hsymm : ∀ p q, r p q → r q p) (g : Γ) {e : Sym2 V} (he : e ∈ (fi24inGraph r).edgeSet) :
    e.map (fun v => g • v) ∈ (fi24inGraph r).edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, fi24in_adj_iff hsymm]
    rw [SimpleGraph.mem_edgeSet, fi24in_adj_iff hsymm] at he
    exact ⟨fun h => he.1 (smul_left_cancel g h), (hinv g a b).2 he.2⟩

@[instance_reducible] def fi24inEdgeAction (hinv : ∀ (g : Γ) p q, r (g • p) (g • q) ↔ r p q)
    (hsymm : ∀ p q, r p q → r q p) : MulAction Γ ↥(fi24inGraph r).edgeSet where
  smul g e := ⟨e.1.map (fun v => g • v), fi24in_smul_mem_edgeSet hinv hsymm g e.2⟩
  one_smul e := Subtype.ext (by
    show e.1.map (fun v => (1 : Γ) • v) = e.1
    simp [one_smul, Sym2.map_id'])
  mul_smul g h e := Subtype.ext (by
    show e.1.map (fun v => (g * h) • v) = (e.1.map (fun v => h • v)).map (fun v => g • v)
    rw [Sym2.map_map]
    simp [mul_smul])

theorem fi24in_exists_odd_index_edge [Finite Γ] [Finite V]
    (hinv : ∀ (g : Γ) p q, r (g • p) (g • q) ↔ r p q) (hsymm : ∀ p q, r p q → r q p)
    {d m : ℕ} (hd : Odd d) (hm : Odd m) (hV : Nat.card V = 2 * m)
    (hdeg : ∀ p : V, Nat.card {q : V // q ≠ p ∧ r p q} = d) :
    ∃ p q : V, p ≠ q ∧ r p q ∧ ∃ H : Subgroup Γ, Odd H.index ∧
      ∀ g ∈ H, (g • p = p ∧ g • q = q) ∨ (g • p = q ∧ g • q = p) := by
  classical
  have := Fintype.ofFinite V
  set G := fi24inGraph r with hG
  have hdegG : ∀ v, G.degree v = d := fun v => by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, ← hdeg v]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [SimpleGraph.mem_neighborSet, hG, fi24in_adj_iff hsymm, ne_comm]
  have hedges : Odd (Nat.card G.edgeSet) := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hdegG, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    rw [← Nat.card_eq_fintype_card, hV] at hsum
    have h2 : Nat.card G.edgeSet = m * d := by
      have h3 : Nat.card G.edgeSet = G.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset, Set.toFinset_card]
      linarith
    rw [h2]
    exact hm.mul hd
  let := fi24inEdgeAction hinv hsymm
  obtain ⟨⟨e, he⟩, hstab⟩ := fi24in_exists_odd_index_stabilizer (Γ := Γ)
    (Ω := ↥G.edgeSet) hedges
  induction e using Sym2.ind with
  | _ p q =>
    rw [SimpleGraph.mem_edgeSet, hG, fi24in_adj_iff hsymm] at he
    refine ⟨p, q, he.1, he.2, _, hstab, fun g hg => ?_⟩
    have h1 : g • (⟨s(p, q), by rw [SimpleGraph.mem_edgeSet, hG, fi24in_adj_iff hsymm]; exact he⟩ :
        ↥G.edgeSet) = ⟨s(p, q), by
          rw [SimpleGraph.mem_edgeSet, hG, fi24in_adj_iff hsymm]; exact he⟩ :=
      mem_stabilizer_iff.1 hg
    have h2 := congrArg Subtype.val h1
    have h3 : s(g • p, g • q) = s(p, q) := h2
    rw [Sym2.eq_iff] at h3
    exact h3

end Edges

section TwoAdic

variable {X : Type} [Group X] [Finite X]

theorem fi24in_relIndex_ne_zero {H K : Subgroup X} : H.relIndex K ≠ 0 :=
  (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card H K) Nat.card_pos).ne'

theorem fi24in_twoAdic_eq_add_of_le {H K : Subgroup X} (h : H ≤ K) :
    twoAdic K = (H.relIndex K).factorization 2 + twoAdic H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left h] at h1
  have h2 : H.relIndex K ≠ 0 := fi24in_relIndex_ne_zero
  unfold twoAdic
  rw [← h1, Nat.factorization_mul h2 Nat.card_pos.ne']
  simp

theorem fi24in_twoAdic_eq_of_odd_relIndex {H K : Subgroup X} (h : H ≤ K)
    (hodd : Odd (H.relIndex K)) : twoAdic H = twoAdic K := by
  have h1 := fi24in_twoAdic_eq_add_of_le h
  have h2 : (H.relIndex K).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
  omega

theorem fi24in_twoAdic_lt_of_even_relIndex {H K : Subgroup X} (h : H ≤ K)
    (heven : Even (H.relIndex K)) : twoAdic H < twoAdic K := by
  have h1 := fi24in_twoAdic_eq_add_of_le h
  have h0 : H.relIndex K ≠ 0 := fi24in_relIndex_ne_zero
  have h2 : 0 < (H.relIndex K).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two h0 (even_iff_two_dvd.1 heven)
  omega

theorem fi24in_mem_vMaximal_of_twoAdic {K : Subgroup X} {u v : X} (hv : v ∈ vCandidates K u)
    (h : twoAdic K ≤ twoAdic (K ⊓ centralizer ({v} : Set X))) : v ∈ vMaximal K u :=
  ⟨hv, fun _ _ => (twoAdic_mono inf_le_left).trans h⟩

end TwoAdic

end CFSG.EvenSporadicStandard.Induction
