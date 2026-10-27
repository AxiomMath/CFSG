module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der65

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section ExtraG

variable {G : Type} [Group G]

structure ExtraG (p : ℕ) (Q : Subgroup G) : Prop where
  card_Z : Nat.card ↥(zOf Q) = p
  comm_eq : ⁅Q, Q⁆ = zOf Q

theorem center_map_eq (Q : Subgroup G) : (Subgroup.center ↥Q).map Q.subtype = zOf Q := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Subgroup.center ↥Q := hx
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨h, hh⟩)
  · rintro ⟨hgQ, hgc⟩
    have hgc' : g ∈ centralizer (Q : Set G) := hgc
    refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
    show (⟨g, hgQ⟩ : ↥Q) ∈ Subgroup.center ↥Q
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc' y y.2)

theorem card_center_eq (Q : Subgroup G) : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(zOf Q) := by
  rw [← center_map_eq, Subgroup.card_map_of_injective Q.subtype_injective]

theorem commutator_map_eq (Q : Subgroup G) : (_root_.commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem frattini_eq_commutator_of_exp {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (hQp : IsPGroup p Q) (hexp : ∀ x : Q, x ^ p = 1) : frattini Q = _root_.commutator Q := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p Q) := ⟨hQp⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (hy | ⟨x, rfl⟩)
    · exact hy
    · show x ^ p ∈ _root_.commutator Q
      rw [hexp x]
      exact one_mem _
  · exact fun y hy => Subgroup.subset_closure (Or.inl hy)

theorem isExtraspecial_of_extraG [Finite G] {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hQp : IsPGroup p ↥Q)
    (hexp : ∀ x ∈ Q, x ^ p = 1) (h : ExtraG p Q) : IsExtraspecialPGroup p ↥Q := by
  have hc : _root_.commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [commutator_map_eq, center_map_eq, h.comm_eq]
  refine ⟨hQp, hc, ?_, ?_⟩
  · rw [frattini_eq_commutator_of_exp hp hQp (fun x => Subtype.ext (by simpa using hexp x x.2)), hc]
  · rw [card_center_eq]
    exact h.card_Z

theorem extraG_of_isExtraspecial {p : ℕ} {Q : Subgroup G} (h : IsExtraspecialPGroup p ↥Q) :
    ExtraG p Q := by
  refine ⟨?_, ?_⟩
  · rw [← card_center_eq]
    exact h.2.2.2
  · have h1 := congrArg (Subgroup.map Q.subtype) h.2.1
    rwa [commutator_map_eq, center_map_eq] at h1

end ExtraG

section Cyc

variable {G : Type} [Group G] [Finite G]

theorem extraG_of_cyclic_center {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hexp : ∀ x ∈ Q, x ^ p = 1) (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hnc : ¬ IsMulCommutative ↥Q) (hcyc : IsCyclic ↥(zOf Q)) : ExtraG p Q := by
  have hQ'0 : ⁅Q, Q⁆ ≠ ⊥ := fun h => hnc (Subgroup.commutator_self_eq_bot_iff.mp h)
  have hQ'Q : ⁅Q, Q⁆ ≤ Q := commutator_le_left_of_normalizes Subgroup.le_normalizer
  have hQ'Z : ⁅Q, Q⁆ ≤ zOf Q := le_inf hQ'Q (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl)
  have hZ0 : zOf Q ≠ ⊥ := fun h => hQ'0 (le_bot_iff.mp (h ▸ hQ'Z))
  have hcardZ : Nat.card ↥(zOf Q) = p := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(zOf Q))
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hexp (g : G) g.2.1)
    have hord : orderOf g = Nat.card ↥(zOf Q) := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      apply hZ0
      apply Subgroup.eq_bot_of_card_eq
      rw [← hord, h1]
    · rw [← hord, h1]
  refine ⟨hcardZ, ?_⟩
  have hQ'card : Nat.card ↥⁅Q, Q⁆ ∣ p := hcardZ ▸ Subgroup.card_dvd_of_le hQ'Z
  rcases (Nat.dvd_prime hp).mp hQ'card with h1 | h1
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hQ'0
  · exact Subgroup.eq_of_le_of_card_ge hQ'Z (by rw [hcardZ, h1])

end Cyc

end CFSG.GH74.GLS.Stage2.Bender.Thm1
