module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Cyclic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Open

theorem center_eq_bot_of_simple_nonabelian {F : Type*} [Group F] (hs : IsSimpleGroup F)
    (hn : ∃ a b : F, a * b ≠ b * a) : center F = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center F) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

structure ThCyc (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  data : ThData ↥L
  mem : t ∈ R
  order_two : orderOf t = 2
  pgroup : IsPGroup 2 R
  cyclic : IsCyclic R
  le_centralizer : R ≤ centralizer (L : Set G)
  centralizer_eq : centralizer ({t} : Set G) = L ⊔ R
  disjoint : Disjoint L R

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_thCyc (h : StdHyp G L) (hD : ThData ↥L) :
    ∃ (R : Subgroup G) (t : G), ThCyc G L R t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
  set C := centralizer (L : Set G) with hC
  have hN := h.centralizer_le_normalizer_centralizer ht ht2
  have hcore := h.oddCore t ht2
  have ht₀ : orderOf (⟨t, ht⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, ht₀, pow_one]) : IsPGroup 2 (zpowers (⟨t, ht⟩ : C))).exists_le_sylow
  have htQ : (⟨t, ht⟩ : C) ∈ (Q : Subgroup C) := hQ (mem_zpowers _)
  have hQcyc : IsCyclic (Q : Subgroup C) :=
    isCyclic_of_isPGroup_of_cyclicSylow h.cyclicSylow Q.isPGroup'
  have hR := inf_centralizer_singleton_eq_map_sylow ht hN hcore Q hQcyc htQ
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  have hRt : (Q : Subgroup C).map C.subtype ≤ centralizer ({t} : Set G) := hR ▸ inf_le_right
  have hRC : (Q : Subgroup C).map C.subtype ≤ C := hR ▸ inf_le_left
  refine ⟨(Q : Subgroup C).map C.subtype, t, ⟨h.simple, h.nonabelian, hD, ?_, ht2,
    Q.isPGroup'.map _, ?_, hRC, ?_, ?_⟩⟩
  · exact hR ▸ ⟨ht, mem_centralizer_singleton_iff.2 rfl⟩
  · let e := Subgroup.equivMapOfInjective (Q : Subgroup C) C.subtype C.subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · refine le_antisymm (fun g hg => ?_) (sup_le hLt hRt)
    have hgN := h.centralizer_le_normalizer ht ht2 hg
    have hgs := normalizer_le_sup_centralizer_of_mulAut_inner hD.allInner hgN
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hgs
    have hcH : c ∈ centralizer ({t} : Set G) := by
      have := (centralizer ({t} : Set G)).mul_mem (inv_mem (hLt hl)) hg
      rwa [inv_mul_cancel_left] at this
    have hcR : c ∈ (Q : Subgroup C).map C.subtype := hR ▸ ⟨hc, hcH⟩
    exact mul_mem_sup hl hcR
  · have hcen : center L = ⊥ := center_eq_bot_of_simple_nonabelian hD.simple hD.nonabelian
    have h1 : L ⊓ C = ⊥ := by
      rw [← map_center_eq_inf_centralizer, hcen, Subgroup.map_bot]
    exact disjoint_iff.2 (eq_bot_iff.2 ((inf_le_inf_left L hRC).trans h1.le))

end CFSG.EvenSporadicStandard.ThStd
