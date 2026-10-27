module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.ONanDefs

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup

variable {G : Type*} [Group G]

abbrev KQ (y : G) : Type _ := centralizer ({y} : Set G) ⧸ zpowers (zIn y)

@[expose] def πQ (y : G) : centralizer ({y} : Set G) →* KQ y := QuotientGroup.mk' _

@[expose] def liftQ (y : G) (H : Subgroup G) : Subgroup (KQ y) :=
  (H.subgroupOf (centralizer ({y} : Set G))).map (πQ y)

theorem πQ_surjective (y : G) : Function.Surjective (πQ y) := QuotientGroup.mk'_surjective _

theorem mem_zpowers_zIn_iff {y : G} (k : centralizer ({y} : Set G)) :
    k ∈ zpowers (zIn y) ↔ (k : G) ∈ zpowers y := by
  rw [mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn]; rfl⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by rw [← hn]; rfl)⟩

theorem πQ_eq_one_iff {y : G} (k : centralizer ({y} : Set G)) :
    πQ y k = 1 ↔ (k : G) ∈ zpowers y := by
  rw [πQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_zIn_iff]

theorem πQ_eq_iff {y : G} (a b : centralizer ({y} : Set G)) :
    πQ y a = πQ y b ↔ (a : G)⁻¹ * b ∈ zpowers y := by
  rw [πQ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    mem_zpowers_zIn_iff]
  rfl

theorem mem_liftQ_iff {y : G} {H : Subgroup G} {x : KQ y} :
    x ∈ liftQ y H ↔ ∃ k : centralizer ({y} : Set G), (k : G) ∈ H ∧ πQ y k = x := by
  rw [liftQ, Subgroup.mem_map]
  rfl

theorem πQ_mem_liftQ {y : G} {H : Subgroup G} {k : centralizer ({y} : Set G)}
    (hk : (k : G) ∈ H) : πQ y k ∈ liftQ y H :=
  mem_liftQ_iff.2 ⟨k, hk, rfl⟩

theorem mem_of_πQ_mem_liftQ {y : G} {H : Subgroup G} (hH : zpowers y ≤ H)
    {k : centralizer ({y} : Set G)} (hk : πQ y k ∈ liftQ y H) : (k : G) ∈ H := by
  obtain ⟨k', hk', he⟩ := mem_liftQ_iff.1 hk
  have h := (πQ_eq_iff k' k).1 he
  have e : (k : G) = k' * ((k' : G)⁻¹ * k) := by group
  rw [e]
  exact mul_mem hk' (hH h)

theorem liftQ_mono {y : G} {H H' : Subgroup G} (h : H ≤ H') : liftQ y H ≤ liftQ y H' :=
  Subgroup.map_mono fun _ hx => h hx

theorem card_liftQ [Finite G] {y : G} {H : Subgroup G} (hH : zpowers y ≤ H)
    (hHC : H ≤ centralizer ({y} : Set G)) :
    Nat.card (liftQ y H) * Nat.card (zpowers y) = Nat.card H := by
  classical
  set f : H.subgroupOf (centralizer ({y} : Set G)) →* KQ y :=
    (πQ y).comp (H.subgroupOf (centralizer ({y} : Set G))).subtype with hf
  have hrange : f.range = liftQ y H := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Nat.card f.ker = Nat.card (zpowers y) := by
    refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨k.1.1.1, ?_⟩) ⟨?_, ?_⟩)
    · have h0 : f k = 1 := k.2
      have h1 : πQ y k.1.1 = 1 := h0
      exact (πQ_eq_one_iff _).1 h1
    · intro a b h
      have h' : a.1.1.1 = b.1.1.1 := congrArg (fun x : zpowers y => (x : G)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    · rintro ⟨g, hg⟩
      have hgC : g ∈ centralizer ({y} : Set G) := hHC (hH hg)
      have hgH : (⟨g, hgC⟩ : centralizer ({y} : Set G)) ∈
          H.subgroupOf (centralizer ({y} : Set G)) := by
        rw [mem_subgroupOf]
        exact hH hg
      refine ⟨⟨⟨⟨g, hgC⟩, hgH⟩, ?_⟩, rfl⟩
      show πQ y ⟨g, hgC⟩ = 1
      exact (πQ_eq_one_iff _).2 hg
  have h1 := f.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker] at h1
  rw [← h1]
  exact Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv

end CFSG.OddStandard.ONanRec
