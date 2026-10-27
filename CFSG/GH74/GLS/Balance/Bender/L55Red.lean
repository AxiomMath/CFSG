module

public import CFSG.GH74.GLS.Balance.Bender.Stmts
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def l55_Claim (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G), Nat.card X ≤ n → IsPStar p ↥X →
    IsPGroup p ↥P → P ≤ normalizer (X : Set G) → X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G))

theorem l55_map_centralizer_le {G : Type} [Group G] {H P : Subgroup G} (hPH : P ≤ H) :
    (centralizer ((P.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype ≤
      centralizer (P : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  intro q hq
  have hq' : (⟨q, hPH hq⟩ : ↥H) ∈ P.subgroupOf H := hq
  have := mem_centralizer_iff.mp hz _ hq'
  exact congrArg Subtype.val this

theorem l55_reduce {p : ℕ} [Fact p.Prime] {n : ℕ}
    (h : ∀ (G : Type) [Group G] [Finite G] (X P : Subgroup G), Nat.card X ≤ n → IsPStar p ↥X →
      IsPGroup p ↥P → P ≤ normalizer (X : Set G) → X ⊔ P = ⊤ →
        X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G))) : l55_Claim p n := by
  intro G _ _ X P hn hX hP hPX
  set H : Subgroup G := X ⊔ P with hH
  have hXH : X ≤ H := le_sup_left
  have hPH : P ≤ H := le_sup_right
  have hcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hXp : IsPStar p ↥(X.subgroupOf H) :=
    IsPStar.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH).symm hX
  have hPp : IsPGroup p ↥(P.subgroupOf H) := hP.comap_subtype
  have hsup : X.subgroupOf H ⊔ P.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXH hPH]
    exact Subgroup.subgroupOf_self H
  have hnorm : P.subgroupOf H ≤ normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro m
    exact mem_normalizer_iff.mp (hPX hg) (m : G)
  have key := h ↥H (X.subgroupOf H) (P.subgroupOf H) (hcard ▸ hn) hXp hPp hnorm hsup
  have hbound : (⁅X.subgroupOf H, P.subgroupOf H⁆ ⊔ (X.subgroupOf H ⊓
      centralizer ((P.subgroupOf H : Subgroup ↥H) : Set ↥H))).map H.subtype ≤
        ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH,
      Subgroup.map_subgroupOf_eq_of_le hPH]
    refine sup_le_sup_left ?_ _
    refine le_inf ?_ ((Subgroup.map_mono inf_le_right).trans (l55_map_centralizer_le hPH))
    exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_subgroupOf_eq_of_le hXH).le
  intro x hx
  have hx' : (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H := hx
  exact hbound (Subgroup.mem_map_of_mem H.subtype (key hx'))

theorem l55_isPStar_map {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) {G G' : Type} [Group G]
    [Finite G] [Group G'] (f : G →* G') (X : Subgroup G) (hX : IsPStar p ↥X) :
    IsPStar p ↥(X.map f) := by
  have := h52ii ↥X (f.subgroupMap X).ker hX
  exact IsPStar.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective _
    (f.subgroupMap_surjective X)) this

theorem l55_card_map_lt {G : Type} [Group G] [Finite G] {X N : Subgroup G} [N.Normal] (hNX : N ≤ X)
    (hN : N ≠ ⊥) : Nat.card ↥(X.map (QuotientGroup.mk' N)) < Nat.card ↥X := by
  have hsurj := (QuotientGroup.mk' N).subgroupMap_surjective X
  have hle : Nat.card ↥(X.map (QuotientGroup.mk' N)) ≤ Nat.card ↥X :=
    Nat.card_le_card_of_surjective _ hsurj
  by_contra hlt
  have hge : Nat.card ↥X ≤ Nat.card ↥(X.map (QuotientGroup.mk' N)) := not_lt.mp hlt
  have hinj := (hsurj.bijective_of_nat_card_le hge).1
  obtain ⟨⟨n, hn⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN
  have h1 : (QuotientGroup.mk' N).subgroupMap X ⟨(n : G), hNX hn⟩ =
      (QuotientGroup.mk' N).subgroupMap X 1 := by
    apply Subtype.ext
    show QuotientGroup.mk' N (n : G) = QuotientGroup.mk' N 1
    rw [map_one]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have h2 := hinj h1
  apply hn1
  apply Subtype.ext
  have := congrArg Subtype.val h2
  simpa using this

theorem l55_of_map_le {G : Type} [Group G] {X R N : Subgroup G} [N.Normal] (hNR : N ≤ R)
    (h : X.map (QuotientGroup.mk' N) ≤ R.map (QuotientGroup.mk' N)) : X ≤ R := by
  intro x hx
  have h1 : (QuotientGroup.mk' N) x ∈ R.map (QuotientGroup.mk' N) :=
    h (Subgroup.mem_map_of_mem _ hx)
  have h2 : x ∈ (R.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := h1
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNR] at h2
  exact h2

end CFSG.GH74.GLS.Balance
