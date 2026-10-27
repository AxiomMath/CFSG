module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Cent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Outer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace U52

theorem nonempty_mulEquiv_X₀ {X : Type} [Group X] (h : LieModel X .PSU 5 2 1) :
    Nonempty (X ≃* X₀) := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
      rw [← Nat.card_eq_fintype_card, hK, CFSG.Fischer.F4.card]
      norm_num
    exact ⟨e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 5 (2 ^ 1))⟩
  all_goals exact absurd h0 (by norm_num)

variable {G : Type} [Group G]

theorem conjNormal_injective {N : Subgroup G} [N.Normal] (hC : centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : g ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [hC, mem_bot] at hgC
  exact hgC

theorem fixedSubgroup_conjNormal (N : Subgroup G) [N.Normal] (t : G) :
    fixedSubgroup (MulAut.conjNormal t : MulAut N) = (centralizer ({t} : Set G)).subgroupOf N := by
  ext x
  change MulAut.conjNormal t x = x ↔ _
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  constructor
  · intro h
    calc (x : G) * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

end U52

theorem cf81X11U52_holds :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
      centralizer (N : Set G) = ⊥ → Blueprint.LieModel ↥N .PSU 5 2 1 → ∀ t : G, orderOf t = 2 →
        Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 82944 ∨
          Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 4608 ∨
          Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 720 := by
  intro G _ _ N hN hC hm t ht
  have := hN
  by_cases htN : t ∈ N
  ·
    obtain ⟨e⟩ := U52.nonempty_mulEquiv_X₀ hm
    set a : ↥N := ⟨t, htN⟩
    have ha : orderOf (e a) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ht
    have h1 : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) =
        Nat.card (centralizer ({e a} : Set U52.X₀)) := by
      rw [← U52.card_centralizer_congr e a, U52.card_centralizer_subtype]
    rw [h1]
    rcases U52.card_centralizer_of_orderOf_eq_two ha with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  ·
    right
    right
    set β : MulAut N := MulAut.conjNormal t
    have hβ : β ∉ inner ↥N := by
      rintro ⟨s, hs⟩
      have hc : MulAut.conjNormal (s : G) = (MulAut.conjNormal t : MulAut N) := by
        rw [MulAut.conjNormal_val]
        exact hs
      apply htN
      rw [← U52.conjNormal_injective hC hc]
      exact s.2
    have hβ1 : β ≠ 1 := fun h1 => hβ (h1 ▸ (inner ↥N).one_mem)
    have hβ2 : orderOf β = 2 := by
      refine orderOf_eq_prime ?_ hβ1
      rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    have hcard : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = Nat.card (fixedSubgroup β) := by
      rw [U52.fixedSubgroup_conjNormal, inf_comm, ← subgroupOf_map_subtype]
      exact Nat.card_congr
        (((centralizer ({t} : Set G)).subgroupOf N).equivMapOfInjective N.subtype
          N.subtype_injective).symm.toEquiv
    rw [hcard]
    exact U52.card_fixedSubgroup_of_not_mem_inner hm β hβ2 hβ

end CFSG.ComponentClassification.GSThmB
