module

public import CFSG.GH74.Generic.S1.Exo.Q3Solv
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem odd_free_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ N : Subgroup B, N.Normal → Odd (Nat.card N) → N = ⊥) :
    ∀ N : Subgroup A, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  have hNn : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN e.toMonoidHom e.surjective
  have hcard : Nat.card ↥(N.map e.toMonoidHom) = Nat.card ↥N :=
    (Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have h1 : N.map e.toMonoidHom = ⊥ := h _ hNn (by rw [hcard]; exact hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).1 h1

theorem solv_balance_barC (hSB : Balance.SolvableL2PrimeBalance) {c x : G}
    (hxc : x ∈ centralizer ({c} : Set G)) (hx2 : orderOf x = 2) {J : Subgroup G}
    (hJc : J ≤ centralizer ({c} : Set G)) (hJx : J ≤ centralizer ({x} : Set G))
    (hinj : Function.Injective ((proj c).comp (Subgroup.inclusion hJc)))
    (hsub : ((J.subgroupOf (centralizer ({c} : Set G))).subgroupOf
      (centralizer ({(⟨x, hxc⟩ : ↥(centralizer ({c} : Set G)))} :
        Set ↥(centralizer ({c} : Set G))))).IsSubnormal)
    (hsl : Nonempty (↥J ≃* SL(2, ZMod 3)))
    (hodd : ∀ N : Subgroup ↥J, N.Normal → Odd (Nat.card N) → N = ⊥) :
    (∀ j ∈ S45.barSub c J, (∃ k : ℕ, j ^ (2 ^ k) = 1) → j ∈ pCore 2 (CentralizerBar c)) ∨
      ∃ N : Subgroup (CentralizerBar c), IsComponent N ∧
        ∀ j ∈ S45.barSub c J, (∃ k : ℕ, j ^ (2 ^ k) = 1) → j ∈ N := by
  classical
  set X : Subgroup G := centralizer ({c} : Set G) with hX
  set xX : ↥X := ⟨x, hxc⟩ with hxX
  have hxX2 : orderOf xX = 2 := by rw [hxX, Subgroup.orderOf_mk]; exact hx2
  set JX : Subgroup ↥X := J.subgroupOf X with hJX
  have hJXle : JX ≤ centralizer ({xX} : Set ↥X) := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := mem_centralizer_singleton_iff.1 (hJx hj)
    exact this
  have e : ↥JX ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJc
  obtain ⟨σ⟩ := hsl
  obtain ⟨V, hV, hJV⟩ := exists_solvTwoComp_of_subnormal_sl23 (X := ↥X) (x := xX) (J := JX) hJXle hsub
    ⟨e.trans σ⟩ (odd_free_of_mulEquiv e hodd)
  have hmain := hSB ↥X xX hxX2 V hV
  have hlift : ∀ j ∈ S45.barSub c J, (∃ k : ℕ, j ^ (2 ^ k) = 1) →
      ∃ (g : ↥X) (hgV : g ∈ V), (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ proj c g = j := by
    intro j hj ⟨k, hk⟩
    obtain ⟨g, hg, hgJ, hgj⟩ := S45.mem_barSub.1 hj
    have hgJX : (⟨g, hg⟩ : ↥X) ∈ JX := hgJ
    refine ⟨⟨g, hg⟩, hJV hgJX, ⟨k, ?_⟩, hgj⟩
    have h1 : ((proj c).comp (Subgroup.inclusion hJc)) ((⟨g, hgJ⟩ : ↥J) ^ (2 ^ k)) =
        ((proj c).comp (Subgroup.inclusion hJc)) 1 := by
      rw [map_pow, map_one]
      change (proj c ⟨g, hg⟩) ^ (2 ^ k) = 1
      rw [hgj]
      exact hk
    have h2 := hinj h1
    have h3 : g ^ (2 ^ k) = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    exact h3
  rcases hmain with h | ⟨L, hL, -, hLle⟩
  · left
    intro j hj hjk
    obtain ⟨g, hgV, ⟨k, hk⟩, hgj⟩ := hlift j hj hjk
    have hres : g ∈ oPrimeResidualOf 2 V := by
      refine ⟨⟨g, hgV⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
      apply Subtype.ext
      exact hk
    have h1 := h hres
    rw [← hgj]
    exact h1
  · right
    obtain ⟨K, hK, -, hLK, -⟩ := hL
    refine ⟨K, hK, ?_⟩
    intro j hj hjk
    obtain ⟨g, hgV, ⟨k, hk⟩, hgj⟩ := hlift j hj hjk
    have hres : g ∈ oPrimeResidualOf 2 V := by
      refine ⟨⟨g, hgV⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
      apply Subtype.ext
      exact hk
    have h1 := hLle hres
    rw [← hLK, ← hgj]
    exact ⟨g, h1, rfl⟩

end CFSG.GH74.Generic.S1.Exo
