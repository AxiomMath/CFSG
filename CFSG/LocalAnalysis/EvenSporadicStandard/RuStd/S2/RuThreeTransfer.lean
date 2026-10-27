module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

@[expose] def ThreeAt {G : Type} [Group G] (r : G) : Prop :=
  Nat.card (centralizer ({r} : Set G)) = 2160 ∧
  (∀ N : Subgroup G, N ≤ centralizer ({r} : Set G) →
    (∀ x ∈ centralizer ({r} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → Odd (Nat.card N) →
      N ≤ zpowers r) ∧
  (∃ φ : ↥(centralizer ({r} : Set G)) →* M10, Function.Surjective φ ∧
    φ.ker = (zpowers r).subgroupOf (centralizer ({r} : Set G))) ∧
  (∃ v ∈ centralizer ({r} : Set G), orderOf v = 2 ∧
    Nat.card (centralizer ({v} : Set G)) = 245760)

theorem ruThreeFacts_of_threeAt {Y : Type} [Group Y]
    (h : ∀ r : Y, orderOf r = 3 → ThreeAt r) : RuThreeFacts Y where
  card r hr := (h r hr).1
  oddCore r hr N hN hnorm hodd := (h r hr).2.1 N hN hnorm hodd
  quot r hr := (h r hr).2.2.1
  inv2A r hr := (h r hr).2.2.2

theorem threeAt_of_ruThreeFacts {Y : Type} [Group Y] (h : RuThreeFacts Y) {r : Y}
    (hr : orderOf r = 3) : ThreeAt r :=
  ⟨h.card r hr, fun N hN hnorm hodd => h.oddCore r hr N hN hnorm hodd, h.quot r hr, h.inv2A r hr⟩

section Map

variable {X Y : Type} [Group X] [Group Y]

theorem ThreeAt.map (e : X ≃* Y) {r : X} (h : ThreeAt r) : ThreeAt (e r) := by
  obtain ⟨hcard, hodd, ⟨φ, hφs, hφk⟩, v, hv, hv2, hvc⟩ := h
  have hC : centralizer ({e r} : Set Y) = (centralizer ({r} : Set X)).map e.toMonoidHom :=
    centralizer_singleton_map e r
  refine ⟨by rw [card_centralizer_equiv, hcard], ?_, ?_, ⟨e v, ?_, ?_, ?_⟩⟩
  · intro N hN hnorm hNodd
    have hN' : N.comap e.toMonoidHom ≤ centralizer ({r} : Set X) := by
      intro x hx
      have hx' : e x ∈ centralizer ({e r} : Set Y) := hN hx
      rw [hC] at hx'
      obtain ⟨y, hy, hye⟩ := hx'
      rwa [← e.injective hye]
    have key := hodd (N.comap e.toMonoidHom) hN' (by
      intro x hx n hn
      have hx' : e x ∈ centralizer ({e r} : Set Y) := by rw [hC]; exact ⟨x, hx, rfl⟩
      simpa using hnorm (e x) hx' (e n) hn) (by
      have : Nat.card (N.comap e.toMonoidHom) = Nat.card N :=
        Nat.card_congr (e.toEquiv.subtypeEquiv fun x => Iff.rfl)
      rwa [this])
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hxN : x ∈ N.comap e.toMonoidHom := hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (key hxN)
    exact mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
  · let ψ : ↥(centralizer ({e r} : Set Y)) →* ↥(centralizer ({r} : Set X)) :=
      ((e.symm : Y →* X).comp (centralizer ({e r} : Set Y)).subtype).codRestrict _ (by
        intro y
        have hy : (y : Y) ∈ (centralizer ({r} : Set X)).map e.toMonoidHom := hC ▸ y.2
        obtain ⟨x, hx, hxe⟩ := hy
        show e.symm (y : Y) ∈ centralizer ({r} : Set X)
        rw [← hxe]
        simpa using hx)
    have hψs : Function.Surjective ψ := by
      intro x
      refine ⟨⟨e x, ?_⟩, ?_⟩
      · rw [hC]
        exact ⟨x, x.2, rfl⟩
      · apply Subtype.ext
        simp [ψ]
    refine ⟨φ.comp ψ, hφs.comp hψs, ?_⟩
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    have hy1 : ψ y ∈ φ.ker ↔ φ (ψ y) = 1 := MonoidHom.mem_ker
    rw [← hy1, hφk, Subgroup.mem_subgroupOf]
    show (e.symm (y : Y)) ∈ zpowers r ↔ (y : Y) ∈ zpowers (e r)
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
      exact mem_zpowers_iff.2 ⟨k, by rw [← map_zpow, hk]; simp⟩
    · intro hz
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
      exact mem_zpowers_iff.2 ⟨k, by
        apply e.injective
        rw [map_zpow, hk]
        simp⟩
  · rw [hC]
    exact ⟨v, hv, rfl⟩
  · rw [MulEquiv.orderOf_eq]
    exact hv2
  · rw [card_centralizer_equiv]
    exact hvc

theorem RuThreeFacts.of_mulEquiv (e : X ≃* Y) (h : RuThreeFacts X) : RuThreeFacts Y :=
  ruThreeFacts_of_threeAt fun r' hr' => by
    have hr : orderOf (e.symm r') = 3 := by rwa [MulEquiv.orderOf_eq]
    have := (threeAt_of_ruThreeFacts h hr).map e
    rwa [MulEquiv.apply_symm_apply] at this

end Map

section Zpowers

variable {G : Type} [Group G]

theorem centralizer_singleton_eq_of_zpowers_eq {r r' : G} (h : zpowers r = zpowers r') :
    centralizer ({r} : Set G) = centralizer ({r'} : Set G) := by
  have key : ∀ {a b : G}, b ∈ zpowers a →
      centralizer ({a} : Set G) ≤ centralizer ({b} : Set G) := by
    intro a b hb x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute x a from hx) k)
  exact le_antisymm (key (h ▸ mem_zpowers r')) (key (h ▸ mem_zpowers r))

theorem ThreeAt.of_zpowers_eq {r r' : G} (h : zpowers r = zpowers r') (hr : ThreeAt r) :
    ThreeAt r' := by
  have hC := centralizer_singleton_eq_of_zpowers_eq h
  unfold ThreeAt at hr ⊢
  rw [← hC, ← h]
  exact hr

end Zpowers

end CFSG.EvenSporadicStandard.RuStd.S2
