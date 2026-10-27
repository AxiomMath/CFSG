module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142CMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

@[expose] def CPlus (G : Type) [Group G] : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧
    (IsChevSimple 2 G ∨ catalogIs G (onLie (· = TauCeti.LieTypeIndex.tits)))

@[reducible, expose] def CompTypesCyc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 →
      ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (I142.centFix (Subgroup.zpowers β)) →
        CPlus (↥K ⧸ Subgroup.center ↥K)

@[reducible, expose] def TitsCentSolv : Prop :=
  ∀ (T : Type) [Group T] [Finite T], catalogIs T (onLie (· = TauCeti.LieTypeIndex.tits)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ F : Subgroup (MulAut T), IsElemAbelian p F → F ≠ ⊥ →
      Group.IsSolvable ↥(I142.centFix F)

section Cert


theorem cyclic_good {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (β : MulAut S) (hβ : β ^ p = 1) :
    ∀ P : Subgroup S, P ≤ I142.centFix (Subgroup.zpowers β) → ⁅P, P⁆ = P →
      P ≤ GLALayer (I142.centFix (Subgroup.zpowers β)) := by
  by_cases hidx : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ p ≠ idx.1.characteristic
  · obtain ⟨idx, hiso, hpq⟩ := hidx
    exact I142.lieSemisimpleCentE_zpowers_of_lie S hS hnc idx hiso hp hp2 hpq β hβ
  · exact I142.residualCyc_holds S hS hnc hchev p hp hp2 (fun idx hiso => by
      by_contra hne
      exact hidx ⟨idx, hiso, fun h => hne h.symm⟩) β hβ

end Cert

theorem fixSubgroup_map_of_comm {S : Type} [Group S] {z e : MulAut S} (he : e * z = z * e) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup z := by
  have key : ∀ u : S, e (z u) = z (e u) := fun u => by
    have := congrArg (fun f : MulAut S => f u) he
    simpa [MulAut.mul_apply] using this
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : z y = y := hy
    show z (e y) = e y
    rw [← key, hy']
  · intro hx
    have hx' : z x = x := hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    show z (e.symm x) = e.symm x
    apply e.injective
    rw [key, e.apply_symm_apply]
    exact hx'

theorem card_range_lt {A G : Type*} [Group A] [Group G] [Finite A] [Finite G] (σ : A →* G) {z : A}
    (hz : z ≠ 1) (hzk : σ z = 1) : Nat.card σ.range < Nat.card A := by
  have h1 := Subgroup.card_ker_mul_card_range σ
  have hk : 1 < Nat.card σ.ker := by
    haveI : Nontrivial σ.ker := ⟨⟨⟨z, hzk⟩, 1, fun h => hz (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hr : 0 < Nat.card σ.range := Nat.card_pos
  rw [← h1]
  nlinarith

theorem isElemAbelian_range {A G : Type*} [Group A] [Group G] (p : ℕ) (σ : A →* G)
    (hc : ∀ a b : A, a * b = b * a) (he : ∀ a : A, a ^ p = 1) :
    IsElemAbelian p σ.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 u.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 v.2
    apply Subtype.ext
    show (u : G) * (v : G) = (v : G) * (u : G)
    rw [← ha, ← hb, ← map_mul, ← map_mul, hc]
  · intro u hu
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hu
    rw [← ha, ← map_pow, he, map_one]

end CFSG.LocalAnalysis.GLTheoremA.I142N
