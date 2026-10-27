module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Base

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec125_sup_mulEquiv {H : Type*} [Group H] {T Y : Subgroup H}
    (hc : ∀ a ∈ T, ∀ b ∈ Y, a * b = b * a) (hd : T ⊓ Y = ⊥) :
    Nonempty (↥(T ⊔ Y) ≃* ↥T × ↥Y) := by
  have hcom : ∀ (a : ↥T) (b : ↥Y), Commute (T.subtype a) (Y.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod T.subtype Y.subtype hcom) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨T.subtype_injective, Y.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr hd
  have hrange : (MonoidHom.noncommCoprod T.subtype Y.subtype hcom).range = T ⊔ Y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

theorem sec125_zpowers_equiv {H : Type*} [Group H] {g : H} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    Nonempty (↥(zpowers g) ≃* Multiplicative (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  refine ⟨mulEquivOfPrimeCardEq (p := 2) ?_ ?_⟩
  · rw [Nat.card_zpowers, ho]
  · rw [Nat.card_congr Multiplicative.toAdd]
    simp

theorem sec125_equiv_of_split {H : Type*} [Group H] {g : H} {P Y : Subgroup H}
    (hg2 : g * g = 1) (hg1 : g ≠ 1) (hgP : g ∈ P) (hYP : Y ≤ P)
    (hc : ∀ y ∈ Y, g * y = y * g) (hne : ∀ y ∈ Y, y ≠ g)
    (hP : ∀ p ∈ P, p ∈ Y ∨ ∃ y ∈ Y, p = y * g) :
    Nonempty (↥P ≃* Multiplicative (ZMod 2) × ↥Y) := by
  have hmem : ∀ c ∈ zpowers g, c = 1 ∨ c = g := by
    intro c hc'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    have ho : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    rw [← zpow_mod_orderOf, ho]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  have hdisj : zpowers g ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro c hc'
    obtain ⟨hcT, hcY⟩ := Subgroup.mem_inf.mp hc'
    rcases hmem c hcT with h1 | h1
    · simp [h1]
    · exact absurd h1 (hne c hcY)
  have hPeq : zpowers g ⊔ Y = P := by
    refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr hgP) hYP) ?_
    intro p hp
    rcases hP p hp with hpY | ⟨y, hy, rfl⟩
    · exact Subgroup.mem_sup_right hpY
    · exact mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  have hcomm : ∀ a ∈ zpowers g, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hgb : Commute g b := hc b hb
    exact (hgb.zpow_left k).eq
  obtain ⟨e1⟩ := sec125_sup_mulEquiv hcomm hdisj
  obtain ⟨e2⟩ := sec125_zpowers_equiv hg2 hg1
  exact ⟨(MulEquiv.subgroupCongr hPeq.symm).trans (e1.trans (e2.prodCongr (MulEquiv.refl _)))⟩

variable {G : Type} [Group G]

theorem sec125_autIn_equiv {V X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hinj : ∀ x ∈ X, x ∈ centralizer (V : Set G) → x = 1) :
    Nonempty (↥(autIn X V) ≃* ↥X) := by
  let φ : ↥X →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ normalizer (V : Set G) := hXN x.2
    have h1 : betaOf V x = 1 := by
      rw [sec127_betaOf_of_mem hxN]
      exact hx
    exact Subtype.ext (hinj x x.2 ((sec127_betaOf_eq_one_iff hxN).mp h1))
  have hrange : φ.range = autIn X V := by
    ext σ
    rw [sec127_mem_autIn_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hXN x.2, (sec127_betaOf_of_mem (hXN x.2)).symm⟩
    · rintro ⟨n, hnX, hnN, rfl⟩
      exact ⟨⟨n, hnX⟩, (sec127_betaOf_of_mem hnN).symm⟩
  exact ⟨((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.OddStandard.SmallF3.Omega
