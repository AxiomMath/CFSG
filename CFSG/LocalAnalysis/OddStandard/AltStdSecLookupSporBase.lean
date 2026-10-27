module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

theorem IsLargeAlt.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsLargeAlt Y') : IsLargeAlt Y := by
  obtain ⟨m, hm, ⟨f⟩⟩ := h
  exact ⟨m, hm, ⟨e.trans f⟩⟩

theorem lookup_factorial_div_two_ne {k c : ℕ} (h1 : k.factorial / 2 < c)
    (h2 : c < (k + 1).factorial / 2) (m : ℕ) : m.factorial / 2 ≠ c := by
  intro h
  rcases le_or_gt m k with hmk | hmk
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le hmk)
    omega
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le (show k + 1 ≤ m by omega))
    omega

theorem lookup_factorial_div_two_ne_of_lt {c m : ℕ} (hc : c < 181440) (hm : 9 ≤ m) :
    m.factorial / 2 ≠ c := by
  have hpos : 0 < m.factorial / 2 :=
    Nat.div_pos ((by omega : 2 ≤ m).trans (Nat.self_le_factorial m)) (by norm_num)
  have h : 181440 ≤ m.factorial / 2 := Nat.le_of_dvd hpos (dvd_factorial_div_two hm)
  omega

theorem not_isLargeAlt_of_card_quotient {Y : Type} [Group Y] {c : ℕ}
    (hc : ∀ m : ℕ, 9 ≤ m → m.factorial / 2 ≠ c) (h : Nat.card (Y ⧸ center Y) = c) :
    ¬ IsLargeAlt Y := by
  rintro ⟨m, hm, ⟨e⟩⟩
  have hz : center Y = ⊥ := center_eq_bot_of_alt (by omega) e
  have hq : Nat.card (Y ⧸ center Y) = Nat.card Y :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).toEquiv
  exact hc m hm (by rw [← h, hq, card_eq_of_equiv_alt (by omega) e])

theorem not_isLargeAlt_of_card {Y : Type} [Group Y] {c : ℕ}
    (hc : ∀ m : ℕ, 9 ≤ m → m.factorial / 2 ≠ c) (h : Nat.card Y = c) : ¬ IsLargeAlt Y := by
  rintro ⟨m, hm, ⟨e⟩⟩
  exact hc m hm (by rw [← h, card_eq_of_equiv_alt (by omega) e])

theorem false_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ β : MulAut (NativeSporadic.Carrier s), β ∈ inner (NativeSporadic.Carrier s))
    {G : Type} [Group G] (e : G ≃* NativeSporadic.Carrier s) {α : MulAut G} (hα : α ∉ inner G) :
    False :=
  CFSG.ComponentClassification.RestrictedStd.Spor.transportAut_not_mem_inner e hα (hinner _)

@[expose] def NoLargeAltComponents (s : TauCeti.SporadicName) : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → ∀ B : Subgroup (centralizer ({t} : Set G)), IsComponent B →
        ¬ IsLargeAlt B) ∧
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        ∀ B : Subgroup (fixSub α), IsComponent B → ¬ IsLargeAlt B

theorem false_of_noLargeAlt {s : TauCeti.SporadicName} (h : NoLargeAltComponents s) {S : Type}
    [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B) (hAlt : IsLargeAlt B) : False := by
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨B', hB', ⟨φ⟩⟩ := isComponent_map_fixedSubgroup_conj ht hB
    exact h.1 S inferInstance ⟨e⟩ t (lookup_orderOf_eq_two_of_conj hna hσ2 hσ1 ht) B' hB'
      (IsLargeAlt.of_mulEquiv φ hAlt)
  · have hfix : fixedSubgroup σ = fixSub σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix
    exact h.2 S inferInstance hna ⟨e⟩ σ hσ2 hout (B.map φ.toMonoidHom)
      (CFSG.LocalCores.isComponent_map_mulEquiv φ hB)
      (IsLargeAlt.of_mulEquiv (B.equivMapOfInjective φ.toMonoidHom φ.injective).symm hAlt)

end CFSG.OddStandard.AltStdSec
