module

public import CFSG.Sporadic.SuzOddCore.CompQuot
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.ConjClassCount
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.CatFC.ResidualA8

open CFSG CFSG.LocalCores Subgroup

@[expose] def cycleThreeFive : Equiv.Perm (Fin 8) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) *
    (Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7)

theorem cycleThreeFive_mem : cycleThreeFive ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

set_option maxRecDepth 100000 in
theorem cycleThreeFive_pow_fifteen : cycleThreeFive ^ 15 = 1 := by decide

set_option maxRecDepth 100000 in
theorem cycleThreeFive_pow_three : cycleThreeFive ^ 3 ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem cycleThreeFive_pow_five : cycleThreeFive ^ 5 ≠ 1 := by decide

theorem orderOf_cycleThreeFive : orderOf cycleThreeFive = 15 := by
  have h1 : orderOf cycleThreeFive ∣ 15 := orderOf_dvd_of_pow_eq_one cycleThreeFive_pow_fifteen
  have h2 : ¬ orderOf cycleThreeFive ∣ 3 := fun h =>
    cycleThreeFive_pow_three (orderOf_dvd_iff_pow_eq_one.1 h)
  have h3 : ¬ orderOf cycleThreeFive ∣ 5 := fun h =>
    cycleThreeFive_pow_five (orderOf_dvd_iff_pow_eq_one.1 h)
  have h4 : orderOf cycleThreeFive ∈ Nat.divisors 15 := Nat.mem_divisors.2 ⟨h1, by norm_num⟩
  have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [hd] at h4
  simp only [Finset.mem_insert, Finset.mem_singleton] at h4
  rcases h4 with h | h | h | h
  · rw [h] at h2
    exact absurd (one_dvd 3) h2
  · rw [h] at h2
    exact absurd (dvd_refl 3) h2
  · rw [h] at h3
    exact absurd (dvd_refl 5) h3
  · exact h

theorem alt_eight_exists_order_fifteen : ∃ g : alternatingGroup (Fin 8), orderOf g = 15 := by
  refine ⟨⟨cycleThreeFive, cycleThreeFive_mem⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_cycleThreeFive

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 8)
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h8 : Nat.factorial 8 = 40320 := by decide
  omega

theorem card_carrier_mul_card_centralizer {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (centralizer ({x} : Set G)) =
      Nat.card G := by
  rw [← CFSG.EvenSporadicStandard.SuzOuter.card_conj_mul_card_centralizer x]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c⁻¹, by rw [← hc]; group⟩
  · rintro ⟨c, hc⟩
    exact ⟨c⁻¹, by rw [hc]; group⟩

theorem no_order_fifteen_of_classes {G : Type*} [Group G] [Finite G] {c : ℕ}
    (e : Fin c ≃ ConjClasses G) (s : Fin c → ℕ) (hs : ∀ l, Nat.card (e l).carrier = s l)
    (l₀ : Fin c) (hl₀ : e l₀ = ConjClasses.mk 1)
    (h : ∀ l, l ≠ l₀ → ¬ 15 ∣ Nat.card G / s l) (g : G) : orderOf g ≠ 15 := by
  intro hg
  obtain ⟨l, hl⟩ := e.surjective (ConjClasses.mk g)
  by_cases hl0 : l = l₀
  · subst hl0
    rw [hl₀, ConjClasses.mk_eq_mk_iff_isConj] at hl
    have hg1 : g = 1 := isConj_one_right.1 hl
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have hcard := card_carrier_mul_card_centralizer g
    rw [← hl, hs l] at hcard
    have hn : 0 < Nat.card G := Nat.card_pos
    have hpos : 0 < s l := by
      rcases Nat.eq_zero_or_pos (s l) with h0 | h0
      · rw [h0, zero_mul] at hcard
        omega
      · exact h0
    have hdiv : Nat.card G / s l = Nat.card (centralizer ({g} : Set G)) :=
      Nat.div_eq_of_eq_mul_right hpos hcard.symm
    have hmem : g ∈ centralizer ({g} : Set G) := mem_centralizer_singleton_iff.2 rfl
    have h15 : 15 ∣ Nat.card (centralizer ({g} : Set G)) := by
      have h1 := orderOf_dvd_natCard (⟨g, hmem⟩ : centralizer ({g} : Set G))
      rw [Subgroup.orderOf_mk, hg] at h1
      exact h1
    exact h l hl0 (hdiv ▸ h15)

theorem not_equiv_alt_eight_of_classes {G : Type*} [Group G] [Finite G] {c : ℕ}
    (e : Fin c ≃ ConjClasses G) (s : Fin c → ℕ) (hs : ∀ l, Nat.card (e l).carrier = s l)
    (l₀ : Fin c) (hl₀ : e l₀ = ConjClasses.mk 1)
    (h : ∀ l, l ≠ l₀ → ¬ 15 ∣ Nat.card G / s l) :
    ¬ Nonempty (G ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨φ⟩
  obtain ⟨a, ha⟩ := alt_eight_exists_order_fifteen
  exact no_order_fifteen_of_classes e s hs l₀ hl₀ h (φ.symm a)
    (by rw [MulEquiv.orderOf_eq]; exact ha)

theorem quotient_center_equiv_of_component {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (D : Subgroup K) (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E} (hB : IsComponent B) :
    Nonempty (B ⧸ center B ≃* D) := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := by rw [← Subgroup.map_commutator, hBB]
  have hle : B.map ρ ≤ D := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (CFSG.Sporadic.SuzOddCore.commutator_le_of_index_two hDi)
  have hsubD : ((B.map ρ).subgroupOf D).IsSubnormal := (hsub.map hρ).subgroupOf
  rcases hsubD.eq_bot_or_top_of_isSimpleGroup hDs with h | h
  · exfalso
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : (⟨ρ b, hle ⟨b, hb, rfl⟩⟩ : D) ∈ (B.map ρ).subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · have hBD : B.map ρ = D := by
      apply le_antisymm hle
      intro d hd
      have : (⟨d, hd⟩ : D) ∈ (B.map ρ).subgroupOf D := h ▸ Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at this
    set ρB : B →* K := ρ.comp B.subtype
    have hrange : ρB.range = D := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hBD]
    have hkerB : ρB.ker = center B := by
      apply le_antisymm
      · rcases quasisimple_normal_subgroups hq (ρB.normal_ker) with h1 | h1
        · exfalso
          obtain ⟨a, b, hab⟩ := hDnc
          obtain ⟨x, hx⟩ := (hrange ▸ a.2 : (a : K) ∈ ρB.range)
          have hx1 : x ∈ ρB.ker := h1 ▸ Subgroup.mem_top x
          rw [MonoidHom.mem_ker, hx] at hx1
          apply hab
          have : a = 1 := Subtype.ext hx1
          rw [this, one_mul, mul_one]
        · exact h1
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hzD : ρB z ∈ D := by rw [← hrange]; exact ⟨z, rfl⟩
        have hc : (⟨ρB z, hzD⟩ : D) ∈ center D := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          have := CFSG.Sporadic.SuzOddCore.center_map_le ρ B hz (g : K) (by rw [hBD]; exact g.2)
          exact this.symm
        rw [CFSG.Sporadic.SuzOddCore.center_eq_bot_of_simple' hDs hDnc, Subgroup.mem_bot] at hc
        exact congrArg Subtype.val hc
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerB.symm).trans
      ((QuotientGroup.quotientKerEquivRange ρB).trans (MulEquiv.subgroupCongr hrange))⟩

@[expose] def NoAltEightComponent (G : Type*) [Group G] : Prop :=
  ∀ B : Subgroup G, IsComponent B → ¬ Nonempty (B ⧸ center B ≃* alternatingGroup (Fin 8))

theorem NoAltEightComponent.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : NoAltEightComponent H) : NoAltEightComponent G := by
  rintro B hB ⟨φ⟩
  let ψ : B ⧸ center B ≃* (B.map e.toMonoidHom) ⧸ center (B.map e.toMonoidHom) :=
    QuotientGroup.congr _ _ (B.equivMapOfInjective e.toMonoidHom e.injective)
      (Subgroup.map_center_eq _)
  exact h (B.map e.toMonoidHom) (isComponent_map_mulEquiv e hB) ⟨ψ.symm.trans φ⟩

theorem NoAltEightComponent.of_no_component {G : Type*} [Group G]
    (h : ∀ B : Subgroup G, ¬ IsComponent B) : NoAltEightComponent G :=
  fun B hB _ => h B hB

theorem NoAltEightComponent.of_surjective_simple {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (D : Subgroup K) (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) (hD : ¬ Nonempty (D ≃* alternatingGroup (Fin 8))) :
    NoAltEightComponent E := by
  rintro B hB ⟨φ⟩
  obtain ⟨ψ⟩ := quotient_center_equiv_of_component ρ hρ hker D hDi hDs hDnc hB
  exact hD ⟨ψ.symm.trans φ⟩

end CFSG.ComponentClassification.CatFC.ResidualA8
