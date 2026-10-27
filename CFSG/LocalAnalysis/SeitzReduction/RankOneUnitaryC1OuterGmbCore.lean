module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section Klein

variable {G : Type*} [Group G]

@[expose] def gmbKlein (u v : G) (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) :
    Subgroup G where
  carrier := {1, u, v, u * v}
  mul_mem' := by
    have hu' : ∀ z : G, u * (u * z) = z := fun z => by rw [← mul_assoc, hu, one_mul]
    have huv' : ∀ z : G, v * (u * z) = u * (v * z) := fun z => by
      rw [← mul_assoc, ← mul_assoc, huv]
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hu, hv, hu', huv', huv.symm]
  one_mem' := Set.mem_insert _ _
  inv_mem' := by
    have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have hv1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hu1]
    · simp [hv1]
    · simp [mul_inv_rev, hu1, hv1, huv]

theorem mem_gmbKlein {u v : G} {hu : u * u = 1} {hv : v * v = 1} {huv : u * v = v * u} {x : G} :
    x ∈ gmbKlein u v hu hv huv ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := Iff.rfl

theorem gmbKlein_mul_self {u v : G} {hu : u * u = 1} {hv : v * v = 1} {huv : u * v = v * u}
    {x : G} (hx : x ∈ gmbKlein u v hu hv huv) : x * x = 1 := by
  rcases mem_gmbKlein.mp hx with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact hu
  · exact hv
  · calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu, hv, one_mul]

theorem gmbKlein_card {u v : G} {hu : u * u = 1} {hv : v * v = 1} {huv : u * v = v * u}
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv1 : u ≠ v) : Nat.card (gmbKlein u v hu hv huv) = 4 := by
  have h1 : (1 : G) ≠ u * v := fun h => huv1 (by
    rw [← mul_one u, h, ← mul_assoc, hu, one_mul])
  have h2 : u ≠ u * v := fun h => hv1 (mul_left_cancel (h.symm.trans (mul_one u).symm))
  have h3 : v ≠ u * v := fun h => hu1 (mul_right_cancel (h.symm.trans (one_mul v).symm))
  have e : Nat.card (gmbKlein u v hu hv huv) = ({1, u, v, u * v} : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [e, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨huv1, h2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1.symm, h1⟩

theorem gmb_commute_of_mul_self {Q : Subgroup G} (hQ : ∀ x ∈ Q, x * x = 1) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  have hxy := hQ _ (Q.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hQ x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hQ y hy)
  have : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [this, mul_inv_rev, hx', hy']

theorem gmb_mem_four [Finite G] {Q : Subgroup G} (h4 : Nat.card Q = 4)
    (hQ : ∀ x ∈ Q, x * x = 1) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x ≠ y) {w : G} (hw : w ∈ Q) : w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  have hle : gmbKlein x y (hQ x hx) (hQ y hy) (gmb_commute_of_mul_self hQ hx hy) ≤ Q := by
    intro z hz
    rcases mem_gmbKlein.mp hz with rfl | rfl | rfl | rfl
    · exact Q.one_mem
    · exact hx
    · exact hy
    · exact Q.mul_mem hx hy
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, gmbKlein_card hx1 hy1 hxy])
  rw [← heq] at hw
  exact mem_gmbKlein.mp hw

end Klein

section Torus

variable {G : Type*} [Group G]

structure GmbTorus (Q H : Subgroup G) : Prop where
  le_normalizer : H ≤ normalizer (Q : Set G)
  odd_card : Odd (Nat.card H)
  comm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  fixed : ∀ x ∈ Q, (∀ h ∈ H, h * x * h⁻¹ = x) → x = 1
  irred : ∀ Y : Subgroup G, Y ≤ Q → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) → Y = ⊥ ∨ Y = Q

theorem gmb_mem_normalizer_of_conj [Finite G] {S : Subgroup G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have hinj : Function.Injective (fun x : S => (⟨g * x * g⁻¹, h x x.2⟩ : S)) := by
    intro a b hab
    have hab' : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hab'))
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨g * y * g⁻¹, hy⟩
  have hx' : g * (x : G) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hx
  rw [← mul_left_cancel (mul_right_cancel hx')]
  exact x.2

theorem GmbTorus.map {G' : Type*} [Group G'] {Q H : Subgroup G} (hH : GmbTorus Q H)
    (φ : G →* G') (hφ : Function.Injective φ) : GmbTorus (Q.map φ) (H.map φ) where
  le_normalizer := (Subgroup.map_mono hH.le_normalizer).trans (Subgroup.le_normalizer_map φ)
  odd_card := by
    rw [Subgroup.card_map_of_injective hφ]
    exact hH.odd_card
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hH.comm a ha b hb]
  fixed := by
    rintro _ ⟨x, hx, rfl⟩ hfix
    have : x = 1 := hH.fixed x hx fun g hg => hφ (by
      rw [map_mul, map_mul, map_inv]
      exact hfix _ ⟨g, hg, rfl⟩)
    rw [this, map_one]
  irred := by
    intro Y hYQ hYH
    have hY : Y.comap φ ≤ Q := by
      intro y hy
      obtain ⟨q, hq, hqy⟩ := hYQ hy
      rwa [hφ hqy] at hq
    have hinv : ∀ g ∈ H, ∀ y ∈ Y.comap φ, g * y * g⁻¹ ∈ Y.comap φ := by
      intro g hg y hy
      show φ (g * y * g⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact hYH _ ⟨g, hg, rfl⟩ _ hy
    have hYr : Y ≤ φ.range := hYQ.trans (Subgroup.map_le_range φ Q)
    rcases hH.irred _ hY hinv with h0 | h1
    · left
      rw [← Subgroup.map_comap_eq_self hYr, h0, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self hYr, h1]

@[expose] def GmbProp (Γ : Type*) [Group Γ] : Prop :=
  ∀ (Q : Sylow 2 Γ) (E : Subgroup Γ), E ≤ normalizer ((Q : Subgroup Γ) : Set Γ) →
    Odd (Nat.card E) → ∃ H : Subgroup Γ, E ≤ H ∧ GmbTorus (Q : Subgroup Γ) H

theorem gmb_transport {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : GmbProp Γ)
    {X : Type*} [Group X] [Finite X] {K : Subgroup X} (e : K ≃* Γ)
    {Q : Subgroup X} (hQ : IsSylowOf 2 Q K) {E : Subgroup X} (hEK : E ≤ K)
    (hEN : E ≤ normalizer (Q : Set X)) (hE : Odd (Nat.card E)) :
    ∃ H : Subgroup X, E ≤ H ∧ H ≤ K ∧ GmbTorus Q H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : Γ →* X := K.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := K.subtype_injective.comp e.symm.injective
  have hrange : K ≤ φ.range := fun x hx => ⟨e ⟨x, hx⟩, by simp [φ]⟩
  have hrange' : φ.range ≤ K := by
    rintro _ ⟨y, rfl⟩
    exact (e.symm y).2
  obtain ⟨hQK, hQp, hQi⟩ := (isSylowOf_iff (p := 2)).mp hQ
  have hQ0p : IsPGroup 2 (Q.comap φ) := hQp.comap_of_injective φ hφ
  have hQ0i : ¬ 2 ∣ (Q.comap φ).index := by
    have : (Q.comap φ).index = Q.relIndex K := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf, hφdef, ← Subgroup.comap_comap,
        Subgroup.index_comap_of_surjective _ e.symm.surjective]
    rw [this]
    exact hQi
  have hEN0 : E.comap φ ≤ normalizer ((Q.comap φ : Subgroup Γ) : Set Γ) :=
    (Subgroup.comap_mono hEN).trans (Subgroup.le_normalizer_comap φ)
  have hEmap : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self (hEK.trans hrange)
  have hE0 : Odd (Nat.card (E.comap φ)) := by
    rw [← Subgroup.card_map_of_injective hφ, hEmap]
    exact hE
  obtain ⟨H₀, hEH₀, hH₀⟩ := hΓ (hQ0p.toSylow hQ0i) (E.comap φ)
    (by rw [IsPGroup.toSylow_coe]; exact hEN0) hE0
  rw [IsPGroup.toSylow_coe] at hH₀
  refine ⟨H₀.map φ, ?_, (Subgroup.map_le_range φ H₀).trans hrange', ?_⟩
  · rw [← hEmap]
    exact Subgroup.map_mono hEH₀
  · have h := hH₀.map φ hφ
    rwa [Subgroup.map_comap_eq_self (hQK.trans hrange)] at h

end Torus

section KleinCriterion

variable {G : Type*} [Group G] [Finite G]

theorem gmb_centralizes_of_fix {Q : Subgroup G} (h4 : Nat.card Q = 4) (hQ : ∀ x ∈ Q, x * x = 1)
    {g : G} (hgN : g ∈ normalizer (Q : Set G)) (hgo : Odd (orderOf g)) {x : G} (hx : x ∈ Q)
    (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ = x) : ∀ y ∈ Q, g * y * g⁻¹ = y := by
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, mul_inv_cancel]
  by_cases hxy : x = y
  · rw [← hxy]
    exact hgx
  have hz : g * y * g⁻¹ ∈ Q := (mem_normalizer_iff.mp hgN y).mp hy
  rcases gmb_mem_four h4 hQ hx hy hx1 hy1 hxy hz with h | h | h | h
  · exfalso
    apply hy1
    have h' : g * y = g * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h
    exact mul_left_cancel h'
  · exfalso
    apply hxy
    have h' : g * y * g⁻¹ = g * x * g⁻¹ := h.trans hgx.symm
    exact (mul_left_cancel (mul_right_cancel h')).symm
  · exact h
  ·
    have hsq : (g * g) * y * (g * g)⁻¹ = y := by
      calc (g * g) * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [h]
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = x * (x * y) := by rw [hgx, h]
        _ = (x * x) * y := by group
        _ = y := by rw [hQ x hx, one_mul]
    have hc2 : Commute (g ^ 2) y := by
      show g ^ 2 * y = y * g ^ 2
      rw [sq]
      calc g * g * y = (g * g) * y * (g * g)⁻¹ * (g * g) := by group
        _ = y * (g * g) := by rw [hsq]
    obtain ⟨k, hk⟩ := hgo
    have hpow : (g ^ 2) ^ (k + 1) = g := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hc : Commute g y := by
      have := hc2.pow_left (k + 1)
      rwa [hpow] at this
    rw [hc.eq, mul_inv_cancel_right]

theorem gmbTorus_of_klein {Q : Subgroup G} (h4 : Nat.card Q = 4) (hQ : ∀ x ∈ Q, x * x = 1)
    (hC : ∀ g : G, (∀ x ∈ Q, g * x * g⁻¹ = x) → g * g = 1)
    {E : Subgroup G} (hEN : E ≤ normalizer (Q : Set G)) (hE : Odd (Nat.card E)) (hE1 : E ≠ ⊥) :
    GmbTorus Q E := by
  have hodd : ∀ e ∈ E, Odd (orderOf e) := fun e he =>
    hE.of_dvd_nat (Subgroup.orderOf_dvd_natCard E he)
  have hS1 : ∀ e ∈ E, ∀ x ∈ Q, x ≠ 1 → e * x * e⁻¹ = x → e = 1 := by
    intro e he x hx hx1 hex
    have hee := hC e (gmb_centralizes_of_fix h4 hQ (hEN he) (hodd e he) hx hx1 hex)
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hee)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have := hodd e he
      rw [h] at this
      exact (Nat.not_odd_iff_even.mpr even_two) this
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
    rcases Q.bot_or_exists_ne_one with h0 | h
    · rw [h0, Subgroup.card_bot] at h4
      omega
    · exact h
  have hcard : Nat.card E ≤ 4 := by
    rw [← h4]
    refine Nat.card_le_card_of_injective
      (fun e : E => (⟨e * x * e⁻¹, (mem_normalizer_iff.mp (hEN e.2) x).mp hx⟩ : Q)) ?_
    intro a b hab
    have hab' : (a : G) * x * (a : G)⁻¹ = b * x * (b : G)⁻¹ := congrArg Subtype.val hab
    have h1 : (b : G)⁻¹ * a = 1 := hS1 _ (E.mul_mem (E.inv_mem b.2) a.2) x hx hx1 (by
      calc (b : G)⁻¹ * a * x * ((b : G)⁻¹ * a)⁻¹ = (b : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * b := by
            group
        _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * b := by rw [hab']
        _ = x := by group)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hE3 : Nat.card E = 3 := by
    have h1 : Nat.card E ≠ 1 := fun h => hE1 (Subgroup.card_eq_one.mp h)
    obtain ⟨k, hk⟩ := hE
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic E := isCyclic_of_prime_card hE3
  have hfix : ∀ y ∈ Q, (∀ h ∈ E, h * y * h⁻¹ = y) → y = 1 := by
    intro y hy hyE
    by_contra hy1
    apply hE1
    rw [eq_bot_iff]
    intro e he
    rw [mem_bot]
    exact hS1 e he y hy hy1 (hyE e he)
  refine ⟨hEN, hE, ?_, hfix, ?_⟩
  · intro a ha b hb
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have : (⟨a, ha⟩ : E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    exact congrArg Subtype.val this
  · intro Y hYQ hYE
    rcases Y.bot_or_exists_ne_one with h0 | ⟨y, hy, hy1⟩
    · exact Or.inl h0
    right
    by_contra hYne
    apply hy1
    refine hfix y (hYQ hy) fun h hh => ?_
    by_contra hne
    apply hYne
    refine le_antisymm hYQ fun w hw => ?_
    have hz : h * y * h⁻¹ ∈ Y := hYE h hh y hy
    have hz1 : h * y * h⁻¹ ≠ 1 := fun h' => hy1 (by
      have h'' : h * y = h * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h'
      exact mul_left_cancel h'')
    rcases gmb_mem_four h4 hQ (hYQ hy) (hYQ hz) hy1 hz1 (Ne.symm hne) hw with
      rfl | rfl | rfl | rfl
    · exact Y.one_mem
    · exact hy
    · exact hz
    · exact Y.mul_mem hy hz

theorem gmbProp_of_klein {Γ : Type*} [Group Γ] [Finite Γ] (Q₀ : Sylow 2 Γ)
    (h4 : Nat.card (Q₀ : Subgroup Γ) = 4) (h2 : ∀ x ∈ (Q₀ : Subgroup Γ), x * x = 1)
    {c : Γ} (hcN : c ∈ normalizer ((Q₀ : Subgroup Γ) : Set Γ)) (hc1 : c ≠ 1)
    (hco : Odd (orderOf c))
    (hC : ∀ g : Γ, (∀ x ∈ (Q₀ : Subgroup Γ), g * x * g⁻¹ = x) → g * g = 1) : GmbProp Γ := by
  intro Q E hEN hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  have hmem : ∀ y, y ∈ ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ) ↔
      g⁻¹ * y * g ∈ (Q₀ : Subgroup Γ) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
  have h4' : Nat.card ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ) = 4 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity Q₀, h4]
  have h2' : ∀ y ∈ ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ), y * y = 1 := by
    intro y hy
    have := h2 _ ((hmem y).mp hy)
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hC' : ∀ h : Γ, (∀ x ∈ ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ), h * x * h⁻¹ = x) →
      h * h = 1 := by
    intro h hh
    have := hC (g⁻¹ * h * g) (fun x hx => by
      have hx' : g * x * g⁻¹ ∈ ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ) :=
        (hmem _).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group])
      have := hh _ hx'
      calc g⁻¹ * h * g * x * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * (g * x * g⁻¹) * h⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [this]
        _ = x := by group)
    calc h * h = g * ((g⁻¹ * h * g) * (g⁻¹ * h * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  by_cases hE1 : E = ⊥
  · have hc'N : g * c * g⁻¹ ∈ normalizer (((g • Q₀ : Sylow 2 Γ) : Subgroup Γ) : Set Γ) := by
      rw [mem_normalizer_iff]
      intro y
      rw [hmem, hmem, mem_normalizer_iff.mp hcN,
        show g⁻¹ * (g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹) * g = c * (g⁻¹ * y * g) * c⁻¹ by group]
    have hc'o : Odd (orderOf (g * c * g⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hco
    refine ⟨zpowers (g * c * g⁻¹), by rw [hE1]; exact bot_le,
      gmbTorus_of_klein h4' h2' hC' ((Subgroup.zpowers_le).mpr hc'N)
        (by rw [Nat.card_zpowers]; exact hc'o) ?_⟩
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    apply hc1
    have h' : g * c = g * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h
    exact mul_left_cancel h'
  · exact ⟨E, le_rfl, gmbTorus_of_klein h4' h2' hC' hEN hE hE1⟩

end KleinCriterion

end CFSG.SeitzReduction.RankOne
