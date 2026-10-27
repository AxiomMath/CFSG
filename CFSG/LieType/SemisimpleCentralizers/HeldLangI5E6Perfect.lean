module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCover
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Aux

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem apply_eq_of_mem_center_of_card_three {L : Type} [Group L] (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center L) = 3) {z : L} (hz : z ∈ Subgroup.center L) : β z = z := by
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have h3 : ∀ x, (β ^ 3) x = β (β (β x)) := fun x => by simp [pow_succ, MulAut.mul_apply]
  have hβz : β z ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    calc g * β z = β (β.symm g * z) := by simp
      _ = β (z * β.symm g) := by rw [hz (β.symm g)]
      _ = β z * g := by simp
  haveI : Finite (Subgroup.center L) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hord : orderOf z = 3 := by
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center L) ∣ 3 := hZ ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hzp : Subgroup.zpowers z = Subgroup.center L := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) ?_
    rw [Nat.card_zpowers, hord, hZ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hzp ▸ hβz)
  have hk3 : z ^ 3 = 1 := hord ▸ pow_orderOf_eq_one z
  have hkm : z ^ k = z ^ (k % 3) := by
    have := zpow_mod_orderOf z k
    rw [hord] at this
    simpa using this.symm
  have hkc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hkc with h | h | h
  · exfalso
    rw [h, zpow_zero] at hkm
    apply hz1
    apply β.injective
    rw [← hk, hkm, map_one]
  · rw [← hk, hkm, h, zpow_one]
  · exfalso
    rw [h] at hkm
    have hβ2 : β z = z ^ 2 := by rw [← hk, hkm]; norm_num
    have e1 : β (z ^ 2) = z := by
      rw [map_pow, hβ2, ← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hk3, mul_one, pow_one]
    have e2 : (β ^ 3) z = z ^ 2 := by rw [h3, hβ2, e1, hβ2]
    rw [hβ3] at e2
    have e3 : z = z ^ 2 := e2
    apply hz1
    have : z * z = z * 1 := by rw [mul_one, ← pow_two]; exact e3.symm
    exact mul_left_cancel this

theorem fixed_of_perfect_fixed {L : Type} [Group L] (β : MulAut L)
    (hcen : ∀ z ∈ Subgroup.center L, β z = z) {J : Subgroup (L ⧸ Subgroup.center L)}
    (hJ : ⁅J, J⁆ = J) (hfix : ∀ j ∈ J, onCenterQuotient β j = j) :
    ∀ x : L, (QuotientGroup.mk x : L ⧸ Subgroup.center L) ∈ J → β x = x := by
  set π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L) with hπ
  set P : Subgroup L := J.comap π with hP
  have hdisp : ∀ a ∈ P, a⁻¹ * β a ∈ Subgroup.center L := by
    intro a ha
    have h1 : π (a⁻¹ * β a) = 1 := by
      have h2 : onCenterQuotient β (π a) = π (β a) := onCenterQuotient_apply_mk β a
      have h3 : onCenterQuotient β (π a) = π a := hfix (π a) ha
      rw [map_mul, map_inv, ← h2, h3, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcomm : ⁅P, P⁆ ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id L) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show β ⁅a, b⁆ = ⁅a, b⁆
    have hβa : β a = a * (a⁻¹ * β a) := by group
    have hβb : β b = b * (b⁻¹ * β b) := by group
    rw [map_commutatorElement, hβa, hβb]
    exact commutatorElement_mul_central_mul_central (hdisp a ha) (hdisp b hb)
  have hmap : P.map π = J := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J
  have hJmap : (⁅P, P⁆).map π = J := by
    rw [Subgroup.map_commutator, hmap, hJ]
  intro x hx
  have hxJ : π x ∈ (⁅P, P⁆).map π := by rw [hJmap]; exact hx
  obtain ⟨c, hc, hcx⟩ := hxJ
  have hcen' : c⁻¹ * x ∈ Subgroup.center L := by
    apply (QuotientGroup.eq_one_iff _).1
    show π (c⁻¹ * x) = 1
    rw [map_mul, map_inv, hcx, inv_mul_cancel]
  have hβc : β c = c := hcomm hc
  calc β x = β (c * (c⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = β c * β (c⁻¹ * x) := map_mul _ _ _
    _ = c * (c⁻¹ * x) := by rw [hβc, hcen _ hcen']
    _ = x := mul_inv_cancel_left _ _

theorem commutator_eq_self_of_isPerfect {G : Type*} [Group G] (A : Subgroup G) [Group.IsPerfect A] :
    ⁅A, A⁆ = A := by
  have h : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
    have := Group.IsPerfect.commutator_eq_top (G := A)
    rwa [commutator_def] at this
  have h2 := congrArg (Subgroup.map A.subtype) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

open CFSG.Open in
theorem exists_elemAbelian_of_le_pRank {G : Type} [Group G] [Finite G] (H : Subgroup G) {k : ℕ}
    (hk : k ≤ CFSG.Open.pRank 3 H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ ∃ m, Nat.card E = 3 ^ m ∧ k ≤ m := by
  set S : Set ℕ := {m | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ m} with hS
  have hbot : IsElemAbelian 3 (⊥ : Subgroup G) :=
    ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩
  have hne : S.Nonempty := ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro m ⟨E, -, -, hE⟩
    have h1 : 3 ^ m ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1
  obtain ⟨E, hEH, hEab, hEcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEH, hEab, _, hEcard, hk⟩

open CFSG.Open in
theorem exists_elemAbelian_of_perfect_fixed_subgroup {L : Type} [Group L] [Finite L] (β : MulAut L)
    (hβ3 : β ^ 3 = 1) (hZ : Nat.card (Subgroup.center L) = 3)
    {J : Subgroup (L ⧸ Subgroup.center L)} (hJ : ⁅J, J⁆ = J)
    (hfix : ∀ j ∈ J, onCenterQuotient β j = j) {H : Type} [Group H] [Finite H] (Ψ : J ≃* H)
    (hH : Subgroup.center H = ⊥)
    (hrank : ∀ (M : Type) [Group M] [Finite M] (π : M →* H), Function.Surjective π →
      (∀ x, π x = 1 ↔ x ∈ Subgroup.center M) → 3 ∣ Nat.card (Subgroup.center M) →
        6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup M)) :
    ∃ E : Subgroup L, E ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id L) ∧ IsElemAbelian 3 E ∧
      ∃ m, Nat.card E = 3 ^ m ∧ 6 ≤ m := by
  classical
  set π₀ : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L) with hπ₀
  set P : Subgroup L := J.comap π₀ with hP
  have hmemP : ∀ x : L, x ∈ P ↔ π₀ x ∈ J := fun x => Iff.rfl
  let φ : P →* J := (π₀.comp P.subtype).codRestrict J fun x => x.2
  have hφ : ∀ x : P, ((φ x : J) : L ⧸ Subgroup.center L) = π₀ x := fun x => rfl
  let π' : P →* H := Ψ.toMonoidHom.comp φ
  have hφs : Function.Surjective φ := by
    intro j
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (j : L ⧸ Subgroup.center L)
    exact ⟨⟨x, (hmemP x).2 (by
      show (QuotientGroup.mk' (Subgroup.center L)) x ∈ J
      rw [QuotientGroup.mk'_apply, hx]; exact j.2)⟩, Subtype.ext hx⟩
  have hπ's : Function.Surjective π' := Ψ.surjective.comp hφs
  have hker : ∀ x : P, π' x = 1 ↔ x ∈ Subgroup.center P := by
    intro x
    have hx1 : π' x = 1 ↔ (x : L) ∈ Subgroup.center L := by
      show Ψ (φ x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, Subtype.ext_iff, Subgroup.coe_one, hφ]
      exact QuotientGroup.eq_one_iff _
    constructor
    · intro h1
      have hxz := hx1.1 h1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 hxz (y : L))
    · intro hxc
      have hcJ : φ x ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro j
        obtain ⟨y, hy⟩ := hφs j
        rw [← hy, ← map_mul, ← map_mul]
        exact congrArg φ (Subgroup.mem_center_iff.1 hxc y)
      have hcH : Ψ (φ x) ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro h
        obtain ⟨j, rfl⟩ := Ψ.surjective h
        rw [← map_mul, ← map_mul]
        exact congrArg Ψ (Subgroup.mem_center_iff.1 hcJ j)
      rw [hH, Subgroup.mem_bot] at hcH
      exact hcH
  have hZP : (Subgroup.center L) ≤ P := fun z hz => (hmemP z).2 (by
    show (QuotientGroup.mk z : L ⧸ Subgroup.center L) ∈ J
    rw [(QuotientGroup.eq_one_iff z).2 hz]
    exact J.one_mem)
  have hZle : (Subgroup.center L).subgroupOf P ≤ Subgroup.center P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz y)
  have hZcard : Nat.card ((Subgroup.center L).subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ]
  have h3 : 3 ∣ Nat.card (Subgroup.center P) := hZcard ▸ Subgroup.card_dvd_of_le hZle
  haveI : Finite P := inferInstance
  obtain ⟨EP, -, hEPab, m, hEPcard, hm⟩ :=
    exists_elemAbelian_of_le_pRank (⊤ : Subgroup P) (hrank P π' hπ's hker h3)
  refine ⟨EP.map P.subtype, ?_, isElemAbelian_map_of_injective _ hEPab, m, ?_, hm⟩
  · rintro _ ⟨x, -, rfl⟩
    exact fixed_of_perfect_fixed β (fun z hz => apply_eq_of_mem_center_of_card_three β hβ3 hZ hz) hJ hfix
      x x.2
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hEPcard]

end CFSG.LieType.SemisimpleCentralizers.HeldLang
