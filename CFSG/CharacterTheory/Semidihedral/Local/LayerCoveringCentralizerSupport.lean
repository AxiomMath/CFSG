module

public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimpleSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open scoped commutatorElement

section IdOrInv

variable {X : Type*} [Group X]

@[expose] def idOrInv (P : Subgroup X) : Subgroup X where
  carrier := {c | (∀ x ∈ P, c * x * c⁻¹ = x) ∨ (∀ x ∈ P, c * x * c⁻¹ = x⁻¹)}
  mul_mem' {a b} ha hb := by
    have hab : ∀ x, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := fun x => by group
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl fun x hx => by rw [hab, hb x hx, ha x hx]
    · exact Or.inr fun x hx => by rw [hab, hb x hx, ha _ (P.inv_mem hx)]
    · exact Or.inr fun x hx => by rw [hab, hb x hx, ha x hx]
    · exact Or.inl fun x hx => by rw [hab, hb x hx, ha _ (P.inv_mem hx), inv_inv]
  one_mem' := Or.inl fun x _ => by group
  inv_mem' {a} ha := by
    rcases ha with ha | ha
    · refine Or.inl fun x hx => ?_
      calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ := by rw [ha x hx]
        _ = x := by group
    · refine Or.inr fun x hx => ?_
      calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x⁻¹ * a⁻¹) * a⁻¹⁻¹ := by
            rw [ha _ (P.inv_mem hx), inv_inv x]
        _ = x⁻¹ := by group

theorem mem_idOrInv {P : Subgroup X} {c : X} :
    c ∈ idOrInv P ↔ (∀ x ∈ P, c * x * c⁻¹ = x) ∨ (∀ x ∈ P, c * x * c⁻¹ = x⁻¹) := Iff.rfl

theorem centralizer_le_idOrInv (P : Subgroup X) :
    Subgroup.centralizer (P : Set X) ≤ idOrInv P := fun c hc => Or.inl fun x hx => by
  rw [← Subgroup.mem_centralizer_iff.mp hc x hx, mul_inv_cancel_right]

theorem mem_centralizer_of_conj_eq {P : Subgroup X} {c : X} (h : ∀ x ∈ P, c * x * c⁻¹ = x) :
    c ∈ Subgroup.centralizer (P : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * c = c * x * c⁻¹ * c := by rw [h x hx]
    _ = c * x := by group

theorem conj_mem_idOrInv {P : Subgroup X} {g c : X} (hg : g ∈ Subgroup.normalizer (P : Set X))
    (hc : c ∈ idOrInv P) : g * c * g⁻¹ ∈ idOrInv P := by
  have hconj : ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun x hx => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    rwa [inv_inv] at h
  have heq : ∀ x, g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * x * g) * c⁻¹) * g⁻¹ :=
    fun x => by group
  rcases hc with hc | hc
  · refine Or.inl fun x hx => ?_
    rw [heq, hc _ (hconj x hx)]
    group
  · refine Or.inr fun x hx => ?_
    rw [heq, hc _ (hconj x hx)]
    group

theorem exists_exponent_of_mem_idOrInv {P : Subgroup X} {c : X} (hc : c ∈ idOrInv P) :
    ∃ e : ℤ, e * e = 1 ∧ (∀ x ∈ P, c * x * c⁻¹ = x ^ e) ∧ (∀ x ∈ P, c⁻¹ * x * c = x ^ e) := by
  rcases hc with hc | hc
  · refine ⟨1, by norm_num, fun x hx => by rw [hc x hx, zpow_one], fun x hx => ?_⟩
    rw [zpow_one]
    calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [hc x hx]
      _ = x := by group
  · refine ⟨-1, by norm_num, fun x hx => by rw [hc x hx, zpow_neg_one], fun x hx => ?_⟩
    rw [zpow_neg_one]
    calc c⁻¹ * x * c = c⁻¹ * (c * x⁻¹ * c⁻¹) * c := by rw [hc _ (P.inv_mem hx), inv_inv]
      _ = x⁻¹ := by group

theorem commutator_idOrInv_le (P : Subgroup X) :
    ⁅idOrInv P, idOrInv P⁆ ≤ Subgroup.centralizer (P : Set X) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨ea, hea, ha1, ha2⟩ := exists_exponent_of_mem_idOrInv ha
  obtain ⟨eb, heb, hb1, hb2⟩ := exists_exponent_of_mem_idOrInv hb
  apply mem_centralizer_of_conj_eq
  intro x hx
  have heq : ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = a * (b * (a⁻¹ * (b⁻¹ * x * b) * a) * b⁻¹) * a⁻¹ := by
    rw [commutatorElement_def]
    group
  have h1 : x ^ eb ∈ P := P.zpow_mem hx eb
  have h2 : (x ^ eb) ^ ea ∈ P := P.zpow_mem h1 ea
  have h3 : ((x ^ eb) ^ ea) ^ eb ∈ P := P.zpow_mem h2 eb
  rw [heq, hb2 x hx, ha2 _ h1, hb1 _ h2, ha1 _ h3, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  have h4 : eb * (ea * (eb * ea)) = 1 := by
    calc eb * (ea * (eb * ea)) = (ea * ea) * (eb * eb) := by ring
      _ = 1 := by rw [hea, heb, one_mul]
  rw [h4, zpow_one]

end IdOrInv

section Package

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizer_kappa_eq (t : G) {ℓ : ℕ} [Fact ℓ.Prime] (P : Sylow ℓ (N t))
    (γ : Gamma t) : ∃ b ∈ Subgroup.normalizer ((((P : Subgroup (N t)).map (N t).subtype :
      Subgroup (C t))) : Set (C t)), kappa t b = γ := by
  have hFr := Sylow.normalizer_sup_eq_top (N := N t) P
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) γ
  have hc : c ∈ Subgroup.normalizer ((((P : Subgroup (N t)).map (N t).subtype :
      Subgroup (C t))) : Set (C t)) ⊔ N t := by
    rw [hFr]
    exact Subgroup.mem_top c
  obtain ⟨b, hb, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  refine ⟨b, hb, ?_⟩
  have hm1 : kappa t m = 1 := (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_sup_left hm)
  change kappa t b = kappa t (b * m)
  rw [map_mul, hm1, mul_one]

theorem kappa_ne_one_of_involution (t : G) (ht : orderOf t = 2) {s : C t} (hs : orderOf s = 2)
    (hst : s ≠ tInC t) : kappa t s ≠ 1 := by
  intro h
  have h1 : s ∈ N t ⊔ Z t := (QuotientGroup.eq_one_iff s).mp h
  obtain ⟨m, hm, z, hz, hmz⟩ := Subgroup.mem_sup_of_normal_right.mp h1
  have hzc : z ∈ Subgroup.center (C t) := Subgroup.zpowers_le.mpr (tInC_central t) hz
  have ht2 : tInC t ^ 2 = 1 := by
    rw [← (show orderOf (tInC t) = 2 by rw [tInC, Subgroup.orderOf_mk, ht])]
    exact pow_orderOf_eq_one _
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hs2 : s ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hm2 : m ^ 2 = 1 := by
    have hms : m = s * z⁻¹ := by rw [← hmz, mul_inv_cancel_right]
    have hcomm : s * z⁻¹ = z⁻¹ * s :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hzc) s)
    have hz2' : z⁻¹ ^ 2 = 1 := by rw [inv_pow, hz2, inv_one]
    calc m ^ 2 = s * (z⁻¹ * s) * z⁻¹ := by rw [hms, sq]; group
      _ = s * (s * z⁻¹) * z⁻¹ := by rw [hcomm]
      _ = s ^ 2 * z⁻¹ ^ 2 := by rw [sq, sq]; group
      _ = 1 := by rw [hs2, hz2', one_mul]
  have hm1 : m = 1 := by
    have hodd := Odd.of_dvd_nat (odd_card_N t) (Subgroup.orderOf_dvd_natCard (N t) hm)
    have hdvd := orderOf_dvd_of_pow_eq_one hm2
    have hcop : Nat.Coprime 2 (orderOf m) := Nat.coprime_two_left.mpr hodd
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)
  rw [hm1, one_mul] at hmz
  rw [← hmz] at hs hst
  have hs1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; exact absurd hs (by norm_num)
  have htne : tInC t ≠ 1 := fun h1 => by
    have h2 : orderOf (tInC t) = 2 := by rw [tInC, Subgroup.orderOf_mk, ht]
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact hst (eq_of_card_eq_two (card_Z t ht) hz (Subgroup.mem_zpowers _) hs1 htne)

end Package

end CFSG.Semidihedral.Local
