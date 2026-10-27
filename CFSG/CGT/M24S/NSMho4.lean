module

public import CFSG.CGT.M24S.NSMho3
public import CFSG.CGT.M24S.NSTypeA4

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

theorem exists_fixed_of_card_four {G : Type} [Group G] {Q A : Subgroup G} [Finite A]
    (hQ : IsPGroup 2 Q) (hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a * q⁻¹ ∈ A) (hA : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ q ∈ Q, q * a * q⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥Q ↥A :=
    { smul := fun q a => ⟨q * a * q⁻¹, hQA q q.2 a a.2⟩
      one_smul := fun a => Subtype.ext (by
        change ((1 : ↥Q) : G) * a * ((1 : ↥Q) : G)⁻¹ = a
        rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun q r a => Subtype.ext (by
        change ((q * r : ↥Q) : G) * a * ((q * r : ↥Q) : G)⁻¹ =
          (q : G) * ((r : G) * a * (r : G)⁻¹) * (q : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have h1 : (1 : ↥A) ∈ MulAction.fixedPoints ↥Q ↥A := fun q => Subtype.ext (by
    change (q : G) * ((1 : ↥A) : G) * (q : G)⁻¹ = ((1 : ↥A) : G)
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel])
  obtain ⟨b, hb, hb1⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥A
    (by rw [hA]; norm_num) h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun q hq => ?_⟩
  exact congrArg Subtype.val (hb ⟨q, hq⟩)

theorem caseB {G : Type} [Group G] [Finite G] {T H : Subgroup G} (hTH : T ≤ H)
    (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H) {x : G} (hxH : x ∈ H) (hxT : x ∉ T)
    (hx2 : x ^ 2 = 1) (hnot : ∀ t ∈ T, t ≠ 1 → ¬ CentreTransvecting T t x) :
    ∃ P : Subgroup G, P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
        Nat.card Q ≤ Nat.card P) ∧ Nat.card P = 2 ^ 7 ∧ ∃ t ∈ T, t ≠ 1 ∧ SqDerivedEq P t := by
  have hT16 := card_T_of_naturalSL hN
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ T, z ≠ 1 := by
    by_contra h
    push Not at h
    have hb : T = ⊥ := eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (h g hg)
    rw [hb, Subgroup.card_bot] at hT16
    norm_num at hT16
  obtain ⟨c₁⟩ := nonempty_natCoord hTH hN hz hz1
  obtain ⟨s, hs, hs1⟩ : ∃ s ∈ T, s * (x * s * x⁻¹) ≠ 1 := by
    by_contra h
    push Not at h
    apply hxT
    refine c₁.mem_T_of_commute hxH fun s hs => ?_
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (mul_self_of_mem_T c₁ hs)
    have h2 : x * s * x⁻¹ = s := (eq_inv_of_mul_eq_one_right (h s hs)).trans hsi
    calc x * s = x * s * x⁻¹ * x := by group
      _ = s * x := by rw [h2]
  have ht₁ : s * (x * s * x⁻¹) ∈ T := T.mul_mem hs (c₁.conj_mem hxH hs)
  obtain ⟨hcard, hsq, hCT, hcomm⟩ := caseB_core hTH hN hns hxH hx2 (hnot _ ht₁ hs1) ht₁ hs1
    ⟨s, hs, rfl⟩
  refine ⟨_, inf_le_left, fun Q hQ hQC => ?_, hcard, _, ht₁, hs1, hsq⟩
  obtain ⟨a, ha, ha1, hfix⟩ := exists_fixed_of_card_four (A := T ⊓ Subgroup.centralizer
    ({x} : Set G)) hQ (fun q hq a ha => ⟨c₁.conj_mem (hQC hq).1 ha.1,
      (Subgroup.centralizer ({x} : Set G)).mul_mem
        ((Subgroup.centralizer ({x} : Set G)).mul_mem (hQC hq).2 ha.2)
        ((Subgroup.centralizer ({x} : Set G)).inv_mem (hQC hq).2)⟩) hCT
  obtain ⟨r, hr, hra⟩ := hcomm a ha.1 (Subgroup.mem_centralizer_singleton_iff.1 ha.2)
  obtain ⟨hcard', -, -, -⟩ := caseB_core hTH hN hns hxH hx2 (hnot a ha.1 ha1) ha.1 ha1
    ⟨r, hr, hra⟩
  rw [hcard, ← hcard']
  refine Subgroup.card_le_of_le fun q hq => ⟨hQC hq, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc q * a = q * a * q⁻¹ * q := by group
    _ = a * q := by rw [hfix q hq]

end CFSG.CGT.M24S.NSB

namespace CFSG.CGT.M24S

open CFSG.CGT.Timmesfeld75

theorem exists_sylow_sqDerivedEq {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    (hns : ¬ HasComplement T H) {x : G} (hxH : x ∈ H) (hxT : x ∉ T) (hx2 : x ^ 2 = 1) :
    ∃ P : Subgroup G, P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
        Nat.card Q ≤ Nat.card P) ∧ Nat.card P = 2 ^ 7 ∧ ∃ t ∈ T, t ≠ 1 ∧ SqDerivedEq P t := by
  by_cases h : ∃ t ∈ T, t ≠ 1 ∧ CentreTransvecting T t x
  · obtain ⟨t, ht, ht1, htc⟩ := h
    obtain ⟨P, h1, h2, h3, h4⟩ := NSB.caseA hTH hN hns ht ht1 hxH hxT hx2 htc
    exact ⟨P, h1, h2, h3, t, ht, ht1, h4⟩
  · push Not at h
    exact NSB.caseB hTH hN hns hxH hxT hx2 fun t ht ht1 => h t ht ht1

end CFSG.CGT.M24S
