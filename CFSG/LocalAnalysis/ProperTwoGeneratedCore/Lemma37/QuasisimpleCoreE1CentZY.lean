module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZQuot

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

abbrev E1M1 (Z : Subgroup G) [Z.Normal] (u m y x : G) : Type :=
  e1M0 Z (u * (x * u * x⁻¹)) ⧸ e1ZM Z u m y x

abbrev E1Y (Z : Subgroup G) [Z.Normal] (u m y x : G) : Type :=
  E1M1 Z u m y x ⧸ CFSG.pPrimeCore 2 (E1M1 Z u m y x)

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem forty_mem_e1M0 :
    caseC3Word (Subgroup.center J) u m y x 40 ∈ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) :=
  d.caseC3BCD.e1RBar_le_e1M0 d.caseC3BCD.forty_mem_e1RBar

theorem card_e1RBar_subgroupOf : Nat.card ((e1RBar (Subgroup.center J) u m y x).subgroupOf
    (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))) = 32 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.caseC3BCD.e1RBar_le_e1M0).toEquiv,
    d.caseC3BCD.card_e1RBar]

theorem mem_e1ZM_iff {w : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))} :
    w ∈ e1ZM (Subgroup.center J) u m y x ↔ (w : J ⧸ Subgroup.center J) = 1 ∨
      (w : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 40 := by
  rw [e1ZM, Subgroup.mem_subgroupOf]
  constructor
  · intro hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h2 : caseC3Word (Subgroup.center J) u m y x 40 ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact d.caseC3BCD.forty_mul_self
    rw [← hk, ← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
    · exact Or.inl (zpow_zero _)
    · exact Or.inr (zpow_one _)
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem card_e1ZM : Nat.card (e1ZM (Subgroup.center J) u m y x) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [e1ZM, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.zpowers_le.mpr d.forty_mem_e1M0)).toEquiv, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact d.caseC3BCD.forty_mul_self)
    (by rw [Ne, d.caseC3BCD.caseC3Word_eq_one_iff]; decide)

theorem isPGroup_e1ZM : IsPGroup 2 (e1ZM (Subgroup.center J) u m y x) :=
  IsPGroup.of_card (n := 1) (by rw [d.card_e1ZM, pow_one])

theorem e1ZM_le : e1ZM (Subgroup.center J) u m y x ≤ (e1RBar (Subgroup.center J) u m y x).subgroupOf
    (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))) :=
  Subgroup.comap_mono (Subgroup.zpowers_le.mpr d.caseC3BCD.forty_mem_e1RBar)

theorem e1Pi_eq_one_iff {r : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))}
    (hr : (r : J ⧸ Subgroup.center J) ∈ e1RBar (Subgroup.center J) u m y x) :
    e1Pi (e1ZM (Subgroup.center J) u m y x) r = 1 ↔ r ∈ e1ZM (Subgroup.center J) u m y x := by
  have hker := ker_e1Pi (e1ZM (Subgroup.center J) u m y x) e1ZM_le_center d.isPGroup_e1ZM
  constructor
  · intro h
    have hk : r ∈ (e1Pi (e1ZM (Subgroup.center J) u m y x)).ker := h
    rw [hker] at hk
    refine mem_of_mem_sup_of_pow_eq_one _ e1ZM_le_center d.isPGroup_e1ZM hk (k := 2) ?_
    apply Subtype.ext
    simpa using d.caseC3BCD.pow_four_eq_one (d.caseC3BCD.e1RBar_le hr)
  · intro h
    have hk : r ∈ (e1Pi (e1ZM (Subgroup.center J) u m y x)).ker := by
      rw [hker]
      exact Subgroup.mem_sup_right h
    exact hk

theorem e1Pi_eq_iff {r s : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))}
    (hr : (r : J ⧸ Subgroup.center J) ∈ e1RBar (Subgroup.center J) u m y x)
    (hs : (s : J ⧸ Subgroup.center J) ∈ e1RBar (Subgroup.center J) u m y x) :
    e1Pi (e1ZM (Subgroup.center J) u m y x) r = e1Pi (e1ZM (Subgroup.center J) u m y x) s ↔
      (r : J ⧸ Subgroup.center J) = s ∨
        (r : J ⧸ Subgroup.center J) = s * caseC3Word (Subgroup.center J) u m y x 40 := by
  have hb := d.caseC3BCD
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul,
    d.e1Pi_eq_one_iff (Subgroup.mul_mem _ hr (Subgroup.inv_mem _ hs)), d.mem_e1ZM_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul,
    (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) _ hs]

theorem commute_of_mem_map_e1Pi {a b : E1Y (Subgroup.center J) u m y x}
    (ha : a ∈ ((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map (e1Pi (e1ZM (Subgroup.center J) u m y x)))
    (hb' : b ∈ ((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x))) :
    a * b = b * a := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hb'
  rw [Subgroup.mem_subgroupOf] at hr hs
  rw [← map_mul, ← map_mul, d.e1Pi_eq_iff (Subgroup.mul_mem _ hr hs) (Subgroup.mul_mem _ hs hr)]
  simp only [Subgroup.coe_mul]
  exact d.caseC3BCD.commute_or_of_mem_e1RBar hr hs

theorem mul_self_of_mem_map_e1Pi {a : E1Y (Subgroup.center J) u m y x}
    (ha : a ∈ ((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x))) :
    a * a = 1 := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_subgroupOf] at hr
  rw [← map_mul, d.e1Pi_eq_one_iff (Subgroup.mul_mem _ hr hr), d.mem_e1ZM_iff]
  simpa using d.caseC3BCD.mul_self_of_mem_e1RBar hr

theorem card_map_e1Pi : Nat.card (((e1RBar (Subgroup.center J) u m y x).subgroupOf
    (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
      (e1Pi (e1ZM (Subgroup.center J) u m y x))) = 16 := by
  have h := card_map_mul_card_ker_subgroupOf (e1ZM (Subgroup.center J) u m y x)
    ((e1RBar (Subgroup.center J) u m y x).subgroupOf (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))))
  have hker : (e1Pi (e1ZM (Subgroup.center J) u m y x)).ker.subgroupOf
      ((e1RBar (Subgroup.center J) u m y x).subgroupOf
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))) =
      (e1ZM (Subgroup.center J) u m y x).subgroupOf ((e1RBar (Subgroup.center J) u m y x).subgroupOf
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))) := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact d.e1Pi_eq_one_iff (Subgroup.mem_subgroupOf.mp r.2)
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.e1ZM_le).toEquiv, d.card_e1ZM,
    d.card_e1RBar_subgroupOf] at h
  omega

@[expose] noncomputable def e1YSylow : Sylow 2 (E1Y (Subgroup.center J) u m y x) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (d.caseC3BCD.e1RSylow S rfl).mapSurjective (e1Pi_surjective (e1ZM (Subgroup.center J) u m y x))

theorem coe_e1YSylow : (d.e1YSylow : Subgroup (E1Y (Subgroup.center J) u m y x)) =
    ((e1RBar (Subgroup.center J) u m y x).subgroupOf
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1Pi (e1ZM (Subgroup.center J) u m y x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [e1YSylow, Sylow.coe_mapSurjective]
  rfl

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
