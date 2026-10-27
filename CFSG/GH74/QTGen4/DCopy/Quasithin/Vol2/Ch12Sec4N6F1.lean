module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem rho_of_mem_CE_F4 (h12210 : Stmt12_2_10_F4) (D : L3Data (autOn L V) ⊤ (fixV (autOn L V)))
    {k : G} (hk : k ∈ Subgroup.centralizer (E : Set G))
    (hkN : k ∈ Subgroup.normalizer (V : Set G)) :
    ∃ γ : Γ, D.rho γ = conjAct V ⟨k, hkN⟩ ∧ act γ (c.cv D) = c.cv D := by
  have hyp := c.cx.hyp
  obtain ⟨-, -, hMV⟩ := h12210 G T L V hyp
  have hkM : k ∈ hyp.MV := ⟨c.CE_le_M hk, hkN⟩
  have hmem : conjAct V ⟨k, hkN⟩ ∈ hyp.MVbar :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hkM)
  rw [hMV] at hmem
  have hle : autOn L V ⊔ autOn T V ≤ autOn L V := sup_le le_rfl ((le_of_eq c.Tbar).trans c.Tsyl.1)
  obtain ⟨γ, hγ⟩ := D.exists_rho (hle hmem)
  exact ⟨γ, hγ, c.act_cv_of_normalizes D hkN (Subgroup.centralizer_le_normalizer (E : Set G) hk) hγ⟩

theorem card_autOn_dvd_three_F4 (h12210 : Stmt12_2_10_F4) {P : Subgroup G}
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    Nat.card (autOn P V) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D⟩ := c.nat.toL3Coord
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPK.trans c.CE_le_NV
  have hle : autOn P V ≤ (StabSub (c.cv D)).map D.rho := by
    intro φ hφ
    obtain ⟨⟨p, hpN⟩, hpP, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨γ, hγ, hγc⟩ := c.rho_of_mem_CE_F4 h12210 D (hPK (Subgroup.mem_subgroupOf.1 hpP)) hpN
    exact ⟨γ, hγc, hγ⟩
  have h24 : Nat.card ((StabSub (c.cv D)).map D.rho) = 24 := by
    rw [Subgroup.card_map_of_injective D.rho_injective, card_StabSub (c.cv_ne D)]
  have hdvd : Nat.card (autOn P V) ∣ 24 := h24 ▸ Subgroup.card_dvd_of_le hle
  have hp : IsPGroup 3 (autOn P V) :=
    (hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map _
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hdvd ⊢
  have h1 : 3 ^ k ∣ 8 * 3 := hdvd
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 8)).dvd_of_dvd_mul_left h1

theorem three_sub_facts_F4 (h12210 : Stmt12_2_10_F4) {P : Subgroup G}
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    (∀ s ∈ P, ∀ s' ∈ P, s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ s ∈ P, s * s * s ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ s ∈ P, s ∉ Subgroup.centralizer (V : Set G) → ∀ y ∈ P,
      y ∈ Subgroup.centralizer (V : Set G) ∨ s⁻¹ * y ∈ Subgroup.centralizer (V : Set G) ∨
        (s * s)⁻¹ * y ∈ Subgroup.centralizer (V : Set G)) := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPK.trans c.CE_le_NV
  have hcard := c.card_autOn_dvd_three_F4 h12210 hPK hP3
  set Pb := autOn P V with hPb
  have hmem : ∀ s (hs : s ∈ P), conjAct V ⟨s, hPN hs⟩ ∈ Pb := fun s hs =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)

  let χ : ↥P →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hPN)
  have hmemχ : ∀ x : ↥P, χ x ∈ Pb := fun x =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
  have hCV : ∀ x : ↥P, χ x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x hx =>
    A4.conjAct_eq_one_iff.1 hx

  have hord : ∀ φ ∈ Pb, φ ^ 3 = 1 := by
    intro φ hφ
    have h1 : orderOf (⟨φ, hφ⟩ : ↥Pb) ∣ 3 := (orderOf_dvd_natCard _).trans hcard
    have h2 : (⟨φ, hφ⟩ : ↥Pb) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2

  have hgen : ∀ φ ∈ Pb, φ ≠ 1 → ∀ ψ ∈ Pb, ψ = 1 ∨ ψ = φ ∨ ψ = φ * φ := by
    intro φ hφ hφ1 ψ hψ
    have hφo : orderOf φ = 3 := orderOf_eq_prime (hord φ hφ) hφ1
    have hz : Subgroup.zpowers φ ≤ Pb := Subgroup.zpowers_le.2 hφ
    have hzeq : Subgroup.zpowers φ = Pb := by
      refine Subgroup.eq_of_le_of_card_ge hz ?_
      rw [Nat.card_zpowers, hφo]
      exact Nat.le_of_dvd (by norm_num) hcard
    exact mem_zpowers_three hφo (hzeq ▸ hψ)

  have hcomm : ∀ φ ∈ Pb, ∀ ψ ∈ Pb, φ * ψ = ψ * φ := by
    intro φ hφ ψ hψ
    by_cases hφ1 : φ = 1
    · rw [hφ1, one_mul, mul_one]
    rcases hgen φ hφ hφ1 ψ hψ with h | h | h <;> rw [h] <;> group
  refine ⟨fun s hs s' hs' => ?_, fun s hs => ?_, fun s hs hsV y hy => ?_⟩
  · have h1 := hCV ((⟨s, hs⟩ : ↥P) * ⟨s', hs'⟩ * (⟨s, hs⟩)⁻¹ * (⟨s', hs'⟩)⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ (hmemχ _) _ (hmemχ _)]
      group)
    exact h1
  · have h1 := hCV ((⟨s, hs⟩ : ↥P) * ⟨s, hs⟩ * ⟨s, hs⟩) (by
      rw [map_mul, map_mul, ← pow_three']
      exact hord _ (hmemχ _))
    exact h1
  · have hs1 : χ ⟨s, hs⟩ ≠ 1 := fun h => hsV (hCV _ h)
    rcases hgen _ (hmemχ ⟨s, hs⟩) hs1 _ (hmemχ ⟨y, hy⟩) with h | h | h
    · exact Or.inl (hCV _ h)
    · refine Or.inr (Or.inl ?_)
      have h1 := hCV ((⟨s, hs⟩ : ↥P)⁻¹ * ⟨y, hy⟩) (by rw [map_mul, map_inv, h, inv_mul_cancel])
      exact h1
    · refine Or.inr (Or.inr ?_)
      have h1 := hCV ((⟨s, hs⟩ * ⟨s, hs⟩ : ↥P)⁻¹ * ⟨y, hy⟩) (by
        rw [map_mul, map_inv, map_mul, h, inv_mul_cancel])
      exact h1

end Ctx

end N1246

end CFSG.Quasithin.H13
