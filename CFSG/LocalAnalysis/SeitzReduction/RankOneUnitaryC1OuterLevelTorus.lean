module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpConf

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem torus_of_mem (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T) {d : G}
    (hC : U3C1Cartan L T D d) {U₁ : Subgroup G} (hDU₁ : D ≤ normalizer (U₁ : Set G)) {e : G}
    (heD : e ∈ D) (heA : ∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b)
    (hfpf : ∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T)) :
    ∃ e ∈ normalizer (U₁ : Set G), e ∈ normalizer (szT₁ L T : Set G) ∧ e * t = t * e ∧
      (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b) ∧
      (∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T)) ∧
      ∀ r ∈ V, e * r * e⁻¹ = r := by
  have hodd : Odd (orderOf e) := Odd.of_dvd_nat hC.odd (Subgroup.orderOf_dvd_natCard D heD)
  exact ⟨e, hDU₁ heD, hC.le_normalizer heD, mem_centralizer_iff.mp h.mem e (hC.le heD), heA, hfpf,
    pushUp_conj_eq_of_odd hc.comm hc.pow (hc.D_le heD) hodd (pow_orderOf_eq_one e)
      fun x hx hx2 => heA x (hc.omega x hx hx2)⟩

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
