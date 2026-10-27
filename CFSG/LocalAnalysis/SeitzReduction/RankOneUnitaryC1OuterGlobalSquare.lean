module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpStep
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeBound

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem U3C1OuterStepHyp.muOneCent_sq_ne_t {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G} {V : Subgroup G}
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (m : G) : m ^ 2 ≠ t := by
  intro hm2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.start
  obtain ⟨-, -, -, -, hdisj, -, -⟩ := h.start_of_card_sylow hS.card_sylow
  obtain ⟨-, -, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS.card_sylow
  have hmt : m ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hm2]
    group
  have hm4 : m ^ (2 ^ 2) = 1 := by
    rw [show (2 ^ 2 : ℕ) = 2 * 2 from rfl, pow_mul, hm2, h.sq_eq_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm4)
  have hp : IsPGroup 2 (zpowers m) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨a, haC, ha⟩ := exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer
    (zpowers_le.mpr hmt) hp
  have hm'T : a⁻¹ * m * a ∈ T := ha m (mem_zpowers m)
  have hat := mem_centralizer_singleton_iff.mp haC
  have hm'2 : (a⁻¹ * m * a) ^ 2 = t := by
    rw [show (a⁻¹ * m * a) ^ 2 = a⁻¹ * m ^ 2 * a by rw [sq, sq]; group, hm2]
    calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
      _ = a⁻¹ * (a * t) := by rw [hat]
      _ = t := by group
  have hm'S : a⁻¹ * m * a ∉ szT₁ L T ⊔ zpowers t := by
    intro hmS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hmS
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact one_pow 2
      · exact h.sq_eq_one
    have hyz' : y * z = z * y := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · group
      · exact mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
    have htT₁ : t ∈ szT₁ L T := by
      rw [← hm'2, ← hyz, Commute.mul_pow hyz' 2, hz2, mul_one]
      exact szA₁_le _ (hsqT y hy)
    have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨htT₁, mem_zpowers t⟩
    rw [hdisj, mem_bot] at ht1
    have hord := h.inv
    rw [ht1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hVR : V = R₂ := hS.conf.eq_of_one hS.r2
  refine h.false_of_sq_eq_t_of_inv hS.card_sylow hS.r2 hS.inv hS.ne hm'T hm'2 hm'S fun r hr => ?_
  rw [← hVR] at hr ⊢
  exact (mem_normalizer_iff.mp (hS.conf.T_le hm'T) r).mp hr

theorem U3C1OuterStepHyp.muOneCent_conj_ne_sq {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G}
    {V : Subgroup G} (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (g s : G) :
    g * t * g⁻¹ ≠ s ^ 2 := by
  intro hgs
  apply hS.muOneCent_sq_ne_t (g⁻¹ * s * g)
  rw [show (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g by rw [sq, sq]; group, ← hgs]
  group

end CFSG.SeitzReduction.RankOne
