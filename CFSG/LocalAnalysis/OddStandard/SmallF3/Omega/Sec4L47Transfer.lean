module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_simple_squares [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} {N : Subgroup G}
    (hN : (N.subgroupOf (⊤ : Subgroup G)).Normal) (hsq : ∀ x ∈ (⊤ : Subgroup G), x ^ 2 ∈ N)
    (htN : t ∉ N) : False := by
  have hNn : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : N ≤ ⊤)).mp hN
  haveI := hNn
  rcases hG.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha2 : a * a = 1 := by
      have h := hsq a (Subgroup.mem_top a)
      simpa [hbot, pow_two] using h
    have hb2 : b * b = 1 := by
      have h := hsq b (Subgroup.mem_top b)
      simpa [hbot, pow_two] using h
    have hab2 : a * b * a * b = 1 := by
      have h := hsq (a * b) (Subgroup.mem_top (a * b))
      rw [hbot, Subgroup.mem_bot, pow_two] at h
      rwa [show a * b * a * b = (a * b) * (a * b) from by group]
    have h2 : a * b * a = b := by
      calc a * b * a = a * b * a * (b * b) := by rw [hb2, mul_one]
        _ = (a * b * a * b) * b := by group
        _ = b := by rw [hab2, one_mul]
    calc a * b = a * b * (a * a) := by rw [ha2, mul_one]
      _ = (a * b * a) * a := by group
      _ = b * a := by rw [h2]
  · exact htN (htop ▸ Subgroup.mem_top t)

end CFSG.OddStandard.SmallF3.Omega
