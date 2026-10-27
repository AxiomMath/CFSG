module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510AltCS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510_CS (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a) (hfin : Asc82FactBCent6)
    (h : Sec510Ctx G t L S z r ρ B A φ) : S ⊓ centralizer (L : Set G) = zpowers t := by
  have c := h.toSec5RCtx
  apply le_antisymm
  · by_contra hne
    obtain ⟨p, hp, hpp⟩ := sec5p510c_exists_p h52a c hne
    rcases sec5p510c_comm_cases hy.h36 h52a c hp hpp with hd | hd
    · have hpA : p ∈ centralizer (A : Set G) := sec5p510c_cent_A c hp hd
      have hrA : r ∈ A := c.A_eq ▸ Subgroup.mem_sup_left (mem_zpowers r)
      have hBA : B ≤ A := c.A_eq ▸ le_sup_right
      obtain ⟨g, hg⟩ := c.conj_r
      have hrD : r ∈ conjClassIn (normalizer (A : Set G)) t := by
        have := sec5p510_tG_inter_A h (g := g) (by rw [hg]; exact hrA)
        rwa [hg] at this
      obtain ⟨m, hm, hmr⟩ := hrD
      have hp'sq : (m * p * m⁻¹) * (m * p * m⁻¹) = r := by
        calc (m * p * m⁻¹) * (m * p * m⁻¹) = m * (p * p) * m⁻¹ := by group
          _ = r := by rw [hpp, hmr]
      have hp'B : ∀ b ∈ B, (m * p * m⁻¹) * b = b * (m * p * m⁻¹) := by
        intro b hb
        have hbA : m⁻¹ * b * m ∈ A := (Subgroup.mem_normalizer_iff''.mp hm b).mp (hBA hb)
        have hcomm := Subgroup.mem_centralizer_iff.mp hpA _ hbA
        calc (m * p * m⁻¹) * b = m * (p * (m⁻¹ * b * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * b * m) * p) * m⁻¹ := by rw [hcomm]
          _ = b * (m * p * m⁻¹) := by group
      have hp'C : m * p * m⁻¹ ∈ centralizer (B : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun b hb => (hp'B b hb).symm
      have hp'N : m * p * m⁻¹ ∈ normalizer (L : Set G) :=
        sec4_mem_normalizer hy.h36 c.toSec3SettingLB _
          (Subgroup.mem_centralizer_singleton_iff.mpr (hp'B t c.B_split.1))
      have hL : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
      have h2c : twoCoreIn L = zpowers t := (hy.h52b G t L h.toSec5Setting).2
      have hsq := hfin G t L r B hL h2c c.B_le c.B_E32 c.B_split.1 c.B_split.2.1
        c.B_split.2.2 c.type_r _ hp'N hp'C
      rw [hp'sq] at hsq
      have hrN : r ∈ normalizer (L : Set G) :=
        sec4_mem_normalizer hy.h36 c.toSec3SettingLB r (c.sylow.1 (c.A_le hrA))
      exact hy.tab.kind_ne_central G L hL r (sec5b_orderOf_r c) hrN
        (Or.inr (Or.inl c.type_r)) hsq
    · exact sec5p510c_no_inv hy h hp hpp hd
  · rw [Subgroup.zpowers_le]
    exact ⟨sec4_t_mem_S h.sylow h.involution, sec4_t_mem_centralizer h.toSec3Setting⟩

end CFSG.OddStandard.SmallF3.Omega
