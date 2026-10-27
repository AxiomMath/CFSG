module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Z2a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_Zt_normalizes_R (c : Ctx4 s e) {x : G} (hx : x ∈ y4Zt c) :
    x ∈ normalizer (s.R : Set G) := by
  apply y4_mem_normalizer_of_conj_mem
  intro r hr
  obtain ⟨-, hcomm⟩ := (y4_mem_Zt c x).mp hx
  have hxr : ⁅x, r⁆ ∈ cen s.fr.B := hcomm r (y4_T_le_T2 s (s.R_le_T hr))
  have hconj : x * r * x⁻¹ = ⁅x, r⁆ * r := by rw [commutatorElement_def]; group
  rw [hconj]
  exact s.R.mul_mem (s.S_le_R (s3_B_le_S s (s3_cenB_le_B s hxr))) hr

theorem y4_Zt_le_T1 (c : Ctx4 s e) : y4Zt c ≤ e.T₁ := by
  intro x hx
  have hxT2 : x ∈ s.T₂ := ((y4_mem_Zt c x).mp hx).1
  have hxN : x ∈ normalizer (s.R : Set G) := y4_Zt_normalizes_R c hx
  have hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t := s3_Q_eq s c.hS c.hZ c.hOut
  have hcenR : cen s.R = zt s := s3_cen_R_eq s c.hS c.hZ hQ
  rw [← y4_normIn_zt c, normIn, Subgroup.mem_inf]
  refine ⟨hxT2, ?_⟩
  rw [← hcenR]
  apply y4_mem_normalizer_of_conj_mem
  intro u hu
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hxN u).mp (Subgroup.mem_inf.mp hu).1
  · rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hxinv : x⁻¹ ∈ normalizer (s.R : Set G) := inv_mem hxN
    have hxrx : x⁻¹ * r * x ∈ s.R := by
      simpa using (Subgroup.mem_normalizer_iff.mp hxinv r).mp hr
    have hucomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2)
      (x⁻¹ * r * x) hxrx
    calc r * (x * u * x⁻¹) = x * ((x⁻¹ * r * x) * u) * x⁻¹ := by group
      _ = x * (u * (x⁻¹ * r * x)) * x⁻¹ := by rw [hucomm]
      _ = (x * u * x⁻¹) * r := by group

end CFSG.OddStandard.HigherRank.YamadaG23
