module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2CT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_comm_t_F (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {m : G} (hm : m ∈ M6 c.e) (hmF : ∀ x ∈ c.s.fr.F, m * x = x * m) :
    ⁅m, c.s.t⁆ ∈ c.s.fr.F := by
  have hY : ∀ a ∈ c.s.fr.A, (∀ x ∈ c.s.fr.F, a * x = x * a) → a ∈ c.s.fr.F := by
    intro a ha haF
    have haL : a ∈ L := s3_A_le_L c.s ha
    have hcent : a ∈ centIn L c.s.fr.F :=
      Subgroup.mem_inf.mpr
        ⟨haL, Subgroup.mem_centralizer_iff.mpr (fun f hf => (haF f hf).symm)⟩
    have hEq : centIn L c.s.fr.F = c.s.fr.F := by
      rw [hH.hLF.fact18.2.2.2.1, f3_zL_eq_bot hH, bot_sup_eq]
    exact hEq ▸ hcent
  exact y7a_comm_t_mem c hH hF (X := c.s.fr.F) (Y := c.s.fr.F) (s3_F_le_A c.s) hY
    (fun y hy => by rw [← pow_two]; exact y54_F_sq hH y hy) (y54_z_mem_F c.s) hm hmF

theorem y7a_cent_M6_F (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : centIn (M6 c.e) c.s.fr.F = M3 c.s := by
  have hM3 := y7a_M3_elemAbelian c hH
  have hcentF : centIn L c.s.fr.F = c.s.fr.F := by
    rw [hH.hLF.fact18.2.2.2.1, f3_zL_eq_bot hH, bot_sup_eq]
  apply le_antisymm
  · intro m hm
    have hmM6 : m ∈ M6 c.e := hm.1
    have hmF' : ∀ x ∈ c.s.fr.F, x * m = m * x :=
      Subgroup.mem_centralizer_iff.mp hm.2
    have hmF : ∀ x ∈ c.s.fr.F, m * x = x * m := fun x hx => (hmF' x hx).symm
    have hcomm : ⁅m, c.s.t⁆ ∈ c.s.fr.F := y7a_comm_t_F c hH hF hmM6 hmF
    have hmem : m * c.s.t * m⁻¹ ∈ c.s.tCoset c.s.fr.F := by
      refine ⟨⁅m, c.s.t⁆, hcomm, ?_⟩
      rw [commutatorElement_def]
      group
    have hconj : conjClass (M3 c.s) c.s.t = c.s.tCoset c.s.fr.F := hF.2.2.1.1.2.2.1
    rw [← hconj] at hmem
    obtain ⟨m', hm'M3, hm'eq⟩ := hmem
    have hnconj : (m'⁻¹ * m) * c.s.t * (m'⁻¹ * m)⁻¹ = c.s.t := by
      calc (m'⁻¹ * m) * c.s.t * (m'⁻¹ * m)⁻¹
          = m'⁻¹ * (m * c.s.t * m⁻¹) * m' := by group
        _ = m'⁻¹ * (m' * c.s.t * m'⁻¹) * m' := by rw [hm'eq]
        _ = c.s.t := by group
    have hnH : m'⁻¹ * m ∈ c.s.H := by
      rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
      calc (m'⁻¹ * m) * c.s.t
          = ((m'⁻¹ * m) * c.s.t * (m'⁻¹ * m)⁻¹) * (m'⁻¹ * m) := by group
        _ = c.s.t * (m'⁻¹ * m) := by rw [hnconj]
    have hm'M6 : m' ∈ M6 c.e := h71.2.2.2.1 hm'M3
    have hnM6 : m'⁻¹ * m ∈ M6 c.e :=
      (M6 c.e).mul_mem ((M6 c.e).inv_mem hm'M6) hmM6
    have hnA : m'⁻¹ * m ∈ c.s.fr.A := by
      have hHA : c.s.H ⊓ M6 c.e = c.s.fr.A := h71.2.1.2.1
      rw [← hHA]
      exact ⟨hnH, hnM6⟩
    have hnF : ∀ f ∈ c.s.fr.F, f * (m'⁻¹ * m) = (m'⁻¹ * m) * f := by
      intro f hf
      have hm'f : m' * f = f * m' := hM3.comm hm'M3 (y7a_F_le_M3 c hf)
      have hmf : m * f = f * m := hmF f hf
      have hm'invf : m'⁻¹ * f = f * m'⁻¹ := by
        calc m'⁻¹ * f = m'⁻¹ * (f * m') * m'⁻¹ := by group
          _ = m'⁻¹ * (m' * f) * m'⁻¹ := by rw [← hm'f]
          _ = f * m'⁻¹ := by group
      calc f * (m'⁻¹ * m) = (f * m'⁻¹) * m := by group
        _ = (m'⁻¹ * f) * m := by rw [← hm'invf]
        _ = m'⁻¹ * (f * m) := by group
        _ = m'⁻¹ * (m * f) := by rw [← hmf]
        _ = (m'⁻¹ * m) * f := by group
    have hnCent : m'⁻¹ * m ∈ centIn L c.s.fr.F :=
      Subgroup.mem_inf.mpr ⟨s3_A_le_L c.s hnA, Subgroup.mem_centralizer_iff.mpr hnF⟩
    have hnFmem : m'⁻¹ * m ∈ c.s.fr.F := hcentF ▸ hnCent
    have hmM3 : m ∈ M3 c.s := by
      have heq : m = m' * (m'⁻¹ * m) := by group
      rw [heq]
      exact (M3 c.s).mul_mem hm'M3 (y7a_F_le_M3 c hnFmem)
    exact hmM3
  · intro m hm
    refine Subgroup.mem_inf.mpr ⟨h71.2.2.2.1 hm, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hM3.comm hm (y7a_F_le_M3 c hf)).symm

end CFSG.OddStandard.HigherRank.YamadaG23
