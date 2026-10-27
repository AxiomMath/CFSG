module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Four
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Pow4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_t_conj_not_mem_L (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) : ∀ g : G, g * s.t * g⁻¹ ∉ L := by
  intro g hg
  set u : G := g * s.t * g⁻¹ with hu
  have huL : u ∈ L := hg
  have hu2 : orderOf u = 2 := by
    rw [hu, show g * s.t * g⁻¹ = MulAut.conj g s.t from (MulAut.conj_apply g s.t).symm,
      MulEquiv.orderOf_eq (MulAut.conj g) s.t, s.t_order]
  have hzL : s.fr.z ∈ L := s3_z_mem_L s
  have hz2 : orderOf s.fr.z = 2 := (lfactsA_of_setting hS hZ s).z_order
  obtain ⟨l, -, hl⟩ := s3_invol_conj hS hZ s huL hu2 hzL hz2
  set y : G := l * g with hy
  have hzy : s.fr.z = y * s.t * y⁻¹ := by
    rw [hl, hu, hy]
    group
  set v₀ : G := s.fr.a₁ * s.fr.h₀ with hv₀
  have hpow : v₀ ^ 4 = s.fr.z := by
    simpa [hv₀] using srel_a1h0_pow4 (s3_srel hS hZ s)
  have hconj : (y⁻¹ * v₀ * y) ^ 4 = y⁻¹ * v₀ ^ 4 * y := by
    simpa using (conj_pow (a := y⁻¹) (b := v₀) (i := 4))
  have hw : (y⁻¹ * v₀ * y) ^ 4 = s.t := by
    rw [hconj, hpow, hzy]
    group
  exact (s3_no_fourth_root s hS hZ hOut hQ (y⁻¹ * v₀ * y)) hw

end CFSG.OddStandard.HigherRank.YamadaG23
