module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_fusion_NT {g : G} (hg : g * s.t * g⁻¹ ∈ cen s.T) :
    ∃ n ∈ normalizer (s.T : Set G), n * (g * s.t * g⁻¹) * n⁻¹ = s.t := by
  have hle : conjSub g⁻¹ s.T ≤ s.H := by
    intro y hy
    rw [conjSub] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    change (MulAut.conj g⁻¹) x ∈ Subgroup.centralizer ({s.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem : g * s.t * g⁻¹ ∈ Subgroup.centralizer (s.T : Set G) :=
      (Subgroup.mem_inf.mp hg).2
    have h1 : x * (g * s.t * g⁻¹) = (g * s.t * g⁻¹) * x :=
      Subgroup.mem_centralizer_iff.mp hmem x hx
    have h2 : ((MulAut.conj g⁻¹) x) * s.t = s.t * ((MulAut.conj g⁻¹) x) := by
      have hc : Commute x (g * s.t * g⁻¹) := h1
      have hconj := (hc.conj g⁻¹).eq
      rw [show g⁻¹ * (g * s.t * g⁻¹) * (g⁻¹)⁻¹ = s.t by group] at hconj
      simpa only [MulAut.conj_apply] using hconj
    exact h2.symm
  have hQ : IsPGroup 2 (conjSub g⁻¹ s.T) :=
    s.sylow_T.2.1.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨h, hh, hconj⟩ := exists_conj_le_isSylowIn s.sylow_T hQ hle
  have hmap : conjSub (h * g⁻¹) s.T ≤ s.T := by
    intro y hy
    rw [conjSub] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hz : (MulAut.conj g⁻¹) x ∈ conjSub g⁻¹ s.T := by
      rw [conjSub]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hz' : (MulAut.conj h) ((MulAut.conj g⁻¹) x) ∈ conjSub h (conjSub g⁻¹ s.T) := by
      rw [conjSub]
      exact Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) x, hz, rfl⟩
    have hmem : (MulAut.conj h) ((MulAut.conj g⁻¹) x) ∈ s.T := hconj hz'
    change (MulAut.conj (h * g⁻¹)) x ∈ s.T
    rw [show (MulAut.conj (h * g⁻¹)) x = (MulAut.conj h) ((MulAut.conj g⁻¹) x) by
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group]
    exact hmem
  have hcard : Nat.card ↥(conjSub (h * g⁻¹) s.T) = Nat.card ↥s.T :=
    Subgroup.card_map_of_injective (MulAut.conj (h * g⁻¹)).injective
  have heq : conjSub (h * g⁻¹) s.T = s.T :=
    Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)
  refine ⟨h * g⁻¹, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [conjSub] using heq),
    ?_⟩
  rw [show (h * g⁻¹) * (g * s.t * g⁻¹) * (h * g⁻¹)⁻¹ = h * s.t * h⁻¹ by group,
    (Subgroup.mem_centralizer_iff.mp hh s.t (by simp)).symm]
  group

end CFSG.OddStandard.HigherRank.YamadaG23
