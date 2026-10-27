module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4G3a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4E32
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4G2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_g_sq (c : Ctx4 s e) (h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂) {g : G}
    (hgT : g ∈ s.T) (hgR : g ∉ s.R) (hgσ : ActsAs L g s.fr'.σ)
    (hg2 : g ^ 2 = 1 ∨ g ^ 2 = s.t) : g ^ 2 = s.t := by
  by_contra hne
  have hg2one : g ^ 2 = 1 := hg2.resolve_right hne
  have hRT : s.R ≠ s.T := by
    intro h
    rw [h] at hgR
    exact hgR hgT
  have hnormT : e.T₁ ≤ Subgroup.normalizer (s.T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer e.T_le).mp
      (s3_T_normal_T1 s c.hA c.h31 e)
  have hY0T : y4Y0 s g ≤ s.T := y4_Y0_le_T c hgT
  have hY0ea : IsElemAbelian 2 (y4Y0 s g) := y4_Y0_isElemAbelian c hg2one hgT hgR hgσ
  have hY0card : Nat.card ↥(y4Y0 s g) = 32 := y4_Y0_card c hg2one hgT hgR hgσ
  have hY0F : y4Y0 s g ⊓ s.fr.B = s.fr.F := y4_Y0_inf_B c hg2one hgT hgR hgσ
  have hT1leT : e.T₁ ≤ s.T := by
    intro x hx
    let f : G →* G := (MulAut.conj x).toMonoidHom
    have hxT2 : x ∈ s.T₂ := f3_c8 c.toF33 hx
    have hxX : x ∈ s.X := y4_T2_le_X c hxT2
    have hxNormB : x ∈ normalizer (s.fr.B : Set G) := f3_X_le_normB c.toF33 hxX
    have hmapT : s.T.map f = s.T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormT hx)
    have hYT : (y4Y0 s g).map f ≤ s.T := by
      rw [← hmapT]
      exact Subgroup.map_mono hY0T
    have hY : IsElemAbelian 2 ((y4Y0 s g).map f) := hY0ea.map f
    have hcard : 32 ≤ Nat.card ↥((y4Y0 s g).map f) := by
      have h := Subgroup.card_map_of_injective (K := y4Y0 s g) (f := f)
        (show Function.Injective f from (MulAut.conj x).injective)
      omega
    have hconjle : (y4Y0 s g).map f ≤ y4Y0 s g := by
      simpa only [y4Y0] using y4_E32_le c hRT hg2one hgT hgR hgσ hYT hY hcard
    have hxNormY : x ∈ normalizer (y4Y0 s g : Set G) :=
      y4_mem_normalizer_of_conj_mem fun u hu => by
        have hmem : f u ∈ (y4Y0 s g).map f := Subgroup.mem_map_of_mem f hu
        exact hconjle (by simpa [f, MulAut.conj_apply] using hmem)
    have hxNormF : x ∈ normalizer (s.fr.F : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hYiff := Subgroup.mem_normalizer_iff.mp hxNormY y
      have hBiff := Subgroup.mem_normalizer_iff.mp hxNormB y
      simp only [← hY0F, Subgroup.mem_inf, hYiff, hBiff]
    exact y4_normT2_F c h42 x hxT2 hxNormF
  have hEq : e.T₁ = s.T := le_antisymm hT1leT e.T_le
  have hdef := c.hDef.2.1
  rw [hEq, Subgroup.relIndex_self] at hdef
  norm_num at hdef

end CFSG.OddStandard.HigherRank.YamadaG23
