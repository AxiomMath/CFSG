module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SNT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NW2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_wr7_of_cfg {c : Ctx7 G L} (h5 : c.toCtx5.Facts5) (h7 : c.Upto79)
    {L1 : Subgroup G} (hL1 : IsCompPre c.s L1) :
    Wr7 c.s.t (P7 c.e) (U7 c L1) ∧ centEl (P7 c.e) c.s.t = c.s.fr.S := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, _⟩, _⟩, _⟩, _⟩, h76⟩, h77⟩, _h78⟩, h79⟩ := h7
  have hdir := isInternalDirect_sylow (h79 L1 hL1).1 h77.1
  have ht : c.s.t ∈ normalizer (P7 c.e : Set G) := c.t_mem_normalizer_P7 h5.2.1 h71
  refine ⟨⟨?_, ?_⟩, h76.2.2.1⟩
  · simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  · rw [show U7 c L1 = ⁅L1, L1⁆ ⊓ P7 c.e from rfl]
    rw [conjSub_inf_of_mem_normalizer ht]
    exact hdir

theorem y7n_P0_normalizes_U0 {t : G} {Lam P1 P0 : Subgroup G} (hp0 : P0 = normIn P1 Lam)
    (hnormal : P1 ≤ normalizer (P0 : Set G)) (hsplit : P1 = P0 ⊔ zpowers t) :
    ∀ y ∈ P0, ∀ u ∈ conjSub t (centIn P1 Lam), y * u * y⁻¹ ∈ conjSub t (centIn P1 Lam) := by
  intro y hy u hu
  rw [mem_conjSub_iff'] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  have hcP1 : c ∈ P1 := hc.1
  have hcC : c ∈ Subgroup.centralizer (Lam : Set G) := hc.2
  have htP1 : t ∈ P1 := by
    rw [hsplit]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htP0 : t ∈ normalizer (P0 : Set G) := hnormal htP1
  have hP0P1 : P0 ≤ P1 := by rw [hp0]; exact inf_le_left
  set y' : G := t⁻¹ * y * t with hy'_def
  have hy'P0 : y' ∈ P0 := by
    rw [hy'_def]
    exact (Subgroup.mem_set_normalizer_iff''.mp htP0 y).mp hy
  have hy'P1 : y' ∈ P1 := hP0P1 hy'P0
  have hy'norm : y' ∈ normalizer (Lam : Set G) := by
    have : y' ∈ normIn P1 Lam := by rw [← hp0]; exact hy'P0
    exact this.2
  have hc'P1 : y' * c * y'⁻¹ ∈ P1 :=
    P1.mul_mem (P1.mul_mem hy'P1 hcP1) (P1.inv_mem hy'P1)
  have hc'C : y' * c * y'⁻¹ ∈ Subgroup.centralizer (Lam : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hyl : y'⁻¹ * l * y' ∈ Lam :=
      (Subgroup.mem_set_normalizer_iff''.mp hy'norm l).mp hl
    have hcomm : (y'⁻¹ * l * y') * c = c * (y'⁻¹ * l * y') :=
      Subgroup.mem_centralizer_iff.mp hcC (y'⁻¹ * l * y') hyl
    calc l * (y' * c * y'⁻¹) = y' * ((y'⁻¹ * l * y') * c) * y'⁻¹ := by group
      _ = y' * (c * (y'⁻¹ * l * y')) * y'⁻¹ := by rw [hcomm]
      _ = y' * c * y'⁻¹ * l := by group
  rw [mem_conjSub_iff']
  refine ⟨y' * c * y'⁻¹, ⟨hc'P1, hc'C⟩, ?_⟩
  rw [hy'_def]
  group

theorem y7n_elemCover_P0 (hB : Sec3Inputs) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h7 : c.Upto79) (hRT : c.s.R ≠ c.s.T)
    {L1 P1 P0 : Subgroup G} (hcfg : NTCfg c L1 P1 P0) : ElemCover 64 P0 := by
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  obtain ⟨hgT, _hgR, hgσ, hg2, -⟩ := c.g_spec hRT
  have hF : SgFacts c.s.fr.S c.s.fr.F c.g := sgFacts_of_setting hH hg2 hgσ
  rcases hcfg.cases with hcase1 | hcase2
  · obtain ⟨g0, hg0U, hg0sq, hg0U', hU0eq, hg0g0t, hdir, ⟨iso⟩⟩ := hcase1
    have hU0 : ElemCover 8 (U07 c L1 P1) := ElemCover.of_mulEquiv iso.symm hF.elemCover
    have hU0t : ElemCover 8 (conjSub c.s.t (U07 c L1 P1)) := ElemCover.conj c.s.t hU0
    have hprod : ElemCover (8 * 8) P0 := ElemCover.prod hdir hU0 hU0t
    simpa using hprod
  · obtain ⟨hU0U, hP0⟩ := hcase2
    obtain ⟨hwr, hcent⟩ := y7n_wr7_of_cfg h5 h7 hcfg.comp
    have htg : c.s.t * c.g = c.g * c.s.t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (c.s.sylow_T.1 hgT)).symm
    have hgP0 : c.g ∈ P0 := by
      rw [hP0]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.g)
    have hgU : ∀ u ∈ U7 c L1, c.g * u * c.g⁻¹ ∈ U7 c L1 := by
      intro u hu
      have hu' : u ∈ conjSub c.s.t (centIn P1 ⁅L1, L1⁆) := by
        rw [← U07, hU0U]
        exact hu
      have h := y7n_P0_normalizes_U0 hcfg.p0 hcfg.normal hcfg.split c.g hgP0 u hu'
      rwa [← U07, hU0U] at h
    have hcov : ElemCover 64 (P7 c.e ⊔ zpowers c.g) := y7n_case2_cover hwr hcent hF htg hgU
    simpa only [hP0] using hcov

end CFSG.OddStandard.HigherRank.YamadaG23
