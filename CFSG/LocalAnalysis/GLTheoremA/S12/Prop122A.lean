module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma6364Aux
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem catalogIs_or {S : Type} [Group S] {Q R : TauCeti.CFSGIndex → Prop} (h : catalogIs S fun i => Q i ∨ R i) :
    catalogIs S Q ∨ catalogIs S R := by
  obtain ⟨i, hi | hi, f⟩ := h
  · exact Or.inl ⟨i, hi, f⟩
  · exact Or.inr ⟨i, hi, f⟩

namespace NbrCfg

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem y_mem_D (h : NbrCfg G m p B x L D K y J) : y ∈ D := by
  rw [h.D_closure]
  exact Subgroup.subset_closure (by simp)

theorem y_not_mem (h : NbrCfg G m p B x L D K y J) : y ∉ Subgroup.zpowers x := by
  intro hy
  have hD : D ≤ Subgroup.zpowers x := by
    rw [h.D_closure, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · exact hy
  have hcard := Subgroup.card_le_of_le hD
  rw [h.cfg.card_D, Nat.card_zpowers] at hcard
  have hp := h.cfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime (h.cfg.elem.2 x h.cfg.xD) h.cfg.tri.ne_one
  rw [hord] at hcard
  have := hp.two_le
  nlinarith

theorem B_le_cy (h : NbrCfg G m p B x L D K y J) : B ≤ Subgroup.centralizer ({y} : Set G) := fun b hb => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact isElemAbelian_commute h.cfg.tri.bmax.1 hb h.yB

theorem pRank_B (h : NbrCfg G m p B x L D K y J) : CFSG.Open.pRank p B = m :=
  L6364.pRank_eq_of_card h.cfg.prime h.cfg.tri.bmax.1 h.cfg.card_B

theorem two_le_index (h : NbrCfg G m p B x L D K y J) (hin : CommonInputs G p) :
    p ^ 2 * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B := by
  rw [S12.centMod_inf_eq h.cfg hin, h.cfg.card_D, h.cfg.card_B, ← pow_add]
  exact Nat.pow_le_pow_right h.cfg.prime.pos h.cfg.four_le

end NbrCfg

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem twoRank_le_top {q : ℕ} (hq : q.Prime) (X : Subgroup G) : GLATwoLocalRank q ↥X ≤ GLATwoLocalRank q G :=
  CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hq X

theorem pcomp_mem_family (hp : p.Prime) {y : G} {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M)
    {𝒞 : Set (Subgroup G)} (h𝒞 : ∀ M' ∈ 𝒞, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M')
    (hMle : M ≤ ⨆ M' ∈ 𝒞, M') : M ∈ 𝒞 :=
  mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞 hM (by rwa [sSup_eq_iSup])

theorem closureIn_J_B (h : NbrCfg G m p B x L D K y J) (hin : CommonInputs G p) :
    closureIn J B = Ky p K y := by
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h.cfg hin h.y_mem_D h.y_not_mem
  have hJ𝒞 : J ∈ 𝒞 := pcomp_mem_family h.cfg.prime h.J_comp hC1 (by rw [hC2]; exact h.J_le_Ky)
  apply le_antisymm
  · rw [closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun b hb => ?_
    have hn := ky_norm h.cfg h.y_mem_D hb
    have h1 : GLBConj b J ≤ GLBConj b (Ky p K y) := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono b h.J_le_Ky
    rwa [mem_normalizer_iff_gLBConj_eq.1 hn] at h1
  · rw [← hC2]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨e, he, rfl⟩ := hC4 J hJ𝒞 M hM
    rw [closureIn_eq_iSup_gLBConj]
    have heB : e ∈ B := (Subgroup.zpowers_le.2 h.cfg.tri.mem) he
    exact le_biSup (fun g => GLBConj g J) heB

theorem x_not_norm (h : NbrCfg G m p B x L D K y J) (hin : CommonInputs G p) (hne : Ky p K y ≠ J) :
    x ∉ Subgroup.normalizer (J : Set G) := by
  intro hxN
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h.cfg hin h.y_mem_D h.y_not_mem
  have hJ𝒞 : J ∈ 𝒞 := pcomp_mem_family h.cfg.prime h.J_comp hC1 (by rw [hC2]; exact h.J_le_Ky)
  apply hne
  apply le_antisymm
  · rw [← hC2]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨e, he, rfl⟩ := hC4 J hJ𝒞 M hM
    have heN : e ∈ Subgroup.normalizer (J : Set G) := (Subgroup.zpowers_le.2 hxN) he
    rw [mem_normalizer_iff_gLBConj_eq.1 heN]
  · exact h.J_le_Ky

theorem ky_eq_J (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) : Ky p K y = J := by
  by_contra hne
  have hcom := hin.l121.common
  have hxJ := x_not_norm h hcom hne
  have hcl := closureIn_J_B h hcom
  have hy1 : y ≠ 1 := h.y_ne_one
  have hKy : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) := kGroup_centralizer h.cfg.ctx.toS6 hy1
  have hK' : GLAPComponent p (closureIn J B ⊓ Subgroup.centralizer ({x} : Set G)) K := by
    rw [hcl]
    exact ky_pcomp_cent h.cfg hcom h.y_mem_D h.y_not_mem
  have hrank : GLATwoLocalRank p ↥(Subgroup.centralizer ({y} : Set G)) ≤ CFSG.Open.pRank p B := by
    rw [h.pRank_B]
    exact (twoRank_le_top h.cfg.prime _).trans h.cfg.ctx.rank.le
  obtain ⟨hp3, hcat, hZ⟩ := hin.i112 p (Subgroup.centralizer ({y} : Set G)) B J K x h.cfg.prime h.cfg.odd hKy
    h.cfg.tri.bmax.1 h.B_le_cy hrank h.J_comp h.cfg.tri.mem hxJ hK' (std_chev2 h.cfg hcom) (std_inner h.cfg hcom)
    (h.two_le_index hcom)
  subst hp3
  rcases catalogIs_or hcat with hl3 | hA6
  ·
    have hyL : y ∈ Subgroup.normalizer (L : Set G) := h.cfg.tri.norm h.yB
    have hy3 : y ^ 3 = 1 := h.cfg.elem.2 y h.y_mem_D
    have hnc : ¬ CentMod 3 L y := fun hc =>
      h.y_not_mem ((h.cfg.tri.cent h.cfg.ctx y h.yB).1 hc)
    have hKc : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) K :=
      std_pcomp_Ly h.cfg hcom h.y_mem_D h.y_not_mem
    refine hin.i1419 _ L K y (kGroup_centralizer h.cfg.ctx.toS6 h.cfg.tri.ne_one) h.cfg.tri.comp hyL hy3 hnc hKc hl3
      hZ ?_
    exact innDiagOn_mono (innDiagOn_of_inner h.cfg.tri.comp (h.cfg.tri.qs h.cfg.ctx) h.cfg.tri.idiag)
      (Subgroup.zpowers_le.2 h.yB)
  ·
    rcases lemma121 h.cfg hin.l121 with ⟨hU, -⟩ | ⟨hns, -⟩
    · exact hin.disj _ hU hA6
    · exact hns (Or.inr hA6)

theorem nbr_norm (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) :
    B ≤ Subgroup.normalizer (J : Set G) := by
  rw [← ky_eq_J h hin]
  exact ky_norm h.cfg h.y_mem_D

end S12

end CFSG.LocalAnalysis.GLTheoremA
