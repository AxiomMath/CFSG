module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Setup
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open scoped commutatorElement

section Comp

variable {G : Type} [Group G] [Finite G]

theorem commutator_barX_gammaD_eq {p : ℕ} {M D L : Subgroup G} (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    ⁅barX p M (gammaD D), barX p M L⁆ = barX p M L :=
  commutator_eq_of_isQuasisimple hL.2.2.1.2.2 hn hnc

theorem gammaD_le_normalizer {p : ℕ} (hp : p.Prime) {M D L : Subgroup G} (hD : Prop95Hyp p M D)
    (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    gammaD D ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hgM : g ∈ M := gammaD_le hD hg
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ ∈ barX p M (gammaD D) :=
    Subgroup.mem_map.2 ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  exact mem_normalizer_of_barX_normalizes hp le_rfl hL hgM (Subgroup.le_normalizer hgM) (hn hmem)

theorem commutator_gammaD_eq {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hD : Prop95Hyp p M D) (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    ⁅gammaD D, L⁆ = L := by
  have hΓL := gammaD_le_normalizer hp hD hL hn
  have hKL : ⁅gammaD D, L⁆ ≤ L := Subgroup.commutator_le.2 fun g hg l hl => by
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hΓL hg) l).1 hl) (L.inv_mem hl)
  have hnorm : (⁅gammaD D, L⁆.subgroupOf L).Normal := normal_subgroupOf_commutator hΓL
  have hsub : CFSG.Open.IsSubnormal ⁅gammaD D, L⁆ M :=
    CFSG.Open.IsSubnormal.step hKL hnorm hL.2.1
  have hbar : barX p M ⁅gammaD D, L⁆ = barX p M L := by
    rw [barX_commutator p (gammaD_le hD) hL.1]
    exact commutator_barX_gammaD_eq hL hn hnc
  by_contra hne
  exact hL.2.2.2 _ (lt_of_le_of_ne hKL hne) hsub hbar

theorem tl_commutator {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    tl M ⁅A, B⁆ = ⁅tl M A, tl M B⁆ := by
  unfold tl
  rw [subgroupOf_commutator hA hB, Subgroup.map_commutator]

theorem tl_commutator_gammaD {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hD : Prop95Hyp p M D) (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    ⁅tl M (gammaD D), tl M L⁆ = tl M L := by
  rw [← tl_commutator (gammaD_le hD) hL.1, commutator_gammaD_eq hp hD hL hn hnc]

theorem tl_pCoreOf_eq_bot (M : Subgroup G) : tl M (pCoreOf 2 M) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, hm, rfl⟩
  have hm2 : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := Subgroup.mem_subgroupOf.1 hm
  have hm' : m ∈ CFSG.pCore 2 ↥M := by
    obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.1 hm2
    have : n = m := Subtype.ext hnm
    exact this ▸ hn
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hm'

theorem tl_mono' {M X Y : Subgroup G} (h : X ≤ Y) : tl M X ≤ tl M Y :=
  Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem tl_glaPPrimeCoreOf_normal (p : ℕ) (M : Subgroup G) :
    (tl M (GLAPPrimeCoreOf p M)).Normal := by
  have hN : ((GLAPPrimeCoreOf p M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).2
      (le_normalizer_glaPPrimeCoreOf p M)
  unfold tl
  exact Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)

theorem commutator_tl_gammaD_glaPPrimeCore_eq_bot {p : ℕ} {M D : Subgroup G}
    (hD : Prop95Hyp p M D) (hQ : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M) :
    ⁅tl M (gammaD D), tl M (GLAPPrimeCoreOf p M)⁆ = ⊥ := by
  have hQM : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  rw [← tl_commutator (gammaD_le hD) hQM, eq_bot_iff]
  calc tl M ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ tl M (pCoreOf 2 M) := tl_mono' hQ
    _ = ⊥ := tl_pCoreOf_eq_bot M

theorem commutator_tl_L_glaPPrimeCore_eq_bot {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hD : Prop95Hyp p M D) (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hQ : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M) :
    ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ = ⊥ := by
  have hb : ⁅tl M (GLAPPrimeCoreOf p M), tl M (gammaD D)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact commutator_tl_gammaD_glaPPrimeCore_eq_bot hD hQ
  have hc : ⁅⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆, tl M (gammaD D)⁆ = ⊥ := by
    haveI := tl_glaPPrimeCoreOf_normal p M
    have h1 : ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ ≤ tl M (GLAPPrimeCoreOf p M) :=
      Subgroup.commutator_le_right _ _
    refine eq_bot_iff.2 ?_
    calc ⁅⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆, tl M (gammaD D)⁆
        ≤ ⁅tl M (GLAPPrimeCoreOf p M), tl M (gammaD D)⁆ := Subgroup.commutator_mono_left h1
      _ = ⊥ := hb
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := tl M (gammaD D)) (H₂ := tl M L) (H₃ := tl M (GLAPPrimeCoreOf p M)) hc
    (by rw [hb]; exact Subgroup.commutator_bot_left _)
  rw [tl_commutator_gammaD hp hD hL hn hnc] at hrot
  exact hrot

end Comp

end CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
