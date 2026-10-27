module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Conc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def S267Conc268X (p : ℕ) {G : Type} [Group G] [Finite G] (L X : Subgroup G) : Prop :=
  ∃ B E D : Subgroup G, B ≤ X ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 4 ∧ E ≤ B ∧ Nat.card E = p ^ 3 ∧
    D ≤ E ∧ Nat.card D = p ^ 2 ∧
    (∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)) ∧
    (∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ D ≤ Subgroup.normalizer (U : Set G) ∧
      CoversMod p (Subgroup.normalizer (U : Set G)) (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)))) ∧
    GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G))
      (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))) ∧
    (∀ b ∈ B, CentMod p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))) b ↔ b ∈ D) ∧
    GLAPLayer p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)) ⊓
      Subgroup.centralizer (E : Set G)) ≠ ⊥

section Amb

variable {G : Type} [Group G] [Finite G]

theorem conc268X_of_Cov {p : ℕ} (hp : p.Prime) {X : Subgroup G} (H : Subgroup G) (hHX : H ≤ X)
    (K₀ : Subgroup ↥H) (h : S267Conc268Cov p K₀) : S267Conc268X p (K₀.map H.subtype) X := by
  classical
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hker : ¬ p ∣ Nat.card H.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff H.subtype).2 hinj, Subgroup.card_bot]
    exact hp.not_dvd_one
  obtain ⟨B₀, E₀, D₀, hBel, hBc, hEB, hEc, hDE, hDc, ⟨T₀, hT0, hT2, hTn⟩, ⟨U₀, hU0, hU2, hDU, hcov⟩,
    hcomp, hcm, hlay⟩ := h
  have hmapC : (K₀ ⊓ Subgroup.centralizer (D₀ : Set ↥H)).map H.subtype =
      K₀.map H.subtype ⊓ Subgroup.centralizer ((D₀.map H.subtype : Subgroup G) : Set G) :=
    map_inf_centralizer_inj H.subtype hinj K₀ D₀
  have hlayer : (GLAPLayer p (K₀ ⊓ Subgroup.centralizer (D₀ : Set ↥H))).map H.subtype =
      GLAPLayer p (K₀.map H.subtype ⊓ Subgroup.centralizer ((D₀.map H.subtype : Subgroup G) : Set G)) := by
    rw [map_glaPLayer hp H.subtype hker, hmapC]
  have hc : ∀ P : Subgroup ↥H, Nat.card (P.map H.subtype) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective hinj
  have hle : ∀ P : Subgroup ↥H, P.map H.subtype ≤ X := fun P =>
    (Subgroup.map_subtype_le P).trans hHX
  refine ⟨B₀.map H.subtype, E₀.map H.subtype, D₀.map H.subtype, hle B₀,
    CFSG.SectionRank.isElemAbelian_map hBel _, by rw [hc]; exact hBc, Subgroup.map_mono hEB,
    by rw [hc]; exact hEc, Subgroup.map_mono hDE, by rw [hc]; exact hDc, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨T₀.map H.subtype, hle T₀, fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective T₀ hinj).1 h),
      hT2.map _, ?_⟩
    exact (Subgroup.map_mono hTn).trans (Subgroup.le_normalizer_map _)
  · refine ⟨U₀.map H.subtype, hle U₀, fun h => hU0 ((Subgroup.map_eq_bot_iff_of_injective U₀ hinj).1 h),
      hU2.map _, (Subgroup.map_mono hDU).trans (Subgroup.le_normalizer_map _), ?_⟩
    rw [← hlayer]
    have hOJ : (GLAPPrimeCoreOf p (GLAPLayer p (K₀ ⊓ Subgroup.centralizer (D₀ : Set ↥H)))).map H.subtype =
        GLAPPrimeCoreOf p ((GLAPLayer p (K₀ ⊓ Subgroup.centralizer (D₀ : Set ↥H))).map H.subtype) :=
      map_glaPPrimeCoreOf hp H.subtype hker _
    have h1 := congrArg (Subgroup.map H.subtype) hcov
    unfold CoversMod
    rw [Subgroup.map_sup, hOJ] at h1
    refine le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _)) ?_
    refine h1.symm.le.trans (sup_le ?_ le_sup_right)
    exact ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf_right _
      (Subgroup.le_normalizer_map _))).trans le_sup_left
  · have := glaPComponent_map hp H.subtype (coprime_inf_ker hp H.subtype hker _) hcomp
    rwa [hmapC, hlayer] at this
  · rintro _ ⟨b₀, hb₀, rfl⟩
    rw [← hlayer, centMod_iff, ← mem_centModSubgroup_map_iff_inj hp H.subtype hinj, ← centMod_iff,
      hcm b₀ hb₀, Subgroup.mem_map_iff_mem hinj]
  · rw [← hlayer, ← map_inf_centralizer_inj H.subtype hinj, glaPLayer_map_ne_bot_iff hp H.subtype hker]
    exact hlay

end Amb

end CFSG.LocalAnalysis.GLTheoremA.S267

end
