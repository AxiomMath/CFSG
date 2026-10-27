module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def lImg (p : ℕ) (L Y : Subgroup G) : Subgroup (PQuot p L) :=
  (Y.subgroupOf L).map (pQuotHom p L)

theorem not_dvd_card_ker_pQuotHom {p : ℕ} (hp : p.Prime) (L : Subgroup G) :
    ¬ p ∣ Nat.card (pQuotHom p L).ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [ker_pQuotHom]
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card

theorem glaPLayer_le_self' {p : ℕ} {G' : Type} [Group G'] (Y : Subgroup G') :
    GLAPLayer p Y ≤ Y := by
  unfold GLAPLayer
  exact sSup_le fun _ hQ => hQ.1

theorem glaPLayer_subgroupOf {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L) :
    (GLAPLayer p Y).subgroupOf L = GLAPLayer p (Y.subgroupOf L) := by
  have h := Y10F.glaPLayer_map hp L.subtype_injective (Y.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hY] at h
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem lImg_glaPLayer {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L) :
    lImg p L (GLAPLayer p Y) = GLAPLayer p (lImg p L Y) := by
  unfold lImg
  rw [glaPLayer_subgroupOf hp hY]
  exact S267.map_glaPLayer hp _ (not_dvd_card_ker_pQuotHom hp L) _

private theorem pQuot_equiv_lImg {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L) :
    Nonempty (PQuot p Y ≃* PQuot p (lImg p L Y)) := by
  obtain ⟨e₀⟩ := nonempty_pQuot_equiv_subgroupOf p hY
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map hp (not_dvd_card_ker_pQuotHom hp L) (Y.subgroupOf L)
  exact ⟨e₀.symm.trans e₁⟩

private theorem isTypeWithCenter_of_pQuot_equiv' {H : Type} [Group H] [Finite H] {p : ℕ}
    {X : Subgroup G} {Y : Subgroup H} (e : PQuot p X ≃* PQuot p Y)
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} (h : IsTypeWithCenter p X Q z) :
    IsTypeWithCenter p Y Q z := by
  obtain ⟨hcat, hcard⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans f⟩⟩
  · rw [← hcard, ← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem isTypeWithCenter_of_lImg {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L)
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} (h : IsTypeWithCenter p (lImg p L Y) Q z) :
    IsTypeWithCenter p Y Q z := by
  obtain ⟨e⟩ := pQuot_equiv_lImg hp hY
  exact isTypeWithCenter_of_pQuot_equiv' e.symm h

private theorem glaPLayer_eq_bot_of_lImg {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L)
    (h : GLAPLayer p (lImg p L Y) = ⊥) : GLAPLayer p Y = ⊥ := by
  rw [eq_bot_iff]
  unfold GLAPLayer
  refine sSup_le fun Q hQ => ?_
  exfalso
  have hQ' := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp hY hQ
  have hQ'' := glaPComponent_map hp (pQuotHom p L)
    (coprime_card_inf_ker_pQuotHom hp L (Y.subgroupOf L)) hQ'
  have hle : (Q.subgroupOf L).map (pQuotHom p L) ≤ GLAPLayer p (lImg p L Y) := by
    unfold GLAPLayer
    exact le_sSup hQ''
  rw [h] at hle
  exact glaPComponent_ne_bot' hQ'' (le_bot_iff.1 hle)

theorem rowK_of_lImg {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hY : Y ≤ L) {row : Row}
    (h : RowK row p (GLAPLayer p (lImg p L Y))) : RowK row p (GLAPLayer p Y) := by
  have hE : GLAPLayer p Y ≤ L := (glaPLayer_le_self' Y).trans hY
  obtain ⟨e⟩ := pQuot_equiv_lImg hp hE
  rw [lImg_glaPLayer hp hY] at e
  cases row with
  | ly => exact glaPLayer_eq_bot_of_lImg hp hY h
  | fi24 => exact glaPLayer_eq_bot_of_lImg hp hY h
  | fi24h => exact glaPLayer_eq_bot_of_lImg hp hY h
  | suz => exact glaPLayer_eq_bot_of_lImg hp hY h
  | suzh => exact glaPLayer_eq_bot_of_lImg hp hY h
  | th => exact glaPLayer_eq_bot_of_lImg hp hY h
  | co2 => exact isTypeWithCenter_of_pQuot_equiv' e.symm h
  | co1 => exact isTypeWithCenter_of_pQuot_equiv' e.symm h
  | m3 => exact isTypeWithCenter_of_pQuot_equiv' e.symm h
  | m5 =>
    obtain ⟨f⟩ := h
    exact ⟨e.trans f⟩

theorem lImg_inf_centralizer {p q : ℕ} (hq : q.Prime) {L : Subgroup G}
    (hkq : ¬ q ∣ Nat.card (pQuotHom p L).ker) {y : G} (hyL : y ∈ L)
    (hy : IsPGroup q (Subgroup.zpowers y)) :
    lImg p L (L ⊓ Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({pQuotHom p L ⟨y, hyL⟩} : Set (PQuot p L)) := by
  unfold lImg
  rw [subgroupOf_inf_centralizer hyL, Subgroup.subgroupOf_self, top_inf_eq]
  have h := map_inf_centralizer_of_ker_le hq hkq (le_top : (pQuotHom p L).ker ≤ ⊤)
    (isPGroup_zpowers_mk hyL hy)
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (pQuotHom_surjective p L), top_inf_eq] at h
  exact h.symm

end CFSG.LocalAnalysis.GLTheoremA.H301
