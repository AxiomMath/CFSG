module

public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.CoprimeNormalizerSup
import CFSG.RankThree.PartOne.CTP.StrongPGlue
import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.RankThree.PartOne

theorem isPGroup_le_of_le_sup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) {F R D : Subgroup X} (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hR3 : IsPGroup 3 R) (hD : IsPGroup p D) (hDle : D ≤ F ⊔ R) : D ≤ F := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  refine CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card
    (Fact.out : p.Prime) hRF hD hDle ?_
  obtain ⟨n, hn⟩ := hR3.exists_card_eq
  rw [hn]
  intro hdiv
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
    (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) hdiv))

theorem sup_inf_eq_of_inf_normalizer_le {X : Type*} [Group X] {F Y R : Subgroup X}
    (hYF : Y ≤ F) (hRY : R ≤ Subgroup.normalizer (Y : Set X))
    (hFY : F ⊓ Subgroup.normalizer (Y : Set X) ≤ Y) : (Y ⊔ R) ⊓ F = Y := by
  refine le_antisymm ?_ (le_inf le_sup_left hYF)
  intro g hg
  obtain ⟨y, hy, r, hr, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := Y) (K := R) hRY).mp hg.1
  have hrF : r ∈ F := by
    have h := F.mul_mem (F.inv_mem (hYF hy)) hg.2
    simpa using h
  exact Y.mul_mem hy (hFY (Subgroup.mem_inf.mpr ⟨hrF, hRY hr⟩))

theorem isStronglyPEmbedded_sup_subgroupOf {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp3 : p ≠ 3) {F Y R : Subgroup X} (hYF : Y ≤ F) (hYne : Y ≠ F)
    (hRF : R ≤ Subgroup.normalizer (F : Set X)) (hRY : R ≤ Subgroup.normalizer (Y : Set X))
    (hR3 : IsPGroup 3 R) (hpY : p ∣ Nat.card Y)
    (hk : ∀ k ∈ F, k ∉ Y →
      ¬ p ∣ Nat.card (Y ⊓ Y.map (MulAut.conj k).toMonoidHom : Subgroup X))
    (hFY : F ⊓ Subgroup.normalizer (Y : Set X) ≤ Y) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p ((Y ⊔ R).subgroupOf (F ⊔ R)) := by
  classical
  have hp : p.Prime := Fact.out
  have hMleA : Y ⊔ R ≤ F ⊔ R := sup_le (hYF.trans le_sup_left) le_sup_right
  have hY'map : ((Y ⊔ R).subgroupOf (F ⊔ R)).map (F ⊔ R).subtype = Y ⊔ R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMleA]
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have hAM : F ⊔ R ≤ Y ⊔ R := Subgroup.subgroupOf_eq_top.mp htop
    have hFM : F ≤ Y ⊔ R := le_sup_left.trans hAM
    have h := sup_inf_eq_of_inf_normalizer_le hYF hRY hFY
    rw [inf_eq_right.mpr hFM] at h
    exact hYne h.symm
  · have hcard : Nat.card ((Y ⊔ R).subgroupOf (F ⊔ R)) = Nat.card ↥(Y ⊔ R) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMleA).toEquiv
    rw [hcard]
    exact hpY.trans (Subgroup.card_dvd_of_le le_sup_left)
  · rintro g hg hpdvd
    obtain ⟨k, hkF, r, hrR, hgr⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := F) (K := R) hRF).mp g.2
    have hkY : k ∉ Y := by
      intro hkY
      exact hg (Subgroup.mem_subgroupOf.mpr (by
        rw [hgr]
        exact (Y ⊔ R).mul_mem (Subgroup.mem_sup_left hkY) (Subgroup.mem_sup_right hrR)))
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    let zA : ↥(F ⊔ R) := z
    have hzAord : orderOf zA = p := (Subgroup.orderOf_coe z).trans hzord
    let D : Subgroup ↥(F ⊔ R) := Subgroup.zpowers zA
    have hDcard : Nat.card D = p := by
      dsimp [D]
      rw [Nat.card_zpowers, hzAord]
    have hDp : IsPGroup p D := IsPGroup.of_card (n := 1) (by rw [hDcard, pow_one])
    have hDleY' : D ≤ (Y ⊔ R).subgroupOf (F ⊔ R) := Subgroup.zpowers_le.mpr z.2.1
    have hDleConj : D ≤ StrongP.conjSub g ((Y ⊔ R).subgroupOf (F ⊔ R)) :=
      Subgroup.zpowers_le.mpr z.2.2
    let E : Subgroup ↥(F ⊔ R) := StrongP.conjSub g⁻¹ D
    have hE_le : E ≤ (Y ⊔ R).subgroupOf (F ⊔ R) := by
      intro x hx
      change x ∈ D.map (MulAut.conj g⁻¹).toMonoidHom at hx
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
      have hd' : d ∈ StrongP.conjSub g ((Y ⊔ R).subgroupOf (F ⊔ R)) := hDleConj hd
      simpa [MulAut.conj_apply] using (StrongP.mem_conjSub_iff.mp hd')
    let DX : Subgroup X := D.map (F ⊔ R).subtype
    let EX : Subgroup X := E.map (F ⊔ R).subtype
    have hDXp : IsPGroup p DX := hDp.map (F ⊔ R).subtype
    have hDXle : DX ≤ F ⊔ R := Subgroup.map_subtype_le D
    have hDXF : DX ≤ F := isPGroup_le_of_le_sup hp3 hRF hR3 hDXp hDXle
    have hDXM : DX ≤ Y ⊔ R := by
      have h := Subgroup.map_mono (f := (F ⊔ R).subtype) hDleY'
      simpa [DX, hY'map] using h
    have hDXY : DX ≤ Y := by
      have h := sup_inf_eq_of_inf_normalizer_le hYF hRY hFY
      intro x hx
      rw [← h]
      exact Subgroup.mem_inf.mpr ⟨hDXM hx, hDXF hx⟩
    have hEp : IsPGroup p E := hDp.map (MulAut.conj g⁻¹).toMonoidHom
    have hEXp : IsPGroup p EX := hEp.map (F ⊔ R).subtype
    have hEXle : EX ≤ F ⊔ R := Subgroup.map_subtype_le E
    have hEXF : EX ≤ F := isPGroup_le_of_le_sup hp3 hRF hR3 hEXp hEXle
    have hEXM : EX ≤ Y ⊔ R := by
      have h := Subgroup.map_mono (f := (F ⊔ R).subtype) hE_le
      simpa [EX, hY'map] using h
    have hEXY : EX ≤ Y := by
      have h := sup_inf_eq_of_inf_normalizer_le hYF hRY hFY
      intro x hx
      rw [← h]
      exact Subgroup.mem_inf.mpr ⟨hEXM hx, hEXF hx⟩
    have hDXcard : Nat.card DX = p := by
      have h := Subgroup.card_map_of_injective (K := D) (f := (F ⊔ R).subtype)
        (F ⊔ R).subtype_injective
      rw [hDcard] at h
      simpa [DX] using h
    have hDXconjG : DX ≤ StrongP.conjSub (g : X) Y := by
      intro d hd
      rw [StrongP.mem_conjSub_iff]
      change d ∈ D.map (F ⊔ R).subtype at hd
      obtain ⟨dA, hdA, rfl⟩ := Subgroup.mem_map.mp hd
      have heE : (MulAut.conj g⁻¹) dA ∈ E :=
        Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hdA
      have heY : (((MulAut.conj g⁻¹) dA : ↥(F ⊔ R)) : X) ∈ Y :=
        hEXY (Subgroup.mem_map_of_mem (F ⊔ R).subtype heE)
      simpa [MulAut.conj_apply] using heY
    have hrY : StrongP.conjSub r Y = Y := by
      simpa [StrongP.conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRY hrR))
    have hconjeq : StrongP.conjSub (g : X) Y = StrongP.conjSub k Y := by
      calc
        StrongP.conjSub (g : X) Y = StrongP.conjSub (k * r) Y := by rw [hgr]
        _ = StrongP.conjSub k (StrongP.conjSub r Y) := (StrongP.conjSub_mul).symm
        _ = StrongP.conjSub k Y := by rw [hrY]
    have hDXconj : DX ≤ StrongP.conjSub k Y := hconjeq ▸ hDXconjG
    have hpdvd' : p ∣ Nat.card (Y ⊓ StrongP.conjSub k Y : Subgroup X) := by
      have hle : DX ≤ Y ⊓ StrongP.conjSub k Y := le_inf hDXY hDXconj
      have h := Subgroup.card_dvd_of_le hle
      rwa [hDXcard] at h
    exact hk k hkF hkY (by simpa [StrongP.conjSub] using hpdvd')

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

end
