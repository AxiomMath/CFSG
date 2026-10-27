module

public import CFSG.GH74.GLS.Stage4.HexRGD
public import CFSG.GH74.GLS.SP.GlueMap
public import CFSG.GH74.GLS.SP.GlueBN

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.TitsSimplicity

namespace CFSG.GH74.GLS.Stage4.Hex

section Quotient

variable {K : Type} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

@[expose] def hexProj (K : Type) [Group K] : K →* K ⧸ Subgroup.center K :=
  QuotientGroup.mk' (Subgroup.center K)

theorem ker_hexProj : (hexProj K).ker = Subgroup.center K := by
  rw [hexProj, QuotientGroup.ker_mk']

theorem hexProj_surjective : Function.Surjective (hexProj K) :=
  QuotientGroup.mk'_surjective _

variable (hd : G2Data X n H)

include hd

theorem hex_center_le_torus : Subgroup.center K ≤ ⨆ i, H i := by
  rw [center_eq_normalCore_borel hd.ct hd.ext hd.bruhat]
  exact normalCore_borel_le_iSup hd.ct hd.bruhat

theorem hex_posUnipotent_inf_center :
    posUnipotent (g2Shape X) ⊓ Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : x ∈ (⨆ i, H i) ⊓ posUnipotent (g2Shape X) :=
    ⟨hex_center_le_torus hd hx.2, hx.1⟩
  have h0 : (⨆ i, H i) ⊓ posUnipotent (g2Shape X) = ⊥ := hd.ext.torus_inf_posPart
  rw [h0] at h
  exact h

theorem hexProj_ker_le : (hexProj K).ker ≤ ⨆ i, H i := by
  rw [ker_hexProj]
  exact hex_center_le_torus hd

theorem posUnipotent_inf_ker_hexProj : posUnipotent (g2Shape X) ⊓ (hexProj K).ker = ⊥ := by
  rw [ker_hexProj]
  exact hex_posUnipotent_inf_center hd

theorem hexQuotRGD2 :
    RGD2 6 ((⨆ i, H i).map (hexProj K)) (hexProj K (n 1)) (hexProj K (n 0))
      ((posUnipotent (g2Shape X)).map (hexProj K)) (fun i => (hexGroup X i).map (hexProj K)) :=
  (hexRGD2 hd).map (hexProj K) (hexProj_ker_le hd) (posUnipotent_inf_ker_hexProj hd)

theorem hexQuotRGD2_gen :
    (((⨆ i, H i).map (hexProj K)) ⊔ (posUnipotent (g2Shape X)).map (hexProj K)) ⊔
      (hexQuotRGD2 hd).N = ⊤ :=
  (hexRGD2 hd).map_gen (hexProj K) hexProj_surjective (hexProj_ker_le hd)
    (posUnipotent_inf_ker_hexProj hd) (hexRGD2_gen hd)

@[expose] def hexQuotPre :
    PreRankTwoSystem (K ⧸ Subgroup.center K) 6 :=
  (hexQuotRGD2 hd).toPre (hexQuotRGD2_gen hd)

@[expose] def hexQuotSystem
    [IsSimpleGroup (K ⧸ Subgroup.center K)] :
    RankTwoSystem (K ⧸ Subgroup.center K) 6 :=
  (hexQuotPre hd).toSystemOfSimple

theorem hexQuotSystem_root
    [IsSimpleGroup (K ⧸ Subgroup.center K)] (i : ℤ) :
    (hexQuotSystem hd).root i = (hexGroup X i).map (hexProj K) :=
  rfl

theorem hexQuotSystem_U
    [IsSimpleGroup (K ⧸ Subgroup.center K)] :
    (hexQuotSystem hd).U = (posUnipotent (g2Shape X)).map (hexProj K) :=
  rfl

omit hd

theorem nat_card_map_of_inf_ker_eq_bot {G G' : Type*} [Group G] [Group G'] (π : G →* G')
    (S : Subgroup G) (h : S ⊓ π.ker = ⊥) : Nat.card (S.map π) = Nat.card S := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap S) ⟨?_, π.subgroupMap_surjective S⟩)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx' : (x : G) ∈ S ⊓ π.ker := ⟨x.2, by simpa using congrArg Subtype.val hx⟩
  rw [h] at hx'
  exact Subtype.ext (by simpa using hx')

include hd

theorem card_hexQuotGroup {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    Nat.card ((hexGroup X i).map (hexProj K)) = Nat.card (hexGroup X i) := by
  refine nat_card_map_of_inf_ker_eq_bot (hexProj K) (hexGroup X i) ?_
  rw [eq_bot_iff, ← posUnipotent_inf_ker_hexProj hd]
  exact inf_le_inf_right _ (hexGroup_le_posUnipotent h1 h6)

end Quotient

end CFSG.GH74.GLS.Stage4.Hex
