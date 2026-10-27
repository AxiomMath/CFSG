module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem psl2_section_of_shape {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape Y F₁ F₂) : IsSection (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁) Y := by
  have h0 : IsSection (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁) SL(2, F₁) :=
    ⟨⊤, (QuotientGroup.mk' (Subgroup.center SL(2, F₁))).comp (⊤ : Subgroup SL(2, F₁)).subtype,
      fun y => by
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, F₁)) y
        exact ⟨⟨g, trivial⟩, hg⟩⟩
  exact IsSection.of_le S.I₁ (IsSection.of_equiv S.e₁ h0)

section D4


theorem d4_psl2_section {M : Type} [Group M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ f) ^ 3 ∧
      IsSection (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ↥(centralizer ({z} : Set M)) := by
  obtain ⟨F₁, F₂, hF₁, hF₂, hfin₁, hfin₂, S, hc₁, hc₂, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hM z hz
  exact ⟨F₁, hF₁, hfin₁, hc₁, psl2_section_of_shape S⟩

theorem not_kfa_D4 {Y : Type} [Group Y] [Finite Y] (hns : ¬ Group.IsSolvable Y) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hM : LieModel Y .trialityD4 0 p f) :
    ¬ KindFactorAll Kind.ly Y := by
  intro hK
  obtain ⟨z, hz⟩ := exists_involution_of_not_solvable hns
  obtain ⟨F, hF, hfin, hcard, hsec⟩ := d4_psl2_section hp hp2 hM z hz
  exact not_kfa_psl2_cube hp hp2 hf hcard (kfa_of_isSection hK (IsSection.of_le _ hsec))

theorem cellAbs_D4 : CellAbs FD4 := by
  intro A _ _ zb Sb Vb J hfr hJ _ hF
  exfalso
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := not_isSolvable_quot_of_quasisimple hJ.1
  have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := not_kfa_D4 hns hp hp2 hf hm
  obtain ⟨hZ, -, -⟩ := hfr.reduce hJ hnk
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmJ : LieModel ↥J .trialityD4 0 p f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm
  obtain ⟨u, hu⟩ := exists_involution_of_not_solvable (not_isSolvable_of_quot (center ↥J) hns)
  obtain ⟨F, hF, hfin, hcard, hsec⟩ := d4_psl2_section hp hp2 hmJ u hu
  have h27 : 4 ≤ Nat.card F := by
    rw [hcard]
    have h3 : 3 ≤ p ^ f := by
      have := hp.two_le
      calc 3 ≤ p := by omega
        _ ≤ p ^ f := Nat.le_self_pow (by omega) p
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left h3 3
  have := psl2_simple h27
  exact not_kfa_psl2_cube hp hp2 hf hcard
    (kfa_of_cent_section hfr J u hu (psl2_not_isSolvable h27) hsec)

end D4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
