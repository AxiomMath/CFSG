module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Facts
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourSymplecticFusion
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem generalizedFitting_Hz_eq_pCore {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    generalizedFitting ↥(Hz z) = pCore 2 ↥(Hz z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNmap : (generalizedFitting ↥(Hz z)).map (Hz z).subtype = Fz z := rfl
  have hNcard : Nat.card ↥(generalizedFitting ↥(Hz z)) = 16 := by
    rw [← card_Fz hZ hz, ← hNmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (Hz z).subtype
      Subtype.val_injective).toEquiv
  have hNnormal : (generalizedFitting ↥(Hz z)).Normal := by
    constructor
    intro n hn g
    have hconj := CFSG.WholeGroup.generalizedFitting_map_mulEquiv (MulAut.conj g)
    have hmem : (MulAut.conj g) n ∈ (generalizedFitting ↥(Hz z)).map
        (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hn
    rw [hconj] at hmem
    simpa using hmem
  have hNp : IsPGroup 2 ↥(generalizedFitting ↥(Hz z)) :=
    IsPGroup.of_card (n := 4) (by rw [hNcard]; norm_num)
  apply le_antisymm
  · exact le_sSup ⟨hNnormal, hNp⟩
  · have hnil : Group.IsNilpotent ↥(pCore 2 ↥(Hz z)) := (pCore_isPGroup).isNilpotent
    have h1 := (CFSG.LocalCores.fitting_characteristic (G := ↥(Hz z))).2.2 (pCore 2 ↥(Hz z))
      pCore_normal hnil
    rw [generalizedFitting.eq_sup]
    exact h1.trans le_sup_left

theorem Fz_eq_inSubgroup_pCore {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    Fz z = inSubgroup (pCore 2) (Hz z) := by
  show Fz z = (pCore 2 ↥(Hz z)).map (Hz z).subtype
  rw [← generalizedFitting_Hz_eq_pCore hZ hz]
  rfl

theorem card_pCore_Hz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    Nat.card ↥(pCore 2 ↥(Hz z)) = 16 := by
  rw [← generalizedFitting_Hz_eq_pCore hZ hz, ← card_Fz hZ hz]
  have hNmap : (generalizedFitting ↥(Hz z)).map (Hz z).subtype = Fz z := rfl
  rw [← hNmap]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ (Hz z).subtype
    Subtype.val_injective).toEquiv

theorem card_center_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    Nat.card ↥(Subgroup.center ↥(Fz z)) = 4 := by
  obtain ⟨Z, A, hZeq, hZc, hZ4, -⟩ := unpack hZ hz
  have h := Subgroup.card_map_of_injective (K := Subgroup.center ↥(Fz z))
    (f := (Fz z).subtype) Subtype.val_injective
  rw [← h]
  show Nat.card ↥(Zc z) = 4
  rw [hZeq, hZ4]

theorem card_Hz_eq_mul {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    ∃ m : ℕ, m ∣ 6 ∧ Nat.card ↥(Hz z) = 16 * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : IsCharacteristicP 2 ↥(Hz z) :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mpr
      (generalizedFitting_Hz_eq_pCore hZ hz)
  obtain ⟨hvel, ⟨v, ⟨hv1, hvfin⟩, -⟩, b, hrule, -, -, -, ρ, -, hker, -, ⟨ι, hιinj, hι⟩, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergCH.core_symplectic_transport (B := ⊥) bot_le hchar
      (by simp) (Fz_eq_inSubgroup_pCore hZ hz) (isCyclic_center_Fz hZ hz)
      (isElementaryAbelian_quot_Fz hZ hz) (z_mem_Zc hZ hz) hz (commutator_Fz hZ hz)
  haveI := hvel
  set P := pCore 2 ↥(Hz z) with hPdef
  have hmap : (pCore 2 ↥(Hz z)).map (Hz z).subtype = Fz z := by
    rw [Fz_eq_inSubgroup_pCore hZ hz]
    rfl
  let eP : ↥(pCore 2 ↥(Hz z)) ≃* ↥(Fz z) :=
    (Subgroup.equivMapOfInjective (pCore 2 ↥(Hz z)) (Hz z).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hPcard : Nat.card ↥(pCore 2 ↥(Hz z)) = 16 := card_pCore_Hz hZ hz
  have hcenP : Nat.card ↥(Subgroup.center ↥(pCore 2 ↥(Hz z))) = 4 := by
    have h1 : Subgroup.map eP (Subgroup.center ↥(pCore 2 ↥(Hz z))) =
        Subgroup.center ↥(Fz z) := Subgroup.map_center_eq eP
    rw [← card_center_Fz hZ hz, ← h1]
    exact (Subgroup.card_map_of_injective (f := eP.toMonoidHom) eP.injective).symm
  have hquot : Nat.card (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z))) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(pCore 2 ↥(Hz z)))
    rw [hcenP, hPcard] at h
    omega
  have hVcard : Nat.card (Additive (↥(pCore 2 ↥(Hz z)) ⧸
      Subgroup.center ↥(pCore 2 ↥(Hz z)))) = 4 :=
    (Nat.card_congr Additive.ofMul).symm.trans hquot
  haveI : Fintype (Additive (↥(pCore 2 ↥(Hz z)) ⧸
      Subgroup.center ↥(pCore 2 ↥(Hz z)))) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive (↥(pCore 2 ↥(Hz z)) ⧸
      Subgroup.center ↥(pCore 2 ↥(Hz z)))) = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2)
      (V := Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z))))
    rw [← Nat.card_eq_fintype_card, hVcard, ZMod.card] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  let bas := Module.finBasisOfFinrankEq (ZMod 2) (Additive (↥(pCore 2 ↥(Hz z)) ⧸
      Subgroup.center ↥(pCore 2 ↥(Hz z)))) hfin
  have hGL : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive (↥(pCore 2 ↥(Hz z)) ⧸
      Subgroup.center ↥(pCore 2 ↥(Hz z))))) = 6 := by
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' bas).toEquiv, Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  have hdvd : Nat.card (↥(Hz z) ⧸ pCore 2 ↥(Hz z)) ∣ 6 := by
    have e1 : Nat.card (↥(Hz z) ⧸ pCore 2 ↥(Hz z)) = Nat.card ↥ι.range :=
      Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv
    have h1 := Subgroup.card_subgroup_dvd_card ι.range
    have h2 := Subgroup.card_subgroup_dvd_card
      (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup b)
    rw [hGL] at h2
    rw [e1]
    exact h1.trans h2
  refine ⟨Nat.card (↥(Hz z) ⧸ pCore 2 ↥(Hz z)), hdvd, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥(Hz z)), hPcard, mul_comm]

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
