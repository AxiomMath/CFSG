module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3QuotLevi
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3QuotResidual
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagStabilizer unitriangular)
open Matrix
open scoped MatrixGroups

theorem exists_levi_data {p : ℕ} [Fact p.Prime] {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ∃ lev : ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
      Function.Surjective lev ∧
        lev.ker.map (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).subtype ≤
          unitriangular 3 (ZMod p) := by
  rcases hi with rfl | rfl
  · exact ⟨leviOne (ZMod p), leviOne_surjective, leviOne_ker_le_unitriangular⟩
  · exact ⟨leviTwo (ZMod p), leviTwo_surjective, leviTwo_ker_le_unitriangular⟩

private theorem not_dvd_natCard_center_sl3 {p d : ℕ} [Fact p.Prime] (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ∣ p + 1) : ¬ d ∣ Nat.card (Subgroup.center SL(3, ZMod p)) := by
  have hZcard : Nat.card (Subgroup.center SL(3, ZMod p)) = Nat.gcd 3 (p - 1) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 (ZMod p),
      CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd (ZMod p) (by norm_num),
      Nat.card_zmod]
  rw [hZcard]
  have hp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hp.one_le
  intro h
  have hp1' : d ∣ p - 1 := h.trans (Nat.gcd_dvd_right 3 (p - 1))
  have h2 : d ∣ (p + 1) - (p - 1) := Nat.dvd_sub hdp hp1'
  rw [show p + 1 - (p - 1) = 2 by omega] at h2
  exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)

private theorem d_ne_p_and_not_dvd_of_dvd_add_one {p d : ℕ} [Fact p.Prime] (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) : d ≠ p ∧ ¬ d ∣ p ^ 3 ∧ ¬ d ∣ p - 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hp.one_le
  have hdp_ne : d ≠ p := by
    intro h
    rw [h] at hdp
    have h1 : p ∣ (p + 1) - p := Nat.dvd_sub hdp (dvd_refl p)
    rw [show p + 1 - p = 1 by omega] at h1
    exact hp.not_dvd_one h1
  refine ⟨hdp_ne, ?_, ?_⟩
  · intro h1
    exact hdp_ne ((Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow h1))
  · intro h1
    have h2 : d ∣ (p + 1) - (p - 1) := Nat.dvd_sub hdp h1
    rw [show p + 1 - (p - 1) = 2 by omega] at h2
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)

private theorem exists_surjection_flagStabilizer_to_Y {p d : ℕ} [Fact p.Prime] (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) {i : ℕ} {Y : Subgroup PSL(3, ZMod p)}
    (hY : Y.comap (QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))) =
      flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) :
    ∃ f : ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) →* ↥Y,
      Function.Surjective f ∧ ¬ d ∣ Nat.card f.ker := by
  classical
  have hYmap : Y = (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).map
      (QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))) := by
    rw [← hY, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (Subgroup.center SL(3, ZMod p)))]
  have hmemY : ∀ q : ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ)),
      QuotientGroup.mk' (Subgroup.center SL(3, ZMod p)) q.1 ∈ Y := by
    intro q
    rw [hYmap]
    exact Subgroup.mem_map_of_mem _ q.2
  let qToY : ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) →* ↥Y :=
    ((QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))).comp
      (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).subtype).codRestrict Y hmemY
  have hqToYsurj : Function.Surjective qToY := by
    intro y
    have hy : (y : PSL(3, ZMod p)) ∈ (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).map
        (QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))) := by
      rw [← hYmap]
      exact y.2
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨q, hq⟩, Subtype.ext hqy⟩
  have hqToYker : qToY.ker = (Subgroup.center SL(3, ZMod p)).subgroupOf
      (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hZle : Subgroup.center SL(3, ZMod p) ≤ flagStabilizer 3 (ZMod p) ({i} : Set ℕ) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_flagStabilizer 3 (ZMod p) _
  refine ⟨qToY, hqToYsurj, ?_⟩
  rw [hqToYker,
    show Nat.card ↥((Subgroup.center SL(3, ZMod p)).subgroupOf
        (flagStabilizer 3 (ZMod p) ({i} : Set ℕ))) =
        Nat.card (Subgroup.center SL(3, ZMod p)) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]
  exact not_dvd_natCard_center_sl3 hd hd2 hdp

private theorem exists_levi_surjection_of_dvd_add_one {p d : ℕ} [Fact p.Prime] {i : ℕ}
    (hi : i = 1 ∨ i = 2) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1) :
    ∃ lev : ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
      Function.Surjective lev ∧ ¬ d ∣ Nat.card lev.ker := by
  obtain ⟨lev, hsurj, hker⟩ := exists_levi_data (p := p) hi
  obtain ⟨-, hdp3, -⟩ := d_ne_p_and_not_dvd_of_dvd_add_one hd hd2 hdp
  refine ⟨lev, hsurj, ?_⟩
  have hunitcard : Nat.card ↥(unitriangular 3 (ZMod p)) = p ^ 3 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular, Nat.card_zmod,
      show 3 * (3 - 1) / 2 = 3 from rfl]
  have hdvd : Nat.card lev.ker ∣ Nat.card ↥(unitriangular 3 (ZMod p)) := by
    rw [← Subgroup.card_map_of_injective
      (f := (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).subtype)
      (flagStabilizer 3 (ZMod p) ({i} : Set ℕ)).subtype_injective]
    exact Subgroup.card_dvd_of_le hker
  rw [hunitcard] at hdvd
  exact fun h => hdp3 (h.trans hdvd)

private theorem not_dvd_natCard_center_gl2 {p d : ℕ} [Fact p.Prime] (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ∣ p + 1) :
    ¬ d ∣ Nat.card (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := ZMod p)).ker := by
  have hcenter : Nat.card (Subgroup.center
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) = p - 1 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (ZMod p)ˣ → Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
      intro x y hxy
      apply Units.ext
      have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hxy
      simpa [Matrix.GeneralLinearGroup.scalar] using h
    calc Nat.card ↥(Matrix.GeneralLinearGroup.scalar (Fin 2) :
            (ZMod p)ˣ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)).range
        = Nat.card (ZMod p)ˣ := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
      _ = p - 1 := by rw [Nat.card_units, Nat.card_zmod]
  rw [Matrix.ProjGenLinGroup.ker_mk, hcenter]
  exact (d_ne_p_and_not_dvd_of_dvd_add_one hd hd2 hdp).2.2

theorem isPSLType_two_oPrimeModPrimeComplement_of_comap_eq_flagStabilizer {p d : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1) {i : ℕ}
    (hi : i = 1 ∨ i = 2) {Y : Subgroup PSL(3, ZMod p)}
    (hY : Y.comap (QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))) =
      flagStabilizer 3 (ZMod p) ({i} : Set ℕ)) :
    IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d Y) := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨fY, hfYsurj, hfYker⟩ := exists_surjection_flagStabilizer_to_Y hd hd2 hdp hY
  obtain ⟨lev, hlevsurj, hlevker⟩ := exists_levi_surjection_of_dvd_add_one hi hd hd2 hdp
  have hmkker := not_dvd_natCard_center_gl2 (p := p) hd hd2 hdp
  obtain ⟨eA⟩ := CFSG.GroupTheory.nonempty_primeResidual_quot_primeComplementCore_mulEquiv
    (A := ↥(flagStabilizer 3 (ZMod p) ({i} : Set ℕ))) (B := ↥Y) hd fY hfYsurj hfYker
  obtain ⟨eB⟩ := CFSG.GroupTheory.nonempty_primeResidual_quot_primeComplementCore_mulEquiv
    hd lev hlevsurj hlevker
  obtain ⟨eC⟩ := CFSG.GroupTheory.nonempty_primeResidual_quot_primeComplementCore_mulEquiv
    hd (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := ZMod p))
    Matrix.ProjGenLinGroup.mk_surjective hmkker
  obtain ⟨eD⟩ := CFSG.GroupTheory.nonempty_primeResidual_pgl2_quot_mulEquiv_PSL hp5 hd hd2 hdp
  exact ⟨(MulEquiv.subgroupCongr (CFSG.GroupTheory.oPPrimeHull_top_eq_primeResidual
    (p := d) (X := CFSG.LocalAnalysis.AGL81TheoremCD.Section12.modPrimeComplement d Y)))
    |>.trans (eA.symm.trans (eB.trans (eC.trans eD)))⟩

end CFSG.LocalAnalysis.AGL81I.Section3
