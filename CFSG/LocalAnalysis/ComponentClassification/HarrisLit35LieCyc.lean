module

public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GH74.Generic.GKFCover
public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

theorem map_perfectResidual_of_isPerfect {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (hH : Group.IsPerfect ↥H) : (perfectResidual ↥H).map H.subtype = H := by
  have htop : Group.IsPerfect ↥(⊤ : Subgroup ↥H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥H)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥H)).symm.surjective
  have h1 : perfectResidual ↥H = ⊤ :=
    top_unique (RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤ htop)
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_perfect_map_eq {S Y : Type} [Group S] [Group Y] [Finite S] [Finite Y]
    (π : S →* Y) (hπ : Function.Surjective π) {Lt : Subgroup Y} (hLt : Group.IsPerfect ↥Lt) :
    ∃ P : Subgroup S, Group.IsPerfect ↥P ∧ P.map π = Lt := by
  set T := Lt.comap π with hT
  set f : ↥T →* Y := π.comp T.subtype with hf
  have hr : f.range = Lt := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hT,
      Subgroup.map_comap_eq_self_of_surjective hπ]
  have hrp : Group.IsPerfect ↥f.range := by
    rw [hr]
    exact hLt
  have hPT : Group.IsPerfect ↥(perfectResidual ↥T) :=
    (perfect_residual_characterization (G := ↥T)).2.2.1
  refine ⟨(perfectResidual ↥T).map T.subtype, Group.IsPerfect.map T.subtype, ?_⟩
  rw [Subgroup.map_map, ← hf, (perfect_residual_transport f).1,
    map_perfectResidual_of_isPerfect hrp, hr]

theorem false_of_cyclicCover {S Y : Type} [Group S] [Group Y] [Finite S] [Finite Y]
    (π : S →* Y) (hπ : Function.Surjective π) {N : Subgroup S}
    (hN : ∀ g : S, g ∈ N ↔ π g ∈ center Y) (hNc : N ≤ center S) (hN4 : Nat.card ↥N = 4)
    (hinv : ∀ x ∈ N, ∀ y ∈ N, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y)
    (hZ2 : Nat.card ↥(center Y) = 2) {Lt : Subgroup Y} (hLt : Group.IsPerfect ↥Lt)
    {z : Y} (hz : z ∈ center Y) (hzL : z ∈ Lt) (hz1 : z ≠ 1)
    (hsmall : ∀ P : Subgroup S, Group.IsPerfect ↥P → P.map π = Lt →
      ¬ 4 ∣ Nat.card ↥(center ↥P)) : False := by
  obtain ⟨P, hP, hPm⟩ := exists_perfect_map_eq π hπ hLt
  rw [← hPm] at hzL
  obtain ⟨t, htP, htz⟩ := hzL
  have htN : t ∈ N := (hN t).mpr (htz ▸ hz)
  have ht1 : t ≠ 1 := fun h1 => hz1 (by rw [← htz, h1, map_one])
  let ρ : ↥N →* ↥(center Y) :=
    { toFun := fun x => ⟨π (x : S), (hN x).mp x.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : S) (b : S)) }
  have hρ : Function.Surjective ρ := by
    rintro ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := hπ c
    exact ⟨⟨g, (hN g).mpr hc⟩, rfl⟩
  have hcard := GH74.Generic.card_eq_card_mul_card_ker ρ hρ
  rw [hN4, hZ2] at hcard
  have hk2 : Nat.card ↥ρ.ker = 2 := by omega
  obtain ⟨k, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hk2]; norm_num))
  have hkk : ((k : ↥N) : S) * ((k : ↥N) : S) = 1 := by
    have h1 : k ^ 2 = 1 := by
      rw [← hk2]
      exact pow_card_eq_one'
    have h2 := congrArg (fun x : ↥ρ.ker => ((x : ↥N) : S)) h1
    simpa [pow_two] using h2
  have hkN : ((k : ↥N) : S) ∈ N := (k : ↥N).2
  have hkπ : π ((k : ↥N) : S) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
  have hk1' : ((k : ↥N) : S) ≠ 1 := fun h1 => hk1 (Subtype.ext (Subtype.ext h1))
  have htt : t * t ≠ 1 := by
    intro htt
    have hte := hinv t htN _ hkN htt hkk ht1 hk1'
    exact hz1 (by rw [← htz, hte, hkπ])
  have ht4 : orderOf t = 4 := by
    have hd : orderOf t ∣ 4 := by
      rw [← hN4, ← Subgroup.orderOf_mk t htN]
      exact orderOf_dvd_natCard _
    obtain ⟨i, hi, hti⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf t ∣ 2 ^ 2 from hd)
    interval_cases i
    · exact absurd (orderOf_eq_one_iff.mp hti) ht1
    · exfalso
      apply htt
      have h2 : orderOf t = 2 := by simpa using hti
      rw [← pow_two, ← h2, pow_orderOf_eq_one]
    · simpa using hti
  have htZ : (⟨t, htP⟩ : ↥P) ∈ center ↥P :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hNc htN) g)
  apply hsmall P hP hPm
  have h1 : orderOf (⟨⟨t, htP⟩, htZ⟩ : ↥(center ↥P)) = 4 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ht4]
  rw [← h1]
  exact orderOf_dvd_natCard _

theorem odd_exceptionalOrders_psl_two {p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
  have h : Odd (exceptionalOrders .PSL 2 p f).1 ∧ Odd (exceptionalOrders .PSL 2 p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  exact h.1.mul h.2

theorem not_four_dvd_card_center (hGA : TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : Group.IsPerfect X) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (X ⧸ center X) .PSL 2 p f) : ¬ 4 ∣ Nat.card ↥(center X) := by
  have hexc := odd_exceptionalOrders_psl_two (f := f) hp2
  have hgen : genericOrders .PSL 2 p f = (2, 1) := by
    have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
      obtain ⟨c, hc⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
      exact Nat.gcd_eq_left ⟨c, by omega⟩
    exact Prod.ext h1 rfl
  have hd := GH74.Generic.card_ker_dvd_hopfMultiplier hX (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk',
    GH74.Generic.card_hopfMultiplier_of_griess hGA
      (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm), hgen] at hd
  intro h4
  have h2 : 4 ∣ 2 * ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
    have := h4.trans hd
    simpa using this
  have h3 : 2 ∣ (exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
      (by simpa [show (4 : ℕ) = 2 * 2 by rfl] using h2)
  exact (Nat.not_even_iff_odd.mpr hexc) (even_iff_two_dvd.mpr h3)

theorem not_four_dvd_card_center_of_map (hGA : TBLit.GriessMultipliersAllModels)
    {S Y : Type} [Group S] [Group Y] [Finite S] (π : S →* Y) {N : Subgroup S}
    (hN : ∀ g : S, g ∈ N ↔ π g ∈ center Y) (hNc : N ≤ center S) {Lt : Subgroup Y}
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (↥(Lt.map (QuotientGroup.mk' (center Y))) ⧸
      center ↥(Lt.map (QuotientGroup.mk' (center Y)))) .PSL 2 p f)
    (P : Subgroup S) (hP : Group.IsPerfect ↥P) (hPm : P.map π = Lt) :
    ¬ 4 ∣ Nat.card ↥(center ↥P) := by
  set φ : S →* Y ⧸ center Y := (QuotientGroup.mk' (center Y)).comp π with hφ
  have hmap : P.map φ = Lt.map (QuotientGroup.mk' (center Y)) := by
    rw [hφ, ← Subgroup.map_map, hPm]
  let δ : ↥P →* ↥(Lt.map (QuotientGroup.mk' (center Y))) :=
    (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (φ.subgroupMap P)
  have hδ : Function.Surjective δ :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (φ.subgroupMap_surjective P)
  have hker : δ.ker ≤ center ↥P := by
    intro x hx
    have h1 : φ (x : S) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : π (x : S) ∈ center Y := by
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hNc ((hN _).mpr h2)) g)
  obtain ⟨e, -⟩ := UnbalancedCorr.exists_centerQuotient_equiv_of_surjective hP δ hδ hker
  exact not_four_dvd_card_center hGA hP hp hp2 (GSThmB.OddQuot.lieModel_of_equiv e.symm hm)

theorem eq_of_mem_statedScalars {n : ℕ} [NeZero n] {F : Type} [Field F]
    {H : Subgroup (GL (Fin n) F)} {x y : ↥H} (hx : x ∈ (StatedScalars (Fin n) F).subgroupOf H)
    (hy : y ∈ (StatedScalars (Fin n) F).subgroupOf H) (hxx : x * x = 1) (hyy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have key : ∀ u : ↥H, u ∈ (StatedScalars (Fin n) F).subgroupOf H → u * u = 1 → u ≠ 1 →
      (u : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) (-1) := by
    intro u hu huu hu1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hu
    have hc' : (c : F) * (c : F) = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin n) (c * c) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) 0 0 = 1 := by
        rw [map_mul, hc, ← Subgroup.coe_mul, huu, Subgroup.coe_one, Units.val_one,
          Matrix.one_apply_eq]
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using h1
    rcases mul_self_eq_one_iff.mp hc' with h1 | h1
    · exfalso
      apply hu1
      apply Subtype.ext
      rw [← hc, Subgroup.coe_one, show c = 1 from Units.ext h1, map_one]
    · rw [← hc, show c = -1 from Units.ext (by simpa using h1)]
  exact Subtype.ext ((key x hx hxx hx1).trans (key y hy hyy hy1).symm)

end CFSG.ComponentClassification.HarrisLit.L35
