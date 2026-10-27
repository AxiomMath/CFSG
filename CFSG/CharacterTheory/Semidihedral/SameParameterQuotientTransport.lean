module

public import CFSG.CharacterTheory.Semidihedral.SameParameterRegularity
public import CFSG.CharacterTheory.Semidihedral.Local.OddKernelLocalParameterSupport
public import CFSG.CharacterTheory.Semidihedral.Local.OddIndexLocalLayer
public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimpleSupport

public noncomputable section

namespace CFSG.Semidihedral.SameParameterQuotientTransport

open CFSG.Open
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SameParameterRegularity
open CFSG.Semidihedral.Local.OddKernel
open CFSG.Semidihedral.Local

universe u

theorem subgroupCentralizerEquiv_tInC {G : Type u} [Group G]
    (U : Subgroup G) (t : U) :
    subgroupCentralizerEquiv U t (tInC t) =
      (⟨tInC (t : G), t.property⟩ : U.subgroupOf (C (t : G))) := rfl

theorem subgroupCentralizerEquiv_Z {G : Type u} [Group G]
    (U : Subgroup G) (t : U) :
    (Z t).map (subgroupCentralizerEquiv U t).toMonoidHom =
      (Z (t : G)).subgroupOf (U.subgroupOf (C (t : G))) := by
  let B := U.subgroupOf (C (t : G))
  let tB : B := ⟨tInC (t : G), t.property⟩
  have htB : Z (t : G) ≤ B := Subgroup.zpowers_le.mpr tB.property
  rw [Z, MonoidHom.map_zpowers]
  change Subgroup.zpowers tB = (Z (t : G)).subgroupOf B
  apply Subgroup.map_injective (f := B.subtype) B.subtype_injective
  rw [MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le htB]
  rfl

theorem subgroupCentralizerEquiv_NZ {G : Type u} [Group G]
    (U : Subgroup G) (t : U) :
    (NZ t).map (subgroupCentralizerEquiv U t).toMonoidHom =
      CFSG.pPrimeCore 2 (U.subgroupOf (C (t : G))) ⊔
        (Z (t : G)).subgroupOf (U.subgroupOf (C (t : G))) := by
  rw [NZ, Subgroup.map_sup, subgroupCentralizerEquiv_oddCore,
    subgroupCentralizerEquiv_Z]
  rfl

@[expose] def subgroupGammaEquiv {G : Type u} [Group G]
    (U : Subgroup G) (t : U) :
    Gamma t ≃* ((U.subgroupOf (C (t : G))) ⧸
      (CFSG.pPrimeCore 2 (U.subgroupOf (C (t : G))) ⊔
        (Z (t : G)).subgroupOf (U.subgroupOf (C (t : G))))) :=
  QuotientGroup.congr (NZ t) _ (subgroupCentralizerEquiv U t)
    (subgroupCentralizerEquiv_NZ U t)

theorem subgroupGammaEquiv_kappa {G : Type u} [Group G]
    (U : Subgroup G) (t : U) (x : C t) :
    subgroupGammaEquiv U t (kappa t x) =
      QuotientGroup.mk'
        (CFSG.pPrimeCore 2 (U.subgroupOf (C (t : G))) ⊔
          (Z (t : G)).subgroupOf (U.subgroupOf (C (t : G))))
        (subgroupCentralizerEquiv U t x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

theorem even_card_of_noncyclic_sylow {G : Type u} [Group G] [Finite G]
    (hnc : ∀ U : Sylow 2 G, ¬ IsCyclic U) : Even (Nat.card G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.choice Sylow.nonempty
  rcases P.isPGroup'.card_eq_or_dvd with hone | htwo
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hone).1
    exact (hnc P (inferInstance : IsCyclic P)).elim
  · exact even_iff_two_dvd.mpr (htwo.trans (Subgroup.card_subgroup_dvd_card P.toSubgroup))

theorem normal_odd_index_sylow_presentation {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) [U.Normal] (hodd : Odd U.index) (n : ℕ) (S : Sylow 2 G)
    (e : SemidihedralGroup n ≃* S) :
    ∃ (SU : Sylow 2 U) (eU : SemidihedralGroup n ≃* SU),
      SU.toSubgroup.map U.subtype = S.toSubgroup ∧
        ∀ x, ((eU x : U) : G) = (e x : G) := by
  have hSU : S.toSubgroup ≤ U := le_of_isPGroup_of_odd_index hodd S.isPGroup'
  let SU := sylowOfOddIndex hodd S hSU
  have hSUdef : SU.toSubgroup = S.toSubgroup.subgroupOf U :=
    coe_sylowOfOddIndex hodd S hSU
  let eU := e.trans ((Subgroup.subgroupOfEquivOfLe hSU).symm.trans
    (MulEquiv.subgroupCongr hSUdef.symm))
  refine ⟨SU, eU, ?_, fun _ => rfl⟩
  rw [hSUdef, Subgroup.map_subgroupOf_eq_of_le hSU]

theorem normal_odd_index_subgroup_preserves_intrinsic_local_layer {G : Type} [Group G]
    [Finite G] (U : Subgroup G) [U.Normal] (hodd : Odd U.index)
    (hU : ∀ W : Subgroup U, W.index ≠ 2) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 U) (fS : SemidihedralGroup n ≃* S) (t : U) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hnc : ∀ W : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic W)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f) :
    let L := CFSG.generalizedFitting (Gamma (t : G))
    let LU := CFSG.generalizedFitting (Gamma t)
    IsSimpleGroup LU ∧ (∃ a b : LU, a * b ≠ b * a) ∧
      Subgroup.centralizer (LU : Set (Gamma t)) = ⊥ ∧
      (∀ W : Sylow 2 LU, ¬ IsCyclic W) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel LU .PSL 2 p f ∧
      (N t).map
        ((U.subgroupOf (C (t : G))).subtype.comp
          (subgroupCentralizerEquiv U t).toMonoidHom) =
        U.subgroupOf (C (t : G)) ⊓ N (t : G) ∧
      ∃ iota : Gamma t →* Gamma (t : G), Function.Injective iota ∧
        (∀ x : C t, iota (kappa t x) = kappa (t : G) (subgroupCentralizerEquiv U t x)) ∧
        LU.map iota = L ∧
        ∃ eL : LU ≃* L, ∀ x : LU, (eL x : Gamma (t : G)) = iota x := by
  intro L LU
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B := U.subgroupOf (C (t : G))
  let R := CFSG.pPrimeCore 2 B
  let Delta := B ⧸ (R ⊔ (Z (t : G)).subgroupOf B)
  let J := CFSG.generalizedFitting Delta
  obtain ⟨-, -, -, -, hR, iotaB, hinjB, hrepB, -, -, -, hJB, hJsimple, hJnonab,
    -, hJcentral, ⟨eJ, heJ⟩, hJmodel, hJnc⟩ :=
    normal_odd_index_subgroup_preserves_actual_local_layer U hodd hU n hn S fS
      (t : G) t.property (by rw [Subgroup.orderOf_mk] at ht; exact ht)
      hnonab (even_card_of_noncyclic_sylow hnc) hcentral
  let : IsSimpleGroup J := hJsimple
  let theta : Gamma t ≃* Delta := subgroupGammaEquiv U t
  have hJmap : J.map theta.symm.toMonoidHom = LU :=
    generalizedFitting_map_of_mulEquiv theta.symm hJnonab hJcentral
  let eU : J ≃* LU := (J.equivMapOfInjective theta.symm.toMonoidHom
    theta.symm.injective).trans (MulEquiv.subgroupCongr hJmap)
  have hLUsimple : IsSimpleGroup LU := eU.symm.isSimpleGroup
  have hLUnonab : ∃ a b : LU, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJnonab
    refine ⟨eU a, eU b, fun h => hab (eU.injective ?_)⟩
    simpa only [map_mul] using h
  have hLUcentral : Subgroup.centralizer (LU : Set (Gamma t)) = ⊥ := by
    rw [← hJmap]
    exact centralizer_map_eq_bot_of_mulEquiv theta.symm J hJcentral
  have hLUnc : ∀ W : Sylow 2 LU, ¬ IsCyclic W :=
    not_isCyclic_sylow_of_mulEquiv eU.symm (hJnc hnc)
  have hLUmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel LU .PSL 2 p f :=
    statedClassicalModel_PSL_of_mulEquiv eU.symm (hJmodel p f hp hpodd hf hmodel)
  let iota := iotaB.comp theta.toMonoidHom
  have hthetaLU : LU.map theta.toMonoidHom = J := by
    rw [← hJmap, Subgroup.map_map]
    have hcomp : theta.toMonoidHom.comp theta.symm.toMonoidHom = MonoidHom.id Delta := by
      ext x
      exact theta.apply_symm_apply x
    rw [hcomp, Subgroup.map_id]
  have hLUmap : LU.map iota = L := by
    change LU.map (iotaB.comp theta.toMonoidHom) = L
    rw [← Subgroup.map_map, hthetaLU]
    exact hJB
  have hcore : (N t).map (B.subtype.comp (subgroupCentralizerEquiv U t).toMonoidHom) =
      B ⊓ N (t : G) := by
    change (N t).map
      ((Subgroup.comap (C (t : G)).subtype U).subtype.comp
        (subgroupCentralizerEquiv U t).toMonoidHom) =
      Subgroup.comap (C (t : G)).subtype U ⊓ N (t : G)
    rw [← Subgroup.map_map, subgroupCentralizerEquiv_oddCore]
    exact hR
  refine ⟨hLUsimple, hLUnonab, hLUcentral, hLUnc, hLUmodel, hcore, iota,
    hinjB.comp theta.injective, ?_, hLUmap, ?_⟩
  · intro x
    change iotaB (theta (kappa t x)) = _
    rw [subgroupGammaEquiv_kappa]
    exact hrepB (subgroupCentralizerEquiv U t x)
  · let eL := (LU.equivMapOfInjective iota (hinjB.comp theta.injective)).trans
      (MulEquiv.subgroupCongr hLUmap)
    exact ⟨eL, fun _ => rfl⟩

end CFSG.Semidihedral.SameParameterQuotientTransport
