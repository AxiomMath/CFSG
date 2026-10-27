module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeTD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.LieType.Ree

section Residual


@[expose] def L154ReeThreeRes : Prop :=
  ∀ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
    ∀ (s : ReeTag.F4.reeGamma K a) (φ : MulAut (ReeTag.F4.reeGamma K a)),
      orderOf s = 3 → φ ^ 3 = 1 → (∀ g, φ ≠ MulAut.conj g) → φ s = s →
      ¬ LargeEvenMarking ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)))
        fun _ _ _ I _ θ => ∃ ψ ∈ I, LargeEvenInduces θ
          (fun z z' : ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) =>
            φ (z : ReeTag.F4.reeGamma K a) = (z' : ReeTag.F4.reeGamma K a)) ψ

end Residual

section Three


theorem l154_false_of_ree_innDiag_three (h3 : L154ReeThreeRes) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore 3 ↥S = ⊥)
    (hc : IsChevSimple 2 (PSimple 3 S)) (hQ : catalogIs (PSimple 3 S) l154ExcRee)
    (hxp : x ^ 3 = 1) (hyp : y ^ 3 = 1) (hxy : x * y = y * x)
    (hInn : InnDiagOn 3 (Subgroup.zpowers x) S) (hF : FieldOn 3 y S)
    (hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod 3 S x)
    (hInnJ : InnDiagOn 3 (Subgroup.zpowers y) J) : False := by
  obtain ⟨a, K, _, _, _, θ, s, φ, ha, hK, hs, hφp, hφout, hφs, hindx, hindy⟩ :=
    l154_ree_setup Nat.prime_three (by norm_num) hSn hqS hSp hc hQ hxp hyp hxy hInn hF hcm
  have hxN := l154_mem_normalizer_of_normal hSn x
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hTc := l154_JImage_glaPComponent Nat.prime_three hxp hxN hJ θ (MulAut.conj s) hindx
  have hTeq := l154_ree_T_eq_centralizer_three ha hK hs hTc
  have hCq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs)
  have hqT : CFSG.Open.IsQuasisimple ↥(l154JImage 3 S J θ) := by
    rw [hTeq]
    exact hCq
  obtain ⟨ψJ, e₀, hψ, he₀⟩ := l154_JImage_equiv Nat.prime_three hSp hJ hJS hJy θ φ hindy hqT
  let eJ : ↥(l154JImage 3 S J θ) ≃*
      ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) := MulEquiv.subgroupCongr hTeq
  let E : PSimple 3 J ≃* ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) :=
    e₀.trans (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ))
  have hMJ : LargeEvenMarking (PQuot 3 J)
      fun _ _ _ I _ θJ => ∃ ψ ∈ I, LargeEvenInduces θJ (indRel 3 J y) ψ :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh y (Subgroup.mem_zpowers y)) hInnJ.2
  refine h3 a K inferInstance inferInstance inferInstance ha hK s φ hs hφp hφout hφs ?_
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
    (l154_marking_transport hCq.1 E hMJ)
  rintro lab R' _ I F θ' ⟨ψ, hψI, hind⟩
  refine ⟨ψ, hψI, ?_⟩
  rw [MI.induces_indRel_iff hJy] at hind
  subst hind
  exact l154_induces_transfer eJ e₀ (MI.indAut 3 J y hJy) ψJ he₀ (fun z => φ z) hψ θ'

end Three

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
