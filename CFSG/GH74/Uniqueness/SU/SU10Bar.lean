module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GH74.Uniqueness.SU.SU0Bender
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

section InjOn

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

omit [Finite A] [Finite B] in
theorem card_map_of_injOn {φ : A →* B} {P : Subgroup A} (h : Set.InjOn φ P) :
    Nat.card (P.map φ) = Nat.card P := by
  have hinj : Function.Injective (φ.subgroupMap P) := by
    intro x y hxy
    exact Subtype.ext (h x.2 y.2 (congrArg Subtype.val hxy))
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, φ.subgroupMap_surjective P⟩)).symm

omit [Finite A] [Finite B] in
theorem map_inf_comap_eq {φ : A →* B} {R : Subgroup A} {E : Subgroup B} (hE : E ≤ R.map φ) :
    (R ⊓ E.comap φ).map φ = E := by
  refine le_antisymm ?_ fun z hz => ?_
  · rw [map_le_iff_le_comap]
    exact inf_le_right
  · obtain ⟨x, hx, rfl⟩ := mem_map.mp (hE hz)
    exact mem_map_of_mem φ (mem_inf.mpr ⟨hx, hz⟩)

omit [Finite A] [Finite B] in
theorem isElemAbelian_map {φ : A →* B} {E : Subgroup A} (hE : Open.IsElemAbelian 2 E) :
    Open.IsElemAbelian 2 (E.map φ) := CFSG.Open.IsElemAbelian.map hE _

omit [Finite A] [Finite B] in
theorem isElemAbelian_of_injOn {φ : A →* B} {P E : Subgroup A} (h : Set.InjOn φ P) (hEP : E ≤ P)
    (hE : Open.IsElemAbelian 2 (E.map φ)) : Open.IsElemAbelian 2 E := by
  rw [SU1.isElemAbelian_iff] at hE ⊢
  obtain ⟨hc, hp⟩ := hE
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · apply h (P.mul_mem (hEP ha) (hEP hb)) (P.mul_mem (hEP hb) (hEP ha))
    rw [map_mul, map_mul]
    exact hc _ (mem_map_of_mem φ ha) _ (mem_map_of_mem φ hb)
  · apply h (P.pow_mem (hEP ha) 2) P.one_mem
    rw [map_pow, map_one]
    exact hp _ (mem_map_of_mem φ ha)

theorem pRank_map_of_injOn {φ : A →* B} {P : Subgroup A} (h : Set.InjOn φ P) :
    Open.pRank 2 (P.map φ) = Open.pRank 2 P := by
  apply le_antisymm
  · obtain ⟨E', hE'R, hE', hcard⟩ := SU1.exists_pRank (p := 2) (by norm_num) (P.map φ)
    have hEP : P ⊓ E'.comap φ ≤ P := inf_le_left
    have hmap : (P ⊓ E'.comap φ).map φ = E' := map_inf_comap_eq hE'R
    have hel : Open.IsElemAbelian 2 (P ⊓ E'.comap φ) :=
      isElemAbelian_of_injOn h hEP (by rw [hmap]; exact hE')
    have hcardE : Nat.card (P ⊓ E'.comap φ : Subgroup A) = 2 ^ Open.pRank 2 (P.map φ) := by
      rw [← hcard]
      conv_rhs => rw [← hmap]
      exact (card_map_of_injOn (fun x hx y hy hxy => h (hEP hx) (hEP hy) hxy)).symm
    exact SU1.le_pRank (by norm_num) hEP hel hcardE
  · obtain ⟨E, hEP, hE, hcard⟩ := SU1.exists_pRank (p := 2) (by norm_num) P
    have hinj : Set.InjOn φ E := fun x hx y hy hxy => h (hEP hx) (hEP hy) hxy
    exact SU1.le_pRank (by norm_num) (map_mono hEP) (isElemAbelian_map hE)
      ((card_map_of_injOn hinj).trans hcard)

end InjOn

section Quot

variable {Y : Type} [Group Y] [Finite Y]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Y)

theorem coprime_card_pPrimeCore : Nat.Coprime 2 (Nat.card (pPrimeCore 2 Y)) :=
  pPrimeCore_coprime_card

theorem inf_pPrimeCore_eq_bot {R : Subgroup Y} (hR : IsPGroup 2 R) :
    R ⊓ pPrimeCore 2 Y = ⊥ :=
  SU0.eq_bot_of_isPGroup_of_coprime hR.to_inf_left inf_le_right coprime_card_pPrimeCore

theorem injOn_of_isPGroup {R : Subgroup Y} (hR : IsPGroup 2 R) : Set.InjOn π R := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ R ⊓ pPrimeCore 2 Y := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hx) hy, ?_⟩
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 Y), MonoidHom.mem_ker, map_mul, map_inv, hxy,
      inv_mul_cancel]
  rw [inf_pPrimeCore_eq_bot hR, mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem normalizer_map_eq {E : Subgroup Y} (hE : IsPGroup 2 E) :
    normalizer ((E.map π : Subgroup (Y ⧸ pPrimeCore 2 Y)) : Set (Y ⧸ pPrimeCore 2 Y)) =
      (normalizer (E : Set Y)).map π := by
  have : Fact (IsPGroup 2 E) := ⟨hE⟩
  exact normalizer_map_quotient_eq_map_normalizer 2 E (pPrimeCore 2 Y) inferInstance
    coprime_card_pPrimeCore

noncomputable def sylowMap (P : Sylow 2 Y) : Sylow 2 (Y ⧸ pPrimeCore 2 Y) :=
  P.mapSurjective (QuotientGroup.mk'_surjective _)

theorem coe_sylowMap (P : Sylow 2 Y) :
    (sylowMap P : Subgroup (Y ⧸ pPrimeCore 2 Y)) = (P : Subgroup Y).map π :=
  Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P

theorem pRank_map_pPrimeCore {P : Subgroup Y} (hP : IsPGroup 2 P) :
    Open.pRank 2 (P.map π) = Open.pRank 2 P :=
  pRank_map_of_injOn (injOn_of_isPGroup hP)

end Quot

end CFSG.GH74.Uniqueness.SU.SU10
