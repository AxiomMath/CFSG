module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneMaximalOvergroups
import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.SmallCentralizerLineMissesDerived
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
  Subgroup

universe u

theorem FNI_prime_cube_centralizer_in_competing_maximum
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_prime_cube_centralizer_in_competing_maximum.{u} := by
  intro G _ _ hG p M T Q D hM hT hp _hpodd hQMT hQnab hQcard hQexp hDM hMD hDp
  have hfact := Fact.mk hp
  have hGmin : IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  set Z : Subgroup G := Q ⊓ centralizer (Q : Set G) with hZdef
  set K : Subgroup G := D ⊓ centralizer (Z : Set G)
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, ← map_center_subtype, Subgroup.card_subtype]
    exact card_center_of_card_eq_prime_cube hp hQcard hQnab
  have hZmem : ∀ z : ↥Q, (z : G) ∈ Z ↔ z ∈ Subgroup.center ↥Q := by
    intro z
    rw [hZdef, ← map_center_subtype]
    exact ⟨fun ⟨w, hw, hwz⟩ => Subtype.ext hwz ▸ hw, fun h => ⟨z, h, rfl⟩⟩
  have hQZ : Q ≤ normalizer (Z : Set G) :=
    le_normalizer_inf_centralizer_self_of_le_normalizer Subgroup.le_normalizer
  have hQT : Q ≤ T := hQMT.trans inf_le_right
  have hQK : Q ≤ normalizer (K : Set G) :=
    le_trans (le_inf ((hQMT.trans inf_le_left).trans hMD)
      (hQZ.trans (normalizer_le_normalizer_centralizer Z)))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKne : K ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ inf_le_left.trans hDM))
  have _hKsolv : Group.IsSolvable ↥K := hG.isSolvable_of_ne_top K hKne
  have hpK : ¬ p ∣ Nat.card ↥K := fun hdvd =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left)) hDp) dvd_rfl)
  set ρ₀ : ↥Q →* MulAut ↥K := conjAction hQK with hρ₀
  have hker : Subgroup.center ↥Q ≤ ρ₀.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hρ₀, coe_conjAction_apply,
      mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 (z : G) ((hZmem z).2 hz)]
    simp
  set ρ : (↥Q ⧸ Subgroup.center ↥Q) →* MulAut ↥K :=
    QuotientGroup.lift (Subgroup.center ↥Q) ρ₀ hker
  have hρmk : ∀ x : ↥Q, ρ (QuotientGroup.mk x) = ρ₀ x := fun _ => rfl
  have htop : ⨆ (a : ↥Q ⧸ Subgroup.center ↥Q) (_ : a ≠ 1), autFixedSubgroup (ρ a) = ⊤ :=
    iSup_autFixedSubgroup_eq_top hp
      (card_quotient_center_of_card_eq_prime_cube hp hQcard hQnab)
      (pow_eq_one_quotient_center_of_card_eq_prime_cube hp hQcard hQnab) ρ hpK
  have hgen : ∀ a : ↥Q ⧸ Subgroup.center ↥Q, a ≠ 1 →
      autFixedSubgroup (ρ a) ≤ T.subgroupOf K := by
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hxZ : (x : G) ∉ Z := fun h => ha ((QuotientGroup.eq_one_iff x).2 ((hZmem x).1 h))
    have hxgp : (x : G) ^ p = 1 := hQexp _ x.2
    have hx1 : (x : G) ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
    set A : Subgroup G := Z ⊔ zpowers (x : G) with hA
    have hAQ : A ≤ Q := sup_le inf_le_left (zpowers_le.2 x.2)
    have hZx : Z ⊓ zpowers (x : G) = ⊥ := by
      rw [inf_comm]
      exact inf_eq_bot_of_natCard_eq_prime_of_not_le hp
        (by rw [Nat.card_zpowers, orderOf_eq_prime hxgp hx1])
        fun h => hxZ (h (mem_zpowers (x : G)))
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hA, natCard_sup_eq_mul_of_le_normalizer ((zpowers_le.2 x.2).trans hQZ) hZx, hZcard,
        Nat.card_zpowers, orderOf_eq_prime hxgp hx1]
      ring
    have hAplane : IsPlaneAt p A :=
      ⟨isElementaryAbelian_iff.2 ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hAcard,
        fun g hg => hQexp g (hAQ hg)⟩, hAcard⟩
    have hCA : centralizer (A : Set G) ≤ T :=
      (FTS_plane_maximal_overgroups h₁ h₂ h₃ h₄ G hGmin T A p hT hp (hAQ.trans hQT) hAplane).1
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    refine hCA ?_
    have hcommxy : (x : G) * ((y : ↥K) : G) = ((y : ↥K) : G) * (x : G) := by
      have h2 : ((ρ₀ x y : ↥K) : G) = ((y : ↥K) : G) :=
        congrArg Subtype.val ((hρmk x) ▸ mem_autFixedSubgroup.1 hy)
      rw [hρ₀, coe_conjAction_apply] at h2
      calc (x : G) * ((y : ↥K) : G)
          = ((x : G) * ((y : ↥K) : G) * (x : G)⁻¹) * (x : G) := by group
        _ = ((y : ↥K) : G) * (x : G) := by rw [h2]
    have hAcent : A ≤ centralizer ({((y : ↥K) : G)} : Set G) := by
      refine sup_le (fun z hz => mem_centralizer_iff.2 ?_)
        (zpowers_le.2 (mem_centralizer_iff.2 ?_))
      · rintro g rfl
        exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 z hz).symm
      · rintro g rfl
        exact hcommxy.symm
    exact mem_centralizer_iff.2 fun g hg => ((mem_centralizer_iff.1 (hAcent hg)) _ rfl).symm
  intro y hy
  exact (Subgroup.mem_subgroupOf).1 ((htop ▸ iSup₂_le hgen) (mem_top (⟨y, hy⟩ : ↥K)))

end

end CFSG.FeitThompson.Proofs
