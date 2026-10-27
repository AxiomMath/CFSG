module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem local_of_psu3 (e : X ≃* PSU3 2 2) (K R S : Subgroup X) (hK : TightlyEmbedded K)
    (hKn : ¬ K.Normal) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R) (h4 : Nat.card R = 4)
    (hS : IsSylowOf 2 S ⊤) (hRS : R ≤ S)
    (hwc : ∀ g : X, rightConjugate R g ≤ S → rightConjugate R g = R) :
    (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := fusionBenderBorel_of_mulEquiv_psu3 (le_refl 2) e
  have : IsSimpleGroup (PSU3 2 2) := CFSG.ShultStronglyClosedTI.unitaryCover_native_simple 2 le_rfl
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top hS
  have hcard := card_sylow_of_mulEquiv_psu3 (le_refl 2) e P
  set H := normalizer (K : Set X) with hHdef
  have hHtop : H ≠ ⊤ := fun h => hKn (normalizer_eq_top_iff.mp h)
  have hRK : R ≤ K := hR.le
  have hKH : K ≤ H := le_normalizer
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hRne : R ≠ ⊥ := fun h => by
    rw [h, card_bot] at h4
    exact absurd h4 (by norm_num)
  have hSN : S ≤ normalizer (R : Set X) := Hall32.le_normalizer_of_weaklyClosed hRS hwc
  have hNH : normalizer (R : Set X) ≤ H := normalizer_two_subgroup_le K R hK hR2 hRK hRne
  have hSH : S ≤ H := hSN.trans hNH
  have hZ : Nat.card (center (P : Subgroup X)) = 4 := by
    have h1 := (hB P).2.2.2.1
    rw [h1]
    norm_num
  have hRinv : ∀ x ∈ S, x ^ 2 = 1 → x ∈ R := by
    set Z := (center (P : Subgroup X)).map (P : Subgroup X).subtype with hZdef
    have hmemZ : ∀ x ∈ S, x ^ 2 = 1 → x ∈ Z := fun x hxS hx2 => by
      have hxP : x ∈ (P : Subgroup X) := by rw [hP]; exact hxS
      have hc := mem_centralizer_of_fusionBenderBorel hB (by norm_num) P hxP hx2
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hc y y.2)
    have hRZ : R ≤ Z := fun r hr => hmemZ r (hRS hr) (hRe.2 r hr)
    have hZcard : Nat.card Z = 4 := by
      rw [hZdef, card_map_of_injective (P : Subgroup X).subtype_injective, hZ]
    have hRZeq : R = Z := eq_of_le_of_card_ge hRZ (by rw [hZcard, h4])
    intro x hxS hx2
    rw [hRZeq]
    exact hmemZ x hxS hx2
  have hNSR : normalizer (S : Set X) ≤ normalizer (R : Set X) := fun g hg => by
    rw [mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      refine hRinv _ ((mem_normalizer_iff.mp hg r).mp (hRS hr)) ?_
      rw [conj_pow, hRe.2 r hr, mul_one, mul_inv_cancel]
    · intro hr
      have hrS : r ∈ S := (mem_normalizer_iff.mp hg r).mpr (hRS hr)
      refine hRinv r hrS ?_
      have h1 : (g * r * g⁻¹) ^ 2 = 1 := hRe.2 _ hr
      rw [conj_pow] at h1
      have h2 : r ^ 2 = g⁻¹ * (g * r ^ 2 * g⁻¹) * g := by group
      rw [h2, h1, mul_one, inv_mul_cancel]
  have hsmul : ∀ (g : X) (T : Sylow 2 X), g ∈ H → (T : Subgroup X) ≤ H →
      ((g • T : Sylow 2 X) : Subgroup X) ≤ H := fun g T hg hT x hx => by
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : g⁻¹ * x * g ∈ (T : Subgroup X) := by simpa [MulAut.conj_apply] using hx
    have e1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem hg (hT hx')) (inv_mem hg)
  have hsyl : ∀ T : Sylow 2 X, (T : Subgroup X) ≤ H → T = P := by
    intro T hTH
    by_contra hTP
    apply hHtop
    have hall : ∀ T' : Sylow 2 X, (T' : Subgroup X) ≤ H := fun T' => by
      by_cases hT' : T' = P
      · rw [hT', hP]
        exact hSH
      · obtain ⟨r, hrP, hr⟩ := exists_mem_smul_eq_of_fusionBenderBorel hB hcard hTP hT'
        rw [← hr]
        exact hsmul r T (hSH (by rw [← hP]; exact hrP)) hTH
    have hN : normalClosure (S : Set X) ≤ H := by
      refine (closure_le H).mpr fun x hx => ?_
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      apply hall (c • P)
      rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
      have e1 : (MulAut.conj c)⁻¹ • (c * a * c⁻¹) = a := by
        rw [MulAut.smul_def, ← map_inv MulAut.conj c, MulAut.conj_apply]
        group
      rw [e1, hP]
      exact ha
    have hNtop : normalClosure (S : Set X) = ⊤ := by
      rcases (normalClosure_normal : (normalClosure (S : Set X)).Normal).eq_bot_or_eq_top with
        h1 | h1
      · exfalso
        apply hRne
        rw [eq_bot_iff]
        intro r hr
        have h2 : r ∈ normalClosure (S : Set X) := subset_normalClosure (hRS hr)
        rwa [h1] at h2
      · exact h1
    rw [eq_top_iff, ← hNtop]
    exact hN
  have hHN : H ≤ normalizer (S : Set X) := fun h hh => by
    have h1 := hsyl (h • P) (hsmul h P hh (by rw [hP]; exact hSH))
    have h2 := Sylow.smul_eq_iff_mem_normalizer.mp h1
    rw [← hP]
    exact h2
  refine ⟨(normal_subgroupOf_iff_le_normalizer hRK).mpr (hKH.trans (hHN.trans hNSR)), ?_⟩
  have hHeq : H = normalizer (S : Set X) := le_antisymm hHN (hNSR.trans hNH)
  rw [hHeq]
  obtain ⟨D, hDc, -, -, hSD⟩ := (hB P).2.1
  rw [hP] at hSD
  set N := normalizer (S : Set X) with hNdef
  have hSN' : S ≤ N := le_normalizer
  have hDN : D ≤ N := hSD ▸ le_sup_right
  set S' := S.subgroupOf N with hS'def
  set D' := D.subgroupOf N with hD'def
  have hS'n : S'.Normal := (normal_subgroupOf_iff_le_normalizer hSN').mpr le_rfl
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have : Group.IsSolvable S' := by
    have hS'2 : IsPGroup 2 S' := hS2.of_equiv (subgroupOfEquivOfLe hSN').symm
    have : Group.IsNilpotent S' := hS'2.isNilpotent
    infer_instance
  have hsup : S' ⊔ D' = ⊤ := by
    rw [hS'def, hD'def, ← subgroupOf_sup hSN' hDN, hSD, subgroupOf_self]
  have hsurj : Function.Surjective ((QuotientGroup.mk' S').comp D'.subtype) := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective S' y
    have hn : (n : N) ∈ ((S' ⊔ D' : Subgroup N) : Set N) := by rw [hsup]; exact mem_top n
    rw [normal_mul] at hn
    obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hn
    refine ⟨⟨d, hd⟩, ?_⟩
    change QuotientGroup.mk' S' d = QuotientGroup.mk' S' (a * d)
    rw [map_mul, show QuotientGroup.mk' S' a = 1 from (QuotientGroup.eq_one_iff a).mpr ha,
      one_mul]
  have : IsCyclic D' := by
    have : IsCyclic D := hDc
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hDN).symm
      (subgroupOfEquivOfLe hDN).symm.surjective
  have : IsCyclic (N ⧸ S') := isCyclic_of_surjective _ hsurj
  have : Group.IsSolvable (N ⧸ S') := Group.isSolvable_of_comm fun a b =>
    (IsCyclic.isMulCommutative (α := N ⧸ S')).is_comm.comm a b
  exact Group.isSolvable_of_ker_le_range S'.subtype (QuotientGroup.mk' S')
    (by rw [QuotientGroup.ker_mk', range_subtype])

end CFSG.ComponentClassification.Asc76X.Thm3Four
