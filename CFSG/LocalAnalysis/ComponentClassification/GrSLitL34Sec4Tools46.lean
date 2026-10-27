module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_eq_of_normalizer_le_of_isSylowTwoIn {S M : Subgroup G} (hS : IsSylowTwoIn S M)
    (hN : normalizer (S : Set G) ≤ M) : ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  obtain ⟨Q, hSQ⟩ := hS2.exists_le_sylow
  refine ⟨Q, le_antisymm ?_ hSQ⟩
  by_contra hQS
  have hlt : S.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hQS fun q hq => ?_
    have : (⟨q, hq⟩ : Q) ∈ S.subgroupOf Q := by rw [htop]; exact mem_top _
    exact mem_subgroupOf.mp this
  have hnil : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyN' : (y : G) ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have h1 : (⟨s, hSQ hs⟩ : Q) ∈ S.subgroupOf Q := mem_subgroupOf.mpr hs
      exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hyN _).mp h1)
    · intro hs
      have hsQ : s ∈ (Q : Subgroup G) := by
        have h1 : (y : G) * s * (y : G)⁻¹ ∈ (Q : Subgroup G) := hSQ hs
        have h2 := mul_mem (mul_mem (inv_mem y.2) h1) y.2
        rwa [show (y : G)⁻¹ * ((y : G) * s * (y : G)⁻¹) * (y : G) = s by group] at h2
      have h1 : y * (⟨s, hsQ⟩ : Q) * y⁻¹ ∈ S.subgroupOf Q := mem_subgroupOf.mpr (by simpa using hs)
      exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hyN _).mpr h1)
  have hyM : (y : G) ∈ M := hN hyN'
  have hQ' : IsPGroup 2 ↥(S ⊔ zpowers (y : G)) :=
    Q.isPGroup'.to_le (sup_le hSQ (zpowers_le.mpr y.2))
  have heq := hS.eq_of_le le_sup_left (sup_le hS.1 (zpowers_le.mpr hyM)) hQ'
  have hyS' : (y : G) ∈ S ⊔ zpowers (y : G) := mem_sup_right (mem_zpowers (y : G))
  rw [heq] at hyS'
  exact hyS (mem_subgroupOf.mpr hyS')

theorem false_of_isolated_two_central [IsSimpleGroup G] (hnab : ∃ g h : G, g * h ≠ h * g)
    (P : Sylow 2 G) {a : G} (haP : a ∈ (P : Subgroup G))
    (haZ : ∀ s ∈ (P : Subgroup G), s * a = a * s)
    (ha2 : orderOf a = 2)
    (hiso : ∀ g : G, g⁻¹ * a * g ∈ (P : Subgroup G) → g⁻¹ * a * g = a) :
    False := by
  set a' : (P : Subgroup G) := ⟨a, haP⟩
  have hcen : a' ∈ center (P : Subgroup G) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (haZ s s.2)
  have ha'2 : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
  obtain ⟨-, hz⟩ := Adapters.glauberman_zStar P a' hcen ha'2 hiso
  have hO : oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore G) with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card (oddCore G) := by
        rw [h, card_top, ← ha2]
        exact orderOf_dvd_natCard a
      have hodd : Nat.Coprime 2 (Nat.card (oddCore G)) := by
        have := pPrimeCore_coprime_card (p := 2) (G := G)
        have heq : oddCore G = pPrimeCore 2 G := by
          rw [oddCore_eq_piCore, pPrimeCore_eq_piCore]
        rwa [heq]
      exact absurd (Nat.Coprime.coprime_dvd_right h2 hodd) (by norm_num)
  have hcenG : a ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h1 := (mem_center_iff.mp hz) (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    rw [hO, mem_bot] at h1
    have : (g * a)⁻¹ * (a * g) = 1 := h1
    rw [inv_mul_eq_one] at this
    exact this
  obtain ⟨g, h, hgh⟩ := hnab
  have hcG : center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
    · rw [h1, mem_bot] at hcenG
      rw [hcenG, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
    · exact h1
  apply hgh
  exact (mem_center_iff.mp (hcG ▸ mem_top g : g ∈ center G) h).symm

omit [Finite G] in
theorem le_normalizer_oddIn_self (J : Subgroup G) :
    J ≤ normalizer ((oddIn J : Subgroup G) : Set G) := fun j hj =>
  mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_oddIn hj hy, fun hy => by
    have := conj_mem_oddIn (inv_mem hj) hy
    rwa [show j⁻¹ * (j * y * j⁻¹) * j⁻¹⁻¹ = y by group] at this⟩

theorem false_of_stronglyClosed_le_zStarIn (hGold : GoldschmidtStronglyClosedInput)
    [IsSimpleGroup G] (hnab : ∃ g h : G, g * h ≠ h * g) (P : Sylow 2 G) {a : G} {J A : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hAJ : A ≤ zStarIn J) (hAP : A ≤ (P : Subgroup G)) (hA : A ≠ ⊥)
    (hsc : ∀ y ∈ A, ∀ g : G, g⁻¹ * y * g ∈ (P : Subgroup G) → g⁻¹ * y * g ∈ A) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hsolv := hGold G hsF hnF P A hAP hA hsc
  have hAJ' : A ≤ J := hAJ.trans (map_subtype_le _)
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hAcen : ∀ f ∈ A, ∀ l ∈ J, f * l * f⁻¹ * l⁻¹ ∈ oddIn J := by
    intro f hf l hl
    have hfK : f ∈ coreActionKernel J := (mem_inf.mp (hzK ▸ hAJ hf)).2
    have h1 := (mem_coreActionKernel.mp (inv_mem hfK)).2 l hl
    rw [inv_inv] at h1
    have h2 := conj_mem_oddIn hl h1
    rwa [show l * (l⁻¹ * f * l * f⁻¹) * l⁻¹ = f * l * f⁻¹ * l⁻¹ by group] at h2
  have hcov := le_pLayer_inf_centralizer_sup hJa hJc (hAJ'.trans hJa)
    (P.isPGroup'.to_le hAP)
    (hAJ'.trans le_normalizer) hAcen
  set C : Subgroup G := J ⊓ centralizer (A : Set G) with hC
  have hCs : Group.IsSolvable C :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective
      (inf_le_right : C ≤ centralizer (A : Set G)))
  set f : C →* (↥J ⧸ pPrimeCore 2 ↥J) := (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp
    (inclusion (inf_le_left : C ≤ J)) with hf
  have hfs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
    have hj := hcov j.2
    have hLN : (pLayer ↥C 2).map C.subtype ≤ normalizer ((oddIn J : Subgroup G) : Set G) :=
      (map_subtype_le _).trans (inf_le_left.trans (le_normalizer_oddIn_self J))
    have hj' : (j : G) ∈ ((pLayer ↥C 2).map C.subtype : Set G) * (oddIn J : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hLN]
      exact hj
    obtain ⟨l, hl, o, ho, hlo⟩ := hj'
    have hlC : l ∈ C := (map_subtype_le _ : (pLayer ↥C 2).map C.subtype ≤ C) hl
    refine ⟨⟨l, hlC⟩, ?_⟩
    simp only [hf, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    obtain ⟨o', ho', rfl⟩ := ho
    have : (inclusion (inf_le_left : C ≤ J) ⟨l, hlC⟩)⁻¹ * j = o' := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [← hlo]
      simp
    rw [this]
    exact ho'
  have hQs : Group.IsSolvable (↥J ⧸ pPrimeCore 2 ↥J) := Group.isSolvable_of_surjective hfs
  have h1 : Group.IsPerfect ↥(J.subgroupOf (centralizer ({a} : Set G))) :=
    CatalogueBAlternating.pComponent_perfect hJc
  have hJper : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJa).toMonoidHom)
      (subgroupOfEquivOfLe hJa).surjective
  have hQper : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hQnt : Nontrivial (↥J ⧸ pPrimeCore 2 ↥J) := by
    obtain ⟨hs, -, -, -⟩ := fusionZStar_quotient_of_isPComponent hJa hJc
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h1 : Subsingleton (↥J ⧸ Open.fusionZStar ↥J) := by
      refine ⟨fun u v => ?_⟩
      induction u using QuotientGroup.induction_on with
      | H u =>
      induction v using QuotientGroup.induction_on with
      | H v =>
      rw [QuotientGroup.eq]
      have hle : pPrimeCore 2 ↥J ≤ Open.fusionZStar ↥J := by
        intro w hw
        rw [GrS4.fusionZStar_eq_comap_pPrimeCore]
        show QuotientGroup.mk' (pPrimeCore 2 ↥J) w ∈ center _
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff w).mpr hw]
        exact one_mem _
      apply hle
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    have := hs.toNontrivial
    exact not_subsingleton _ h1
  obtain ⟨n, hn⟩ := hQs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hn
  exact top_ne_bot hn

theorem wGroup_eq_of_le_of_connected (hGW : GWTwoBalanced G) {J P R W : Subgroup G}
    (hP : IsSylowTwoIn P J) (hWR : wGroup R = W)
    (hJW : J ≤ normalizer (W : Set G))
    (hconn : ∀ F : Subgroup G, F ≤ P → IsEightGroup F →
      ∃ j ∈ J, AbelianConnectedIn J 3 R (conjugate F j))
    {F : Subgroup G} (hFJ : F ≤ J) (hF : IsEightGroup F) : wGroup F = W := by
  obtain ⟨c, hcJ, hc⟩ := hP.exists_conj_le hFJ hF.1.isPGroup
  set F' : Subgroup G := F.map (MulAut.conj c).toMonoidHom with hF'
  have hF'P : F' ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have hF'8 : IsEightGroup F' :=
    ⟨hF.1.map_conj c, by rw [hF', card_map_of_injective (MulAut.conj c).injective, hF.2]⟩
  obtain ⟨j, hjJ, hj⟩ := hconn F' hF'P hF'8
  have h1 := wGroup_eq_of_abelianConnected hGW hj.abelianConnected
  rw [hWR, wGroup_conjugate, hF', wGroup_map_conj] at h1
  unfold conjugate at h1
  rw [map_map] at h1
  have hcomp : (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (j⁻¹ * c)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp] at h1
  have hW' : W.map (MulAut.conj (j⁻¹ * c)).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (hJW (mul_mem (inv_mem hjJ) hcJ))
  apply map_injective (f := (MulAut.conj (j⁻¹ * c)).toMonoidHom) (MulAut.conj (j⁻¹ * c)).injective
  rw [← h1, hW']

end CFSG.ComponentClassification.GrSLit.GrS4
