module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympField
import CFSG.GH74.Generic.GKFCover
import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerEmbed
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm (mem_spFixedGroup spFixedGroup_fieldAut_eq_range subfieldInj
  subfieldInj_injective range_subfieldInj simple_perfect_statedProj statedProjEquivSympFour
  subfieldProj subfieldProj_eq_one_iff)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour)
open scoped commutatorElement

private theorem isSubnormal_inf {G : Type*} [Group G] {H K : Subgroup G} (h : IsSubnormal H K)
    (N : Subgroup G) : IsSubnormal (H ⊓ N) (K ⊓ N) := by
  induction h with
  | refl H => exact IsSubnormal.refl _
  | @step H M K hle hnormal _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hle)]
    rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
    rintro h m ⟨hh, hhN⟩ ⟨hm, hmN⟩
    exact ⟨hnormal h m hh hm, N.mul_mem (N.mul_mem hmN hhN) (N.inv_mem hmN)⟩

private theorem eq_bot_or_top_of_isSubnormal_simple {S : Type*} [Group S] [IsSimpleGroup S]
    {L : Subgroup S} (h : IsSubnormal L ⊤) : L = ⊥ ∨ L = ⊤ := by
  suffices ∀ M K : Subgroup S, IsSubnormal M K → K = ⊤ → M = ⊥ ∨ M = ⊤ from this L ⊤ h rfl
  intro M K hMK
  induction hMK with
  | refl => intro hK; exact Or.inr hK
  | @step H M K hle hnormal _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hle)
    · subst hM
      have hN : H.Normal := by
        rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
        exact ⟨fun x hx g => hnormal x g hx (Subgroup.mem_top g)⟩
      haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem eq_of_isComponentOf_of_simple {S : Type*} [Group S] {C N K : Subgroup S}
    (hNC : N ≤ C) (hN : IsSimpleGroup ↥N) (hcomm : ⁅C, C⁆ ≤ N) (hK : IsComponentOf K C) :
    K = N := by
  obtain ⟨hKC, hsub, hq⟩ := hK
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨hq.1⟩
  have hKN : K ≤ N := by
    calc K = ⁅K, K⁆ := hperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hKC hKC
      _ ≤ N := hcomm
  have hsubN : IsSubnormal K N := by
    have := isSubnormal_inf hsub N
    rwa [inf_eq_left.2 hKN, inf_eq_right.2 hNC] at this
  have hsubN' : IsSubnormal (K.subgroupOf N) ⊤ := by
    have := LieSemisimple.isSubnormal_comap_of_injective N.subtype N.subtype_injective
      (by rw [Subgroup.range_subtype]) hsubN
    change IsSubnormal (K.subgroupOf N) (N.subgroupOf N) at this
    rwa [Subgroup.subgroupOf_self] at this
  haveI := hN
  rcases eq_bot_or_top_of_isSubnormal_simple hsubN' with h | h
  · exfalso
    have hK1 : K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hKN hx⟩ : ↥N) ∈ K.subgroupOf N := hx
      rw [h, Subgroup.mem_bot] at h1
      simpa using congrArg Subtype.val h1
    subst hK1
    have := hq.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup S) ⧸ Subgroup.center ↥(⊥ : Subgroup S))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a b))
  · exact le_antisymm hKN (Subgroup.subgroupOf_eq_top.1 h)

private theorem eq_map_commutator_of_isComponentOf {S : Type*} [Group S] {C K : Subgroup S}
    {H : Type*} [Group H] (E : ↥C ≃* H) (hs : IsSimpleGroup ↥(commutator H))
    (hK : IsComponentOf K C) : K = (commutator ↥C).map C.subtype := by
  set D : Subgroup ↥C := commutator ↥C with hD
  have hmap : D.map E.toMonoidHom = commutator H := by
    rw [hD, commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      E.toMonoidHom.range_eq_top_of_surjective E.surjective]
  let e₁ : ↥D ≃* ↥(commutator H) :=
    (D.equivMapOfInjective E.toMonoidHom E.injective).trans (MulEquiv.subgroupCongr hmap)
  haveI : IsSimpleGroup ↥D := e₁.isSimpleGroup
  have hN : IsSimpleGroup ↥(D.map C.subtype) :=
    (D.equivMapOfInjective C.subtype C.subtype_injective).symm.isSimpleGroup
  refine eq_of_isComponentOf_of_simple ?_ hN ?_ hK
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    exact ⟨⁅(⟨g₁, h₁⟩ : ↥C), ⟨g₂, h₂⟩⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), rfl⟩

private theorem exists_cover_of_range_eq {X Y S : Type*} [Group X] [Group Y] [Group S]
    (ι : X →* Y) (hι : Function.Injective ι) (ψ : Y →* S) (hψ : ψ.ker ≤ Subgroup.center Y)
    {K : Subgroup S} (h : (ψ.comp ι).range = K) :
    ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  refine ⟨(ψ.comp ι).codRestrict K (fun x => h ▸ ⟨x, rfl⟩), ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← h] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ψ (ι x) = 1 := congrArg Subtype.val hx
    have h2 : ι x ∈ Subgroup.center Y := hψ h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 h2 (ι g)

private theorem noThreeCover_statedProj_sp_two_eight
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8) :
    NoThreeCover (StatedProj (StatedSp 2 K)) := by
  intro Y _ _ hY ⟨e⟩ h3
  obtain ⟨-, ⟨m⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier
    (K := K) (n := 2) (f := 3) (by rw [hK]; norm_num) (by norm_num) le_rfl
    (fun _ => by norm_num)
  have hY' : CFSG.IsQuasisimple Y :=
    ⟨⟨hY.1⟩, hY.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hY' e
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSp 2 K))) = 1 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr m.toEquiv]
    have : Nat.gcd 2 (Nat.card K - 1) = 1 := by rw [hK]; norm_num
    rw [this]
    simp
  rw [hcard] at hdvd
  have := Nat.le_of_dvd (by norm_num) (h3.trans hdvd)
  omega

private theorem fixSubgroup_fieldAut_eq_range {r : ℕ} [NeZero r] {K : Type} [Field K] {p : ℕ}
    (hp : Odd p) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    fixSubgroup (SymplecticHigher.fieldAut r K σ) = (subfieldProj (r := r) σ).range := by
  rw [← spFixedGroup_fieldAut_eq_range hp hσ]
  exact Subgroup.ext fun x => mem_fixSubgroup.trans mem_spFixedGroup.symm

private theorem nonempty_fixSubgroup_equiv {r : ℕ} [NeZero r] {K : Type} [Field K] {p : ℕ}
    (hp : Odd p) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    Nonempty (↥(fixSubgroup (SymplecticHigher.fieldAut r K σ)) ≃*
      StatedProj (StatedSp r (descentField σ))) := by
  have hfix : fixSubgroup (SymplecticHigher.fieldAut r K σ) = (subfieldInj (r := r) σ).range :=
    (fixSubgroup_fieldAut_eq_range hp hσ).trans (range_subfieldInj σ).symm
  exact ⟨(MulEquiv.subgroupCongr hfix).trans
    (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ)).symm⟩

private theorem card_descentField_pow {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    Nat.card (descentField σ) ^ orderOf σ = Nat.card K := by
  have h : descentField σ = CFSG.GH74.GLS.IVK.fixedField σ := by
    ext x
    rw [CFSG.GH74.GLS.IVK.mem_fixedField_iff]
    exact mem_descentField
  rw [h]
  exact CFSG.GH74.GLS.IVK.fixedField_card_pow σ

private theorem ker_subfieldProj_le_center {r : ℕ} [NeZero r] {K : Type} [Field K]
    (σ : K ≃+* K) :
    (subfieldProj (r := r) σ).ker ≤ Subgroup.center ↥(StatedSp r (descentField σ)) := by
  intro g hg
  rw [MonoidHom.mem_ker, subfieldProj_eq_one_iff] at hg
  exact SymplecticHigher.spScalars_le_center hg

private theorem ringChar_eq_two_of_card_descentField {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hk2 : Nat.card ↥(descentField σ) = 2) : ringChar K = 2 := by
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  have hk2' : Fintype.card ↥(descentField σ) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hk2
  have hc2 : ringChar ↥(descentField σ) = 2 := by
    apply CharP.ringChar_of_prime_eq_zero Nat.prime_two
    have := FiniteField.cast_card_eq_zero ↥(descentField σ)
    rwa [hk2'] at this
  exact (Algebra.ringChar_eq (descentField σ) K).symm.trans hc2

private theorem prod_ne_two_two {r : ℕ} {k : Type} [Field k] [Finite k] [Fintype k]
    (hex : ¬(r = 2 ∧ Nat.card k = 2)) : (r, Fintype.card k) ≠ (2, 2) := by
  intro h
  apply hex
  refine ⟨congrArg Prod.fst h, ?_⟩
  rw [Nat.card_eq_fintype_card]
  exact congrArg Prod.snd h

theorem sp_fieldAut_comp_generic (hSp : SpFactorFacts) {p : ℕ} (hp : Odd p) {r : ℕ} (hr : 2 ≤ r)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ : σ ^ p = 1)
    (hex : ¬(r = 2 ∧ Nat.card ↥(descentField σ) = 2)) :
    LieFactorData (ringChar K) ↥(StatedSp r (descentField σ)) ∧
      ∀ K' : Subgroup (StatedProj (StatedSp r K)),
        IsComponentOf K' (fixSubgroup (SymplecticHigher.fieldAut r K σ)) →
        ∃ f : ↥(StatedSp r (descentField σ)) →* ↥K', Function.Surjective f ∧
          f.ker ≤ Subgroup.center ↥(StatedSp r (descentField σ)) := by
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := r) hp hσ
  have hCr := fixSubgroup_fieldAut_eq_range (r := r) hp hσ
  refine ⟨?_, fun K' hK' => ?_⟩
  · have := hSp (descentField σ) r hr (prod_ne_two_two hex)
    rwa [Algebra.ringChar_eq (descentField σ) K] at this
  · obtain ⟨hs, -⟩ := simple_perfect_statedProj (k := descentField σ) hr hex
    haveI : IsSimpleGroup ↥(fixSubgroup (SymplecticHigher.fieldAut r K σ)) := e.isSimpleGroup
    have hKC : K' = fixSubgroup (SymplecticHigher.fieldAut r K σ) :=
      eq_of_isComponentOf_of_simple le_rfl inferInstance
        (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
          (Subgroup.inv_mem _ h₂)) hK'
    exact exists_cover_of_range_eq (MonoidHom.id _) Function.injective_id
      (subfieldProj (r := r) σ) (ker_subfieldProj_le_center σ)
      (by rw [MonoidHom.comp_id, hKC, hCr])

theorem sp_fieldAut_comp_two (hSp42 : SpFourTwoFacts) {p : ℕ} (hp : Odd p) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hσ : σ ^ p = 1) (hk2 : Nat.card ↥(descentField σ) = 2) :
    LieFactorData (ringChar K) ↥(commutator ↥(StatedSp 2 (descentField σ))) ∧
      ∀ K' : Subgroup (StatedProj (StatedSp 2 K)),
        IsComponentOf K' (fixSubgroup (SymplecticHigher.fieldAut 2 K σ)) →
        ∃ f : ↥(commutator ↥(StatedSp 2 (descentField σ))) →* ↥K', Function.Surjective f ∧
          f.ker ≤ Subgroup.center ↥(commutator ↥(StatedSp 2 (descentField σ))) := by
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := 2) hp hσ
  have hCr := fixSubgroup_fieldAut_eq_range (r := 2) hp hσ
  refine ⟨?_, fun K' hK' => ?_⟩
  · rw [ringChar_eq_two_of_card_descentField hk2]
    refine hSp42 (descentField σ) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hk2
  · have hE : ↥(fixSubgroup (SymplecticHigher.fieldAut 2 K σ)) ≃* sympFour :=
      e.trans (statedProjEquivSympFour hk2)
    set C := fixSubgroup (SymplecticHigher.fieldAut 2 K σ)
    set ψ : ↥(StatedSp 2 (descentField σ)) →* StatedProj (StatedSp 2 K) :=
      subfieldProj (r := 2) σ
    let φ : ↥(StatedSp 2 (descentField σ)) →* ↥C :=
      ψ.codRestrict C (fun y => by rw [hCr]; exact ⟨y, rfl⟩)
    have hφ : Function.Surjective φ := by
      intro c
      have hc : (c : StatedProj (StatedSp 2 K)) ∈ ψ.range := by
        rw [← hCr]
        exact c.2
      obtain ⟨y, hy⟩ := hc
      exact ⟨y, Subtype.ext hy⟩
    have hmapφ : (commutator ↥(StatedSp 2 (descentField σ))).map φ = commutator ↥C := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        φ.range_eq_top_of_surjective hφ]
    have hKeq := eq_map_commutator_of_isComponentOf hE isSimpleGroup_commutator_sympFour hK'
    refine exists_cover_of_range_eq (commutator ↥(StatedSp 2 (descentField σ))).subtype
      (Subgroup.subtype_injective _) ψ (ker_subfieldProj_le_center σ) ?_
    rw [hKeq, MonoidHom.range_comp, Subgroup.range_subtype, ← hmapφ, Subgroup.map_map]
    rfl

theorem lieCompExport_fieldAut_sp
    (hSp : SpFactorFacts) (hSp6 : SpAltSixFacts)
    (hSp42 : SpFourTwoFacts) {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    LieCompExport (ringChar K) (SymplecticHigher.fieldAut r K σ) := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hodd : Odd 3 := by decide
  have hlayer := LieSemisimple.perfectInLayer_fieldAut_sp hr Nat.prime_three (by norm_num) σ hσ3
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  by_cases hex : r = 2 ∧ Nat.card ↥(descentField σ) = 2
  ·
    obtain ⟨rfl, hk2⟩ := hex
    obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_two hSp42 hodd σ hσ3 hk2
    refine ⟨hlayer, fun K' hK' => ?_, fun _ => ?_⟩
    · obtain ⟨f, hf, hfk⟩ := hcover K' hK'
      exact ⟨_, inferInstance, inferInstance, hLF, f, hf, hfk⟩
    · haveI : CharP K 2 := ringChar_eq_two_of_card_descentField hk2 ▸ ringChar.charP K
      have hK8 : Nat.card K = 8 := by
        rw [← card_descentField_pow σ, hσ, hk2]
        norm_num
      exact noThreeCover_statedProj_sp_two_eight hK8
  ·
    obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_generic hSp hodd hr σ hσ3 hex
    refine ⟨hlayer, fun K' hK' => ?_, fun ⟨K', hK', ⟨a⟩⟩ => ?_⟩
    · obtain ⟨f, hf, hfk⟩ := hcover K' hK'
      exact ⟨_, inferInstance, inferInstance, hLF, f, hf, hfk⟩
    · exfalso
      obtain ⟨f, hf, hfk⟩ := hcover K' hK'
      obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hLF.perfect f hf hfk
      exact (hSp6 (descentField σ) r hr (prod_ne_two_two hex)).false (e'.trans a)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
