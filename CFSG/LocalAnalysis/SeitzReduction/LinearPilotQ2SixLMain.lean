module

import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixLModel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixLLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWStd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (oddCoreLift HasBLift)

theorem lSixFieldNOneLiftInput_holds : LSixFieldNOneLiftInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc hLK hKt' htK _hZ
    hmodel a b hab hca hcb X₀ hX₀ hX₀c
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨F, _, _, hF, S, hSK, hSp, hSX, ⟨eS⟩⟩ :=
    exists_specialLinear_three_le_centralizer_of_fieldType hset hK e ht hKt hW₁c hW₁2 hW₁t htN
      hLN hLK hKt' hmodel hab hca hcb hX₀
  obtain ⟨htW, hs, hLs, hLq, hLZ, hCs⟩ :=
    seitzLeviBar_facts_six hset hK e ht hKt hW₁c hW₁2 hW₁t htN hLN
  have hmap : (seitzLeviBar e c W₁).map (QuotientGroup.mk' (oddCore (seitzBar W₁))) =
      seitzLeviHat e c W₁ := by
    rw [seitzLeviBar, seitzLeviHat, Subgroup.map_map]
    rfl
  obtain ⟨hcomp, -, -⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ hCs
  rw [hmap] at hcomp
  have hsN : QuotientGroup.mk' (oddCore (seitzBar W₁))
      (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩) ∈
        normalizer (Kc : Set (seitzHat W₁)) :=
    mem_normalizer_iff_map_conj_eq.2 hKt'
  have hs2 : seitzHatMap W₁ ⟨t, htN⟩ * seitzHatMap W₁ ⟨t, htN⟩ = 1 := by
    rw [← sq, ← orderOf_seitzHatMap_eq_two htN ht htW, pow_orderOf_eq_one]
  have hCY := centralizer_mk_le_sup_of_le_sup hs hCs
  rw [hmap] at hCY
  have hsC : QuotientGroup.mk' (oddCore (seitzBar W₁))
      (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩) ∉
        centralizer (Kc : Set (seitzHat W₁)) := by
    intro h
    have hle : Kc ≤ Kc ⊓ centralizer ({seitzHatMap W₁ ⟨t, htN⟩} : Set (seitzHat W₁)) :=
      le_inf le_rfl fun k hk => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h k hk)
    exact hLK.not_ge (hle.trans (inf_centralizer_le_of_not_mem hs2 hLK.le hcomp.1 hCY htK))
  obtain ⟨hB, -, -, -, -⟩ := isComponent_oddCoreLift_of_le_sup hs hLs hLq hLZ hCs hKc hsN hsC
  have hLbp : ⁅seitzLeviBar e c W₁, seitzLeviBar e c W₁⁆ = seitzLeviBar e c W₁ :=
    Subgroup.isPerfect_iff.mp ⟨hLq.1⟩
  have hLbK : seitzLeviBar e c W₁ ≤ oddCoreLift Kc :=
    F4Pilot.le_oddCoreLift_of_perfect hLbp (by rw [hmap]; exact hLK.le)
  have hab' : ({a, b} : Finset (Fin 6)) ⊆ {c}ᶜ := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_compl, Finset.mem_singleton]
    rcases hy with rfl | rfl
    · exact fun h => hca h.symm
    · exact fun h => hcb h.symm
  have hXL₁ : modelToG e X₀ ≤ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) :=
    modelToG_mono e (hX₀.trans (blockSL_mono hab'))
  have hXN : modelToG e X₀ ≤ normalizer (W₁ : Set G) := hXL₁.trans hLN
  have hXK : ((modelToG e X₀).subgroupOf (normalizer (W₁ : Set G))).map
      (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))) ≤ oddCoreLift Kc :=
    le_trans (map_mono fun x hx => mem_subgroupOf.2 (hXL₁ (mem_subgroupOf.1 hx))) hLbK
  have hXc : Nat.card ((modelToG e X₀).subgroupOf (normalizer (W₁ : Set G))) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv, natCard_modelToG_eq, hX₀c, hK]
  have hX3 : IsPGroup 3 ((modelToG e X₀).subgroupOf (normalizer (W₁ : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hW3 : ¬ 3 ∣ Nat.card (W₁.subgroupOf (normalizer (W₁ : Set G))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, hW₁c]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKp : ⁅Kc, Kc⁆ = Kc := Subgroup.isPerfect_iff.mp hKc.1.1
  have hSX' : S ≤ centralizer (((((modelToG e X₀).subgroupOf (normalizer (W₁ : Set G))).map
      (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))))).map
        (QuotientGroup.mk' (oddCore (seitzBar W₁))) : Subgroup (seitzHat W₁)) :
          Set (seitzHat W₁)) := by
    rw [Subgroup.map_map]
    exact hSX
  obtain ⟨P, hPX, hPp, hPmap⟩ := exists_perfect_le_centralizer_map_map_eq_of_hasBLift 3
    (W₁.subgroupOf (normalizer (W₁ : Set G))) hW3 hX3 hKp hB hXK hSp hSK hSX'
  have hPS : P.map (seitzHatMap W₁) = S := by
    rw [← hPmap, Subgroup.map_map]
    rfl
  refine ⟨P.map (normalizer (W₁ : Set G)).subtype, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hPX hp) ⟨x, hXN hx⟩ (mem_subgroupOf.2 hx))
  · rw [← map_commutator, hPp]
  ·
    have hmem : ∀ p : P, ((seitzHatMap W₁).comp P.subtype) p ∈ S := fun p => by
      rw [← hPS]
      exact ⟨p, p.2, rfl⟩
    let g₂ : P →* S := ((seitzHatMap W₁).comp P.subtype).codRestrict S hmem
    have hg₂ : Function.Surjective g₂ := by
      rintro ⟨y, hy⟩
      rw [← hPS] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨⟨p, hp⟩, rfl⟩
    let f : P.map (normalizer (W₁ : Set G)).subtype →* LinearFlag.projectiveSL 3 F :=
      (LinearFlag.proj 3 F).comp (eS.toMonoidHom.comp (g₂.comp
        (P.equivMapOfInjective _ (normalizer (W₁ : Set G)).subtype_injective).symm.toMonoidHom))
    have hf : Function.Surjective f :=
      (LinearFlag.proj_surjective 3 F).comp (eS.surjective.comp (hg₂.comp (MulEquiv.surjective _)))
    exact ⟨f.ker, inferInstance, lieModel_of_mulEquiv_projectiveSL le_rfl (by norm_num) hF
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end CFSG.SeitzReduction.LinearPilot
