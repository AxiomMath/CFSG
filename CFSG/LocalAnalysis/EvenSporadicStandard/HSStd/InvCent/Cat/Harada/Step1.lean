module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
import CFSG.GH74.GLS.Stage2.Local.P27.P1Abs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Perm5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SolMax.FiveCat CFSG.ComponentClassification.CatLeaf
open scoped commutatorElement

theorem fusionOddCore_eq_bot_of_simple {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (h2 : 2 ∣ Nat.card H) : Open.fusionOddCore H = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hodd⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · exact hb.le
  · exfalso
    rw [ht, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem pPrimeCore_eq_bot_of_simple {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (h2 : 2 ∣ Nat.card H) : pPrimeCore 2 H = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 H) with hb | ht
  · exact hb
  · exfalso
    have hc : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 H)) := pPrimeCore_coprime_card
    rw [ht, Subgroup.card_top] at hc
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h2) (by norm_num)

theorem fusionZStar_eq_bot_of_simple {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) (h2 : 2 ∣ Nat.card H) : Open.fusionZStar H = ⊥ := by
  have hO := fusionOddCore_eq_bot_of_simple (H := H) h2
  have hinj : Function.Injective (QuotientGroup.mk' (Open.fusionOddCore H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  rw [eq_bot_iff]
  intro x hx
  have hx' : QuotientGroup.mk' (Open.fusionOddCore H) x ∈ Subgroup.center _ := hx
  rw [Subgroup.mem_center_iff] at hx'
  have hcen : x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hinj
    rw [map_mul, map_mul]
    exact hx' _
  rw [center_eq_bot_of_simple hna] at hcen
  exact hcen

section Conj

variable {G : Type*} [Group G]

theorem mul_self_eq_one_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [ht, sq] at h
  exact h

theorem ne_one_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at ht
  omega

theorem conjNormal_involutive {S : Subgroup G} [S.Normal] {t : G} (ht2 : t * t = 1) (y : ↥S) :
    MulAut.conjNormal (H := S) t (MulAut.conjNormal (H := S) t y) = y := by
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply]
  have h1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [h1]
  calc t * (t * (y : G) * t) * t = (t * t) * (y : G) * (t * t) := by group
    _ = y := by rw [ht2]; group

theorem mem_fixedSubgroup_conjNormal {S : Subgroup G} [S.Normal] {t : G} (ht2 : t * t = 1)
    (x : ↥S) : x ∈ fixedSubgroup (MulAut.conjNormal (H := S) t) ↔ (x : G) * t = t * (x : G) := by
  have h1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  change MulAut.conjNormal (H := S) t x = x ↔ _
  rw [Subtype.ext_iff, MulAut.conjNormal_apply, h1]
  constructor
  · intro h
    calc (x : G) * t = (t * (x : G) * t) * t := by rw [h]
      _ = t * (x : G) := by
        calc t * (x : G) * t * t = t * (x : G) * (t * t) := by group
          _ = t * (x : G) := by rw [ht2]; group
  · intro h
    calc t * (x : G) * t = (x : G) * t * t := by rw [← h]
      _ = x := by
        calc (x : G) * t * t = (x : G) * (t * t) := by group
          _ = x := by rw [ht2]; group

theorem centralizerDerived_le (t : G) : centralizerDerived t ≤ centralizer ({t} : Set G) :=
  Subgroup.map_subtype_le _

theorem conj_mem_centralizerDerived {t c p : G} (hc : c ∈ centralizer ({t} : Set G))
    (hp : p ∈ centralizerDerived t) : c * p * c⁻¹ ∈ centralizerDerived t := by
  obtain ⟨q, hq, rfl⟩ := hp
  refine ⟨(⟨c, hc⟩ : ↥(centralizer ({t} : Set G))) * q *
    (⟨c, hc⟩ : ↥(centralizer ({t} : Set G)))⁻¹, ?_, rfl⟩
  exact (inferInstance : (commutator ↥(centralizer ({t} : Set G))).Normal).conj_mem q hq _

theorem le_centralizerDerived_of_perfect {t : G} {B : Subgroup G}
    (hB : B ≤ centralizer ({t} : Set G)) (hperf : ⁅B, B⁆ = B) : B ≤ centralizerDerived t := by
  rw [← hperf]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  refine ⟨⁅(⟨x, hB hx⟩ : ↥(centralizer ({t} : Set G))), ⟨y, hB hy⟩⁆, ?_, ?_⟩
  · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rfl

end Conj

theorem nonab_alternatingGroup_five :
    ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := rhyp_perm5.nonab
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

theorem natCard_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

section Main

variable {G : Type} [Group G] [Finite G]

theorem fivePumpOutcome_of_derived (hleaf : FivePumpLeaf)
    {S : Subgroup G} [hSn : S.Normal] (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hcat : Blueprint.Catalog ↥S)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2)
    (hPS : centralizerDerived t ≤ S)
    (hP5 : Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 5))) :
    FivePumpOutcome ↥S := by
  classical
  obtain ⟨e5⟩ := hP5
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := rhyp_perm5.simple
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  set P : Subgroup G := centralizerDerived t with hPdef
  have hPC : P ≤ centralizer ({t} : Set G) := centralizerDerived_le t
  set σ : MulAut ↥S := MulAut.conjNormal t with hσdef
  have hσ : ∀ y, σ (σ y) = y := conjNormal_involutive ht2
  set D : Subgroup ↥S := fixedSubgroup σ with hD
  have hmemD : ∀ x : ↥S, x ∈ D ↔ (x : G) * t = t * (x : G) := mem_fixedSubgroup_conjNormal ht2
  set PS : Subgroup ↥S := P.subgroupOf S with hPSdef
  have hPSD : PS ≤ D := by
    intro x hx
    rw [hmemD]
    exact mem_centralizer_singleton_iff.1 (hPC hx)
  let eA : ↥PS ≃* alternatingGroup (Fin 5) := (Subgroup.subgroupOfEquivOfLe hPS).trans e5
  haveI hPSsimple : IsSimpleGroup ↥PS := eA.isSimpleGroup
  have hcard : Nat.card ↥PS = 60 := by
    rw [Nat.card_congr eA.toEquiv, natCard_alternatingGroup_five]
  have h2 : 2 ∣ Nat.card ↥PS := by rw [hcard]; norm_num
  have hZ : Open.fusionZStar ↥PS = ⊥ :=
    fusionZStar_eq_bot_of_simple (by
      obtain ⟨a, b, hab⟩ := nonab_alternatingGroup_five
      exact ⟨eA.symm a, eA.symm b, fun h => hab (eA.symm.injective (by
        rw [map_mul, map_mul]; exact h))⟩) h2
  have hO : pPrimeCore 2 ↥PS = ⊥ := pPrimeCore_eq_bot_of_simple h2
  have hnormA : (PS.subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥S) : G) ∈ P := hn
    have hg : ((g : ↥S) : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 ((hmemD g).1 g.2)
    exact conj_mem_centralizerDerived hg hn'
  have hperf : ∀ B : Subgroup ↥D, ⁅B, B⁆ = B → B.map (MonoidHom.id ↥D) ≤ PS.subgroupOf D := by
    intro B hB x hx
    let f : ↥D →* G := S.subtype.comp D.subtype
    have hB' : B.map f ≤ P := by
      refine le_centralizerDerived_of_perfect ?_ ?_
      · rintro _ ⟨b, hb, rfl⟩
        exact mem_centralizer_singleton_iff.2 ((hmemD b.1).1 b.2)
      · rw [← Subgroup.map_commutator, hB]
    have hx' : f x ∈ B.map f := ⟨x, by simpa using hx, rfl⟩
    exact hB' hx'
  have hAs : IsSimpleGroup ↥(PS.subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe hPSD).isSimpleGroup
  have hAn : ∃ a b : ↥(PS.subgroupOf D), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := nonab_alternatingGroup_five
    let e : ↥(PS.subgroupOf D) ≃* alternatingGroup (Fin 5) :=
      (Subgroup.subgroupOfEquivOfLe hPSD).trans eA
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hA2 : 2 ∣ Nat.card ↥(PS.subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPSD).toEquiv]
    exact h2
  obtain ⟨P₀, hP₀, hmap, -⟩ := CFSG.GH74.GLS.Stage2.Local.P27.unique_pComponent_of_simple_image
    (MonoidHom.id ↥D) (fun x hx => by
      have : x = 1 := by simpa [MonoidHom.mem_ker] using hx
      rw [this, orderOf_one]; exact odd_one)
    (PS.subgroupOf D) hAs hAn hA2 (fun x _ => ⟨x, rfl⟩) (by
      rw [Subgroup.comap_id]; exact hnormA.isSubnormal) hperf
  rw [Subgroup.map_id] at hmap
  have hcomp : IsPComponent 2 (PS.subgroupOf D) := (hP₀ _).2 hmap.symm
  have hPStop : PS ≠ ⊤ := by
    intro htop
    apply ne_one_of_orderOf_eq_two ht
    have : t ∈ centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxP : (⟨x, hx⟩ : ↥S) ∈ PS := htop ▸ Subgroup.mem_top _
      exact mem_centralizer_singleton_iff.1 (hPC hxP)
    rw [hcent, Subgroup.mem_bot] at this
    exact this
  refine hleaf ↥S hS hnab hcat σ PS ⟨hσ, hPSD, hcomp, hPStop⟩ (by rw [hZ, hO]) ?_ ?_
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eA)⟩
  · rintro P' ⟨-, hP'D, hP'comp, -⟩
    have h1 : P'.subgroupOf D = PS.subgroupOf D := ((hP₀ _).1 hP'comp).trans hmap
    have h2 := Subgroup.subgroupOf_inj.1 h1
    rwa [inf_eq_left.2 hP'D, inf_eq_left.2 hPSD] at h2

end Main

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
