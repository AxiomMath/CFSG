module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution.LBalanceProof

open CFSG CFSG.ComponentClassification Subgroup
open scoped commutatorElement

theorem exists_twoComponent_centralizer {H : Type} [Group H] [Finite H] (K : Subgroup H) (hK : IsPComponent 2 K)
    (z : H) (hz : orderOf z = 2) (hKz : ⁅K, zpowers z⁆ ≤ pPrimeCore 2 H) :
    ∃ K1 : Subgroup (centralizer ({z} : Set H)), IsPComponent 2 K1 ∧
      K ≤ K1.map (centralizer ({z} : Set H)).subtype ⊔ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kt, hKt, -, hmap, -⟩ := hK
  set N := pPrimeCore 2 H with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have := ComponentClassification.OddCore.odd_card H
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hcop : Nat.Coprime 2 (Nat.card N) := (Nat.coprime_two_left).2 hNodd
  let q := QuotientGroup.mk' N
  let C : Subgroup H := centralizer ({z} : Set H)
  let Ĉ : Subgroup (H ⧸ N) := centralizer ({q z} : Set (H ⧸ N))
  have hKtC : Kt ≤ Ĉ := by
    rw [← hmap]
    rintro _ ⟨k, hk, rfl⟩
    change q k ∈ centralizer ({q z} : Set (H ⧸ N))
    rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := N)).2
    have h1 : ⁅k⁻¹, z⁻¹⁆ ∈ ⁅K, zpowers z⁆ :=
      commutator_mem_commutator (K.inv_mem hk) (Subgroup.inv_mem _ (Subgroup.mem_zpowers z))
    have h2 := hKz h1
    have h3 := N.inv_mem h2
    simpa [commutatorElement_def, mul_assoc] using h3
  have hcomp : IsComponent (Kt.subgroupOf Ĉ) :=
    LocalAnalysis.ComponentInitial.component_overgroup hKt hKtC
  have hOddĈ : Odd (Nat.card (pPrimeCore 2 Ĉ)) := by
    have := ComponentClassification.OddCore.odd_card Ĉ
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hsolv : Group.IsSolvable (pPrimeCore 2 Ĉ) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOddĈ
  have hKtP : IsPComponent 2 (Kt.subgroupOf Ĉ) :=
    LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
      (LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp hsolv)
  have : Fact (IsPGroup 2 (zpowers z)) := ⟨by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hz]
    exact ⟨1, by norm_num⟩⟩
  have hcent : Ĉ = C.map q := by
    have h : centralizer (((zpowers z).map q : Subgroup (H ⧸ N)) : Set (H ⧸ N)) =
        (centralizer ((zpowers z : Subgroup H) : Set H)).map q :=
      centralizer_map_quotient_eq_map_centralizer 2 (zpowers z) N hNn hcop
    rw [MonoidHom.map_zpowers] at h
    simp only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  let f : C →* Ĉ := (q.comp C.subtype).codRestrict Ĉ
    (fun c => by rw [hcent]; exact ⟨c, c.2, rfl⟩)
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hcent] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hf_ker : Odd (Nat.card f.ker) := by
    have hinj : Function.Injective
        ((((C.subtype.comp f.ker.subtype).codRestrict N
          (fun c => by
            have h1 : f (c : C) = 1 := c.2
            have h2 := congrArg Subtype.val h1
            change q (c : C) = 1 at h2
            exact (QuotientGroup.eq_one_iff _).1 h2)) : f.ker →* N)) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective _ hinj)
  have hKtT : TwoComponents.IsTwoComponent (Kt.subgroupOf Ĉ) :=
    (CatalogueBAlternating.pComponent_two_iff _).1 hKtP
  obtain ⟨K1, hK1, hK1map⟩ :=
    OddKernelTwoComponents.exists_lift f hf_surj hf_ker (Kt.subgroupOf Ĉ) hKtT
  refine ⟨K1, (CatalogueBAlternating.pComponent_two_iff K1).2 hK1, ?_⟩
  have himg : (K1.map C.subtype).map q = Kt := by
    have h0 : (K1.map C.subtype).map q = (K1.map f).map Ĉ.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h0, hK1map, Subgroup.map_subgroupOf_eq_of_le hKtC]
  have hle : K.map q ≤ (K1.map C.subtype).map q := by rw [himg, hmap]
  have h := Subgroup.map_le_iff_le_comap.1 hle
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
end CFSG.ClassicalInvolution.LBalanceProof
