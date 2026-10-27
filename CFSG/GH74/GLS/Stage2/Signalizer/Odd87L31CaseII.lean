module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseIIData
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseIIAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSolv
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDm12Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Kinds

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Core

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem l31c_core {k : Kind} (hctx : Stage2Ctx G z k S) (hk : IsClassicalKind k)
    {R J₀ : Subgroup G} (hRS : R ≤ S) (hR : IsPGroup 2 ↥R) (hzR : z ∈ R)
    (hzZ : ∀ r ∈ R, r * z = z * r) (hrk : ∃ v ∈ R, v * v = 1 ∧ v ∉ zpowers z)
    (hcomm : ∀ x ∈ J₀, ∀ r ∈ R, x * r = r * x) (hJ₀ : ¬ Group.IsSolvable ↥J₀) :
    IsDihedral ↥R := by
  have hz2 : orderOf z = 2 := hctx.central.1
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  obtain ⟨v, hvR, hv2, hvz⟩ := hrk
  have hv1 : v ≠ 1 := fun h => hvz (by rw [h]; exact one_mem _)
  have hzv_ne : z ≠ v := fun h => hvz (by rw [← h]; exact mem_zpowers z)
  have hzv : z * v = v * z := (hzZ v hvR).symm
  have hRC : R ≤ Cen z := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzZ r hr)
  have hJC : J₀ ≤ Cen z := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hK : IsKleinFour ↥(NCDm12.fourSg z v) :=
    NCDm12.isKleinFour_fourSg hzz hv2 hzv hz1 hv1 hzv_ne
  have hU₀ : IVK.IsFourSubgroup (NCDm12.fourSg z v) := IVK.isFourSubgroup_of_isKleinFour hK
  have hU₀R : NCDm12.fourSg z v ≤ R := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hzR
    · rw [Set.mem_singleton_iff.mp hx]
      exact hvR
  have hJU : J₀ ≤ centralizer ((NCDm12.fourSg z v : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm x hx u (hU₀R hu)).symm
  have hnsC : ¬ Group.IsSolvable ↥(centralizer ((NCDm12.fourSg z v : Subgroup G) : Set G)) :=
    fun hs => hJ₀ (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJU)
      (Subgroup.inclusion_injective hJU))
  have hsw0 : ∃ u ∈ NCDm12.fourSg z v, SwapsComps z u := by
    by_contra h
    push Not at h
    exact hnsC (isSolvable_of_hasNormal2Compl (hasNormal2Compl_of_nonswap hctx hk hU₀
      (NCDm12.x_mem_fourSg z v) (hU₀R.trans hRS) h))
  obtain ⟨t, htU, hswc⟩ := hsw0
  obtain ⟨q, L₁, L₂, hp, hreach⟩ := l31c_classical_data hctx hk
  have hsw : Swaps z t L₁ L₂ := l31c_swaps_of_swapsComps hp hswc
  obtain ⟨htC, h12, h21⟩ := l31c_swap_conj hsw
  have htR : t ∈ R := hU₀R htU
  have ht2 : t * t = 1 := four_sq_eq_one hU₀ htU
  have htn : toBar z ⟨t, htC⟩ ∉ normalizer (L₁ : Set (CentralizerBar z)) :=
    not_mem_normalizer_of_swaps hp.ne htC hsw
  obtain ⟨P, hPJ, hPperf, hPns⟩ := l31c_exists_perfect hJ₀
  have hPC : P ≤ Cen z := hPJ.trans hJC
  have hPbperf := l31c_barOf_perfect hPC hPperf
  have hPbns := l31c_barOf_not_solvable hPC hPperf hPns
  obtain ⟨hPn₁, hPn₂⟩ := l31c_perfect_normalizes hp.ne hp.isComponent₁ hp.isComponent₂
    (l31c_all_comps hp) hPbperf
  have hPL : barOf z P ≤ L₁ ⊔ L₂ := by
    have h4 : 4 ≤ q := by have := hp.gt₁; omega
    obtain ⟨F₁, hF₁, hFin₁, hq₁, ⟨e₁⟩⟩ := hp.sl₁
    obtain ⟨F₂, hF₂, hFin₂, hq₂, ⟨e₂⟩⟩ := hp.sl₂
    have hq₁' : Nat.card F₁ = q := hq₁
    have hq₂' : Nat.card F₂ = q := hq₂
    exact l31c_perfect_le_sup hp.prod.2.1 (fun c h1 h2 => centralizer_pair_le_inf hp c h1 h2)
      (by omega) (by omega) (e₁.trans (specialLinearGroupEquivStatedSL 2 F₁).symm)
      (e₂.trans (specialLinearGroupEquivStatedSL 2 F₂).symm) hPbperf hPn₁ hPn₂
  have hcommP : ∀ r ∈ R, ∀ hr : r ∈ Cen z, ∀ p ∈ barOf z P,
      toBar z ⟨r, hr⟩ * p = p * toBar z ⟨r, hr⟩ := by
    intro r hrR hr p hp'
    obtain ⟨x, hx, rfl⟩ := hp'
    show toBar z ⟨r, hr⟩ * toBar z x = toBar z x * toBar z ⟨r, hr⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm (x : G) (hPJ (Subgroup.mem_subgroupOf.mp hx)) r hrR).symm
  have hnon : ∀ n ∈ R, ∀ hn : n ∈ Cen z,
      toBar z ⟨n, hn⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) → n ∈ zpowers z := by
    intro n hnR hn hnN
    have hin : toBar z ⟨n, hn⟩ ∈ L₁ ⊓ L₂ :=
      l31c_key hp hz2 hPL hPbperf hPbns h12 h21 (hcommP t htR htC) hnN
        (hreach n (hRS hnR) hn hnN) (hcommP n hnR hn)
    rw [inf_eq_zpowers_zbar hp hz2] at hin
    exact l31c_mem_zpowers_of_toBar hzz hR hzR hnR hn hin
  have ht1 : t ≠ 1 := by
    intro h
    apply htn
    have : toBar z ⟨t, htC⟩ = 1 := by
      have : (⟨t, htC⟩ : ↥(Cen z)) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [this]
    exact one_mem _
  have htz : z ≠ t := by
    intro h
    apply htn
    have e : toBar z ⟨t, htC⟩ = toBar z ⟨z, z_mem_cen z⟩ := by
      congr 1
      exact Subtype.ext h.symm
    rw [e, Subgroup.mem_normalizer_iff]
    intro a
    rw [zbar_central z a]
    simp
  have hzt : z * t = t * z := (hzZ t htR).symm
  have hRle : R ≤ NCDm12.fourSg z t := by
    intro r hr
    rw [NCDm12.mem_fourSg hzz ht2 hzt]
    by_cases hrn : toBar z ⟨r, hRC hr⟩ ∈ normalizer (L₁ : Set (CentralizerBar z))
    · rcases l31c_zpowers_two hzz (hnon r hr (hRC hr) hrn) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hmul : toBar z ⟨t, htC⟩ * toBar z ⟨r, hRC hr⟩ ∈
          normalizer (L₁ : Set (CentralizerBar z)) :=
        L29Pair.mul_mem_normalizer_of_not_mem hp.ne hp.isComponent₁ hp.isComponent₂
          (l31c_all_comps hp) hrn htn
      have htrC : t * r ∈ Cen z := (Cen z).mul_mem htC (hRC hr)
      have hmul' : toBar z ⟨t * r, htrC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) := by
        have e : toBar z ⟨t * r, htrC⟩ = toBar z ⟨t, htC⟩ * toBar z ⟨r, hRC hr⟩ := by
          rw [← map_mul]
          rfl
        rw [e]
        exact hmul
      have hrt : r = t * (t * r) := by
        calc r = (t * t) * r := by rw [ht2, one_mul]
          _ = t * (t * r) := by rw [mul_assoc]
      rcases l31c_zpowers_two hzz (hnon (t * r) (R.mul_mem htR hr) htrC hmul') with h | h
      · right; right; left
        rw [hrt, h, mul_one]
      · right; right; right
        rw [hrt, h, hzt]
  have hleR : NCDm12.fourSg z t ≤ R := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hzR
    · rw [Set.mem_singleton_iff.mp hx]
      exact htR
  have hReq : R = NCDm12.fourSg z t := le_antisymm hRle hleR
  rw [hReq]
  exact NCDm12.isDihedral_fourSg hzz ht2 hzt hz1 ht1 htz

theorem l31_a_central {k : Kind} (hctx : Stage2Ctx G z k S) (hk : IsClassicalKind k)
    {R J₀ : Subgroup G} (hR : IsPGroup 2 ↥R) (hzR : z ∈ R) (hzZ : ∀ r ∈ R, r * z = z * r)
    (hrk : ∃ v ∈ R, v * v = 1 ∧ v ∉ zpowers z) (hcomm : ∀ x ∈ J₀, ∀ r ∈ R, x * r = r * x)
    (hJ₀ : ¬ Group.IsSolvable ↥J₀) : IsCyclic ↥R ∨ IsDihedral ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : R ≤ Cen z := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzZ r hr)
  obtain ⟨T, hT, hRT⟩ := NCDm12.exists_isSylowOf_ge hRC hR
  obtain ⟨c, hcC, hc⟩ := IsSylowOf.exists_mem_conj hctx.sylow hT
  have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hcz : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hzc]
      _ = z := by group
  let R' : Subgroup G := R.map (MulAut.conj c⁻¹).toMonoidHom
  let J' : Subgroup G := J₀.map (MulAut.conj c⁻¹).toMonoidHom
  let eR : ↥R ≃* ↥R' := Subgroup.equivMapOfInjective R (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective
  let eJ : ↥J₀ ≃* ↥J' := Subgroup.equivMapOfInjective J₀ (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective
  have hR'S : R' ≤ S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (l31c_mem_conjMap_iff c R y).mp hy
    exact (hc x).mp (hRT hx)
  have hzR' : z ∈ R' := (l31c_mem_conjMap_iff c R z).mpr ⟨z, hzR, hcz.symm⟩
  have hzZ' : ∀ r ∈ R', r * z = z * r := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := (l31c_mem_conjMap_iff c R r).mp hr
    calc c⁻¹ * x * c * z = c⁻¹ * x * c * (c⁻¹ * z * c) := by rw [hcz]
      _ = c⁻¹ * (x * z) * c := by group
      _ = c⁻¹ * (z * x) * c := by rw [hzZ x hx]
      _ = c⁻¹ * z * c * (c⁻¹ * x * c) := by group
      _ = z * (c⁻¹ * x * c) := by rw [hcz]
  have hrk' : ∃ v ∈ R', v * v = 1 ∧ v ∉ zpowers z := by
    obtain ⟨v, hvR, hv2, hvz⟩ := hrk
    refine ⟨c⁻¹ * v * c, (l31c_mem_conjMap_iff c R _).mpr ⟨v, hvR, rfl⟩, ?_, ?_⟩
    · calc c⁻¹ * v * c * (c⁻¹ * v * c) = c⁻¹ * (v * v) * c := by group
        _ = 1 := by rw [hv2]; group
    · intro hmem
      apply hvz
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcom : c * z ^ m = z ^ m * c :=
        Commute.zpow_right (show Commute c z from hzc) m
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      calc z ^ m = z ^ m * c * c⁻¹ := by group
        _ = c * z ^ m * c⁻¹ := by rw [hcom]
        _ = c * (c⁻¹ * v * c) * c⁻¹ := by rw [hm]
        _ = v := by group
  have hcomm' : ∀ x ∈ J', ∀ r ∈ R', x * r = r * x := by
    intro x hx r hr
    obtain ⟨x₀, hx₀, rfl⟩ := (l31c_mem_conjMap_iff c J₀ x).mp hx
    obtain ⟨r₀, hr₀, rfl⟩ := (l31c_mem_conjMap_iff c R r).mp hr
    calc c⁻¹ * x₀ * c * (c⁻¹ * r₀ * c) = c⁻¹ * (x₀ * r₀) * c := by group
      _ = c⁻¹ * (r₀ * x₀) * c := by rw [hcomm x₀ hx₀ r₀ hr₀]
      _ = c⁻¹ * r₀ * c * (c⁻¹ * x₀ * c) := by group
  have hns' : ¬ Group.IsSolvable ↥J' := by
    intro hsol
    exact hJ₀ (Group.isSolvable_of_isSolvable_injective (f := eJ.toMonoidHom) eJ.injective)
  have hD := l31c_core hctx hk hR'S (hR.of_equiv eR) hzR' hzZ' hrk' hcomm' hns'
  exact Or.inr (l31c_isDihedral_of_equiv eR hD)

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
