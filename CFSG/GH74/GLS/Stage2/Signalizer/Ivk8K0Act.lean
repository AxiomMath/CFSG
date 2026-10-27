module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

variable {G : Type} [Group G]

noncomputable abbrev thetaZ (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) :
    MulAut ↥J := J.normalizerMonoidHom ⟨z, hz⟩

theorem thetaZ_coe (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) (x : ↥J) :
    ((thetaZ J hz x : ↥J) : G) = z * (x : G) * z⁻¹ := rfl

theorem thetaZ_thetaZ (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) (hz2 : z * z = 1)
    (x : ↥J) : thetaZ J hz (thetaZ J hz x) = x := by
  apply Subtype.ext
  rw [thetaZ_coe, thetaZ_coe]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [hzi]
  calc z * (z * (x : G) * z) * z = (z * z) * (x : G) * (z * z) := by group
    _ = x := by rw [hz2]; group

noncomputable abbrev alphaZ (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) :
    MulAut (↥J ⧸ center ↥J) := YCfg.yAct J ⟨z, hz⟩

theorem alphaZ_mk (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) (x : ↥J) :
    alphaZ J hz (QuotientGroup.mk x) = QuotientGroup.mk (thetaZ J hz x) :=
  YCfg.yAct_apply_mk J ⟨z, hz⟩ x

theorem thetaZ_fixed_iff (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G)) {y : ↥J} :
    thetaZ J hz y = y ↔ (y : G) * z = z * (y : G) := by
  constructor
  · intro h
    have h1 : z * (y : G) * z⁻¹ = y := congrArg Subtype.val h
    calc (y : G) * z = (z * (y : G) * z⁻¹) * z := by rw [h1]
      _ = z * (y : G) := by group
  · intro h
    apply Subtype.ext
    rw [thetaZ_coe, ← h]
    group

theorem lift_fixed_odd [Finite G] (J : Subgroup G) {z : G} (hz : z ∈ normalizer (J : Set G))
    (hz2 : z * z = 1) {c : ↥J ⧸ center ↥J} (hc : alphaZ J hz c = c) (hodd : Odd (orderOf c)) :
    ∃ y : ↥J, (y : G) * z = z * (y : G) ∧ (QuotientGroup.mk y : ↥J ⧸ center ↥J) = c := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨y₁, hy₁, hodd₁⟩ := exists_odd_order_lift (N := center ↥J) y₀ hodd
  have hfix : y₁⁻¹ * thetaZ J hz y₁ ∈ center ↥J := by
    rw [← QuotientGroup.eq, ← alphaZ_mk, hy₁]
    exact hc.symm
  obtain ⟨y, hθy, hy⟩ := exists_fixed_lift_of_odd (thetaZ J hz) (thetaZ_thetaZ J hz hz2) hodd₁ hfix
  refine ⟨y, (thetaZ_fixed_iff J hz).mp hθy, ?_⟩
  rw [← hy₁]
  exact (QuotientGroup.eq.mpr (by simpa using Subgroup.inv_mem _ hy)).symm

theorem lift_fixed_of_card_odd [Finite G] (J : Subgroup G) {z : G}
    (hz : z ∈ normalizer (J : Set G)) (hz2 : z * z = 1) (hZ : Odd (Nat.card (center ↥J)))
    {c : ↥J ⧸ center ↥J} (hc : alphaZ J hz c = c) :
    ∃ y : ↥J, (y : G) * z = z * (y : G) ∧ (QuotientGroup.mk y : ↥J ⧸ center ↥J) = c := by
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective c
  have hfix : y₁⁻¹ * thetaZ J hz y₁ ∈ center ↥J := by
    rw [← QuotientGroup.eq, ← alphaZ_mk]
    exact hc.symm
  obtain ⟨y, hθy, hy⟩ :=
    exists_fixed_lift_of_card_odd (thetaZ J hz) (thetaZ_thetaZ J hz hz2) hZ hfix
  refine ⟨y, (thetaZ_fixed_iff J hz).mp hθy, ?_⟩
  exact (QuotientGroup.eq.mpr (by simpa using Subgroup.inv_mem _ hy)).symm

section Pbar

noncomputable abbrev Pbar (J P : Subgroup G) : Subgroup (MulAut (↥J ⧸ center ↥J)) :=
  (P.subgroupOf (normalizer (J : Set G))).map (YCfg.yAct J)

theorem mem_Pbar {J P : Subgroup G} {e : MulAut (↥J ⧸ center ↥J)} :
    e ∈ Pbar J P ↔ ∃ (x : G) (hx : x ∈ normalizer (J : Set G)), x ∈ P ∧
      YCfg.yAct J ⟨x, hx⟩ = e := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, n.2, hn, rfl⟩
  · rintro ⟨x, hx, hxP, rfl⟩
    exact ⟨⟨x, hx⟩, hxP, rfl⟩

theorem yAct_mem_Pbar {J P : Subgroup G} {x : G} (hx : x ∈ normalizer (J : Set G)) (hxP : x ∈ P) :
    YCfg.yAct J ⟨x, hx⟩ ∈ Pbar J P :=
  mem_Pbar.mpr ⟨x, hx, hxP, rfl⟩

theorem isPGroup_Pbar {J P : Subgroup G} {p : ℕ} (hP : IsPGroup p ↥P) : IsPGroup p ↥(Pbar J P) :=
  (hP.comap_subtype (K := normalizer (J : Set G))).map _

theorem Pbar_ne_bot {J P : Subgroup G} [Group.IsPerfect ↥J] (hPN : P ≤ normalizer (J : Set G))
    (hnc : ¬ P ≤ centralizer (J : Set G)) : Pbar J P ≠ ⊥ := by
  intro h
  obtain ⟨x, hxP, hxc⟩ := Set.not_subset.mp hnc
  have hmem := yAct_mem_Pbar (hPN hxP) hxP
  rw [h, Subgroup.mem_bot] at hmem
  exact hxc ((YCfg.yAct_eq_one_iff J ⟨x, hPN hxP⟩).mp hmem)

theorem comm_Pbar {J P : Subgroup G} {z : G} (hz : z ∈ normalizer (J : Set G))
    (hPz : ∀ x ∈ P, z * x = x * z) {e : MulAut (↥J ⧸ center ↥J)} (he : e ∈ Pbar J P) :
    e * alphaZ J hz = alphaZ J hz * e := by
  obtain ⟨x, hx, hxP, rfl⟩ := mem_Pbar.mp he
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hPz x hxP).symm

theorem conj_mem_Pbar {J P : Subgroup G} {y : ↥J} (hy : (y : G) ∈ normalizer (P : Set G))
    {e : MulAut (↥J ⧸ center ↥J)} (he : e ∈ Pbar J P) :
    MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J) * e *
      (MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J))⁻¹ ∈ Pbar J P := by
  obtain ⟨x, hx, hxP, rfl⟩ := mem_Pbar.mp he
  have hyN : (y : G) ∈ normalizer (J : Set G) := le_normalizer y.2
  have h1 : MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J) = YCfg.yAct J ⟨(y : G), hyN⟩ :=
    (YCfg.yAct_of_mem J y).symm
  rw [h1, ← map_inv, ← map_mul, ← map_mul]
  have hxP' : (y : G) * x * (y : G)⁻¹ ∈ P := (mem_normalizer_iff.mp hy x).mp hxP
  have hmem : (y : G) * x * (y : G)⁻¹ ∈ normalizer (J : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hx) (Subgroup.inv_mem _ hyN)
  exact (yAct_mem_Pbar hmem hxP')

theorem conj_mem_normalizer_Pbar {J P : Subgroup G} {y : ↥J}
    (hy : (y : G) ∈ normalizer (P : Set G)) :
    MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J) ∈
      normalizer ((Pbar J P : Subgroup (MulAut (↥J ⧸ center ↥J))) : Set _) := by
  rw [mem_normalizer_iff]
  intro e
  constructor
  · exact fun he => conj_mem_Pbar hy he
  · intro he
    have hy' : ((y⁻¹ : ↥J) : G) ∈ normalizer (P : Set G) := by
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ hy
    have := conj_mem_Pbar hy' he
    rw [QuotientGroup.mk_inv, map_inv, inv_inv] at this
    simpa [mul_assoc] using this

theorem comm_mem_sup {J : Subgroup G} [Group.IsPerfect ↥J] {x z : G}
    (hx : x ∈ normalizer (J : Set G)) (hz : z ∈ normalizer (J : Set G))
    (hcell : ⁅YCfg.yAct J ⟨x, hx⟩, alphaZ J hz⁆ ∈ innSub (↥J ⧸ center ↥J)) :
    ⁅x, z⁆ ∈ J ⊔ centralizer (J : Set G) := by
  obtain ⟨yb, hyb⟩ := hcell
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hyN : (y : G) ∈ normalizer (J : Set G) := le_normalizer y.2
  set n : ↥(normalizer (J : Set G)) := ⟨x, hx⟩ with hn
  set ζ : ↥(normalizer (J : Set G)) := ⟨z, hz⟩ with hζ
  set η : ↥(normalizer (J : Set G)) := ⟨(y : G), hyN⟩ with hη
  have h1 : MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J) = YCfg.yAct J η :=
    (YCfg.yAct_of_mem J y).symm
  have hcomm : YCfg.yAct J ⁅n, ζ⁆ = ⁅YCfg.yAct J n, alphaZ J hz⁆ :=
    map_commutatorElement (YCfg.yAct J) n ζ
  have h2 : YCfg.yAct J (η⁻¹ * ⁅n, ζ⁆) = 1 := by
    rw [map_mul, map_inv, hcomm, ← hyb, ← h1]
    exact inv_mul_cancel _
  have h4 : ((η⁻¹ * ⁅n, ζ⁆ : ↥(normalizer (J : Set G))) : G) ∈ centralizer (J : Set G) :=
    (YCfg.yAct_eq_one_iff J _).mp h2
  have h4' : (y : G)⁻¹ * ⁅x, z⁆ ∈ centralizer (J : Set G) := h4
  have h5 : ⁅x, z⁆ = (y : G) * ((y : G)⁻¹ * ⁅x, z⁆) := by group
  rw [h5]
  exact Subgroup.mul_mem_sup y.2 h4'

theorem exists_gen_of_cyclic {J P : Subgroup G} [Group.IsPerfect ↥J]
    (hPN : P ≤ normalizer (J : Set G)) (hcyc : IsCyclic ↥(Pbar J P)) :
    ∃ x ∈ P, P ≤ zpowers x ⊔ centralizer (J : Set G) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨x, hxN, hxP, hxg⟩ := mem_Pbar.mp g.2
  refine ⟨x, hxP, fun u hu => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, yAct_mem_Pbar (hPN hu) hu⟩)
  have hm' : (YCfg.yAct J ⟨x, hxN⟩) ^ m = YCfg.yAct J ⟨u, hPN hu⟩ := by
    rw [hxg]; exact congrArg Subtype.val hm
  have h1 : YCfg.yAct J ((⟨x, hxN⟩ : ↥(normalizer (J : Set G))) ^ (-m) * ⟨u, hPN hu⟩) = 1 := by
    rw [map_mul, map_zpow, zpow_neg, hm', inv_mul_cancel]
  have h2 : (x ^ (-m) * u : G) ∈ centralizer (J : Set G) := (YCfg.yAct_eq_one_iff J _).mp h1
  have h3 : u = x ^ m * (x ^ (-m) * u) := by rw [zpow_neg]; group
  rw [h3]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers x m) h2

theorem relIndex_eq_card_Pbar {J P : Subgroup G} [Group.IsPerfect ↥J]
    (hPN : P ≤ normalizer (J : Set G)) :
    (P ⊓ centralizer (J : Set G)).relIndex P = Nat.card ↥(Pbar J P) := by
  have hker : (YCfg.yAct J).ker =
      (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, YCfg.yAct_eq_one_iff]
    rfl
  rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf hPN, ← hker, Subgroup.relIndex_ker]

end Pbar

theorem quasisimple_of_isCompIn {H J : Subgroup G} (h : IsCompIn H J) : IsQuasisimple ↥J :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
