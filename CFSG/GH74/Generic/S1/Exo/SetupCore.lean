module

public import CFSG.GH74.Generic.S1.Exo.ExoticAt
public import CFSG.GH74.Generic.S1.Exo.ModelCore
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

@[expose] noncomputable def layerOf (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (e : ↥K ≃* ↥S) : LayerData x S :=
  ⟨K, Subgroup.isPerfect_iff.mp hset.comp.1.1, normal_of_layer_eq hfront.layer_eq,
    fun P hP => hfront.good_le P (Or.inl hP), hExact G x K hset hfront, e⟩

theorem proj_layerOf_ι {y : G} (D : LayerData y S) (k : ↥D.K) :
    proj y (D.ιC (D.iso k)) = (k : CentralizerBar y) := by
  rw [D.proj_ιC]
  simp

theorem exotic_setup_core (mc : ModelCore S) (hExact : S1LiftExactProp)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) {q : ℕ} (hq1 : 1 < q)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1)
    (hvK : barOf hv ∉ K) (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hExo : IsExoticAutAt q α) :
    ∃ (wK : ↥K) (w : G) (hwx : w ∈ centralizer ({x} : Set G)) (h : G) (Dx : LayerData x S)
      (Dv : LayerData v S), w ∈ centralizer ({v} : Set G) ∧ orderOf v = 2 ∧
      wK * wK = 1 ∧ wK ≠ 1 ∧ wK ≠ ⟨xbar x, hset.shape.2⟩ ∧ α wK = wK ∧
      w = (layerOf hExact hset hfront e).ι (e wK) ∧ barOf hwx = (wK : CentralizerBar x) ∧
      h * w * h⁻¹ = w * v ∧ Dx.K = K ∧ Dx.ι mc.z0 = w ∧ Dv.ι mc.z0 = w ∧ Dv.ι mc.neg = v := by
  classical
  have hqodd := hExo.odd
  have hx : orderOf x = 2 := hset.inv
  have hxK : xbar x ∈ K := hset.shape.2
  set z : ↥K := ⟨xbar x, hxK⟩ with hzdef
  have hzc : z ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  have hz1 : z ≠ 1 := fun h => xbar_ne_one hx (congrArg Subtype.val h)
  set D := layerOf hExact hset hfront e with hD
  have hE1 : ExoticFixedGroup α z q := hExo.exoticFixedGroup hzc hz1
  obtain ⟨Ω, hΩfix, hΩs, hΩp, hzΩ, hΩall, wK, hwKΩ, hwK2, hwK1⟩ :=
    hE1.exists_involution_full hqodd hq1
  have hwKz : wK ≠ z := fun h => hzΩ (h ▸ hwKΩ)
  have hℓx : ∀ k : ↥K, D.ι (e k) ∈ centralizer ({x} : Set G) := fun k => D.ι_mem_cent (e k)
  have hℓproj : ∀ k : ↥K, barOf (hℓx k) = (k : CentralizerBar x) := fun k => proj_layerOf_ι D k
  have hℓcomm : ∀ k : ↥K, α k = k → D.ι (e k) * v = v * D.ι (e k) := by
    intro k hk
    refine D.ι_comm_of_fixed hv ?_
    have h1 : (D.iso.symm (e k) : ↥D.K) = k := e.symm_apply_apply k
    rw [h1, ← hα k, hk]
  set w : G := D.ι (e wK) with hw
  have hwx : w ∈ centralizer ({x} : Set G) := hℓx wK
  have hwv' : w * v = v * w := hℓcomm wK (hΩfix wK hwKΩ)
  have hwv : w ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hwv'
  have hw2 : w * w = 1 := by
    rw [hw, ← map_mul, ← map_mul, hwK2, map_one, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply hwK1
    apply e.injective
    apply D.ι_injective
    rw [← hw, h, map_one, map_one]
  have hwbar : barOf hwx = (wK : CentralizerBar x) := hℓproj wK
  have hwbar_ne : barOf hwx ≠ xbar x := by
    rw [hwbar]
    intro h
    exact hwKz (Subtype.ext h)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  subst hc
  have hsetv := hset.conj c
  have hfrontv := hfront.conj c
  set Kv := K.map (barConj x c).toMonoidHom with hKv
  let ev : ↥Kv ≃* ↥S :=
    (K.equivMapOfInjective (barConj x c).toMonoidHom (barConj x c).injective).symm.trans e
  set Dv₀ : LayerData (c * x * c⁻¹) S := layerOf hExact hsetv hfrontv ev with hDv₀
  have hvord : orderOf (c * x * c⁻¹) = 2 := by
    rw [← hx]
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x)
  set Ωhat : Subgroup G := Ω.map (D.ι.comp e.toMonoidHom) with hΩhat
  have hperf : ⁅Ωhat, Ωhat⁆ = Ωhat := by
    rw [hΩhat, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hΩp]
  have hCv : Ωhat ≤ centralizer ({c * x * c⁻¹} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hℓcomm k (hΩfix k hk))
  have hrange := Dv₀.le_range_ι hperf hCv
  have hwΩ : w ∈ Ωhat := ⟨wK, hwKΩ, rfl⟩
  obtain ⟨sv, hsv⟩ := hrange hwΩ
  have hxKv : xbar (c * x * c⁻¹) ∈ Dv₀.K := hsetv.shape.2
  have hvneg : Dv₀.ι mc.neg = c * x * c⁻¹ := ι_neg_eq_core mc Dv₀ hvord hxKv
  have hxneg : D.ι mc.neg = x := ι_neg_eq_core mc D hx hxK
  have hv_ne : w ≠ c * x * c⁻¹ := by
    intro h
    apply hvK
    have h1 : barOf hv = barOf hwx := by
      unfold barOf
      congr 1
      exact Subtype.ext h.symm
    rw [h1, hwbar]
    exact wK.2
  have hsv2 : sv * sv = 1 := Dv₀.ι_injective (by rw [map_mul, hsv, hw2, map_one])
  have hsv1 : sv ≠ 1 := fun h => hw1 (by rw [← hsv, h, map_one])
  have hsvneg : sv ≠ mc.neg := fun h => hv_ne (by rw [← hsv, h]; exact hvneg)
  have hezneg : e z = mc.neg := iso_xbar_eq_neg_core mc D hx hxK
  have hewK1 : e wK ≠ 1 := fun h => hwK1 (e.injective (by rw [h, map_one]))
  have hewKneg : e wK ≠ mc.neg := by
    intro h
    exact hwKz (e.injective (by rw [h, hezneg]))
  obtain ⟨Px, hPx⟩ := mc.norm (e wK) (by rw [← map_mul, hwK2, map_one]) hewK1 hewKneg
  obtain ⟨Pv, hPv⟩ := mc.norm sv hsv2 hsv1 hsvneg
  set Dx : LayerData x S := D.conjIso (MulAut.conj Px) with hDx
  set Dv : LayerData (c * x * c⁻¹) S := Dv₀.conjIso (MulAut.conj Pv) with hDv
  have hwDx : Dx.ι mc.z0 = w := by
    rw [hDx, LayerData.conjIso_ι, MulAut.conj_symm_apply, hw]
    congr 1
    rw [← hPx]
    group
  have hwDv : Dv.ι mc.z0 = w := by
    rw [hDv, LayerData.conjIso_ι, MulAut.conj_symm_apply, ← hsv]
    congr 1
    rw [← hPv]
    group
  have hnegDv : Dv.ι mc.neg = c * x * c⁻¹ := by
    rw [hDv, LayerData.conjIso_ι, MulAut.conj_symm_apply]
    have hc : Pv⁻¹ * mc.neg * Pv = mc.neg := by
      have := Subgroup.mem_center_iff.1 (mc.neg_mem_center) Pv⁻¹
      rw [this]
      group
    rw [hc, hvneg]
  obtain ⟨hS, hhS⟩ := mc.swap
  have hDxK : Dx.K = K := by rw [hDx, LayerData.conjIso_K]; rfl
  have h1 : Dv.ι hS * w * (Dv.ι hS)⁻¹ = (c * x * c⁻¹) * w := by
    have hmap : Dv.ι hS * Dv.ι mc.z0 * (Dv.ι hS)⁻¹ = Dv.ι (hS * mc.z0 * hS⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    calc Dv.ι hS * w * (Dv.ι hS)⁻¹ = Dv.ι hS * Dv.ι mc.z0 * (Dv.ι hS)⁻¹ := by rw [hwDv]
      _ = Dv.ι (hS * mc.z0 * hS⁻¹) := hmap
      _ = Dv.ι (mc.neg * mc.z0) := by rw [hhS]
      _ = (c * x * c⁻¹) * w := by rw [map_mul, hnegDv, hwDv]
  have h2 : Dv.ι hS * w * (Dv.ι hS)⁻¹ = w * (c * x * c⁻¹) := by rw [h1]; exact hwv'.symm
  exact ⟨wK, w, hwx, Dv.ι hS, Dx, Dv, hwv, hvord, hwK2, hwK1, hwKz, hΩfix wK hwKΩ, rfl, hwbar, h2, hDxK,
    hwDx, hwDv, hnegDv⟩

theorem exotic_w_facts (hExact : S1LiftExactProp)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) {wK : ↥K} {w : G} (hwx : w ∈ centralizer ({x} : Set G)) (hwK2 : wK * wK = 1)
    (hwK1 : wK ≠ 1) (hwKz : wK ≠ ⟨xbar x, hset.shape.2⟩)
    (hw : w = (layerOf hExact hset hfront e).ι (e wK)) (hwbar : barOf hwx = (wK : CentralizerBar x)) :
    orderOf w = 2 ∧ (⟨w, hwx⟩ : ↥(centralizer ({x} : Set G))) ∈ liftL x K ∧ barOf hwx ≠ xbar x := by
  set D := layerOf hExact hset hfront e with hD
  have hw2 : w * w = 1 := by
    rw [hw, ← map_mul, ← map_mul, hwK2, map_one, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply hwK1
    apply e.injective
    apply D.ι_injective
    rw [← hw, h, map_one, map_one]
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1, ?_, ?_⟩
  · have h1 : D.ιC (e wK) = ⟨w, hwx⟩ := Subtype.ext hw.symm
    have h2 := D.ιC_mem (e wK)
    rwa [h1] at h2
  · rw [hwbar]
    intro h
    exact hwKz (Subtype.ext h)

end CFSG.GH74.Generic.S1.Exo
