module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenDelta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fixSp_piOrth_mul {t : OGroup Q} (htt : t * t = 1) : fixSp (piOrth Q * t) = commSp t := by
  ext v
  rw [mem_fixSp_iff, mem_commSp_iff htt]
  change ((piOrth Q : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) v = v ↔
    (t : V ≃ₗ[ZMod 3] V) v = -v
  rw [LinearEquiv.mul_apply, coe_piOrth_apply, neg_eq_iff_eq_neg]

@[expose] noncomputable def layersInO (hQ : Q.Nondegenerate) (zb : omegaProj hQ) :
    Subgroup (OGroup Q) :=
  ((genLayers zb).comap (omegaToProj hQ)).map (omegaGroup hQ).subtype

theorem mem_layersInO_iff (hQ : Q.Nondegenerate) (zb : omegaProj hQ) {g : omegaGroup hQ} :
    (g : OGroup Q) ∈ layersInO hQ zb ↔ omegaToProj hQ g ∈ genLayers zb := by
  constructor
  · rintro ⟨g', hg', hg'g⟩
    have h : g' = g := Subtype.ext hg'g
    rw [← h]
    exact hg'
  · intro h
    exact ⟨g, h, rfl⟩

@[expose] def ReflOk (Q : QuadraticForm (ZMod 3) V) (H' : Subgroup (OGroup Q)) (u v : V) : Prop :=
  Q u ≠ 0 ∧ Q u = Q v ∧ ∀ (hu : Q u ≠ 0) (hv : Q v ≠ 0), reflOf Q u hu * reflOf Q v hv ∈ H'

theorem ReflOk.symm {H' : Subgroup (OGroup Q)} {u v : V} (h : ReflOk Q H' u v) :
    ReflOk Q H' v u := by
  obtain ⟨hu, huv, hmem⟩ := h
  have hv : Q v ≠ 0 := huv ▸ hu
  refine ⟨hv, huv.symm, fun hv' hu' => ?_⟩
  have h1 := H'.inv_mem (hmem hu hv)
  rwa [mul_inv_rev, reflOf_inv, reflOf_inv] at h1

theorem ReflOk.trans {H' : Subgroup (OGroup Q)} {u v w : V} (h1 : ReflOk Q H' u v)
    (h2 : ReflOk Q H' v w) : ReflOk Q H' u w := by
  obtain ⟨hu, huv, hm1⟩ := h1
  obtain ⟨hv, hvw, hm2⟩ := h2
  refine ⟨hu, huv.trans hvw, fun hu' hw' => ?_⟩
  have h3 := mul_mem (hm1 hu hv) (hm2 hv hw')
  rwa [mul_assoc, ← mul_assoc (reflOf Q v hv), reflOf_mul_self, one_mul] at h3

theorem reflOk_of_layer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {zb : omegaProj hQ} {d : omegaGroup hQ}
    (hdd : (d : OGroup Q) * d = 1) (htd : invType (d : OGroup Q) = (2, -1))
    (hcore : omegaToProj hQ d ∈ genPocketCore zb) {u v : V} (hu : u ∈ fixSp (d : OGroup Q))
    (hv : v ∈ fixSp (d : OGroup Q)) (hQu : Q u ≠ 0) (huv : Q u = Q v) :
    ReflOk Q (layersInO hQ zb) u v := by
  refine ⟨hQu, huv, fun hu' hv' => ?_⟩
  have hmem : reflOf Q u hu' * reflOf Q v hv' ∈ omegaGroup hQ :=
    reflOf_mul_reflOf_mem_omegaGroup hQ u v hu' hv' huv
  exact (mem_layersInO_iff hQ zb (g := ⟨_, hmem⟩)).mpr
    (layer_reflPair_mem hQ hdim hσ hdd htd hcore u v hu' hv' hu hv huv ⟨_, hmem⟩ rfl)

theorem genP_omegaProj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {y : omegaGroup hQ} (hyy : (y : OGroup Q) * y = 1)
    (hty : invType (y : OGroup Q) = (4, 1)) : GenP (omegaToProj hQ y) := by
  have hπΩ : piOrth Q ∈ omegaGroup hQ := by
    refine (piOrth_mem_omegaGroup_iff hQ).mpr ⟨?_, ?_⟩
    · rw [hdim]
      decide
    · rw [hdim, hσ]
      decide
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : omegaGroup hQ, (y₂ : OGroup Q) = piOrth Q * (y : OGroup Q) :=
    ⟨⟨_, mul_mem hπΩ y.2⟩, rfl⟩
  have hyy₂ : (y₂ : OGroup Q) * y₂ = 1 := by
    rw [hy₂]
    exact piOrth_mul_mul_self hyy
  have hty₂ : invType (y₂ : OGroup Q) = (4, 1) := by
    have hd : invDim (y : OGroup Q) = 4 := by
      simpa only [invType, invDim] using congrArg Prod.fst hty
    have hs : invSign (y : OGroup Q) = 1 := by
      simpa only [invType, invSign] using congrArg Prod.snd hty
    rw [hy₂, invType_piOrth_mul hQ hyy, hdim, hσ, hd, hs]
    decide
  have hωy₂ : omegaToProj hQ y₂ = omegaToProj hQ y := by
    apply Subtype.ext
    change toProj Q (y₂ : OGroup Q) = toProj Q (y : OGroup Q)
    rw [hy₂, map_mul, toProj_piOrth, one_mul]
  have hcomm : commSp (y₂ : OGroup Q) = fixSp (y : OGroup Q) := by
    rw [hy₂]
    exact commSp_piOrth_mul hyy
  have hfixsp : fixSp (y₂ : OGroup Q) = commSp (y : OGroup Q) := by
    rw [hy₂]
    exact fixSp_piOrth_mul hyy
  obtain ⟨D₁, hD₁, hfix₁, hrep₁⟩ := exists_delta_data hQ hdim hyy hty
  obtain ⟨D₂, hD₂, hfix₂, hrep₂⟩ := exists_delta_data hQ hdim hyy₂ hty₂
  rw [hωy₂] at hD₂
  have layer₁ : ∀ d ∈ D₁, ∀ u v : V, u ∈ fixSp (d : OGroup Q) → v ∈ fixSp (d : OGroup Q) →
      Q u ≠ 0 → Q u = Q v → ReflOk Q (layersInO hQ (omegaToProj hQ y)) u v := by
    intro d hd u v hu hv hQu huv
    obtain ⟨hdd, htd, hcore, -⟩ := hD₁ d hd
    exact reflOk_of_layer hQ hdim hσ hdd htd hcore hu hv hQu huv
  have layer₂ : ∀ d ∈ D₂, ∀ u v : V, u ∈ fixSp (d : OGroup Q) → v ∈ fixSp (d : OGroup Q) →
      Q u ≠ 0 → Q u = Q v → ReflOk Q (layersInO hQ (omegaToProj hQ y)) u v := by
    intro d hd u v hu hv hQu huv
    obtain ⟨hdd, htd, hcore, -⟩ := hD₂ d hd
    exact reflOk_of_layer hQ hdim hσ hdd htd hcore hu hv hQu huv
  have key : ∀ c : ZMod 3, c ≠ 0 → ∀ u₀ ∈ fixSp (y : OGroup Q), Q u₀ = c → ∀ u : V, Q u = c →
      ReflOk Q (layersInO hQ (omegaToProj hQ y)) u u₀ := by
    intro c hc u₀ hu₀F hQu₀
    have case1 : ∀ (w a : V), w ∈ fixSp (y : OGroup Q) → a ∈ commSp (y : OGroup Q) →
        Q a ≠ 0 → Q (w + a) = c →
        ReflOk Q (layersInO hQ (omegaToProj hQ y)) (w + a) u₀ := by
      intro w a hw ha hQa hQwa
      obtain ⟨d, hdD, hda⟩ := hfix₁ a ha hQa
      obtain ⟨-, -, -, hdF⟩ := hD₁ d hdD
      refine layer₁ d hdD (w + a) u₀ ?_ ?_ (by rw [hQwa]; exact hc) (by rw [hQwa, hQu₀])
      · rw [mem_fixSp_iff, map_add, hdF w hw, hda]
      · rw [mem_fixSp_iff]
        exact hdF u₀ hu₀F
    intro u hQu
    obtain ⟨w, a, rfl⟩ := exists_fixSp_add_commSp hyy u
    by_cases hQa : Q (a : V) = 0
    · have hQw : Q (w : V) = c := by
        rw [← hQu, map_add_of_fixSp_commSp hyy w.2 a.2, hQa, add_zero]
      have hwc : (w : V) ∈ commSp (y₂ : OGroup Q) := by
        rw [hcomm]
        exact w.2
      obtain ⟨d₂, hd₂D, hd₂w⟩ := hfix₂ (w : V) hwc (by rw [hQw]; exact hc)
      obtain ⟨-, -, -, hdU₂⟩ := hD₂ d₂ hd₂D
      obtain ⟨a'', ha'', hQa''⟩ := hrep₁ c
      have hfixU₂ : ∀ x ∈ commSp (y : OGroup Q),
          ((d₂ : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x := fun x hx => hdU₂ x (by rw [hfixsp]; exact hx)
      have h1 : ReflOk Q (layersInO hQ (omegaToProj hQ y)) ((w : V) + (a : V)) a'' :=
        layer₂ d₂ hd₂D _ _ (by rw [mem_fixSp_iff, map_add, hd₂w, hfixU₂ a a.2])
          (by rw [mem_fixSp_iff]; exact hfixU₂ a'' ha'') (by rw [hQu]; exact hc)
          (by rw [hQu, hQa''])
      have h2 : ReflOk Q (layersInO hQ (omegaToProj hQ y)) a'' u₀ := by
        have h3 := case1 0 a'' (zero_mem _) ha'' (by rw [hQa'']; exact hc)
          (by rw [zero_add, hQa''])
        rwa [zero_add] at h3
      exact h1.trans h2
    · exact case1 w a w.2 a.2 hQa hQu
  have hall : ∀ (u v : V) (hu : Q u ≠ 0) (hv : Q v ≠ 0), Q u = Q v →
      reflOf Q u hu * reflOf Q v hv ∈ layersInO hQ (omegaToProj hQ y) := by
    intro u v hu hv huv
    obtain ⟨u₀, hu₀, hQu₀⟩ := hrep₂ (Q u)
    have hu₀F : u₀ ∈ fixSp (y : OGroup Q) := by
      rw [← hcomm]
      exact hu₀
    have h1 := key (Q u) hu u₀ hu₀F hQu₀ u rfl
    have h2 := key (Q u) hu u₀ hu₀F hQu₀ v huv.symm
    exact (h1.trans h2.symm).2.2 hu hv
  have hΩ : omegaGroup hQ ≤ layersInO hQ (omegaToProj hQ y) :=
    omegaGroup_le_of_reflection_pairs hQ (by omega) _ hall
  unfold GenP
  intro p _
  obtain ⟨g, rfl⟩ := omegaToProj_surjective hQ p
  exact (mem_layersInO_iff hQ _).mp (hΩ g.2)

end CFSG.OddStandard.SmallF3.Omega
