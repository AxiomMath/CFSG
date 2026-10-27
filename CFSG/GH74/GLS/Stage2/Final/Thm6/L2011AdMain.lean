module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdX
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdF0
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdZ
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdCfg
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdCentBar

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

structure JSetup20' {G : Type} [Group G] [Finite G] (z : G) (S : Subgroup G) (g : G) : Prop where
  comp : IsPComponent 2 ((J0 z g).subgroupOf (H0 z g))
  simple : IsSimpleGroup (HBar (J0 z g))
  nonab : ∃ a b : HBar (J0 z g), a * b ≠ b * a
  layer_le : Em (Cen z) ≤ J0 z g
  z_mem : z ∈ J0 z g
  t_mem : zc z g ∈ J0 z g
  cfg : ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G),
    Stage1Pair G z S q L₁ L₂ → CompData z K₁ K₂ L₁ L₂ →
      IVK.Proofs2.Ivk93Cfg (mkH (J0 z g) ⟨z, z_mem⟩) q (barIn (J0 z g) K₁) (barIn (J0 z g) K₂)

structure Facts {G : Type} [Group G] [Finite G] (z : G) (g : G) (K₁ K₂ : Subgroup G) (q : ℕ) : Prop where
  pair : PairG z K₁ K₂ q
  pair' : PairG (zc z g) (conjugate K₁ g) (conjugate K₂ g) q
  zH : z ∈ H0 z g
  tH : zc z g ∈ H0 z g
  K₁H : K₁ ≤ H0 z g
  K₂H : K₂ ≤ H0 z g
  K₁gH : conjugate K₁ g ≤ H0 z g
  K₂gH : conjugate K₂ g ≤ H0 z g
  K₁J : K₁ ≤ J0 z g
  K₂J : K₂ ≤ J0 z g
  K₁gJ : conjugate K₁ g ≤ J0 z g
  K₂gJ : conjugate K₂ g ≤ J0 z g

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Facts.of_data {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hz2 : orderOf z = 2) (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (g : G) :
    Facts z g K₁ K₂ q := by
  have hpair : PairG z K₁ K₂ q := PairG.of_data hz2 hP hK
  have hpair' : PairG (zc z g) (conjugate K₁ g) (conjugate K₂ g) q := hpair.conj g
  have hzH : z ∈ H0 z g := mem_H0_of_comm (fun f hf => F0_comm_z hf)
  have htH : zc z g ∈ H0 z g := mem_H0_of_comm (fun f hf => F0_comm_t hf)
  have hK₁le : K₁ ≤ Em (Cen z) := hK.layer ▸ le_sup_left
  have hK₂le : K₂ ≤ Em (Cen z) := hK.layer ▸ le_sup_right
  have hK₁H : K₁ ≤ H0 z g := fun a ha =>
    mem_H0_of_comm (fun f hf => F0_comm_layer hK (hK₁le ha) hf)
  have hK₂H : K₂ ≤ H0 z g := fun a ha =>
    mem_H0_of_comm (fun f hf => F0_comm_layer hK (hK₂le ha) hf)
  have hK₁gH : conjugate K₁ g ≤ H0 z g := fun a ha =>
    mem_H0_of_comm (fun f hf => F0_comm_conj_layer hK (hK₁le (mem_conjugate_iff'.mp ha)) hf)
  have hK₂gH : conjugate K₂ g ≤ H0 z g := fun a ha =>
    mem_H0_of_comm (fun f hf => F0_comm_conj_layer hK (hK₂le (mem_conjugate_iff'.mp ha)) hf)
  exact ⟨hpair, hpair', hzH, htH, hK₁H, hK₂H, hK₁gH, hK₂gH,
    hpair.le_pLayerOf₁ hzH hK₁H, hpair.le_pLayerOf₂ hzH hK₂H,
    hpair'.le_pLayerOf₁ htH hK₁gH, hpair'.le_pLayerOf₂ htH hK₂gH⟩

omit [Finite G] in
theorem barIn_sup {H K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ H) (h₂ : K₂ ≤ H) :
    barIn H (K₁ ⊔ K₂) = barIn H K₁ ⊔ barIn H K₂ := by
  unfold barIn
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem exists_odd_of_centralizes {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hz2 : orderOf z = 2) (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂)
    {H : Subgroup G} (hzH : z ∈ H) (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H) :
    ∀ u : HBar H, u * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * u →
      (∀ k ∈ barIn H K₁ ⊔ barIn H K₂, u * k = k * u) →
      ∃ v : HBar H, Odd (orderOf v) ∧ v * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * v ∧
        (u = v ∨ u = mkH H ⟨z, hzH⟩ * v) := by
  intro u hux huK
  have hu : u ∈ centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hux
  rw [centralizer_mk_eq H hz2 hzH] at hu
  obtain ⟨c', hc', rfl⟩ := hu
  have hcC : (c' : G) ∈ Cen z := Subgroup.mem_subgroupOf.mp hc'
  have hcH : (c' : G) ∈ H := c'.2
  have hcomm : ∀ k ∈ K₁ ⊔ K₂, ⁅(c' : G), k⁆ ∈ pPrimeCoreOf 2 H := by
    intro k hk
    have hkH : k ∈ H := (sup_le hK₁H hK₂H) hk
    have hkb : mkH H ⟨k, hkH⟩ ∈ barIn H K₁ ⊔ barIn H K₂ := by
      rw [← barIn_sup hK₁H hK₂H]
      exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h1 := huK _ hkb
    refine ⟨⁅c', ⟨k, hkH⟩⁆, (mkH_eq_one_iff H).mp ?_, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1
  obtain ⟨a, ha, hca⟩ := cent_bar_pair hz2 hP hK hK₁H hK₂H hcC hcH hcomm
  have haH : a ∈ H := by
    rcases hca with h | h
    · exact h ▸ hcH
    · have : a = z⁻¹ * (c' : G) := by rw [h]; group
      rw [this]
      exact H.mul_mem (H.inv_mem hzH) hcH
  have haodd : Odd (orderOf a) := by
    obtain ⟨a', ha', rfl⟩ := ha
    have := P34.odd_orderOf_of_mem_pPrimeCore (X := ↥(Cen z)) ha'
    show Odd (orderOf (a' : G))
    rwa [Subgroup.orderOf_coe]
  refine ⟨mkH H ⟨a, haH⟩, ?_, ?_, ?_⟩
  · have h1 : orderOf (mkH H ⟨a, haH⟩) ∣ orderOf (⟨a, haH⟩ : ↥H) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat haodd h1
  · have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (oddCore_le_Cen z ha)
    rw [← map_mul, ← map_mul]
    exact congrArg (mkH H) (Subtype.ext haz)
  · rcases hca with h | h
    · left
      congr 1
      exact Subtype.ext h
    · right
      rw [← map_mul]
      congr 1
      exact Subtype.ext h

theorem jSetup20'_of_ctx (hC : Ctx2011 G z k S) {g : G} (hg : Case20A z S g) : JSetup20' z S g := by
  obtain ⟨q, L₁, L₂, K₁, K₂, hP, hK⟩ := exists_data hC
  have hz2 := orderOf_z_of_ctx hC
  have hF := Facts.of_data hz2 hP hK g
  have hzH := hF.zH
  have htH := hF.tH
  have hz_mem : z ∈ J0 z g := hF.K₁J hF.pair.mem₁
  have ht_mem : zc z g ∈ J0 z g := hF.K₁gJ hF.pair'.mem₁
  have hlayer : Em (Cen z) ≤ J0 z g := hK.layer ▸ sup_le hF.K₁J hF.K₂J
  have hX₁ := hF.pair.toPairX hzH hF.K₁H hF.K₂H
  have hX₂ := hF.pair'.toPairX htH hF.K₁gH hF.K₂gH
  have ht2 : orderOf (zc z g) = 2 := hF.pair'.ord
  have hzt : z * zc z g = zc z g * z := by
    have htC : zc z g ∈ Cen z := hC.1.ctx.ctx17.ctx.sylow.le hg.t_mem
    exact (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
  have hne : z ≠ zc z g := fun h => hg.t_ne (h ▸ Subgroup.mem_zpowers z)
  have hneq : mkH (H0 z g) ⟨z, hzH⟩ ≠ mkH (H0 z g) ⟨zc z g, htH⟩ :=
    mkH_ne_of_comm hzH htH hz2 ht2 hzt hne
  have hE : ∀ K : Subgroup G, K ≤ J0 z g → barIn (H0 z g) K ≤ layer (HBar (H0 z g)) := by
    intro K hKJ
    rw [← barIn_pLayerOf]
    exact barIn_mono' hKJ
  obtain ⟨Q, hQ, hQsup, hone⟩ := layer_unique_component hX₁ hX₂ hneq (hE _ hF.K₁J)
    (hE _ hF.K₂J) (hE _ hF.K₁gJ) (hE _ hF.K₂gJ)
  have hO : pPrimeCore 2 (HBar (H0 z g)) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hlayerQ : layer (HBar (H0 z g)) = Q := layer_eq_of_unique hQ hone
  have hZ : ∀ u ∈ Q, (∀ q ∈ Q, u * q = q * u) → u = 1 :=
    center_layer_trivial hO hX₁ hQ hone (le_sup_left.trans hQsup) (le_sup_right.trans hQsup)
      (exists_odd_of_centralizes hz2 hP hK hzH hF.K₁H hF.K₂H)
  have hsimpleQ : IsSimpleGroup ↥Q := isSimpleGroup_of_isComponent_center_trivial hQ hZ
  have hbarJ : barIn (H0 z g) (J0 z g) = Q := by
    rw [← hlayerQ]
    exact barIn_pLayerOf _
  obtain ⟨e⟩ := exists_equiv_HBar_barIn (J0_le_H0 z g) (fun h hh j hj => J0_conj_mem z g hh hj)
  have hsb : IsSimpleGroup ↥(barIn (H0 z g) (J0 z g)) := by
    rw [hbarJ]
    exact hsimpleQ
  have hsimple : IsSimpleGroup (HBar (J0 z g)) := by
    have := hsb
    exact MulEquiv.isSimpleGroup e
  have hnonab : ∃ a b : HBar (J0 z g), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply not_comm_of_isComponent hQ
    intro a ha b hb
    have ha' : a ∈ barIn (H0 z g) (J0 z g) := hbarJ ▸ ha
    have hb' : b ∈ barIn (H0 z g) (J0 z g) := hbarJ ▸ hb
    have h1 := hcon (e.symm ⟨a, ha'⟩) (e.symm ⟨b, hb'⟩)
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact congrArg Subtype.val h2
  have hcomp : IsPComponent 2 ((J0 z g).subgroupOf (H0 z g)) := by
    have h := isPComponent_pLayer_of_layer_single (Y := ↥(H0 z g)) hQ hone
    have h1 : (J0 z g).subgroupOf (H0 z g) = CFSG.pLayer ↥(H0 z g) 2 := by
      have h2 : J0 z g = (CFSG.pLayer ↥(H0 z g) 2).map (H0 z g).subtype := by
        unfold J0
        rw [TwoThin.pLayerOf_two_eq_map,
          CFSG.ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer]
      rw [h2]
      exact Subgroup.comap_map_eq_self_of_injective (H0 z g).subtype_injective _
    rw [h1]
    exact h
  refine ⟨hcomp, hsimple, hnonab, hlayer, hz_mem, ht_mem, ?_⟩
  intro q' L₁' L₂' K₁' K₂' hP' hK'
  have hF' := Facts.of_data hz2 hP' hK' g
  exact cfg_of_components hz_mem hz2 hF'.pair.odd hF'.pair.five hF'.K₁J hF'.K₂J
    hF'.pair.le₁ hF'.pair.le₂ hF'.pair.quasi₁ hF'.pair.quasi₂ hF'.pair.sub₁ hF'.pair.sub₂
    hF'.pair.mem₁ hF'.pair.mem₂ hF'.pair.comm hF'.pair.sl₁ hF'.pair.sl₂

@[expose] def Central20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → ∀ h : JSetup20' z S g, IsCentralInvolution (mkH (J0 z g) ⟨z, h.z_mem⟩)

theorem adapter20_9_of_central (hc : Central20) : Adapter20_9 := by
  intro G _ _ z k S hC g hg
  have h := jSetup20'_of_ctx hC hg
  exact ⟨h.comp, h.simple, h.nonab, h.layer_le, h.z_mem, h.t_mem, hc G z k S hC g hg h, h.cfg⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
