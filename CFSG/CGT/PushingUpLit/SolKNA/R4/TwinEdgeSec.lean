module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocle
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThm4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem F2ConfigR.exists_sectionDatum (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W) (htw : ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W)) :
    ∃ S : Sylow 2 ↥(K.subgroupOf W),
      TightDatum (K.subgroupOf W) S ⟨z, hKW hz.mem⟩ ∧
        TightClsR r ↥W (K.subgroupOf W) S ⟨z, hKW hz.mem⟩ ∧
        tightCore (K.subgroupOf W) = K.subgroupOf W := by
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L
  have hm := hc.min
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hm.hyp.odd W hWs
  have hΔW : TwinT4Hyp r ↥W (restrictFamily Δ W) := hm.hyp.restrict W hO
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩ with ht
  have hRΔ : R ∈ restrictFamily Δ W := subgroupOf_mem_restrictFamily hK hKW
  have hut : IsUniqueInvolution R t := isUniqueInvolution_subgroupOf hz hKW
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  have hd : Q8TwinDatum R S t := hΔW.q8Datum hRΔ hut S
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    obtain ⟨e⟩ := hΔW.quat R hRΔ _ (isSylow2In_map_sylow R S)
    exact ⟨((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).trans e⟩
  have htc : tightCore R = R := hΔW.tightCore_eq hRΔ
  have hconj : ∀ g : ↥W, (conjSub g R).map W.subtype = conjSub (g : G) K := by
    intro g
    have hle : conjSub (g : G) K ≤ W := by
      have := conjSub_mono (n := (g : G)) hKW
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [hR, conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenW : (⨆ g : ↥W, conjSub g R) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hWg
  have hgenR : TightSelfGen R := by
    show (⨆ g : ↥W, conjSub g (tightCore R)) = ⊤
    rw [htc]; exact hgenW
  have hzK : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
  have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
      {tightCore R} := by
    ext K'
    constructor
    · intro hK'
      by_contra hne
      exact htw ⟨K', hK', hne⟩
    · intro hK'
      rw [Set.mem_singleton_iff] at hK'
      subst hK'
      exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
  have hnormal := (twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
    (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
  rw [htc] at hnormal
  exact ⟨S, hd.toTightDatum hnormal, ⟨hq, hgenR, hO⟩, htc⟩

theorem F2ConfigR.exists_embSec (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {W : Subgroup G}
    (hKW : K ≤ W) (hWs : IsSubnormal W ⊤) (hWg : (⨆ x : W, conjSub (x : G) K) = W)
    (htw : ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W)) (hedge : TightEdgeless (K.subgroupOf W)) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (ι : Y →* G ⧸ Subgroup.center G) (R : Subgroup Y)
      (S : Sylow 2 R) (t : Y), Function.Injective ι ∧ socleOf L₀ ≤ ι.range ∧
        TightDatum R S t ∧ TightClsR r Y R S t ∧ tightCore R = R ∧ ι t ∈ socleOf L₀ ∧
        ¬ TightInO2 t ∧ R.map ι = K.map (QuotientGroup.mk' (Subgroup.center G)) ∧
        Nat.card Y ≤ Nat.card G := by
  have hm := hc.min
  obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
  have hzW : z ∈ W := hKW hz.mem
  have hzL : z ∈ L₀ := hc.invMem K hK z hz
  have hnoO2 : ¬ TightInO2 z := hc.noInvO2 K hK z hz
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← hc.pCoreEq]
    exact pCore_isPGroup
  have hzZ : z ∉ Subgroup.center G := fun h => hnoO2 ⟨Subgroup.center G, inferInstance, hZ2, h⟩
  have hzc : (⟨z, hzL⟩ : ↥L₀) ∉ Subgroup.center ↥L₀ := fun h => hzZ (by
    rw [← hc.centralizerEq]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨g, hg⟩))
  have hLW : L₀ ≤ W := le_of_mem_isSubnormal hc.isComp.1 hWs hzL hzW hzc
  obtain ⟨S, hdt, hcl, htc⟩ := hc.exists_sectionDatum hr hK hz hKW hWs hWg htw
  set N : Subgroup ↥W := (Subgroup.center G).subgroupOf W with hN
  have hNc : N ≤ Subgroup.center ↥W := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx y.1)
  have hNn : N.Normal := inferInstance
  have hN2 : IsPGroup 2 ↥N := hZ2.comap_subtype
  have htN : (⟨z, hzW⟩ : ↥W) ∉ N := hzZ
  have hnt : ∀ y : ↥W, ∀ n ∈ N, y * (⟨z, hzW⟩ : ↥W) * y⁻¹ = (⟨z, hzW⟩ : ↥W) * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact hdt.not_edgeless_of_twin (hNc hn) h1 hy hedge
  have hRN := TwistQ.inf_eq_bot hdt hN2 htN
  have hd' := TwistQ.datum hdt hN2 htN hnt
  have hc' := twistQ_clsR hdt hNc hN2 htN hcl
  let φ : ↥W →* G ⧸ Subgroup.center G := (QuotientGroup.mk' (Subgroup.center G)).comp W.subtype
  have hker : N ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr hx
  let ι : ↥W ⧸ N →* G ⧸ Subgroup.center G := QuotientGroup.lift N φ hker
  have hιmk : ∀ x : ↥W, ι (QuotientGroup.mk' N x) = QuotientGroup.mk' (Subgroup.center G) (x : G) :=
    fun x => rfl
  refine ⟨↥W ⧸ N, inferInstance, inferInstance, ι, (K.subgroupOf W).map (QuotientGroup.mk' N),
    TwistQ.sylowMap N S, QuotientGroup.mk' N ⟨z, hzW⟩, ?_, ?_, hd', hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    rw [hιmk, hιmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    exact hab
  · rintro _ ⟨l, hl, rfl⟩
    exact ⟨QuotientGroup.mk' N ⟨l, hLW hl⟩, rfl⟩
  · have := TwistQ.tightCore_map (N := N) hRN
    rw [htc] at this
    exact this.symm
  · rw [hιmk]
    exact Subgroup.mem_map_of_mem _ hzL
  · intro h
    exact hnoO2 (F2.tightInO2_of_subnormal hWs hzW (TwistQ.inO2_of hN2 h))
  · rw [Subgroup.map_map]
    have : ι.comp (QuotientGroup.mk' N) = φ := rfl
    rw [this, show (K.subgroupOf W).map φ = ((K.subgroupOf W).map W.subtype).map
      (QuotientGroup.mk' (Subgroup.center G)) by rw [Subgroup.map_map],
      Subgroup.map_subgroupOf_eq_of_le hKW]
  · exact (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N)).trans
      (Subgroup.card_le_card_group W)

end CFSG.CGT.PushingUpLit.SolKNA.R4
