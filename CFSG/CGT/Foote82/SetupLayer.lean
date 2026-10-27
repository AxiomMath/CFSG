module

public import CFSG.CGT.Foote82.Lemma62
import CFSG.ClassicalInvolution.Balance.Layer
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralizingLayerLift

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.ComponentClassification

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private instance instFiniteGLVLayer : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

namespace SetupLayerAux

variable {Γ : Type*} [Group Γ]

private theorem le_normalizer_map_subtype {G : Subgroup Γ} (N : Subgroup ↥G) [N.Normal] :
    G ≤ Subgroup.normalizer ((N.map G.subtype : Subgroup Γ) : Set Γ) := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).mp ?_
  rwa [show (N.map G.subtype).subgroupOf G = N from
    Subgroup.comap_map_eq_self_of_injective G.subtype_injective N]

private theorem centralizer_subgroupOf_eq {G T : Subgroup Γ} (hTG : T ≤ G) :
    Subgroup.centralizer ((T.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (G ⊓ Subgroup.centralizer (T : Set Γ)).subgroupOf G := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, fun t ht => ?_⟩
    have := h ⟨t, hTG ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
    exact congrArg Subtype.val this
  · rintro ⟨-, h⟩ t ht
    apply Subtype.ext
    exact h _ (Subgroup.mem_subgroupOf.mp ht)

private theorem isPGroup_subgroupOf {G T : Subgroup Γ} (hTG : T ≤ G) (hT : IsPGroup 2 ↥T) :
    IsPGroup 2 ↥(T.subgroupOf G) :=
  IsPGroup.of_surjective hT (Subgroup.subgroupOfEquivOfLe hTG).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTG).symm.surjective

end SetupLayerAux

theorem Setup6.le_layerIn {G S L : Subgroup (GLV V)} (h : Setup6 G S L) : L ≤ layerIn G := by
  obtain ⟨hLC, hLsub, hLq⟩ := h.component
  have hLG : L ≤ G := hLC.trans inf_le_left
  let A : Subgroup ↥G := S.subgroupOf G
  let L' : Subgroup ↥G := L.subgroupOf G
  let e : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hA : IsPGroup 2 ↥A := SetupLayerAux.isPGroup_subgroupOf h.S_le h.isPGroup
  have hcent := SetupLayerAux.centralizer_subgroupOf_eq (G := G) h.S_le
  have hLA : L' ≤ Subgroup.centralizer (A : Set ↥G) := by
    rw [hcent]
    exact fun x hx => hLC hx
  have hsub : CFSG.Open.IsSubnormal L' (Subgroup.centralizer (A : Set ↥G)) := by
    have h1 := LBalance.subnormal_subgroupOf hLsub G
    rwa [← hcent] at h1
  have hq' : CFSG.Open.IsQuasisimple ↥L' := Components.quasisimple_of_equiv e hLq
  have hperf : commutator ↥L' = ⊤ := hq'.1
  have hq : CFSG.Open.IsQuasisimple (↥L' ⧸ componentClassificationOddCore ↥L') :=
    Quasisimple.central_quotient hq' _
      (CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hq')
  have h2 : L' ≤ TwoLayer.subgroup ↥G :=
    CFSG.ClassicalInvolution.Balance.le_twoLayer_of_l2PrimeBalance
      CFSG.ClassicalInvolution.l2PrimeBalance hA hLA hsub hperf hq
  have hcomm : ⁅L', componentClassificationOddCore ↥G⁆ = ⊥ := by
    let O : Subgroup ↥G := componentClassificationOddCore ↥G
    have hKodd : Odd (Nat.card ↥(O.map G.subtype)) := by
      rw [Subgroup.card_map_of_injective G.subtype_injective]
      exact OddCore.odd_card ↥G
    have hnorm := SetupLayerAux.le_normalizer_map_subtype (G := G) O
    have hK : ⁅O.map G.subtype, L⁆ = ⊥ :=
      lemma62 h (Subgroup.map_subtype_le O) hKodd (h.S_le.trans hnorm) (hLG.trans hnorm)
    apply (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLG, Subgroup.commutator_comm]
    exact hK
  have : Group.IsPerfect ↥L' := ⟨hperf⟩
  have h3 := PerfectCentralizingLayerLift.twoLayer_enters_layer_of_core_centralization L' hcomm h2
  rw [← CFSG.layer_eq_componentClassification] at h3
  calc L = L'.map G.subtype := (Subgroup.map_subgroupOf_eq_of_le hLG).symm
    _ ≤ layerIn G := Subgroup.map_mono h3

theorem Setup6Irr.eq_layerIn_sup {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    G = layerIn G ⊔ S := by
  have hL : L ≤ layerIn G := h.toSetup6.le_layerIn
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hnc : normalClosure G L ≤ layerIn G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    obtain ⟨l₀, hl₀, rfl⟩ := hL hl
    exact ⟨⟨γ, hγ⟩ * l₀ * ⟨γ, hγ⟩⁻¹, Subgroup.Normal.conj_mem inferInstance l₀ hl₀ ⟨γ, hγ⟩,
      by simp⟩
  exact le_antisymm (h.gen.le.trans (sup_le_sup_right hnc S))
    (sup_le (Subgroup.map_subtype_le _) h.S_le)

end CFSG.CGT.Foote82
