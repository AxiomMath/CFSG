module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big15
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big18
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS6

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.innerPart_inf_actTrivSubgroup_eq (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hr : 4 ≤ r) :
    innerPart (linkLayer R t) (edgeCent (P : Subgroup Y) t u ⊓
        actTrivSubgroup (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) =
      innerPart (linkLayer R t) (edgeCent (P : Subgroup Y) t u) ∧
    IsSylow2In (innerPart (linkLayer R t) (edgeCent (P : Subgroup Y) t u)) ⊤ := by
  have hArith := z2BigModelArith_holds r
  have hCent := z2BigModelCent_holds r
  obtain ⟨S₂, hT₀S₂, hS₂Λ, hS₂2, hS₂syl, hS₂T, hS₂u, hS₂t⟩ := hs.exists_S2 hr hArith
  obtain ⟨R₁, hR₁, hR₁u, htR₁, hR₁Λ, hcomm⟩ := hs.exists_Rprime hS₂Λ hS₂2 hS₂u
  have hsplit := hs.actsTriv_or_actsTriv_mul_t hr hArith hCent hS₂u hS₂T hR₁ htR₁ hR₁Λ hcomm
  obtain ⟨k, hk, hkB⟩ := hs.exists_conj_sup_le hS₂2 hS₂t
  have hkN : k ∈ Subgroup.normalizer (linkLayer R t : Set Y) :=
    hs.mem_normalizer_linkLayer hk.1.1
  have hinj := hs.conj_injective_quot hr hArith
  have hA2 : IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) := edgeCent_isPGroup P t u
  have hSH₀ : ((S₂.subgroupOf (linkLayer R t)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayer R t)))) ≤
      innerPart (linkLayer R t)
        ((S₂ ⊔ Subgroup.zpowers t) ⊓ (Subgroup.centralizer ({t} : Set Y) ⊓
          Subgroup.centralizer ({u} : Set Y) ⊓
            actTrivSubgroup (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u))) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hqS₂ : (q : Y) ∈ S₂ := hq
    have hqC : (q : Y) ∈ Subgroup.centralizer ({t} : Set Y) := hS₂t hqS₂
    have hqU : (q : Y) ∈ Subgroup.centralizer ({u} : Set Y) := hS₂u hqS₂
    have hqΛ : (q : Y) ∈ linkLayer R t := q.2
    rcases hsplit (q : Y) hqS₂ with htr | htr
    · refine mem_innerPart_of_actsLike
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hqS₂, ?_⟩)
        (hs.mem_normalizer_linkLayer hqC) hqΛ (actsLike_refl (linkLayer R t) (q : Y))
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hqC, hqU⟩,
        mem_actTrivSubgroup.mpr ⟨hs.mem_normalizer_linkLayerAt hqU, htr⟩⟩
    · have htC : t ∈ Subgroup.centralizer ({t} : Set Y) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have htU : t ∈ Subgroup.centralizer ({u} : Set Y) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm
      have hqtC : (q : Y) * t ∈ Subgroup.centralizer ({t} : Set Y) :=
        Subgroup.mul_mem _ hqC htC
      have hqtU : (q : Y) * t ∈ Subgroup.centralizer ({u} : Set Y) :=
        Subgroup.mul_mem _ hqU htU
      refine mem_innerPart_of_actsLike
        (Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hqS₂)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)), ?_⟩)
        (hs.mem_normalizer_linkLayer hqtC) hqΛ ?_
      · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hqtC, hqtU⟩,
          mem_actTrivSubgroup.mpr ⟨hs.mem_normalizer_linkLayerAt hqtU, htr⟩⟩
      · intro z hz
        have hzt : t * z = z * t :=
          (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
        have hconj : ((q : Y) * t) * z * ((q : Y) * t)⁻¹ =
            (q : Y) * z * (q : Y)⁻¹ := by
          calc ((q : Y) * t) * z * ((q : Y) * t)⁻¹
              = (q : Y) * (t * z * t⁻¹) * (q : Y)⁻¹ := by group
            _ = (q : Y) * z * (q : Y)⁻¹ := by
                rw [show t * z * t⁻¹ = z by rw [hzt]; group]
        have hone : ((q : Y) * t) * z * ((q : Y) * t)⁻¹ *
            ((q : Y) * z * (q : Y)⁻¹)⁻¹ = 1 := by
          rw [hconj, mul_inv_cancel]
        rw [hone]
        exact Subgroup.one_mem _
  exact innerPart_eq_and_isSylow hinj hA2 inf_le_left hkN hkB hS₂syl hSH₀

theorem Z2SetR.exists_sylow_conj_le_actAut_image (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hr : 4 ≤ r) :
    ∃ S₁ : Subgroup (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)),
      IsSylow2In S₁ ⊤ ∧
        S₁.map (MulAut.conj : (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) →*
            MulAut (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t))) ≤
          ((edgeCent (P : Subgroup Y) t u).subgroupOf
            (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))).map
              (actAut (linkLayer R t)) := by
  refine ⟨innerPart (linkLayer R t) (edgeCent (P : Subgroup Y) t u),
    (hs.innerPart_inf_actTrivSubgroup_eq hr).2, ?_⟩
  rw [innerPart]
  exact Subgroup.map_comap_le (MulAut.conj) _

private theorem s8_isSylow2In_map_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {P : Subgroup G} (h : IsSylow2In P ⊤) : IsSylow2In (P.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.2.1.map e.toMonoidHom, ?_⟩
  intro V _ hV2 hPV
  have h1 : IsPGroup 2 (V.map e.symm.toMonoidHom) :=
    hV2.of_surjective (e.symm.toMonoidHom.subgroupMap V) (MonoidHom.subgroupMap_surjective _ _)
  have h2 : P ≤ V.map e.symm.toMonoidHom := by
    intro x hx
    exact ⟨e x, hPV ⟨x, hx, rfl⟩, by simp⟩
  have h3 := h.2.2 _ le_top h1 h2
  ext y
  constructor
  · intro hy
    have : e.symm y ∈ V.map e.symm.toMonoidHom := ⟨y, hy, rfl⟩
    rw [h3] at this
    exact ⟨e.symm y, this, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ V.map e.symm.toMonoidHom := by rw [h3]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    have : e x = y := by rw [← hyx]; simp
    simpa [this] using hy

theorem Z2SetR.exists_sylow_conj_le_actAut_image_linkGrp (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hr : 4 ≤ r) :
    ∃ S₁ : Subgroup ↥(linkGrp R t), IsSylow2In S₁ ⊤ ∧
      S₁.map (MulAut.conj : ↥(linkGrp R t) →* MulAut ↥(linkGrp R t)) ≤
        (((edgeCent (P : Subgroup Y) t u).subgroupOf
          (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))).map
            (actAut (linkLayer R t))).map (MulAut.congr (linkLayerEquiv hs.large)).toMonoidHom := by
  obtain ⟨S₁', hS₁', hle⟩ := hs.exists_sylow_conj_le_actAut_image hr
  let φ : (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) ≃*
      ↥(linkGrp R t) := linkLayerEquiv hs.large
  refine ⟨S₁'.map φ.toMonoidHom, s8_isSylow2In_map_equiv φ hS₁', ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  change s ∈ Subgroup.map φ.toMonoidHom S₁' at hs
  rw [Subgroup.mem_map] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  change MulAut.conj (φ x) ∈
    Subgroup.map (MulAut.congr φ).toMonoidHom
      (Subgroup.map (actAut (linkLayer R t)) ((edgeCent (P : Subgroup Y) t u).subgroupOf
        (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))))
  rw [← mulAut_congr_conj φ x]
  exact Subgroup.mem_map_of_mem (MulAut.congr φ).toMonoidHom
    (hle (Subgroup.mem_map_of_mem (MulAut.conj) hx))

theorem z2BigSplit_holds (r n : ℕ) : Z2BigSplit r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs _ x hx hin
  obtain ⟨w, hw, hxw⟩ := hin
  have hxN : x ∈ Subgroup.normalizer (linkLayer R t : Set Y) := hs.mem_normalizer_linkLayer hx.1.2
  have hwA : (QuotientGroup.mk (⟨w, hw⟩ : ↥(linkLayer R t)) :
      ↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) ∈
      innerPart (linkLayer R t) (edgeCent (P : Subgroup Y) t u) :=
    mem_innerPart_of_actsLike hx hxN hw hxw
  rw [(hs.innerPart_inf_actTrivSubgroup_eq hr).1.symm] at hwA
  obtain ⟨b, hbB, _, hbw⟩ := exists_actsLike_of_mem_innerPart hw hwA
  exact ⟨b, hbB.1, actsLike_trans hbw (actsLike_symm hxw),
    (mem_actTrivSubgroup.mp hbB.2).2⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
