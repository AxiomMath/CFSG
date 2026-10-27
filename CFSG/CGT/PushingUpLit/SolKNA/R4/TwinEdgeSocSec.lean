module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSec

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem F2ConfigR.soc_isPGroup_center (hc : F2ConfigR r J L L₀) :
    IsPGroup 2 ↥(Subgroup.center G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hc.pCoreEq]
  exact pCore_isPGroup

theorem F2ConfigR.soc_not_mem_center (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) : z ∉ Subgroup.center G :=
  fun h => hc.noInvO2 K hK z hz ⟨Subgroup.center G, inferInstance, hc.soc_isPGroup_center, h⟩

theorem F2ConfigR.soc_inf_center_eq_bot (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) :
    K ⊓ Subgroup.center G = ⊥ := by
  obtain ⟨z, hz⟩ := (hc.min.hyp.hyp.omega1 K hK).1
  by_contra hne
  have h2 : IsPGroup 2 ↥(K ⊓ Subgroup.center G) := hc.soc_isPGroup_center.to_le inf_le_right
  have hcard : 2 ≤ Nat.card ↥(K ⊓ Subgroup.center G) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := K ⊓ Subgroup.center G)).mpr hne
  exact hc.soc_not_mem_center hK hz
    (Subgroup.mem_inf.mp (mem_of_isUniqueInvolution_of_isPGroup hz inf_le_left h2 hcard)).2

theorem F2ConfigR.soc_le_section (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {W : Subgroup G}
    (hKW : K ≤ W) (hWs : IsSubnormal W ⊤) : L₀ ≤ W := by
  obtain ⟨z, hz⟩ := (hc.min.hyp.hyp.omega1 K hK).1
  have hzL : z ∈ L₀ := hc.invMem K hK z hz
  have hzc : (⟨z, hzL⟩ : ↥L₀) ∉ Subgroup.center ↥L₀ := fun h => hc.soc_not_mem_center hK hz (by
    rw [← hc.centralizerEq]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨g, hg⟩))
  exact le_of_mem_isSubnormal hc.isComp.1 hWs hzL (hKW hz.mem) hzc

theorem F2ConfigR.soc_mem_normalizer_of_section (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀)
    {K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W) (htw : ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W))
    {w : G} (hw : w ∈ W) (hwz : w * z * w⁻¹ = z) : w ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨S, hd, -, -⟩ := hc.exists_sectionDatum hr hK hz hKW hWs hWg htw
  have hcent : (⟨w, hw⟩ : ↥W) ∈ Subgroup.centralizer ({(⟨z, hKW hz.mem⟩ : ↥W)} : Set ↥W) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show w * z = z * w
    calc w * z = (w * z * w⁻¹) * w := by group
      _ = z * w := by rw [hwz]
  have := hd.le_normalizer hcent
  exact (mem_normalizer_subgroupOf_iff hKW).mpr this

theorem F2ConfigR.soc_eq_of_edgeless (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W) (htw : ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W))
    (hedge : TightEdgeless (K.subgroupOf W)) {R : Subgroup G} (hR : IsSylow2In R K) {w : G}
    (hw : w ∈ W) (hcent : ∀ ρ ∈ R, ρ * (w * z * w⁻¹) = (w * z * w⁻¹) * ρ) :
    w * z * w⁻¹ = z := by
  by_contra hne
  obtain ⟨S, -, -, htc⟩ := hc.exists_sectionDatum hr hK hz hKW hWs hWg htw
  have hs2 : IsUniqueInvolution (conjSub w K) (w * z * w⁻¹) := hz.conj w
  have hK'W : conjSub w K ≤ W := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := hKW hx
    have h2 : x = w * (w⁻¹ * x * w) * w⁻¹ := by group
    rw [h2]
    exact W.mul_mem (W.mul_mem hw this) (W.inv_mem hw)
  have hKne : conjSub w K ≠ K := by
    intro h
    have hsK : w * z * w⁻¹ ∈ K := h ▸ hs2.mem
    rcases hz.unique _ hsK hs2.sq with h1 | h1
    · exact hs2.ne_one h1
    · exact hne h1
  have hRN : R ≤ Subgroup.normalizer ((conjSub w K : Subgroup G) : Set G) := by
    intro ρ hρ
    have hρW : ρ ∈ W := hKW (hR.1 hρ)
    have hρ'W : w⁻¹ * ρ * w ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hw) hρW) hw
    have h1 : ρ * (w * z * w⁻¹) * ρ⁻¹ = w * z * w⁻¹ := by
      have := hcent ρ hρ
      calc ρ * (w * z * w⁻¹) * ρ⁻¹ = ((w * z * w⁻¹) * ρ) * ρ⁻¹ := by rw [this]
        _ = w * z * w⁻¹ := by group
    have hρ'z : (w⁻¹ * ρ * w) * z * (w⁻¹ * ρ * w)⁻¹ = z := by
      calc (w⁻¹ * ρ * w) * z * (w⁻¹ * ρ * w)⁻¹
          = w⁻¹ * (ρ * (w * z * w⁻¹) * ρ⁻¹) * w := by group
        _ = w⁻¹ * (w * z * w⁻¹) * w := by rw [h1]
        _ = z := by group
    have hρ'N := hc.soc_mem_normalizer_of_section hr hK hz hKW hWs hWg htw hρ'W hρ'z
    rw [mem_normalizer_iff_conjSub_eq] at hρ'N ⊢
    rw [← conjSub_mul]
    have : ρ * w = w * (w⁻¹ * ρ * w) := by group
    rw [this, conjSub_mul, hρ'N]
  set Ω := CoreAssembly.conjClass (tightCore (K.subgroupOf W)) with hΩ
  have hK1 : K.subgroupOf W ∈ Ω := by rw [hΩ, htc]; exact CoreAssembly.mem_conjClass_self _
  have hK2 : (conjSub w K).subgroupOf W ∈ Ω := by
    rw [hΩ, htc]
    exact ⟨⟨w, hw⟩, conjSub_subgroupOf W ⟨w, hw⟩ K⟩
  have hRs := hR.subgroupOf hKW
  have hnbr : K.subgroupOf W ∈ omegaNbr Ω ((conjSub w K).subgroupOf W) :=
    ⟨hK1, subgroupOf_ne_of_ne hK'W hKW hKne.symm, R.subgroupOf W, mem_RSet_of_isSylow2In hK1 hRs,
      hRs.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hK'W).mp (hRN (Subgroup.mem_subgroupOf.mp hx))⟩
  exact hedge _ hK2 _ hK1 (Or.inl hnbr)

theorem F2ConfigR.soc_eq_of_mk_eq (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W) (htw : ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W))
    (hedge : TightEdgeless (K.subgroupOf W)) {R : Subgroup G} (hR : IsSylow2In R K) {x : G}
    (hx : x ∈ L₀) {c : G} (hcZ : c ∈ Subgroup.center G) (hxz : x * z * x⁻¹ = z * c) :
    x * z * x⁻¹ = z := by
  have hxW : x ∈ W := hc.soc_le_section hK hKW hWs hx
  refine hc.soc_eq_of_edgeless hr hK hz hKW hWs hWg htw hedge hR hxW fun ρ hρ => ?_
  rw [hxz]
  have h1 : z * ρ = ρ * z := hz.commute_of_mem (hR.1 hρ)
  have h2 : ρ * c = c * ρ := Subgroup.mem_center_iff.mp hcZ ρ
  calc ρ * (z * c) = (ρ * z) * c := by group
    _ = z * ρ * c := by rw [← h1]
    _ = z * (ρ * c) := by group
    _ = z * (c * ρ) := by rw [h2]
    _ = z * c * ρ := by group

end CFSG.CGT.PushingUpLit.SolKNA.R4
