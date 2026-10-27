module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0Cls

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem asc82FactB5_of_pockets
    (hA : ∀ {y c : P45}, c ∈ QP45.originalSubgroup → c * Certificates.P43Twin.tA () * c⁻¹ = y →
      IsI4PlusIn QP45.originalSubgroup y)
    (hB : ∀ {y c : P45}, c ∈ QP45.originalSubgroup → c * Certificates.P43Twin.tB () * c⁻¹ = y →
      ¬ IsI4PlusIn QP45.originalSubgroup y) : Asc82FactB5 := by
  intro G _ _ L hL P hP
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hFP⟩ := F0.exists_frame_syl hP
  have hPL : P ≤ L := hP.1
  obtain ⟨φL, hφ⟩ := F.exists_phiL
  have hmod : IsPermModuleVia IsEvenVec (fun v => (φL v : G)) (F.pre B0)
      (L ⊓ normalizer ((F.pre B0 : Subgroup G) : Set G)) (alternatingGroup (Fin 5)) := by
    unfold IsPermModuleVia
    refine ⟨fun v w hv hw => ?_, fun v w hv hw h => ?_, fun x => ?_, fun h hh => ?_,
      fun σ hσ => ?_⟩
    · have h1 : φL (v + w) = φL v * φL w := F.ψ_injective (by
        rw [map_mul, hφ v hv, hφ w hw, hφ _ (isEvenVec_add_vec hv hw), phiB_add])
      exact congrArg Subtype.val h1
    · exact phiB_inj hv hw (by rw [← hφ v hv, ← hφ w hw]; exact congrArg F.ψ (Subtype.ext h))
    · constructor
      · intro hx
        obtain ⟨hxL, hψ⟩ := PspFrame.mem_pre.1 hx
        obtain ⟨v, hv, hveq⟩ := mem_B0_iff_phiB.1 hψ
        refine ⟨v, hv, ?_⟩
        have : φL v = ⟨x, hxL⟩ := F.ψ_injective (by rw [hφ v hv, hveq])
        exact congrArg Subtype.val this
      · rintro ⟨v, hv, rfl⟩
        refine PspFrame.mem_pre.2 ⟨(φL v).2, ?_⟩
        show F.ψ (φL v) ∈ B0
        rw [hφ v hv]
        exact phiB_mem_B0 hv
    · obtain ⟨hhL, hhN⟩ := Subgroup.mem_inf.1 hh
      let y : ↥(normalizer (L : Set G)) := ⟨h, Subgroup.le_normalizer hhL⟩
      have hn1 : ∀ b ∈ B0, F.φ y * b * (F.φ y)⁻¹ ∈ B0 := fun b hb => F.phi_conj_mem_B0 y hhN hb
      have hn2 : ∀ b ∈ B0, (F.φ y)⁻¹ * b * F.φ y ∈ B0 := fun b hb =>
        F.phi_conj_inv_mem_B0 y hhN hb
      obtain ⟨σ, hσ, hact⟩ := phiB_act_P (F.mem_P y hhL) hn1 hn2
      exact ⟨σ, hσ, fun v hv => F.conj_phiL hφ y σ hact hv⟩
    · obtain ⟨n, hnP, ⟨h1, h2⟩, hact⟩ := exists_phiB_act hσ
      have hn : n ∈ F.img (L ⊓ normalizer ((F.pre B0 : Subgroup G) : Set G)) := by
        rw [F.img_inf_normalizer (PspFrame.pre_le B0), PspFrame.img_pre B0_le_P]
        exact Subgroup.mem_inf.2 ⟨hnP, mem_normalizer_B0 h1 h2⟩
      obtain ⟨l, hl, rfl⟩ := PspFrame.mem_img.1 hn
      exact ⟨(l : G), hl, fun v hv => F.conj_phiL hφ ⟨l, Subgroup.le_normalizer l.2⟩ σ hact hv⟩
  refine ⟨F.pre B0, F.isMaxElemAbelianIn_pre hFP hPL, F.card_pre_B0,
    fun B' hB'P hc hcard => F.eq_pre_B0_of_abelian hFP hPL hB'P hc hcard,
    F.centralizer_pre_B0, fun v => (φL v : G), hmod, fun v hv h4 => ?_, fun v hv h2 => ?_,
    fun g hg => ?_⟩
  · rw [F.isI4PlusIn_img_iff (φL v).2]
    show IsI4PlusIn QP45.originalSubgroup (F.ψ (φL v))
    rw [hφ v hv]
    obtain ⟨c, hc, hce⟩ := phiB_class4 hv h4
    exact hA hc hce
  · rw [F.isI4PlusIn_img_iff (φL v).2]
    show ¬ IsI4PlusIn QP45.originalSubgroup (F.ψ (φL v))
    rw [hφ v hv]
    obtain ⟨c, hc, hce⟩ := phiB_class2 hv h2
    exact hB hc hce
  · obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.1 hg
    let y : ↥(normalizer (L : Set G)) := ⟨g, hgL⟩
    have hn1 : ∀ b ∈ B0, F.φ y * b * (F.φ y)⁻¹ ∈ B0 := fun b hb => F.phi_conj_mem_B0 y hgN hb
    have hn2 : ∀ b ∈ B0, (F.φ y)⁻¹ * b * F.φ y ∈ B0 := fun b hb =>
      F.phi_conj_inv_mem_B0 y hgN hb
    obtain ⟨σ, hact⟩ := phiB_act_A (F.mem_A y) hn1 hn2
    exact ⟨σ, fun v hv => F.conj_phiL hφ y σ hact hv⟩

end CFSG.OddStandard.SmallF3.Omega
