module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Case2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem centralizer_omegaCenter_eq_of_center (h : CampbellHyp X K R P) {C₀ : Subgroup A}
    (hN : HasNatSection K (CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K)) C₀)
    (hdisj : C₀ ⊓ ⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K), K⁆ = ⊥) :
    X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) = P := by
  set Q := CFSG.Quasithin.c134Q X K
  set D := CFSG.Quasithin.centerOf Q
  obtain ⟨hKD, -, a, b, ha, hker, -, hbker, hequiv⟩ := hN
  obtain ⟨e, he, hfix⟩ := sylow_fixed_line (h.sylow_image_card a ha hker)
  have hline : ∀ v : Fin 3 → ZMod 2, (∀ s : ↥K, (s : A) ∈ R →
      ((a s : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = e := by
    intro v hv
    refine (hfix v).1 fun g hg => ?_
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
    exact hv s (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
  obtain ⟨hP₂X, hP₂idx⟩ := h.stabSub_index a ha hker he
  have hkey : ∀ u ∈ D, (∀ r ∈ R, r * u * r⁻¹ = u) → ∀ k : ↥K, a k ∈ vecStab e →
      (k : A) * u * (k : A)⁻¹ = u := by
    intro u hu huR k hk
    have hv : (k : A) * u * (k : A)⁻¹ ∈ D := (mem_normalizer_iff.1 (hKD k.2) u).1 hu
    have hcoord : Multiplicative.toAdd (b ⟨u, hu⟩) = 0 ∨ Multiplicative.toAdd (b ⟨u, hu⟩) = e := by
      apply hline
      intro s hs
      exact (hequiv s ⟨u, hu⟩ ⟨u, hu⟩ (huR s hs).symm).symm
    have hbk : b ⟨(k : A) * u * (k : A)⁻¹, hv⟩ = b ⟨u, hu⟩ := by
      apply Multiplicative.toAdd.injective
      rw [hequiv k ⟨u, hu⟩ ⟨(k : A) * u * (k : A)⁻¹, hv⟩ rfl]
      rcases hcoord with h0 | h1
      · rw [h0, Matrix.mulVec_zero]
      · rw [h1]
        exact hk
    have hC₀ : (k : A) * u * (k : A)⁻¹ * u⁻¹ ∈ C₀ := by
      have h1 : (⟨(k : A) * u * (k : A)⁻¹, hv⟩ : ↥D) * (⟨u, hu⟩ : ↥D)⁻¹ ∈ b.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hbk]
        exact mul_inv_cancel _
      rw [hbker, mem_subgroupOf] at h1
      simpa using h1
    have hcomm : (k : A) * u * (k : A)⁻¹ * u⁻¹ ∈ ⁅D, K⁆ := by
      have := commutator_mem_commutator k.2 hu
      rw [commutator_comm] at this
      simpa [commutatorElement_def] using this
    have h1 : (k : A) * u * (k : A)⁻¹ * u⁻¹ ∈ C₀ ⊓ ⁅D, K⁆ := ⟨hC₀, hcomm⟩
    rw [hdisj, mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hP₂le : stabSub K a e (pCoreOf 2 X) ≤
      X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨hP₂X hg, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨c, u, hzcu, hcX, huQ, huR, huQX⟩ := h.trace_decomposition hz
    have huD : u ∈ D := by
      refine ⟨huQ, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      have hqO : q ∈ pCoreOf 2 X :=
        (Subgroup.commutator_le.2 fun o ho k _ => by
          have hk' : (k : A) ∈ normalizer (pCoreOf 2 X : Set A) :=
            normalizer_pCoreOf X (h.K_le ‹k ∈ K›)
          have e1 : ⁅o, k⁆ = o * (k * o⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
          rw [e1]
          exact mul_mem ho ((mem_normalizer_iff.1 hk' o⁻¹).1 (inv_mem ho))) hq
      exact huQX q hqO
    have hle : stabSub K a e (pCoreOf 2 X) ≤ centralizer ({z} : Set A) := by
      refine sup_le (fun k hk => ?_) (fun o ho => ?_)
      · obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
        have hkX : (k' : A) ∈ X := h.K_le k'.2
        have hkc : (k' : A) * c = c * (k' : A) := mul_inv_eq_iff_eq_mul.1 (hcX _ hkX)
        have hku : (k' : A) * u = u * (k' : A) :=
          mul_inv_eq_iff_eq_mul.1 (hkey u huD huR k' hk')
        rw [mem_centralizer_singleton_iff, hzcu]
        exact stabCent_comm_mul hkc hku
      · have hoX : o ∈ X := pCoreOf_le_self X ho
        have hoc : o * c = c * o := mul_inv_eq_iff_eq_mul.1 (hcX _ hoX)
        rw [mem_centralizer_singleton_iff, hzcu]
        exact stabCent_comm_mul hoc (huQX o ho)
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hP₂P : stabSub K a e (pCoreOf 2 X) ≤ P := hP₂le.trans h.cent_le
  have hEq : stabSub K a e (pCoreOf 2 X) = P :=
    centEq_eq_of_relIndex_eq hP₂P h.P_le hP₂idx h.P_index
  refine le_antisymm h.cent_le ?_
  rw [← hEq]
  exact hP₂le

theorem false_of_notCentralizer (h : CampbellHyp X K R P)
    (hNot : CFSG.Quasithin.C134NotCentralizerCore X (pCoreOf 2 P))
    (hC : X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) = P) : False := by
  have := hNot R ⟨h.R_le, h.R_two, h.R_sylow⟩ h.pCore_P_le_R
  rw [omegaOneCenterOf_eq_omegaCenter, hC] at this
  exact this rfl

theorem not_isC134Case3 (h : CampbellHyp X K R P) :
    ¬ CFSG.Quasithin.IsC134Case3 X (pCoreOf 2 P) K := by
  rintro ⟨⟨n, F, _, _, α, hF, hα, hZ, -⟩, hNot⟩
  have hF2 := h.card_field_eq_two hF α hα
  refine false_of_notCentralizer h hNot (centralizer_omegaCenter_eq_of_center h
    (hasNatSection_of_via hF2 hα hZ) ?_)
  exact bot_inf_eq _

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
