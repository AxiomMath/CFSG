module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTwoFinal
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX17KindsWrap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX17Kinds
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRParrott
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Transport
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmFinal
public import CFSG.Sporadic.Schreier.RuB1Objects
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuFrameA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuJFacts
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPlaneUniq

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm
open CFSG.Sporadic.RuSchreier (RuB1NativeFacts ruESub ruXN ruG5)

@[expose] def RuH1Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A₁ Q X R : Subgroup G) (f : G),
    Q ≤ centralizer ({f} : Set G) → centralizer ({f} : Set G) ≤ normalizer (Q : Set G) →
    (∃ σ : centralizer ({f} : Set G) →* Equiv.Perm (Fin 5), Function.Surjective σ ∧
      σ.ker = Q.subgroupOf (centralizer ({f} : Set G))) →
    Nat.card Q = 2 ^ 11 → R = pCoreOf 2 (normalizer (A₁ : Set G)) →
    A₁ ≤ X → X ≤ R → Nat.card X = 32 →
    (∀ Y : Subgroup G, A₁ ≤ Y → Y ≤ R → Nat.card Y = 32 →
      centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Y : Set G) → Y = X) →
    (∀ u ∈ Q, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ zpowers f) →
    ∀ f₂ : ↥ruM2 ≃* ↥(normalizer (A₁ : Set G)),
      (∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂ m : ↥(normalizer (A₁ : Set G))) : G) = f) →
      (∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A₁ : Set G))) : G) ∈ A₁) →
      ∃ f₂' : ↥ruM2 ≃* ↥(normalizer (A₁ : Set G)),
        (∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂' m : ↥(normalizer (A₁ : Set G))) : G) = f) ∧
        (∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂' m : ↥(normalizer (A₁ : Set G))) : G) ∈ A₁) ∧
        ∃ f₁ : ↥ruM1 ≃* ↥(centralizer ({f} : Set G)), IsNormCz f₁ A₁ ∧
          RuEdgeAgree f₁ f₂' (MonoidHom.id _)

theorem dempwolffRuMin_of_open
    (hF : Foundation) (hN : RuB1NativeFacts ruESub ruXN ruG5) (hH1 : RuH1Stmt) :
    DempwolffRuMin := by
  have hS3 : B1Stage3 :=
    b1Stage3_of (b1Stage3Transport_of_native hN) b1Stage3Alpha
  refine dempwolffRuMin_of_edgeData fun G _ _ L hM T₀ hT₀ h4' => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h3 : Sec3 G L T := ⟨hM.hyp, hT⟩
  have h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 := by
    rw [h3.isSylowOf_T₀.card_eq, ← hT₀.card_eq, h4']
  have hZ : Odd (Nat.card (center L)) := hM.hyp.odd_card_center hF
  have hO := dempwolffOddCore_of hF hS3 G L hM T₀ hT₀ h4'
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le eS
  obtain ⟨y₀, hy₀⟩ := hX.exists_isTorus h3
  obtain ⟨R, y, d, hS⟩ := h3.exists_szR hF hZ hM.one_le eS
    (hy₀.exists_translation_of_affine h313 hX h3 hF hksRegularNormalAffine)
  obtain ⟨R₂, hR₂⟩ := hS.exists_isR₂ h34
  have hCV := hM.centralizer_gmsV_eq h3 hS.foundation hZ h4 hO
  have hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L := fun e he he1 =>
    hM.centralizer_eq_sup h3 hS.foundation hZ h4 hO he he1
  have hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G) := fun a haL ha1 ha2 =>
    hM.isPGroup_inf_centralizer h3 hS.foundation hZ h4 hO haL ha1 ha2
  have hNS := hS.not_isSylowOf_normalizer hM hR₂
  have h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G) := fun _ hF₁ hc =>
    hS.normalizer_le_of_le_gmsA_of_card_eq_four h34 hR₂ h4 hCV hCe hCL hNS hF₁ hc
  have hNC := Sec3.SzR.normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hidx := Sec3.SzR.relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
  have h217 := hM.dempwolff217_of_min hF hS3 hS hR₂ h4 h216 (hS.hkinds_of_core h34 hR₂ h4 hCV hCe
    hCL hNS fun _ _ hMC _ _ hΦ => Sec3.SzR.kinds_of_model hMC hΦ hNC hidx h216)
  obtain ⟨μ, ν, S, f, X, J, hD⟩ := hM.exists_frameData hF hS3 hS hR₂ h4
  have h217' := h217 μ ν hD.coords S hD.sylow f hD.mem_gmsA hD.ne_one hD.center_eq X hD.plane
  have hXH := h217'.resolve_left hD.not_le
  obtain ⟨Q, -, -, hQC, hCQ, hσ, hQc, -, -, -, hQX⟩ := hD.coords.jFacts hS h34 hR₂ h4 hCV hCe
    hCL hNS h216 hD.sylow hD.mem_gmsA hD.ne_one hD.center_eq hD.plane h217'
  obtain ⟨Φ, hΦ⟩ := hD.coords.exists_sModel_false hD.isPGroup hD.inf_centralizer hD.relIndex
    hD.normalizer_gmsA h216 hD.sylow hD.mem_gmsA hD.ne_one hD.conj_eq hD.plane hXH hD.not_le
  obtain ⟨f₂, hf₂⟩ := ruNAIso_of_model (RuN.exists_ruNIso hD.coords hΦ hD.inf_centralizer
    hD.relIndex (by rw [hD.card_R]; norm_num) hD.normalizer_gmsA)
  obtain ⟨f₂a, hz₂, hA₂⟩ := exists_aligned ruAlignFacts hD.mem_gmsA hD.ne_one f₂ hf₂
  obtain ⟨f₂', -, -, f₁, hf₁, hag⟩ := hH1 G (gmsA L T) Q X R f hQC hCQ hσ hQc hD.pCoreOf_eq.symm
    (hD.coords.gmsA_le_plane hD.plane) (Sec3.SzR.MaskCoords.plane_le hD.plane)
    (hD.coords.card_plane hD.plane hD.mem_gmsA hD.ne_one)
    (fun Y hAY hYR hY hYn => hD.coords.eq_plane_of_le hD.inf_centralizer hD.relIndex hD.mem_gmsA
      hD.ne_one hD.plane hAY hYR hY hYn) hQX f₂a hz₂ hA₂
  obtain ⟨e, he, he2, hec⟩ := hM.exists_mem_normalizer_card_centralizer h3 hS.foundation hZ h4 hO
  have hSC : S ≤ centralizer ({f} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (by
      have := hD.conj_eq s hs
      calc s * f = s * f * s⁻¹ * s := by group
        _ = f * s := by rw [this])
  have hfc : 2 ^ 9 ∣ Nat.card (centralizer ({f} : Set G)) := by
    have h14 := Sec3.SzR.card_sylow_normalizer hS h34 hR₂ h4 hCV hNS hD.sylow
    exact (pow_dvd_pow 2 (by norm_num : 9 ≤ 14)).trans (h14 ▸ Subgroup.card_dvd_of_le hSC)
  exact ⟨f, e, gmsA L T, f₁, f₂', hf₁, hag, hfc, he, he2, hec⟩

end CFSG.ComponentClassification.GMS78
