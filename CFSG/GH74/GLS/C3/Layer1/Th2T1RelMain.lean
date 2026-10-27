module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1End

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

@[expose] def Thm1P31a_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      ¬ CFSG.GH74.IsCentralInvolution x ∧
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      ∀ T : Subgroup G, Setup1D x K T →
        (∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n) ∧
        ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
          ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z

@[expose] def B_thm1_fusion_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T : Subgroup G) (f : G), Is2TerminalU2Triple x y K → Setup1D x K T → IsFMember x K T f →
      ∀ z ∈ T ⊓ K, orderOf z = 2 → (∀ p ∈ T ⊓ K, z * p = p * z) →
        ∀ u ∈ T ⊓ K ⊔ zpowers f, orderOf u = 2 →
          ¬ HasL2Model (kBar K) (fun q => q = 5) →
          ∃ g : G, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z

@[expose] def B_thm1_L39_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    (∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K ∧
      ¬ HasL2Model (kBar K) (fun q => q = 5)) →
    ∃ (x y : G) (K T : Subgroup G) (f : G), FMax3 x y K f ∧ ¬ HasL2Model (kBar K) (fun q => q = 5) ∧
      Setup1D x K T ∧ IsFMember x K T f ∧
      ∀ V : Subgroup G, IsSylowOf 2 V (centralizer ({f} : Set G)) → (∀ t ∈ T, f * t = t * f → t ∈ V) →
        IsSylowOf 2 V ⊤

@[expose] def B_thm1_L310_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G) (f : G), FMax3 x y K f →
      ∀ T V : Subgroup G, Setup1D x K T → IsFMember x K T f →
        IsSylowOf 2 V (centralizer ({f} : Set G)) → (∀ t ∈ T, f * t = t * f → t ∈ V) → IsSylowOf 2 V ⊤ →
          ¬ HasL2Model (kBar K) (fun q => q = 5) →
          (∀ v ∈ V, ∀ p ∈ T ⊓ K, v * p * v⁻¹ ∈ T ⊓ K) ∧
          ∃ V₀ : Subgroup G, V₀ ≤ V ∧ (∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) ∧ x ∉ V₀ ∧
            (∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) ∧ T ⊓ K ⊔ zpowers f ≤ V₀ ∧
            ∀ u ∈ V₀, u * u = 1 → u ∈ T ⊓ K ⊔ zpowers f

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

theorem thm1_P31a_of_rel (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : P34.S_prop34)
    (hP : B_thm1_P31s_rel) : Thm1P31a_rel := by
  intro G _ _ hG hNo x y K hu2 h5
  have hshape := kBar_model_of_U2 hG h102 hL34 hu2
  obtain ⟨hnormal, hunique, hQ, hT⟩ := hP G hG hNo x y K hu2 hshape h5
  refine ⟨?_, hnormal, fun T hT' => ⟨(hT T hT').2.1, (hT T hT').2.2⟩⟩
  intro hcen
  obtain ⟨T, hTsetup⟩ := exists_setup1D x K
  obtain ⟨⟨f, hfmem, hfind⟩, -, -⟩ := hT T hTsetup
  have hfT : f ∈ T := hfmem.1
  have hf2 : orderOf f = 2 := hfmem.2.1
  have hxc : f ∈ centralizer ({x} : Set G) := hTsetup.sylowT.le hfT
  have hyp : P34.Prop34Hyp G x K :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := hcen
      comp := hu2.1.1.2
      unique := hunique
      shape := hshape
      sylowQ := hQ }
  exact hS34 G x K hyp f hxc hf2 hfind

theorem s_thm1_rel_of (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : P34.S_prop34)
    (hP31 : B_thm1_P31s_rel) (hF : B_thm1_fusion_rel) (h39 : B_thm1_L39_rel)
    (h310 : B_thm1_L310_rel) : S_thm1_rank4_rel := by
  have hP : Thm1P31a_rel := thm1_P31a_of_rel h102 hL34 hS34 hP31
  intro G _ _ hG hNo x₀ y₀ K₀ hU₀
  by_contra h5₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, y, K, T, f, hmax, h5, hsetup, hmem, h39'⟩ := h39 G hG hNo ⟨x₀, y₀, K₀, hU₀, h5₀⟩
  obtain ⟨hu2, -⟩ := hmax.1.1.1
  have hfT : f ∈ T := hmem.1
  have hf2 : orderOf f = 2 := hmem.2.1
  have hfP : ∀ p ∈ T ⊓ K, f * p = p * f := hmem.2.2.1
  have hCTf : IsPGroup 2 ↥(T ⊓ centralizer ({f} : Set G)) := hsetup.sylowT.isPGroup.to_inf_left
  obtain ⟨V, hCV, hVN, hVp, hVidx⟩ :=
    P34.exists_sylow_ge (N := centralizer ({f} : Set G)) inf_le_right hCTf
  have hVsyl : IsSylowOf 2 V (centralizer ({f} : Set G)) := isSylowOf_iff.2 ⟨hVN, hVp, hVidx⟩
  have hTV : ∀ t ∈ T, f * t = t * f → t ∈ V := fun t ht hft =>
    hCV ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hft.symm⟩
  have hVtop : IsSylowOf 2 V ⊤ := h39' V hVsyl hTV
  obtain ⟨hPn, V₀, hV0, hV0n, hxV0, hcyc, -, hom⟩ :=
    h310 G hG hNo x y K f hmax T V hsetup hmem hVsyl hTV hVtop h5
  obtain ⟨hnc, -, hPT⟩ := hP G hG hNo x y K hu2 h5
  have hx : orderOf x = 2 := hu2.1.1.1
  have hxT : x ∈ T :=
    Back.mem_of_isSylowOf_of_central hsetup.sylowT (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs => mem_centralizer_singleton_iff.1 hs) hx
  have hfx : f * x = x * f := mem_centralizer_singleton_iff.1 (hsetup.sylowT.le hfT)
  have hVtopS := isSylowOf_iff.1 hVtop
  have hVidxTop : ¬ 2 ∣ V.index := by
    have := hVtopS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact Thm1.thm1_false_of_end hG.kproper.1 hG.kproper.2.1 hx hxT hnc hfT hf2 hfx hfP inf_le_left
    (hPT T hsetup).2
    (fun z hz hz2 hzc u hu hu2' => hF G hG hNo x y K T f hu2 hsetup hmem z hz hz2 hzc u hu hu2' h5)
    hVtopS.2.1 hVidxTop
    (fun v hv => mem_centralizer_singleton_iff.1 (hVN hv)) hTV hPn hV0 hV0n hxV0 hcyc hom

end CFSG.GH74.GLS.C3.Layer1.Thm1
