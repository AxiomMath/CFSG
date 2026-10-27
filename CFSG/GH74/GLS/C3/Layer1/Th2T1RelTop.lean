module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelMain
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelP31
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelL34
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelL36
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

theorem thm1_fusion_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hL1 : B_thm1_P31_comp_rel) (hL3 : B_thm1_FmemberF_rel) : B_thm1_fusion_rel := by
  intro G _ _ hG hV x y K T f h𝒰 hT hfm z hz hz2 hzc u hu hu2 h5
  have hshape := C3.Layer1.Thm1.kBar_model_of_U2 hG h102 hL34 h𝒰
  obtain ⟨hKN, -⟩ := hL1 G hG hV x y K h𝒰 hshape h5
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hQ2 := C3.Layer1.Thm1.card_le_two_of_noV2Fine hV h𝒰 h5
  obtain ⟨hcen, hAut⟩ := C3.Layer1.Thm1.kBar_autData_rel h2hb hV h𝒰 hshape h5
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    C3.Layer1.Thm1.exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  have hfind := hL3 G hG hV x y K h𝒰 hshape hKN T hT f hfm h5
  obtain ⟨hfN, hF⟩ := hfind
  have hfinn : ∀ hfC : f ∈ centralizer ({x} : Set G),
      Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K) := fun hfC =>
    C3.Layer1.Thm1.not_mem_innAut_of_isFAutL2A7 hF
  exact C3.Layer1.Thm1.transport_fusion_G hKC hKN hT.sylowT hcen hAut hE₁T hE₁ hE₁16 hQ2
    hfm.1 hfm.2.1 hfm.2.2.1 hfinn hz hz2 hzc u hu hu2

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

theorem thm1_L39_of_rel (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hP31 : B_thm1_P31s_rel)
    (hP31a : Thm1P31a_rel) (h35 : B_thm1_L35_rel) (h36 : B_thm1_L36_rel)
    (hcore : B_thm1_L39core_rel) : B_thm1_L39_rel := by
  intro G _ _ hG hNo hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, y₀, K₀, hu₀, h5₀⟩ := hU
  have hshape := kBar_model_of_U2 hG h102 hL34 hu₀
  obtain ⟨-, -, -, hT⟩ := hP31 G hG hNo x₀ y₀ K₀ hu₀ hshape h5₀
  obtain ⟨T₀, hT₀⟩ := exists_setup1D x₀ K₀
  obtain ⟨⟨f₀, hf₀, -⟩, -, -⟩ := hT T₀ hT₀
  have hFU₀ : IsFU2 x₀ y₀ K₀ f₀ := ⟨hu₀, T₀, hT₀, hf₀⟩
  obtain ⟨x, y, K, f, hmax3⟩ := exists_fmax3 ⟨x₀, y₀, K₀, f₀, hFU₀⟩
  have h5 : ¬ HasL2Model (kBar K) (fun q => q = 5) :=
    fmax1_not_five h102 hL34 hG hmax3.1.1 hFU₀ h5₀
  obtain ⟨hu2, T, hsetup, hmem⟩ := hmax3.1.1.1
  obtain ⟨f₁, hmax3', hmem', hspec⟩ := exists_special hmax3 hmem
  refine ⟨x, y, K, T, f₁, hmax3', h5, hsetup, hmem', ?_⟩
  intro V hV hCV
  by_contra hnot
  obtain ⟨W, hVW, -, hWp, hWidx⟩ := P34.exists_sylow_ge (N := (⊤ : Subgroup G)) (K := V) le_top
    hV.isPGroup
  have hWsyl : IsSylowOf 2 W ⊤ := isSylowOf_iff.2 ⟨le_top, hWp, hWidx⟩
  have hne : V ≠ W := fun h => hnot (h ▸ hWsyl)
  obtain ⟨-, hnormal, hTz⟩ := hP31a G hG hNo x y K hu2 h5
  obtain ⟨z, hzP, hz2, hzT⟩ := exists_z hsetup hnormal (hTz T hsetup).2
  have cfg : Cfg3 x y K T V W f₁ z := ⟨hmax3', hsetup, hmem', ⟨hzP, hz2, hzT⟩, hV, hCV, hWsyl, hVW⟩
  have hA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := fun h =>
    hne (h35 G hG hNo x y K T V W f₁ z cfg h h5)
  have hle : Nat.card ↥V ≤ Nat.card ↥T := by
    rcases h36 G hG hNo x y K T V W f₁ z cfg h5 with h | h
    · exact absurd h hne
    · exact h
  exact hcore G hG hNo x y K T V W f₁ z cfg hspec hne hA7 hle h5

theorem thm1_L310_of_rel (hP31a : Thm1P31a_rel) (hL32 : B_thm1_L32'_rel)
    (h33e : B_thm1_L33e_rel) (h33f : B_thm1_L33f_rel) (h34 : B_thm1_L34_rel)
    (hV0 : B_thm1_L310_V0_rel) : B_thm1_L310_rel := by
  intro G _ _ hG hNo x y K f hmax T V hsetup hmem hV hCV hVtop h5
  have hu2 : Is2TerminalU2Triple x y K := hmax.1.1.1.1
  obtain ⟨-, hnormal, hTz⟩ := hP31a G hG hNo x y K hu2 h5
  obtain ⟨z, hzP, hz2, hzT⟩ := exists_z hsetup hnormal (hTz T hsetup).2
  have cfg : Cfg3 x y K T V V f z :=
    ⟨hmax, hsetup, hmem, ⟨hzP, hz2, hzT⟩, hV, hCV, hVtop, le_rfl⟩
  have hf2 : orderOf f = 2 := hmem.2.1
  have hfV : f ∈ V :=
    Back.mem_of_isSylowOf_of_central hV (mem_centralizer_singleton_iff.2 rfl)
      (fun s hs => mem_centralizer_singleton_iff.1 hs) hf2
  have hVtopS := isSylowOf_iff.1 hVtop
  have hVidx : ¬ 2 ∣ V.index := by
    have := hVtopS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hfCI : CFSG.GH74.IsCentralInvolution f :=
    isCentralInvolution_of_mem_center_sylow hVtopS.2.1 hVidx hfV
      (fun v hv => mem_centralizer_singleton_iff.1 (hV.le hv)) hf2
  have hJ : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) := by
    by_contra hne
    have hle : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) ≤ pumpJ K f :=
      sup_le (layerI_le_pumpJ K f) (pPrimeCoreOf_le_self _)
    have hlt : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f :=
      lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨⟨w, -, hw⟩, -⟩ := h34 G hG hNo x y K T f hmax hsetup hmem hlt h5
    exact (hP31a G hG hNo f w (pumpJ K f) hw
      (Thm1L34.pumpJ_not_five_of_L32 hL32 hG hNo hmax h5 hlt)).1 hfCI
  have hz : ¬ IsConj z f := fun hc =>
    (h33f G hG hNo x y K T V V f z ⟨cfg, hJ⟩ hc h5).1 rfl
  have hPV := h33e G hG hNo x y K T V V f z ⟨cfg, hJ⟩ hz h5
  exact ⟨hPV, hV0 G hG hNo x y K T V f z cfg hJ hPV h5⟩

theorem s_thm1_of_fine_rel (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : P34.S_prop34)
    (hP31 : B_thm1_P31s_rel) (hF : B_thm1_fusion_rel) (hL32 : B_thm1_L32'_rel)
    (h33e : B_thm1_L33e_rel) (h33f : B_thm1_L33f_rel) (h34 : B_thm1_L34_rel)
    (h35 : B_thm1_L35_rel) (h36 : B_thm1_L36_rel) (hcore : B_thm1_L39core_rel)
    (hV0 : B_thm1_L310_V0_rel) : S_thm1_rank4_rel := by
  have hP31a : Thm1P31a_rel := thm1_P31a_of_rel h102 hL34 hS34 hP31
  exact s_thm1_rel_of h102 hL34 hS34 hP31 hF (thm1_L39_of_rel h102 hL34 hP31 hP31a h35 h36 hcore)
    (thm1_L310_of_rel hP31a hL32 h33e h33f h34 hV0)

end CFSG.GH74.GLS.C3.Layer1.Thm1

namespace CFSG.GH74.GLS

theorem s_thm1_of_base_rel
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : C3.Layer1.P34.S_prop34)
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL29 : B_inC2_L29) (hC2 : C3.Layer1.PumpCalc.C2Facts)
    (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) (h33c : B_thm1_L33c'_rel)
    (h33d : B_thm1_L33d_rel)
    (h33e : B_thm1_L33e_rel) (h33f : B_thm1_L33f_rel) (h35 : B_thm1_L35_rel)
    (hcore : B_thm1_L39core_rel) (hV0 : B_thm1_L310_V0_rel) : S_thm1_rank4_rel := by
  have hU : B_thm1_P31_unique_rel := C3.Layer1.Thm1L3Uniq.thm1_P31_unique_of_rel hP31c
  have hcomp : B_thm1_P31_comp_rel := thm1_P31_comp_of_rel hU
  have hP31s : B_thm1_P31s_rel :=
    C3.Layer1.Thm1.thm1_P31s_of_rel IVK.Proofs2.ivk_1_2h_b hcomp
      (thm1_P31_layer_of_rel IVK.Proofs2.ivk_1_2h_b)
  have h34a : B_thm1_L34a_rel :=
    C3.Layer1.Thm1L34.thm1_L34a_of_rel h610 h720 h14 h103 hL34 hL29 h102 hC2 hP31s hL32
  have h34 : B_thm1_L34_rel := C3.Layer1.Thm1L34.b_thm1_L34_of_rel hL32 h34a hP31c
  have hA7 : B_thm1_L36A7_rel :=
    C3.Layer1.Thm1L3A7.thm1_L36A7_of_rel h34a hP31c hP31s hL32
  have h36 : B_thm1_L36_rel :=
    C3.Layer1.Thm1L36.thm1_L36_of_rel h34a h35 h33c h33d h33f hL32 hP31s h102 hL34 hA7
  exact C3.Layer1.Thm1.s_thm1_of_fine_rel h102 hL34 hS34 hP31s
    (thm1_fusion_of_rel IVK.Proofs2.ivk_1_2h_b h102 hL34 hcomp
      (thm1_FmemberF_of_rel IVK.Proofs2.ivk_1_2h_b))
    hL32 h33e h33f h34 h35 h36 hcore hV0

end CFSG.GH74.GLS
