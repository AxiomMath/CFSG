module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelP31

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Env

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

structure Env31 (x y : G) (K T : Subgroup G) (f z : G) : Prop where
  hu2 : Is2TerminalU2Triple x y K
  hshape : HasL2Model (kBar K) Odd
  hrk : pRank 2 ↥(CxK x K) ≤ 1
  hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  huniq : ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K
  hsetup : Setup1D x K T
  hfT : f ∈ T
  hf2 : orderOf f = 2
  hfc : ∀ p ∈ T ⊓ K, f * p = p * f
  hind : P34.InducesFAutL2A7 f K
  hfout : ∀ hfC : f ∈ centralizer ({x} : Set G), Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K)
  hdih : ∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n
  hzP : z ∈ T ⊓ K
  hz2 : orderOf z = 2
  hzc : ∀ p ∈ T ⊓ K, z * p = p * z
  hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z
  hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  hAut : AutLevelF (kBar K)

theorem pRank_le_one_of_card_le_two
    (hQ2 : ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
      Nat.card ↥A ≤ 2) : pRank 2 ↥(CxK x K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hAel, hA4⟩ := CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank
    (G := ↥(CxK x K)) hlt
  have hAel' : IsElementaryAbelian 2 ↥(A.map (CxK x K).subtype) := by
    have := hAel
    exact IsElementaryAbelian.map_subtype
  have hcard : Nat.card ↥(A.map (CxK x K).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (CxK x K).subtype_injective, hA4]
    norm_num
  have hle := hQ2 (A.map (CxK x K).subtype) (Subgroup.map_subtype_le A : _ ≤ CxK x K) hAel'
  omega

theorem exists_env31
    (h2hb : IVK.IVK_1_2h_b) (hG : C3Hyp G) (hV : NoV2Fine G) (h𝒰 : Is2TerminalU2Triple x y K)
    (hL2 : HasL2Model (kBar K) Odd) (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5))
    (huniq : ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K)
    {T : Subgroup G} (hT : Setup1D x K T) : ∃ f z : G, Env31 x y K T f z := by
  have hQ2 := card_le_two_of_noV2Fine hV h𝒰 h5
  have hrk := pRank_le_one_of_card_le_two hQ2
  have hKN := thm1_P31_normal_rel hV h𝒰 (Or.inl hL2) h5
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hV h𝒰 (Or.inl hL2) h5
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f, z, hfT, hf2, hfc, hfx, hind, hinn, hdih, hzP, hz2, hzc, hzu⟩ :=
    transport_G hKC hKN hT.sylowT hxC hxK hcen hAut hE₁T hE₁ hE₁16 hQ2
  exact ⟨f, z, ⟨h𝒰, hL2, hrk, hKN, huniq, hT, hfT, hf2, hfc, hind, hinn, hdih, hzP, hz2, hzc, hzu,
    hcen, hAut⟩⟩

end Env

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
