module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Aut

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

structure Env37 {G : Type} [Group G] [Finite G] (x y : G) (K T V W : Subgroup G) (f z : G) :
    Prop where
  cfg : Cfg3 x y K T V W f z
  hVW : V ≠ W
  hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  hPK : IsSylowOf 2 (T ⊓ K) K
  hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(T ⊓ K) n
  hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z
  hfC : f ∈ centralizer ({x} : Set G)
  hfFaut : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩)
  hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  hAut : AutLevelF (kBar K)
  hQ2 : ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
    Nat.card ↥A ≤ 2
  hAutC : AutLevelC' (kBar K)
  hxS : IsSylowOf 2 (zpowers x) (CxK x K)
  hshape : HasL2Model (kBar K) Odd
  hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  hE₁ : ∃ E₁ : Subgroup G, E₁ ≤ T ∧ IsElementaryAbelian 2 ↥E₁ ∧ 16 ≤ Nat.card ↥E₁

theorem env37_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (h35 : B_thm1_L35_rel)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) (hNo : NoV2Fine G)
    {x y : G} {K T V W : Subgroup G} {f z : G} (cfg : Cfg3 x y K T V W f z) (hVW : V ≠ W)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) : Env37 x y K T V W f z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshape0 := Thm1.kBar_model_of_U2 hG h102 hL34 cfg.hu2
  have hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := fun h =>
    hVW (h35 G hG hNo x y K T V W f z cfg h h5)
  have hshape : HasL2Model (kBar K) Odd := hshape0.resolve_right hnotA7
  obtain ⟨hKN, hKuniq, -, hTdata⟩ := hP31s G hG hNo x y K cfg.hu2 hshape0 h5
  obtain ⟨-, ⟨n, hn3, hdih⟩, z₁, hz₁P, hz₁2, hz₁c, hz₁u⟩ := hTdata T cfg.setup
  have hz2 : orderOf z = 2 := cfg.z_mem.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
    have hzz₁ : z = z₁ := by
      rcases hz₁u z cfg.z_mem.1 (fun p hp => (cfg.z_mem.2.2 p hp.1).symm) with h | h
      · exact absurd h hz1
      · exact h
    intro w hw hwc
    rcases hz₁u w hw hwc with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzz₁.symm)
  have hfC : f ∈ centralizer ({x} : Set G) := cfg.setup.sylowT.le cfg.mem.1
  have hfFaut : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩) := by
    obtain ⟨hfN, hF⟩ := thm1_FmemberF_of_rel h2hb G hG hNo x y K cfg.hu2 hshape0 hKN T cfg.setup f
      cfg.mem h5
    exact hF
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hNo cfg.hu2 hshape0 h5
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model hshape
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ cfg.setup.sylowT (by rw [cfg.hu2.2.2.1.2, hG.pRank_eq_four])
  exact ⟨cfg, hVW, hKN, cfg.setup.sylowT.inf_of_le_normalizer cfg.hKx
    (fun c hc => U1a.mem_normalizer_of_norm hKN hc), ⟨n, hn3, hdih⟩, hzu, hfC, hfFaut, hcen,
    hAut, card_le_two_of_noV2Fine hNo cfg.hu2 h5, autLevelC'_of_L2 hF e,
    hP31c G hG hNo x y K cfg.hu2 h5, hshape, hnotA7, E₁, hE₁T, hE₁, hE₁16⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
