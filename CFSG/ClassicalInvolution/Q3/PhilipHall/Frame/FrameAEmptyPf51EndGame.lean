module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.BenderNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43EndGame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def Lemma39FStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CaseIAmbient G] (H : Subgroup G) (z : G), H ≠ ⊤ →
    orderOf z = 2 → (∃! c : G ⧸ H, z • c = c) →
      (∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
        ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c) →
      z ∈ genFittingFStar G ∧ CFSG.BenderSuzuki.IsBenderGroup ↥(genFittingFStar G)

theorem lemma39FStar_of_certs :
    Lemma39FStar := by
  intro G _ _ _ H z hH hz h1 h2
  haveI : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hFnab : ∃ x ∈ genFittingFStar G, ∃ y ∈ genFittingFStar G, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ :=
      (CaseIAmbient.fstar_nonabelian : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  obtain ⟨hcl, hB, -⟩ := CFSG.StronglyEmbedded.UniqueCoset.lemma_3_9 hH hz h1 h2
    CaseIAmbient.fstar_simple hFnab CaseIAmbient.centralizer_fstar_eq_bot
  exact ⟨hcl ▸ Subgroup.subset_normalClosure (Set.mem_singleton z), hB⟩

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] [CaseIAmbient T] {K : Subgroup T} {z : T}
  {J : Subgroup T} {zJ : T} {S : Subgroup T}

theorem endgame_fstar (h39 : Lemma39FStar)
    (cfg : FrameCfg K z J zJ S) (hU : UniqueCosetZ K z)
    (hprod : ∀ h : T, h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = h⁻¹ * z * h * z →
      ∃! c : T ⧸ sigmaNorm K, (z * (h⁻¹ * z * h)) • c = c) : False := by
  have hz := cfg.datum.unique
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzM : z ∈ sigmaNorm K :=
    cfg.cz_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h1 : ∃! c : T ⧸ sigmaNorm K, z • c = c := fixesUnique_of_only_base hzM hU
  obtain ⟨hzF, hB⟩ := h39 T (sigmaNorm K) z cfg.sigmaNorm_ne_top hz2 h1 hprod
  haveI : (genFittingFStar T).Normal := genFittingFStar_normal T
  exact FStar.frame_not_bender_normal cfg.datum (genFittingFStar T)
    CaseIAmbient.centralizer_fstar_eq_bot hzF hB

end FrameCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
