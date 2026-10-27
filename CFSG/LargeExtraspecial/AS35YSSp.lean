module

public import CFSG.LargeExtraspecial.AS35YSSpB
public import CFSG.LargeExtraspecial.AS35YSOmB
public import CFSG.LargeExtraspecial.AS35YSSpA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.Sporadic.Co2Smith AS35YR

namespace AS35YS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem card_le_of_hPU [FiniteDimensional (ZMod 2) V] [Finite V]
    (hq : q.polarBilin.Nondegenerate) {τ : V ≃ₗ[ZMod 2] V} (hA : IsTypeA q τ 2)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPU : ∀ p ∈ P, (∀ v, q (p v) = q v) ∧ (∀ v ∈ commSpace τ, p v = v) ∧
      ∀ v ∈ fixSpace τ, p v - v ∈ commSpace τ) :
    Nat.card P ≤ 2 ^ (2 * finrank (ZMod 2) V - 7) := by
  obtain ⟨F, hFℓ, rfl⟩ := exists_frame_of_isTypeA hq hA
  have hdim := finrank_Xp_add_eq hq F
  have hcardX : Nat.card F.Xp = 2 ^ (finrank (ZMod 2) V - 4) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  have hU : ∀ p ∈ P, F.InU p := by
    intro p hp
    obtain ⟨hiso, hfix, hsub⟩ := hPU p hp
    refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso,
      hfix _ (hFℓ ▸ F.a_mem_ell), hfix _ (hFℓ ▸ F.b_mem_ell), fun v ha hb => ?_⟩
    have hv : v ∈ fixSpace F.t := by
      rw [fixSpace_eq_orthogonal_commSpace hq F.t_mem F.t_mul_self, F.commSpace_t,
        OrthoF2.mem_orthogonal_iff_polar]
      intro u hu
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [polar_add_right, polar_smul_right, polar_smul_right, ha, hb]
      simp
    have := hsub v hv
    rwa [hFℓ] at this
  have h := card_le_of_inU F hU
  rw [hcardX, ← pow_add, ← pow_succ'] at h
  calc Nat.card P ≤ 2 ^ (finrank (ZMod 2) V - 4 + (finrank (ZMod 2) V - 4) + 1) := h
    _ = 2 ^ (2 * finrank (ZMod 2) V - 7) := by congr 1; omega

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem card_pbar_le_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    Nat.card (S.PbarAsc g) ≤ 2 ^ (2 * finrank (ZMod 2) (V0_YS S) - 7) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (V0_YS S) := Module.finite_of_finite (ZMod 2)
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have h1 := card_le_of_hPU (q0_YS_nondegenerate h) (isTypeA_act0_YS hS hst h htD)
    (pbar0_inU_YS hS hst hnd h ht htM)
  rwa [card_map_act0_YS hS hst h ht htM le_rfl] at h1

theorem fixW_eq_bot_of_spin_YS (hS : S.SixHyp)
    (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc) (h : RadSing_YS S)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp 3 2 1)
    (h8 : finrank (ZMod 2) (V0_YS S) = 8) : fixW_YS S = ⊥ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra hW0
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel
      hL
  have θ : S.LbarAsc ≃* Sp62 := (AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have htL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hPcard := (S14.asc512PbarStmt G S hS g ht htM).2.2.1
  have hle := card_pbar_le_YS hS hst hnd h ht htM
  rw [hPcard, h8] at hle
  have hle' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  obtain ⟨hsum, hRW⟩ := finrank_V0_add_YS (S := S)
  have hn3 := hS.three_le_width
  have hW1 : 1 ≤ finrank (ZMod 2) (fixW_YS S) :=
    Nat.pos_of_ne_zero fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
  rcases (show S.width = 5 ∨ S.width = 6 by omega) with h5 | h6
  ·
    have hW2 : finrank (ZMod 2) (fixW_YS S) ≤ 2 := by omega
    have hWc : Nat.card (fixW_YS S) ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      calc 2 ^ finrank (ZMod 2) (fixW_YS S) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hW2
        _ = 4 := by norm_num
    refine false_of_small_YS hS hst θ hc ht htM (fixW_YS S)
      (fun m hm w hw => fixW_YS_invariant hst hm hw)
      (fun w hw => mem_fixSpace.mpr (hw _ htL)) (fun hle => hW0 ?_) hWc
    have hinf := fixW_inf_commSpace_YS hS hst hnd htD
    rwa [inf_eq_left.mpr hle] at hinf
  ·
    exact false_of_sylow_YS hS hst θ hc ht htM (by rw [hPcard, h6])

end Setting

end CFSG.LargeExtraspecial
