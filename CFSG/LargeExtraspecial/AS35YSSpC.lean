module

public import CFSG.LargeExtraspecial.AS35YRSet
public import CFSG.LargeExtraspecial.AS35YSIrr
public import CFSG.LargeExtraspecial.AS35YSSpA
public import CFSG.LargeExtraspecial.AS35YSSpB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.Sporadic.Co2Smith

namespace AS35YS

theorem card_linearEquiv_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] :
    Nat.card (V ≃ₗ[ZMod 2] V) ≤ 2 ^ (finrank (ZMod 2) V * finrank (ZMod 2) V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V →ₗ[ZMod 2] V) := Module.finite_of_finite (ZMod 2)
  have h1 : Nat.card (V →ₗ[ZMod 2] V) = 2 ^ (finrank (ZMod 2) V * finrank (ZMod 2) V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap]
  rw [← h1]
  exact Nat.card_le_card_of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V →ₗ[ZMod 2] V))
    fun e e' h => LinearEquiv.ext (LinearMap.congr_fun h)

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem card_inf_le_radU_YS :
    Nat.card (fixW_YS S ⊓ commU_YS S : Submodule (ZMod 2) S.Qt) ≤
      Nat.card (AS35YS.radU S.q (commU_YS S)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (AS35YS.radU S.q (commU_YS S)) := Module.finite_of_finite (ZMod 2)
  refine Nat.card_le_card_of_injective
    (fun w => (⟨⟨w, (Submodule.mem_inf.mp w.2).2⟩, AS35YS.mem_radU.mpr fun u hu => by
      rw [polar_comm]
      exact mem_commU_YS.mp hu _ (Submodule.mem_inf.mp w.2).1⟩ :
        AS35YS.radU S.q (commU_YS S))) fun w w' h => ?_
  exact Subtype.ext (congrArg (fun z : AS35YS.radU S.q (commU_YS S) => ((z : commU_YS S) :
    S.Qt)) h)

theorem radSing_of_sp6_YS (hS : S.SixHyp)
    (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp 3 2 1) : RadSing_YS S := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  intro v hvW hvperp
  by_contra hqv
  have hqv1 : S.q v = 1 := (AS35YR.Frame.zmod2_cases_YR _).resolve_left hqv
  have hv0 : v ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hqv1; exact zero_ne_one hqv1
  have hvU : v ∈ commU_YS S := mem_commU_YS.mpr hvperp
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel
      hL
  have θ : S.LbarAsc ≃* Sp62 := (AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e
  have hLcard : Nat.card S.LbarAsc = 1451520 := by
    rw [Nat.card_congr θ.toEquiv, natCard_sp62]
  have hk : 5 ≤ finrank (ZMod 2) (V0_YS S) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card S.LbarAsc ≤ Nat.card (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := by
      have : Finite (V0_YS S) := Module.finite_of_finite (ZMod 2)
      have : Finite (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := AS35YR.finite_linearEquiv_YR
      exact Nat.card_le_card_of_injective _ (actL_YS_injective hst)
    have h2 := card_linearEquiv_le (V := V0_YS S)
    have hk4 : finrank (ZMod 2) (V0_YS S) ≤ 4 := by omega
    have hk16 : finrank (ZMod 2) (V0_YS S) * finrank (ZMod 2) (V0_YS S) ≤ 16 :=
      (Nat.mul_le_mul hk4 hk4).trans (by norm_num)
    have h3 : 2 ^ (finrank (ZMod 2) (V0_YS S) * finrank (ZMod 2) (V0_YS S)) ≤ 2 ^ 16 :=
      Nat.pow_le_pow_right (by norm_num) hk16
    omega
  have hR1 : 1 ≤ finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) := by
    refine Nat.pos_of_ne_zero fun h0 => hv0 ?_
    have hmem : (⟨v, hvU⟩ : commU_YS S) ∈ AS35YS.radU S.q (commU_YS S) :=
      AS35YS.mem_radU.mpr fun u hu => by
        rw [polar_comm]
        exact mem_commU_YS.mp hu _ hvW
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨hsum, hRW⟩ := finrank_V0_add_YS (S := S)
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have htL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hPcard := (S14.asc512PbarStmt G S hS g ht htM).2.2.1
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  obtain ⟨Φ, hΦ⟩ := AS35QCo.exists_retraction S hst θ hc
  have hinj := phi_inj_pbar_YS hS θ ht htM Φ hΦ
  have hdvd : Nat.card (S.PbarAsc g) ∣ 1451520 := by
    rw [← natCard_sp62, ← Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hPcard] at hdvd
  have hn6 : S.width ≤ 6 := by
    by_contra h7
    push Not at h7
    have h10 : 2 ^ 10 ∣ 2 ^ (2 * S.width - 3) := Nat.pow_dvd_pow 2 (by omega)
    exact absurd (h10.trans hdvd) (by norm_num)
  rcases (show S.width = 4 ∨ S.width = 5 ∨ S.width = 6 by omega) with h4 | h5 | h6
  · exact AS35QCo.false_of_fixL S hS hst ⟨h4, hL⟩ S14.asc512SymStmt S14.asc512PbarStmt hqv1
      ((AS35QCo.mem_fixL S).mpr hvW)
  ·
    have hR2 : finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) ≤ 2 := by omega
    have hWc : Nat.card (fixW_YS S ⊓ commU_YS S : Submodule (ZMod 2) S.Qt) ≤ 4 := by
      refine card_inf_le_radU_YS.trans ?_
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      calc 2 ^ finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) ≤ 2 ^ 2 :=
            Nat.pow_le_pow_right (by norm_num) hR2
        _ = 4 := by norm_num
    refine false_of_small_YS hS hst θ hc ht htM (fixW_YS S ⊓ commU_YS S)
      (fun m hm w hw => Submodule.mem_inf.mpr ⟨fixW_YS_invariant hst hm (Submodule.mem_inf.mp hw).1,
        commU_YS_invariant hst hm (Submodule.mem_inf.mp hw).2⟩)
      (fun w hw => mem_fixSpace.mpr ((Submodule.mem_inf.mp hw).1 _ htL)) (fun hle => hv0 ?_) hWc
    have hmem : v ∈ fixW_YS S ⊓ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      ⟨hvW, hle (Submodule.mem_inf.mpr ⟨hvW, hvU⟩)⟩
    rwa [fixW_inf_commSpace_YS hS hst hnd htD, Submodule.mem_bot] at hmem
  · exact false_of_sylow_YS hS hst θ hc ht htM (by rw [hPcard, h6])

end Setting

end CFSG.LargeExtraspecial
