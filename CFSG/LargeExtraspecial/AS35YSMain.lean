module

public import CFSG.LargeExtraspecial.AS35YSDefs
public import CFSG.LargeExtraspecial.AS35YSSpC
public import CFSG.LargeExtraspecial.AS35YSU33
public import CFSG.LargeExtraspecial.AS35YLMLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
open CFSG.QuasithinUnique.Setup.Family (GL32)

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem false_of_psl3_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 3 2 1) : False := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
  set E : S.LbarAsc ≃* GL32 := (AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e with hE
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨x, hxM, ⟨k, hxk⟩, hxt, hfpf⟩ := S14.asc512FiveTwelveSevenStmt G S hS g ht htM
  have hx3 : x ^ (3 ^ k) = 1 := by rw [← hxk]; exact pow_orderOf_eq_one x
  have hxL : ∀ l ∈ S.LbarAsc, x * l * x⁻¹ ∈ S.LbarAsc := fun l hl => hst.normal x hxM l hl
  have hxL' : ∀ l ∈ S.LbarAsc, x⁻¹ * l * x ∈ S.LbarAsc := fun l hl => by
    have := hst.normal x⁻¹ (S.Mbar.inv_mem hxM) l hl
    rwa [inv_inv] at this
  have hαk := AS35YL.conjAut_YL_pow_eq_one S.LbarAsc x hxL hxL' hx3
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hαt := AS35YL.conjAut_YL_fix S.LbarAsc x hxL hxL' (l := ⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩)
    hxt
  have hTT : (⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩ : S.LbarAsc) * ⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩
      = 1 := Subtype.ext (mul_self_of_mem_DbarAsc_YL htD)
  have hT1 : (⟨S.ρ ⟨_, htM⟩, subset_closure htD⟩ : S.LbarAsc) ≠ 1 := fun h1 =>
    (isTypeA_of_mem_DbarAsc_YL hS htD).2.1 (by
      have := congrArg (fun y : S.LbarAsc => ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
      simpa using this)
  have hα1 := AS35YL.aut_eq_one_of_GL32_YL E _ hαk hTT hT1 hαt
  have hcomm : ∀ l ∈ S.LbarAsc, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * x := fun l hl =>
    congrArg Subtype.val (AS35YL.commute_of_conjAut_YL_eq_one S.LbarAsc x hxL hxL' hα1 hl)
  exact not_inspNondeg_of_fpf_YL hS hst
    (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v) hcomm htD hfpf hnd

theorem card_dvd_card_O_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h : RadSing_YS S) :
    Nat.card (S.LbarAsc ⧸ center S.LbarAsc) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hle : (actL_YS hst).range ≤ TauCeti.QuadraticMap.orthogonalGroup (q0_YS h) := by
    rintro _ ⟨l, rfl⟩
    rw [actL_YS_apply]
    exact act0_YS_mem_O h hst _
  have h1 : Nat.card (S.LbarAsc ⧸ center S.LbarAsc) = Nat.card (actL_YS hst).range := by
    rw [Nat.card_congr (AS35YL.quotEquiv_YL S.LbarAsc hc).toEquiv]
    exact Nat.card_congr (MonoidHom.ofInjective (actL_YS_injective hst)).toEquiv
  rw [h1]
  exact Subgroup.card_dvd_of_le hle

theorem card_O_eq_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S)
    (hX : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) =
      2 * Nat.card (S.LbarAsc ⧸ center S.LbarAsc)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (q0_YS h)) = 2 * Nat.card S.LbarAsc := by
  rw [hX, Nat.card_congr
    (AS35YL.quotEquiv_YL S.LbarAsc (center_LbarAsc_eq_bot_YL hS hst hnd)).toEquiv]

theorem radSing_YS
    (hRad : S14.Asc512FixRadSingStmt) (hU33 : S14.Asc512U33FixNonsingStmt) (hS : S.SixHyp)
    (hst : S.Asc512Standing)
    (hfam : S14.Asc512PSLFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512PSpFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512POmegaFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc) : RadSing_YS S := by
  rcases hfam with ⟨hnd, m, hm, hL⟩ | ⟨hnd, m, hm, hL⟩ | ⟨hnd, m, hm, hL⟩ | ⟨hnd, hL⟩
  · by_cases hm4 : 4 ≤ m
    · exact fun v hv hvv => hRad G S hS hst hnd ⟨m, hm4, Or.inl hL⟩ v hv hvv
    · obtain rfl : m = 3 := by omega
      exact (false_of_psl3_YS hS hst hnd hL).elim
  · by_cases hm4 : 4 ≤ m
    · exact fun v hv hvv => hRad G S hS hst hnd ⟨m, hm4, Or.inr (Or.inl hL)⟩ v hv hvv
    · obtain rfl : m = 3 := by omega
      exact radSing_of_sp6_YS hS hst hnd hL
  · exact fun v hv hvv => hRad G S hS hst hnd ⟨m, hm, Or.inr (Or.inr hL)⟩ v hv hvv
  · intro v hv hvv
    by_contra hq
    exact hU33 G S hS hst ⟨hnd, hL⟩ (width_eq_four_of_u33_YS hS hst hnd hL) v hv
      ((AS35YR.Frame.zmod2_cases_YR _).resolve_left hq)

end Setting

end CFSG.LargeExtraspecial
