module

public import CFSG.LargeExtraspecial.AS35YSIrr
public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LargeExtraspecial.AS35YRSet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace AS35YT

variable {X V : Type} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem exists_finrank_eq_two_mul (hq : q.polarBilin.Nondegenerate) :
    ∃ k, finrank (ZMod 2) V = 2 * k := by
  have hev := S2.sp_even_finrank (f := q.polarBilin) (fun x => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul,
      ZModModule.add_self]) hq
  obtain ⟨k, hk⟩ := hev
  exact ⟨k, by omega⟩

theorem card_dvd_spOrd (hq : q.polarBilin.Nondegenerate) {k : ℕ}
    (hk : finrank (ZMod 2) V = 2 * k) (ρ : X →* (V ≃ₗ[ZMod 2] V)) (hinj : Function.Injective ρ)
    (hiso : ∀ x v, q (ρ x v) = q v) :
    Nat.card X ∣ 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) := by
  rw [← S12DW.card_orthogonalGroup_mul_ncard_eq hq hk]
  have hmem : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup q := fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hiso x)
  have hinj' : Function.Injective (ρ.codRestrict _ hmem) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  exact (Subgroup.card_dvd_of_injective _ hinj').mul_right _

theorem two_mul_card_le_spOrd (hq : q.polarBilin.Nondegenerate) {k : ℕ}
    (hk : finrank (ZMod 2) V = 2 * k) (ρ : X →* (V ≃ₗ[ZMod 2] V)) (hinj : Function.Injective ρ)
    (hiso : ∀ x v, q (ρ x v) = q v) {v : V} (hv0 : v ≠ 0) (hqv : q v = 0) :
    2 * Nat.card X ≤ 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := AS35YR.finite_linearEquiv_YR
  rw [← S12DW.card_orthogonalGroup_mul_ncard_eq hq hk]
  have hle : Nat.card X ≤ Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) :=
    Nat.card_le_card_of_injective
      (fun x => (⟨ρ x, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hiso x)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup q))
      fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hZ : 2 ≤ {x | q x = 0}.ncard := by
    have hsub : ({0, v} : Set V) ⊆ {x | q x = 0} := by
      rintro x (rfl | rfl)
      · exact map_zero _
      · exact hqv
    calc 2 = ({0, v} : Set V).ncard := (Set.ncard_pair (Ne.symm hv0)).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  calc 2 * Nat.card X ≤ 2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) :=
        Nat.mul_le_mul_left _ hle
    _ = Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) * 2 := mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ hZ

end AS35YT

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem a2Action_V0_YT (hS : S.SixHyp) (hst : S.Asc512Standing) (hc : center S.LbarAsc = ⊥)
    (h : RadSing_YS S) : A2Mod.A2Action S.EhatAsc (q0_YS h) (rhoX_YS hst hc) := by
  refine ⟨q0_YS_nondegenerate h, rhoX_YS_injective hst hc, fun x v => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center S.LbarAsc) x
    rw [rhoX_YS_mk, actL_YS_apply]
    exact q0_act0_YS h hst _ v
  · rintro _ ⟨l, hl, rfl⟩
    rw [rhoX_YS_mk, actL_YS_apply]
    exact isTypeA_act0_YS hS hst h hl

theorem irred_rhoX_YT (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hc : center S.LbarAsc = ⊥) (h5127 : S14.Asc512FiveTwelveSevenStmt) (h : RadSing_YS S) :
    ∀ Z : Submodule (ZMod 2) (V0_YS S), (∀ x, ∀ z ∈ Z, rhoX_YS hst hc x z ∈ Z) →
      Z = ⊥ ∨ Z = ⊤ := by
  intro Z hZ
  refine irred_V0_YS hS hst hnd h5127 h Z fun l hl z hz => ?_
  have := hZ (QuotientGroup.mk' (center S.LbarAsc) ⟨l, hl⟩) z hz
  rwa [rhoX_YS_mk, actL_YS_apply] at this

theorem exists_sing_V0_YT (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S) : ∃ v : V0_YS S, v ≠ 0 ∧ q0_YS h v = 0 := by
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  have hA := isTypeA_act0_YS hS hst h ht₀
  have hne : commSpace (act0_YS hst ⟨t₀, DbarAsc_subset_Mbar_YL ht₀⟩) ≠ ⊥ := by
    intro hb
    have h2 := hA.2.2.2.1
    rw [hb, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, hv0, hA.2.2.2.2 v hv⟩

end Setting

end CFSG.LargeExtraspecial
