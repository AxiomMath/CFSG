module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSylow
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G Γ : Type*} [Group G] [Group Γ] {X D : Subgroup G} {ψ : ↥X →* Γ}

theorem map_subgroupOf_le_map_subgroupOf_iff (hker : ψ.ker = D.subgroupOf X)
    {K K' : Subgroup G} (hKX : K ≤ X) (hDK' : D ≤ K') :
    (K.subgroupOf X).map ψ ≤ (K'.subgroupOf X).map ψ ↔ K ≤ K' := by
  constructor
  · intro h
    rw [Subgroup.map_le_map_iff, hker] at h
    have hsup : K'.subgroupOf X ⊔ D.subgroupOf X = K'.subgroupOf X :=
      sup_eq_left.mpr fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hDK' (Subgroup.mem_subgroupOf.mp hx))
    rw [hsup] at h
    intro k hk
    have hk' : (⟨k, hKX hk⟩ : ↥X) ∈ K.subgroupOf X := Subgroup.mem_subgroupOf.mpr hk
    exact Subgroup.mem_subgroupOf.mp (h hk')
  · intro h
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem map_subgroupOf_inj (hker : ψ.ker = D.subgroupOf X) {K K' : Subgroup G} (hKX : K ≤ X)
    (hK'X : K' ≤ X) (hDK : D ≤ K) (hDK' : D ≤ K') :
    (K.subgroupOf X).map ψ = (K'.subgroupOf X).map ψ ↔ K = K' := by
  constructor
  · intro h
    exact le_antisymm
      ((map_subgroupOf_le_map_subgroupOf_iff hker hKX hDK').mp h.le)
      ((map_subgroupOf_le_map_subgroupOf_iff hker hK'X hDK).mp h.ge)
  · intro h
    rw [h]

theorem map_subgroupOf_inf (hker : ψ.ker = D.subgroupOf X) (K : Subgroup G) {K' : Subgroup G}
    (hDK' : D ≤ K') :
    ((K ⊓ K').subgroupOf X).map ψ = (K.subgroupOf X).map ψ ⊓ (K'.subgroupOf X).map ψ := by
  apply le_antisymm
  · rw [show (K ⊓ K').subgroupOf X = K.subgroupOf X ⊓ K'.subgroupOf X from
      Subgroup.comap_inf K K' X.subtype]
    exact Subgroup.map_inf_le _ _ _
  · rintro y ⟨hyK, hyK'⟩
    obtain ⟨a, haK, rfl⟩ := Subgroup.mem_map.mp hyK
    obtain ⟨b, hbK', hb⟩ := Subgroup.mem_map.mp hyK'
    have hmem : b⁻¹ * a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
    have hD : (↑(b⁻¹ * a) : G) ∈ D :=
      Subgroup.mem_subgroupOf.mp (hker ▸ hmem)
    have haK'G : (↑a : G) ∈ K' := by
      have haeq : (↑a : G) = (↑b : G) * (↑(b⁻¹ * a) : G) := by
        rw [← Subgroup.coe_mul]
        exact (congrArg Subtype.val (mul_inv_cancel_left b a)).symm
      rw [haeq]
      exact K'.mul_mem (Subgroup.mem_subgroupOf.mp hbK') (hDK' hD)
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr
      ⟨Subgroup.mem_subgroupOf.mp haK, haK'G⟩, rfl⟩

theorem map_subgroupOf_eq_bot (hker : ψ.ker = D.subgroupOf X) {K : Subgroup G} (hKD : K ≤ D) :
    (K.subgroupOf X).map ψ = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, hker]
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (hKD (Subgroup.mem_subgroupOf.mp hx))

theorem card_map_subgroupOf (hker : ψ.ker = D.subgroupOf X) {K : Subgroup G} (hKX : K ≤ X) :
    Nat.card ((K.subgroupOf X).map ψ) = D.relIndex K := by
  rw [← Subgroup.relIndex_ker (K.subgroupOf X) ψ, hker]
  exact Subgroup.relIndex_subgroupOf hKX

theorem nonempty_mulEquiv_map_subgroupOf (hker : ψ.ker = D.subgroupOf X) {K : Subgroup G}
    (hKX : K ≤ X) [(D.subgroupOf K).Normal] :
    Nonempty (↥((K.subgroupOf X).map ψ) ≃* ↥K ⧸ D.subgroupOf K) := by
  let f : ↥K →* Γ := ψ.comp (Subgroup.inclusion hKX)
  have hrange : f.range = (K.subgroupOf X).map ψ := by
    change (ψ.comp (Subgroup.inclusion hKX)).range = (K.subgroupOf X).map ψ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range hKX]
  have hker' : f.ker = D.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψ (Subgroup.inclusion hKX k) = 1 ↔ (k : G) ∈ D
    rw [← MonoidHom.mem_ker (f := ψ), hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker'))⟩

theorem isSylowOf_map_subgroupOf [Finite G] [Finite Γ] {p : ℕ} [Fact p.Prime] {K S : Subgroup G}
    (hKX : K ≤ X) (hS : IsSylowOf p S K) :
    IsSylowOf p ((S.subgroupOf X).map ψ) ((K.subgroupOf X).map ψ) := by
  have hS' : IsSylowOf p (S.subgroupOf X) (K.subgroupOf X) := by
    rw [isSylowOf_iff]
    obtain ⟨hle, hP, hdvd⟩ := isSylowOf_iff.mp hS
    exact ⟨fun x hx => hle (Subgroup.mem_subgroupOf.mp hx), hP.comap_subtype,
      by rwa [Subgroup.relIndex_subgroupOf hKX]⟩
  obtain ⟨Q, hQ⟩ := hS'
  let φ : ↥(K.subgroupOf X) →* ↥((K.subgroupOf X).map ψ) := ψ.subgroupMap (K.subgroupOf X)
  have hφ : Function.Surjective φ := ψ.subgroupMap_surjective (K.subgroupOf X)
  refine ⟨Q.mapSurjective hφ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : ((K.subgroupOf X).map ψ).subtype.comp φ =
      ψ.comp (K.subgroupOf X).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hQ]

theorem normalizer_map_subgroupOf [Finite G] (hψ : Function.Surjective ψ)
    (hker : ψ.ker = D.subgroupOf X) (hDX : D ≤ X) {S : Subgroup G} (hSX : S ≤ X)
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.relIndex D) :
    normalizer (((S.subgroupOf X).map ψ : Subgroup Γ) : Set Γ) =
      ((X ⊓ normalizer (S : Set G)).subgroupOf X).map ψ := by
  have hDnorm : (D.subgroupOf X).Normal := hker ▸ MonoidHom.normal_ker ψ
  have hSD : S ≤ Subgroup.normalizer (D : Set G) :=
    hSX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mp hDnorm)
  have hidx : ¬ 2 ∣ (S.subgroupOf X).relIndex ((S.subgroupOf X) ⊔ ψ.ker) := by
    rw [hker, ← Subgroup.subgroupOf_sup hSX hDX, Subgroup.relIndex_subgroupOf (sup_le hSX hDX),
      (relIndex_sup_eq_relIndex_inf_of_le_normalizer hSD).1, Subgroup.inf_relIndex_right]
    exact hodd
  have hlit := CFSG.OddStandard.HigherRank.YamadaG23.lit_normalizer_map ψ hψ
    (A := S.subgroupOf X) hS.comap_subtype hidx
  have hnorm : normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (X ⊓ normalizer (S : Set G)).subgroupOf X := by
    rw [← Subgroup.subgroupOf_normalizer_eq hSX, Subgroup.inf_subgroupOf_left]
  rw [hlit, hnorm]

end CFSG.GroupTheory
