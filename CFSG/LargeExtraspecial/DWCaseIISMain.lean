module

public import CFSG.LargeExtraspecial.DWCaseIISSection
public import CFSG.LargeExtraspecial.DWCaseIIBConfig
public import CFSG.LargeExtraspecial.DWTransCaseI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem exists_invariant_complement (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G)) (hS : SpConfig S A hM) :
    ∃ W : Submodule (ZMod 2) S.Qt, (∀ w ∈ W, S.q w = 0) ∧ W ⊓ S.clSub A = ⊥ ∧
      finrank (ZMod 2) W = S.width ∧
      ∀ x : S.Mbar, ∀ w ∈ W, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨ω, hnd, hωa, hrange⟩ := hS
  have hUsing : ∀ u ∈ S.clSub A, S.q u = 0 := fun u hu => q_clSub hu
  have h6 : 6 ≤ finrank (ZMod 2) (S.clSub A) := by
    obtain ⟨k, hk⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) hωa hnd
    have := hA.finrank_clSub
    omega
  let ρE : S.Mbar →* (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.O.subtype.comp S.Mbar.subtype
  have hρq : ∀ g x, S.q (ρE g x) = S.q x := fun g x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (g : S.O).2 x
  have hrω : ∀ g x y, ω (resAt S A hM g x) (resAt S A hM g y) = ω x y := fun g =>
    (hrange _).mp ⟨g, rfl⟩
  have hrt : ∀ v, ∃ g, ∀ x, resAt S A hM g x = x + ω x v • v := by
    intro v
    obtain ⟨g, hg⟩ := (hrange (LinearEquiv.ofInvolutive (tv ω v) (tv_tv ω hωa v))).mpr
      (fun x y => tv_isometry hωa v x y)
    exact ⟨g, fun x => by rw [hg]; rfl⟩
  have hker : ∀ g, resAt S A hM g = 1 → ρE g = 1 := fun g hg => by
    rw [hA.resAt_injective hM (hg.trans (map_one _).symm), map_one]
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_invariant_section S.q_nondegenerate hUsing
    hA.orthogonal_clSub hωa hnd h6 ρE (resAt S A hM) hρq (fun g u => rfl) hrω hrt hker
  have hinj : Function.Injective σ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).mpr (hnd.1 x fun a => ?_)
    rw [← hσ1, hx, polar_zero_left]
  refine ⟨LinearMap.range σ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hσ2 x
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, rfl⟩, hxU⟩
    have hx : x = 0 := hnd.1 x fun a => by
      rw [← hσ1]
      exact polar_eq_zero_of_mem hUsing hxU a.2
    rw [hx, map_zero]
    exact zero_mem _
  · rw [LinearMap.finrank_range_of_inj hinj, hA.finrank_clSub]
  · rintro g _ ⟨x, rfl⟩
    exact ⟨resAt S A hM g x, (hσ3 g x).symm⟩

end MaxEA

theorem caseII_of_sp (hA : MaxEA S A) (h5 : 5 ≤ S.width) (hM : S.M ≤ normalizer (A : Set G))
    {g : G} (hgA : g * S.z * g⁻¹ ∈ A) (hgz : g * S.z * g⁻¹ ≠ S.z) (hS : SpConfig S A hM) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) := by
  obtain ⟨W, hWq, hWU, hWdim, hWinv⟩ := hA.exists_invariant_complement h5 hM hS
  have hWpolar : ∀ u ∈ W, ∀ v ∈ W, polar S.q u v = 0 := fun u hu v hv =>
    polar_eq_zero_of_mem hWq hu hv
  have hEA : IsElementaryAbelian 2 (S.clPre W) :=
    { is_comm := ⟨fun x y => Subtype.ext ((S.polar_cl_eq_zero_iff x.2.1 y.2.1).mp
        (hWpolar _ x.2.2 _ y.2.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using (S.q_cl_eq_zero_iff x.2.1).mp (hWq _ x.2.2)) }
  have hB : MaxEA S (S.clPre W) :=
    ⟨S.clPre_le_QG W, by rw [S.card_clPre, S.card_submodule, hWdim, pow_succ, mul_comm]⟩
  have key : ∀ m ∈ S.M, ∀ n ∈ S.clPre W, m * n * m⁻¹ ∈ S.clPre W := by
    intro m hm n hn
    refine S.mem_clPre.mpr ⟨S.conj_mem_QG hm (S.mem_clPre.mp hn).1, ?_⟩
    rw [← S.ρ_cl ⟨m, hm⟩ (S.mem_clPre.mp hn).1]
    exact hWinv ⟨S.ρ ⟨m, hm⟩, ⟨m, hm⟩, rfl⟩ _ (S.mem_clPre.mp hn).2
  have hMB : S.M ≤ normalizer (S.clPre W : Set G) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro n
    refine ⟨key m hm n, fun h => ?_⟩
    have h1 := key m⁻¹ (S.M.inv_mem hm) _ h
    rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
      mul_one] at h1
  have hxQ : g * S.z * g⁻¹ ∈ S.QG := hA.le_QG hgA
  have hxB : g * S.z * g⁻¹ ∉ S.clPre W := by
    intro hx
    have h1 : S.cl (g * S.z * g⁻¹) ∈ W ⊓ S.clSub A :=
      ⟨(S.mem_clPre.mp hx).2, S.cl_mem_clSub hgA hxQ⟩
    rw [hWU, Submodule.mem_bot, S.cl_eq_zero_iff hxQ] at h1
    rcases h1 with h | h
    · exact S.z_ne_one (by simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) h)
    · exact hgz h
  exact hB.nonempty_centralizer_mulEquiv_of_not_mem h5 hMB hxQ hxB

end CFSG.LargeExtraspecial.DW
