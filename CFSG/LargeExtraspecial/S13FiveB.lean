module

public import CFSG.LargeExtraspecial.S13FiveA
public import CFSG.LargeExtraspecial.S13SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem comm_commute_K {l y : S.O} (hl : l ∈ S.Lbar g) (hlE : l ∉ Ebar S g K)
    (hyM : y ∈ S.Mbar) {k : S.O} (hk : k ∈ K) :
    k * (l * y * l⁻¹ * y⁻¹) = (l * y * l⁻¹ * y⁻¹) * k := by
  have hinv := Y.inv_of_not_mem hl hlE
  have hk' : y⁻¹ * k * y ∈ K := by
    have := Y.normal _ (inv_mem hyM) k hk
    simpa using this
  have h1 : l * (y⁻¹ * k * y)⁻¹ * l⁻¹ = y⁻¹ * k * y := by
    rw [hinv _ (inv_mem hk'), inv_inv]
  have h2 := hinv k hk
  have e : (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹ = k := by
    calc (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹
        = l * y * (l⁻¹ * (y⁻¹ * k * y) * l) * y⁻¹ * l⁻¹ := by group
      _ = l * y * (l⁻¹ * (l * (y⁻¹ * k * y)⁻¹ * l⁻¹) * l) * y⁻¹ * l⁻¹ := by rw [h1]
      _ = (l * k * l⁻¹)⁻¹ := by group
      _ = k := by rw [h2, inv_inv]
  calc k * (l * y * l⁻¹ * y⁻¹)
      = (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹ * (l * y * l⁻¹ * y⁻¹) := by rw [e]
    _ = (l * y * l⁻¹ * y⁻¹) * k := by group

omit Y in
theorem comm_commute_K' (hN : NormalInMbar S K) {l y : S.O} (hl : ∀ k ∈ K, k * l = l * k)
    (hyM : y ∈ S.Mbar) {k : S.O} (hk : k ∈ K) :
    k * (l * y * l⁻¹ * y⁻¹) = (l * y * l⁻¹ * y⁻¹) * k := by
  have hk' : y⁻¹ * k * y ∈ K := by
    have := hN _ (inv_mem hyM) k hk
    simpa using this
  have h1 := hl _ hk'
  have h2 := hl k hk
  have e1 : l⁻¹ * (y⁻¹ * k * y) * l = y⁻¹ * k * y := by
    rw [mul_assoc, h1]; group
  have e2 : l * k * l⁻¹ = k := by rw [← h2]; group
  have e : (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹ = k := by
    calc (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹
        = l * y * (l⁻¹ * (y⁻¹ * k * y) * l) * y⁻¹ * l⁻¹ := by group
      _ = l * k * l⁻¹ := by rw [e1]; group
      _ = k := e2
  calc k * (l * y * l⁻¹ * y⁻¹)
      = (l * y * l⁻¹ * y⁻¹) * k * (l * y * l⁻¹ * y⁻¹)⁻¹ * (l * y * l⁻¹ * y⁻¹) := by rw [e]
    _ = (l * y * l⁻¹ * y⁻¹) * k := by group

theorem conj_mem_Lbar_of_fix {c m : S.M} {l : S.O} (hl : l ∈ S.Lbar ((c : G) * g))
    (hfix : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹)) =
      S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹)) :
    S.ρ m * l * (S.ρ m)⁻¹ ∈ S.Lbar ((c : G) * g) := by
  have h1 := conj_mem_Lbar_mul S m hl
  have hcQ := conj_mem_QG' S c.2 Y.haQ
  have e : ((m : G) * ((c : G) * g)) = ((m * c : S.M) : G) * g := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [e] at h1
  rwa [Lbar_eq_of_cl_eq S hcQ (conj_ne_z' S c.2 Y.hne) (conj_mem_QG' S (m * c).2 Y.haQ)
    (by rw [← e, ← ρ_cl_conj_z S m hcQ, hfix])] at h1

omit Y in
theorem comm_eq_of_moved (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {τ t : S.O}
    (hτ : τ ∈ S.Lbar g) (hτE : τ ∉ Ebar S g K) (ht : t ∈ Ebar S g K) {x c w m : S.M}
    (hτc : τ ∈ S.Lbar ((c : G) * g)) (htc : t ∈ S.Lbar ((c : G) * g))
    (hτw : τ ∈ S.Lbar ((w : G) * g)) (htw : t ∈ S.Lbar ((w : G) * g))
    (hy : S.ρ m ∈ S.Lbar ((x : G) * g))
    (hτN : τ ∈ normalizer (S.Lbar ((x : G) * g) : Set S.O))
    (htN : t ∈ normalizer (S.Lbar ((x : G) * g) : Set S.O))
    (hfix : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹)) =
      S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹))
    (hmove : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((w : G) * g * S.z * ((w : G) * g)⁻¹)) =
        S.cl ((w : G) * g * S.z * ((w : G) * g)⁻¹) + S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹))
    (hxV : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∉ Vt S g t)
    {U : Submodule (ZMod 2) S.Qt}
    (hL : ∀ m' : S.M, τ ∈ S.Lbar ((m' : G) * g) →
      S.cl ((m' : G) * g * S.z * ((m' : G) * g)⁻¹) ∈ U)
    (hwU : S.cl ((w : G) * g * S.z * ((w : G) * g)⁻¹) ∈ U)
    (hxU : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∉ U) :
    τ * S.ρ m * τ⁻¹ = t * S.ρ m * t⁻¹ := by
  have hyM : S.ρ m ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨m, rfl⟩
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have Yx : Hyp13 S ((x : G) * g) K := Y.mul rfl
  have hwQ := conj_mem_QG' S w.2 Y.haQ
  have hpt : S.cl (((m * w : S.M) : G) * g * S.z * (((m * w : S.M) : G) * g)⁻¹) =
      S.cl ((w : G) * g * S.z * ((w : G) * g)⁻¹) +
        S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) := by
    rw [← hmove, ρ_cl_conj_z S m hwQ, Subgroup.coe_mul, mul_assoc (m : G) (w : G) g]
  have hmw : ∀ {l : S.O}, l ∈ S.Lbar ((w : G) * g) → l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ = 1 →
      l ∈ S.Lbar (((m * w : S.M) : G) * g) := by
    intro l hl h1
    have e : S.ρ m * l * (S.ρ m)⁻¹ = l := by
      have h2 : l * S.ρ m * l⁻¹ = S.ρ m := mul_inv_eq_one.mp h1
      calc S.ρ m * l * (S.ρ m)⁻¹ = (l * S.ρ m * l⁻¹) * l * (S.ρ m)⁻¹ := by rw [h2]
        _ = l := by group
    have h3 := conj_mem_Lbar_mul S m hl
    rwa [e, ← mul_assoc, ← Subgroup.coe_mul] at h3
  have hmem : ∀ {l : S.O}, l ∈ S.Lbar ((c : G) * g) →
      l ∈ normalizer (S.Lbar ((x : G) * g) : Set S.O) →
      (∀ k ∈ K, k * (l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹) = (l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹) * k) →
      l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ Ebar S ((c : G) * g) K ⊓ Ebar S ((x : G) * g) K := by
    intro l hlc hlN hK
    have hx : l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ S.Lbar ((x : G) * g) :=
      mul_mem ((mem_normalizer_iff.mp hlN _).mp hy) (inv_mem hy)
    have hc : l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ ∈ S.Lbar ((c : G) * g) := by
      have h1 := Y.conj_mem_Lbar_of_fix (inv_mem hlc) hfix
      rw [show l * S.ρ m * l⁻¹ * (S.ρ m)⁻¹ = l * (S.ρ m * l⁻¹ * (S.ρ m)⁻¹) by group]
      exact mul_mem hlc h1
    exact Subgroup.mem_inf.mpr ⟨(mem_Ebar).mpr ⟨hc, hK⟩, (mem_Ebar).mpr ⟨hx, hK⟩⟩
  have hτm := hmem hτc hτN (fun k hk => Y.comm_commute_K hτ hτE hyM hk)
  have htm := hmem htc htN (fun k hk =>
    comm_commute_K' Y.normal (fun k hk => ((mem_Ebar).mp ht).2 k hk) hyM hk)
  have hτ1 : τ * S.ρ m * τ⁻¹ * (S.ρ m)⁻¹ ≠ 1 := by
    intro h1
    have h2 := hL _ (hmw hτw h1)
    rw [hpt] at h2
    exact hxU (by simpa using sub_mem h2 hwU)
  have ht1 : t * S.ρ m * t⁻¹ * (S.ρ m)⁻¹ ≠ 1 := by
    intro h1
    have h2 := cl_mem_Vt (hmw htw h1)
    rw [hpt] at h2
    exact hxV (by simpa using sub_mem h2 (cl_mem_Vt htw))
  have hne : Fbar S ((x : G) * g) K ≠ Fbar S ((c : G) * g) K := by
    intro h
    apply hxV
    have h1 : S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) ∈ Fbar S ((x : G) * g) K :=
      cl_mem_Fbar Yx.H
    rw [h] at h1
    exact Yc.Fbar_le_Vt (g₀ := g) (h₀ := c) rfl
      ((mem_Ebar).mpr ⟨htc, ((mem_Ebar).mp ht).2⟩) h1
  have heq := eq_of_mem_Ebar_inf hCE Yc (h := x * c⁻¹) (coe_mul_inv_mul x c g).symm hne hτm htm
    hτ1 ht1
  exact mul_right_cancel heq

end Hyp13

end CFSG.LargeExtraspecial.S13
