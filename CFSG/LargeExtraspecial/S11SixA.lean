module

public import CFSG.LargeExtraspecial.S11Dual
public import CFSG.LargeExtraspecial.S11Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

omit [Finite G] in
theorem dual_mul_z_eq {k : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    (u⁻¹ * k) * S.z * (u⁻¹ * k)⁻¹ = u⁻¹ * S.z * u * S.z := by
  calc (u⁻¹ * k) * S.z * (u⁻¹ * k)⁻¹ = u⁻¹ * (k * S.z * k⁻¹) * u := inv_mul_conj_z u k
    _ = u⁻¹ * ((τ : G) * S.z) * u := by rw [hk]
    _ = u⁻¹ * (S.z * τ) * u := by rw [S.z_comm τ.2]
    _ = u⁻¹ * S.z * u * S.z := by rw [hτu]; group

omit [Finite G] in
theorem commute_of_mem_Qa' {k x : G} (hx : x ∈ S.Qa k) :
    x * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * x :=
  (S.conjBy k).z_comm_QG hx

omit [Finite G] in
theorem conj_mem_Qa_of_commute' {k x y : G} (hx : x ∈ S.Qa k)
    (hy : y * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * y) : y * x * y⁻¹ ∈ S.Qa k := by
  have hyM : y ∈ (S.conjBy k).M := by
    rw [(S.conjBy k).mem_M_iff]
    exact hy
  exact (S.conjBy k).conj_mem_QG hyM hx

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.dual_base : (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ ∈ S.QG ∧
    (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ ≠ S.z := by
  refine ⟨by rw [inv_mul_conj_z]; exact (S11.mem_Qa_iff S u _).mp K.mem_Qa, ?_⟩
  rw [inv_mul_conj_z]
  intro h
  apply K.not_mem_QG
  rw [K.conj_eq, show u * S.z * u⁻¹ = g * S.z * g⁻¹ by
    calc u * S.z * u⁻¹ = u * (u⁻¹ * (g * S.z * g⁻¹) * u) * u⁻¹ := by rw [h]
      _ = g * S.z * g⁻¹ := by group]
  exact hy.hyp4.conj_mem

theorem Conf.inf_le_QG_of_conj_mul_z {k : G} (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    S.Qa u ⊓ S.Qa k ≤ S.QG := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hyd := hy.of_conj (K.dual_base hy).1 (K.dual_base hy).2
  have Kd' := Kd.mul_z hyd (dual_mul_z_eq K.conj_eq hk)
  intro β hβ
  by_cases hβ1 : β = 1
  · rw [hβ1]
    exact S.QG.one_mem
  have hβ' : u⁻¹ * β * u ∈ S.QG ⊓ S.Qa (u⁻¹ * k) :=
    ⟨(S11.mem_Qa_iff S u β).mp hβ.1, conj_mem_Qa_inv_mul hβ.2⟩
  have hβ'1 : u⁻¹ * β * u ≠ 1 := fun h => hβ1 (by
    calc β = u * (u⁻¹ * β * u) * u⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨j, hj⟩ := Kd'.exists_conj hyd hβ' hβ'1
  have hβj : (u * j) * S.z * (u * j)⁻¹ = β := by
    calc (u * j) * S.z * (u * j)⁻¹ = u * (j * S.z * j⁻¹) * u⁻¹ := by group
      _ = β := by rw [hj]; group
  have hzτ : S.z ∉ S.Qa u := K.z_not_mem
  have hτQk : (τ : G) ∉ S.Qa k := by
    intro h
    have hne : k * S.z * k⁻¹ ≠ u * S.z * u⁻¹ := by
      rw [hk, ← K.conj_eq]
      intro e
      exact S.z_ne_one (by simpa using e)
    have h1 := S.mem_Qa_symm hne.symm (K.conj_eq ▸ h)
    rw [hk] at h1
    apply hzτ
    have := mul_mem (inv_mem (K.conj_eq ▸ S.conj_z_mem_Qa u)) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hτβ : (τ : G) ∈ S.Qa (u * j) := by
    have hne : (u * j) * S.z * (u * j)⁻¹ ≠ u * S.z * u⁻¹ := by
      rw [hβj, ← K.conj_eq]
      intro e
      exact hτQk (e ▸ hβ.2)
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne (hβj ▸ hβ.1)
  have hτzβ : (τ : G) * S.z ∈ S.Qa (u * j) := by
    have hne : (u * j) * S.z * (u * j)⁻¹ ≠ k * S.z * k⁻¹ := by
      rw [hβj, hk]
      intro e
      apply hzτ
      have := mul_mem (inv_mem (K.conj_eq ▸ S.conj_z_mem_Qa u)) (e ▸ hβ.1)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rw [← hk]
    exact S.mem_Qa_symm hne (hβj ▸ hβ.2)
  have hzβ : S.z ∈ S.Qa (u * j) := by
    have := mul_mem (inv_mem hτβ) hτzβ
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hne : (1 : G) * S.z * (1 : G)⁻¹ ≠ (u * j) * S.z * (u * j)⁻¹ := by
    rw [hβj]
    intro e
    exact hzτ (by rw [show S.z = β by simpa using e]; exact hβ.1)
  have h1 := S.mem_Qa_symm hne (by simpa using hzβ)
  rw [S.Qa_one, hβj] at h1
  exact h1

theorem Conf.commute_of_conj_mul_z (hCE : CentralExtInput.{u_G}) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) {x y : G} (hx : x ∈ S.Qa g ⊓ S.Qa u ⊓ S.M)
    (hyu : y ∈ S.Qa u ⊓ S.M) : x * y = y * x := by
  have K' := K.mul_z hy hk
  have hyu1 : y ∈ S.Qa u := (mem_inf.mp hyu).1
  have hxN : S.ρ ⟨x, hx.2⟩ ∈ Nbar S g t := by
    have h1 := K.Lbar_inf_Nbar_eq hy ⟨hy.hyp4.conj_mem, K.mem_Qa⟩
    have h2 : S.ρ ⟨x, hx.2⟩ ∈ S.Lbar g ⊓ Nbar S g t := by
      rw [h1]
      exact ⟨⟨x, hx.2⟩, mem_subgroupOf.mpr hx, rfl⟩
    exact h2.2
  obtain ⟨x', hx'', hx'eq⟩ := (S4.mem_Lbar S).mp (K'.timmesfeld_11_5 hy hCE hxN)
  have hx'Q : (x' : G) ∈ S.Qa k := (mem_inf.mp hx'').1
  have hτ : (τ : G) = u * S.z * u⁻¹ := K.conj_eq
  have hx'τz : (x' : G) * ((τ : G) * S.z) = (τ : G) * S.z * x' := by
    rw [← hk]
    exact commute_of_mem_Qa' hx'Q
  have hx'z : (x' : G) * S.z = S.z * x' := S.z_comm x'.2
  have hx'τ : (x' : G) * τ = τ * x' := by
    calc (x' : G) * τ = (x' : G) * ((τ : G) * S.z) * S.z := by
          rw [mul_assoc (x' : G), mul_assoc (τ : G), S.z_mul_z, mul_one]
      _ = (τ : G) * S.z * (x' * S.z) := by rw [hx'τz, mul_assoc]
      _ = τ * x' := by rw [hx'z, ← mul_assoc, mul_assoc (τ : G), S.z_mul_z, mul_one]
  have hyτ : y * τ = τ * y := by
    have := commute_of_mem_Qa' hyu1
    rwa [← hτ] at this
  have hyz : y * S.z = S.z * y := S.z_comm hyu.2
  have hyτz : y * ((τ : G) * S.z) = (τ : G) * S.z * y := by
    rw [← mul_assoc, hyτ, mul_assoc, hyz, ← mul_assoc]
  have hc : (x' : G) * y * (x' : G)⁻¹ * y⁻¹ ∈ S.QG := by
    refine K.inf_le_QG_of_conj_mul_z hy hk (mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 := conj_mem_Qa_of_commute' (k := u) hyu1
        (y := (x' : G)) (by rw [← hτ]; exact hx'τ)
      exact mul_mem h1 (inv_mem hyu1)
    · have h1 := conj_mem_Qa_of_commute' (k := k) (inv_mem hx'Q) (y := y)
        (by rw [hk]; exact hyτz)
      rw [show (x' : G) * y * (x' : G)⁻¹ * y⁻¹ = x' * (y * (x' : G)⁻¹ * y⁻¹) by group]
      exact mul_mem hx'Q h1
  have hρ1 : S.ρ (x' * ⟨y, hyu.2⟩ * x'⁻¹ * ⟨y, hyu.2⟩⁻¹) = 1 := (S.ρ_eq_one_iff _).mpr hc
  have hρ2 : S.ρ (⟨x, hx.2⟩ * ⟨y, hyu.2⟩ * ⟨x, hx.2⟩⁻¹ * ⟨y, hyu.2⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hx'eq, ← map_inv, ← map_inv, ← map_mul,
      ← map_mul, ← map_mul]
    exact hρ1
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ S.QG := (S.ρ_eq_one_iff _).mp hρ2
  rcases (S.conjBy u).commutator_eq_one_or_z hx.1.2 hyu1 with h | h
  · calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  · exfalso
    apply K.not_mem_QG
    have h4 : (S.conjBy u).z ∈ S.QG := h ▸ h3
    rw [hτ]
    exact h4

theorem Conf.commute_of_conj_mul_z' (hCE : CentralExtInput.{u_G}) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) {x y : G}
    (hx : x ∈ S.Qa g ⊓ S.QG ⊓ centralizer ({(τ : G)} : Set G))
    (hyc : y ∈ S.QG ⊓ centralizer ({(τ : G)} : Set G)) : x * y = y * x := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hyd := hy.of_conj (K.dual_base hy).1 (K.dual_base hy).2
  have hk' := dual_mul_z_eq K.conj_eq hk
  have hτ : (τ : G) = u * S.z * u⁻¹ := K.conj_eq
  have hconjM : ∀ v : G, v ∈ centralizer ({(τ : G)} : Set G) → u⁻¹ * v * u ∈ S.M := by
    intro v hv
    have hv' : v * τ = τ * v := mem_centralizer_singleton_iff.mp hv
    rw [S.mem_M_iff]
    calc u⁻¹ * v * u * S.z = u⁻¹ * (v * (u * S.z * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * S.z * u⁻¹) * v) * u := by rw [← hτ, hv']
      _ = S.z * (u⁻¹ * v * u) := by group
  have hconjQ : ∀ v : G, v ∈ S.QG → u⁻¹ * v * u ∈ S.Qa u⁻¹ := fun v hv => by
    have := conj_mem_Qa_inv_mul (S := S) (w := u) (k := 1) (by rw [S.Qa_one]; exact hv)
    simpa using this
  have hx1 : x ∈ S.Qa g := (mem_inf.mp (mem_inf.mp hx).1).1
  have hx2 : x ∈ S.QG := (mem_inf.mp (mem_inf.mp hx).1).2
  have hx3 : x ∈ centralizer ({(τ : G)} : Set G) := (mem_inf.mp hx).2
  have hy2 : y ∈ S.QG := (mem_inf.mp hyc).1
  have hy3 : y ∈ centralizer ({(τ : G)} : Set G) := (mem_inf.mp hyc).2
  have key := Kd.commute_of_conj_mul_z hyd hCE hk' (x := u⁻¹ * x * u) (y := u⁻¹ * y * u)
    (mem_inf.mpr ⟨mem_inf.mpr ⟨conj_mem_Qa_inv_mul hx1, hconjQ x hx2⟩, hconjM x hx3⟩)
    (mem_inf.mpr ⟨hconjQ y hy2, hconjM y hy3⟩)
  have := congrArg (fun v => u * v * u⁻¹) key
  simpa [mul_assoc] using this

end CFSG.LargeExtraspecial.S11
