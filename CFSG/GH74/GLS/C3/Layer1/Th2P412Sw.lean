module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Cls
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem mem_aT {s : G} (hs : s ∈ S) (hsT : s ∉ T) : a⁻¹ * s ∈ T :=
  (F.S_cases s hs).resolve_left hsT

theorem a_P_a_inv {p : G} (hp : p ∈ T ⊓ K) : a * p * a⁻¹ ∈ conjugate (T ⊓ K) a := by
  rw [mem_conjugate_iff']
  have e : a * (a * p * a⁻¹) * a⁻¹ = (a * a) * p * (a * a)⁻¹ := by group
  rw [e]
  exact F.core.P_norm _ F.core.a_sq_mem p hp

theorem swap_P {s p : G} (hs : s ∈ S) (hsT : s ∉ T) (hp : p ∈ T ⊓ K) :
    s * p * s⁻¹ ∈ conjugate (T ⊓ K) a := by
  have hτ := F.mem_aT hs hsT
  have e : s * p * s⁻¹ = a * ((a⁻¹ * s) * p * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
  rw [e]
  exact F.a_P_a_inv (F.core.P_norm _ hτ p hp)

theorem swap_P' {s w : G} (hs : s ∈ S) (hsT : s ∉ T) (hw : w ∈ conjugate (T ⊓ K) a) :
    s * w * s⁻¹ ∈ T ⊓ K := by
  have hτ := F.mem_aT hs hsT
  have e : s * w * s⁻¹ = a * ((a⁻¹ * s) * w * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
  rw [e]
  exact mem_conjugate_iff'.1 (F.core.conj_norm F.core.P_norm _ hτ w hw)

theorem T_central_x : ∀ t ∈ T, t * x * t⁻¹ = x := fun t ht => by
  have h := Subgroup.mem_centralizer_singleton_iff.1 (F.T_le_C ht)
  rw [h]; group

theorem T_central_z [Finite G] : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
  have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ ht
  obtain ⟨p, hp, q, hq, rfl⟩ := CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
  have h1 : p * z = z * p := F.z_central p hp
  have h2 : q * z = z * q := (F.core.comm_P_conj z F.z_mem q hq).symm
  calc p * q * z * (p * q)⁻¹ = p * (q * z) * q⁻¹ * p⁻¹ := by group
    _ = p * (z * q) * q⁻¹ * p⁻¹ := by rw [h2]
    _ = (p * z) * p⁻¹ := by group
    _ = (z * p) * p⁻¹ := by rw [h1]
    _ = z := by group

theorem a_z : a * z * a⁻¹ = x := by
  have h1 : a * z * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by
    calc a * z * a⁻¹ = a * (a * x * a⁻¹) * a⁻¹ := by rw [F.a_x]
      _ = (a * a) * x * (a * a)⁻¹ := by group
  rw [h1]
  exact F.T_central_x _ F.core.a_sq_mem

theorem swap_x {s : G} (hs : s ∈ S) (hsT : s ∉ T) : s * x * s⁻¹ = z := by
  have hτ := F.mem_aT hs hsT
  have e : s * x * s⁻¹ = a * ((a⁻¹ * s) * x * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
  rw [e, F.T_central_x _ hτ, F.a_x]

theorem exists_conj_of_involutions [Finite G] {s s' : G} (hs : s ∈ S) (hsT : s ∉ T)
    (hs' : s' ∈ S) (hs'T : s' ∉ T) (hs2 : s * s = 1) (hs'2 : s' * s' = 1) :
    ∃ u ∈ T ⊓ K, u * s * u⁻¹ = s' := by
  have hτ := F.mem_aT hs hsT
  have hτ' := F.mem_aT hs' hs'T
  have htT : s' * s⁻¹ ∈ T := by
    have e : s' * s⁻¹ = a * ((a⁻¹ * s') * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
    rw [e]
    exact F.core.a_norm (T.mul_mem hτ' (T.inv_mem hτ))
  have ht' : s' * s⁻¹ ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ htT
  obtain ⟨t₁, ht₁, t₂, ht₂, htt⟩ := CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hconj : s * (s' * s⁻¹) * s⁻¹ = (s' * s⁻¹)⁻¹ := by
    rw [hsi]
    calc s * (s' * s) * s = s * s' * (s * s) := by group
      _ = s * s' := by rw [hs2, mul_one]
      _ = (s' * s)⁻¹ := by rw [mul_inv_rev, hsi, hs'i]
  have hq : s * t₁ * s⁻¹ ∈ conjugate (T ⊓ K) a := F.swap_P hs hsT ht₁
  have hp : s * t₂ * s⁻¹ ∈ T ⊓ K := F.swap_P' hs hsT ht₂
  have hE1 : (s * t₁ * s⁻¹) * (s * t₂ * s⁻¹) = (t₁ * t₂)⁻¹ := by
    have h1 : (s * t₁ * s⁻¹) * (s * t₂ * s⁻¹) = s * (t₁ * t₂) * s⁻¹ := by group
    rw [h1, ← htt, hconj]
  have hE2 : (s * t₂ * s⁻¹) * (s * t₁ * s⁻¹) = t₁⁻¹ * t₂⁻¹ := by
    rw [F.core.comm_P_conj _ hp _ hq, hE1, mul_inv_rev]
    exact (F.core.comm_P_conj t₁⁻¹ (Subgroup.inv_mem _ ht₁) t₂⁻¹ (Subgroup.inv_mem _ ht₂)).symm
  obtain ⟨-, hqeq⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj hp (Subgroup.inv_mem _ ht₁)
    hq (Subgroup.inv_mem _ ht₂) hE2
  refine ⟨t₁, ht₁, ?_⟩
  calc t₁ * s * t₁⁻¹ = t₁ * (s * t₁⁻¹ * s⁻¹) * s := by group
    _ = t₁ * (s * t₁ * s⁻¹)⁻¹ * s := by rw [show s * t₁⁻¹ * s⁻¹ = (s * t₁ * s⁻¹)⁻¹ by group]
    _ = t₁ * t₂ * s := by rw [hqeq, inv_inv]
    _ = s' := by rw [← htt]; group

end Frame

end CFSG.GH74.GLS.Th2.P43f
