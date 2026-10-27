module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04y
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05
public import CFSG.ClassicalInvolution.Asc77.AscS24BHyp

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

namespace Ctx8Frame

theorem r_conj_j : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]

theorem t_conj_j : C.D.F.ρ'.r * C.D.F.j * C.D.F.ρ'.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.t₃, C.D.comm23.symm.mul_pow, C.x₂_sq]

theorem comm_jz : C.D.F.j * z = z * C.D.F.j :=
  Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW _
    (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2) z C.hd.hzW

theorem J_ne_K : C.D.F.ρ₃.K ≠ K := fun h => C.D.F.hne₁ (C.hK.trans h.symm)

theorem J_ne_K' : C.D.F.ρ₃.K ≠ K' := fun h => C.D.F.hne₂ (C.hK'.trans h.symm)

theorem J_inf_W : C.D.F.ρ₃.K ⊓ W = Subgroup.zpowers C.D.x₃ := by
  have hle : Subgroup.zpowers C.D.x₃ ≤ C.D.F.ρ₃.K ⊓ W :=
    Subgroup.zpowers_le.mpr ⟨C.x₃_mem_J, C.D.x₃_mem⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [C.card_J_inf_W, Nat.card_zpowers, C.orderOf_x₃]

end Ctx8Frame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure HFrame (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  C : Ctx8Frame Ω K K' W S R R' z u
  a : G
  T₃ : Subgroup G
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haR : R ≤ Subgroup.centralizer ({a} : Set G)
  haR' : R' ≤ Subgroup.centralizer ({a} : Set G)
  hT : IsSylow2In T₃ C.D.F.ρ₃.K
  hTN : T₃ ≤ Subgroup.normalizer (W : Set G)
  hTa : T₃ ≤ Subgroup.centralizer ({a} : Set G)

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame

theorem comm_R {x : G} (hx : x ∈ R) : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR hx)

theorem comm_R' {x : G} (hx : x ∈ R') : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR' hx)

theorem comm_T {x : G} (hx : x ∈ H.T₃) : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.hTa hx)

theorem x₃_mem_T : H.C.D.x₃ ∈ H.T₃ := by
  set J := H.C.D.F.ρ₃.K with hJ
  have hJW2 : IsPGroup 2 ↥(J ⊓ W) := (Thompson.isPGroup_of_mem_WSet H.C.hd.hW).to_inf_right
  have hTN' : H.T₃ ≤ Subgroup.normalizer ((J ⊓ W : Subgroup G) : Set G) := by
    intro y hy
    have hyJ : y ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer (H.hT.1 hy)
    have hyW := H.hTN hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxJ, hxW⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hyJ x).mp hxJ,
        (Subgroup.mem_normalizer_iff.mp hyW x).mp hxW⟩
    · rintro ⟨hxJ, hxW⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hyJ x).mpr hxJ,
        (Subgroup.mem_normalizer_iff.mp hyW x).mpr hxW⟩
  have h2 : IsPGroup 2 ↥(H.T₃ ⊔ (J ⊓ W)) := IsPGroup.to_sup_of_normal_right' H.hT.2.1 hJW2 hTN'
  have hle : H.T₃ ⊔ (J ⊓ W) ≤ J := sup_le H.hT.1 inf_le_left
  have heq : H.T₃ ⊔ (J ⊓ W) = H.T₃ := H.hT.2.2 _ hle h2 le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right ⟨H.C.x₃_mem_J, H.C.D.x₃_mem⟩

theorem comm_x₁ : H.C.D.x₁ * H.a = H.a * H.C.D.x₁ := H.comm_R H.C.x₁_mem_R

theorem comm_x₃ : H.C.D.x₃ * H.a = H.a * H.C.D.x₃ := H.comm_T H.x₃_mem_T

theorem comm_W {w : G} (hw : w ∈ W) : w * H.a = H.a * w := by
  obtain ⟨i, k, rfl⟩ := H.C.exists_nf hw
  have h1 : Commute (H.C.D.x₁ ^ i) H.a := (Commute.zpow_left H.comm_x₁ i)
  have h3 : Commute (H.C.D.x₃ ^ k) H.a := (Commute.zpow_left H.comm_x₃ k)
  exact (h1.mul_left h3).eq

theorem comm_r : H.C.D.F.ρ.r * H.a = H.a * H.C.D.F.ρ.r := H.comm_R H.C.r_mem_R

theorem comm_t : H.C.D.F.ρ'.r * H.a = H.a * H.C.D.F.ρ'.r := H.comm_R' H.C.t_mem_R'

theorem not_le_centralizer_z : ¬ H.T₃ ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hc
  have hΩ := H.C.hyp
  have hJΩ : H.C.D.F.ρ₃.K ∈ Ω := H.C.D.F.ρ₃.hK
  have hTR : H.T₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ H.hT
  have h8 := hΩ.eight_le_of_mem_RSet hTR
  have hTN := hΩ.le_normalizer_of_le_centralizer H.C.mem hJΩ
    (Ne.symm H.C.J_ne_K) H.C.hzK H.hT.1 H.hT.2.1 (by omega) hc
  have hnbr : H.C.D.F.ρ₃.K ∈ omegaNbr Ω K := ⟨hJΩ, H.C.J_ne_K, H.T₃, hTR, H.hT.1, hTN⟩
  have hperp : H.C.D.F.ρ₃.K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [H.C.perp] at hperp
  rcases hperp with h | h
  · exact H.C.J_ne_K h
  · exact H.C.J_ne_K' h

theorem a_ne_z : H.a ≠ z := by
  intro h
  apply H.not_le_centralizer_z
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← h]
  exact H.comm_T hx

theorem a_ne_j : H.a ≠ H.C.D.F.j := by
  intro h
  have h1 := H.C.r_conj_j
  rw [← h] at h1
  have h2 : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
  rw [h2] at h1
  exact H.C.hzK.ne_one (left_eq_mul.mp h1)

theorem a_ne_jz : H.a ≠ H.C.D.F.j * z := by
  intro h
  have h1 : H.C.D.F.ρ.r * (H.C.D.F.j * z) * H.C.D.F.ρ.r⁻¹ = H.C.D.F.j := by
    have hrz : H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹ = z := by
      rw [e189_commute_of_mem H.C.hzK H.C.r_mem_K |>.symm]; group
    calc H.C.D.F.ρ.r * (H.C.D.F.j * z) * H.C.D.F.ρ.r⁻¹
        = (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹) := by
          group
      _ = H.C.D.F.j := by rw [H.C.r_conj_j, hrz, mul_assoc, H.C.hzK.sq, mul_one]
  rw [← h] at h1
  have h2 : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
  rw [h2] at h1
  exact H.a_ne_j h1

theorem a_not_mem : H.a ∉ Subgroup.closure ({H.C.D.F.j, z} : Set G) := by
  intro h
  rcases T7B.mem_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one
    H.C.comm_jz h with h1 | h1 | h1 | h1
  · exact H.ha1 h1
  · exact H.a_ne_j h1
  · exact H.a_ne_z h1
  · exact H.a_ne_jz h1

@[expose] def B : Subgroup G := Subgroup.closure ({H.C.D.F.j * H.a, H.C.D.F.j, z} : Set G)

theorem ja_mem_B : H.C.D.F.j * H.a ∈ H.B := Subgroup.subset_closure (by simp)

theorem j_mem_B : H.C.D.F.j ∈ H.B := Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ H.B := Subgroup.subset_closure (by simp)

theorem a_mem_B : H.a ∈ H.B := by
  have e : H.a = H.C.D.F.j⁻¹ * (H.C.D.F.j * H.a) := by group
  rw [e]
  exact H.B.mul_mem (H.B.inv_mem H.j_mem_B) H.ja_mem_B

end HFrame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame

@[expose] def rt : G := H.C.D.F.ρ.r * H.C.D.F.ρ'.r

@[expose] def Js : Subgroup G := conjSub H.rt H.C.D.F.ρ₃.K

@[expose] def Ts : Subgroup G := conjSub H.rt H.T₃

theorem comm_rt : H.rt * H.a = H.a * H.rt := by
  unfold rt
  rw [mul_assoc, H.comm_t, ← mul_assoc, H.comm_r, mul_assoc]

theorem rt_conj_j : H.rt * H.C.D.F.j * H.rt⁻¹ = H.C.D.F.j := by
  have hrz : H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem H.C.hzK H.C.r_mem_K).symm]; group
  have hzz : z * z = 1 := H.C.hzK.sq
  calc H.rt * H.C.D.F.j * H.rt⁻¹
      = H.C.D.F.ρ.r * (H.C.D.F.ρ'.r * H.C.D.F.j * H.C.D.F.ρ'.r⁻¹) * H.C.D.F.ρ.r⁻¹ := by
        unfold rt; group
    _ = (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹) := by
        rw [H.C.t_conj_j]; group
    _ = H.C.D.F.j := by rw [H.C.r_conj_j, hrz, mul_assoc, hzz, mul_one]

theorem rt_conj_x₃ : H.rt * H.C.D.x₃ * H.rt⁻¹ = z * H.C.D.x₃⁻¹ := by
  have hc : H.C.D.x₃ * H.C.D.x₁ = H.C.D.x₁ * H.C.D.x₃ := H.C.D.comm13.eq.symm
  have h4 : H.C.D.x₃ ^ 4 = 1 := by rw [← H.C.orderOf_x₃]; exact pow_orderOf_eq_one _
  have e1 : H.rt * H.C.D.x₃ * H.rt⁻¹ =
      (H.C.D.F.ρ.r * H.C.D.x₃ * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.C.D.x₂ * H.C.D.F.ρ.r⁻¹) := by
    have e : H.rt * H.C.D.x₃ * H.rt⁻¹ =
        H.C.D.F.ρ.r * (H.C.D.F.ρ'.r * H.C.D.x₃ * H.C.D.F.ρ'.r⁻¹) * H.C.D.F.ρ.r⁻¹ := by
      unfold rt; group
    rw [e, H.C.D.t₃]
    group
  rw [e1, H.C.D.r₃, H.C.D.r₂, H.C.x₂_eq]
  calc H.C.D.x₃ * H.C.D.x₁ * (H.C.D.x₁ * H.C.D.x₃ ^ 2)
      = (H.C.D.x₃ * H.C.D.x₁) * H.C.D.x₁ * H.C.D.x₃ ^ 2 := by group
    _ = (H.C.D.x₁ * H.C.D.x₃) * H.C.D.x₁ * H.C.D.x₃ ^ 2 := by rw [hc]
    _ = H.C.D.x₁ * (H.C.D.x₃ * H.C.D.x₁) * H.C.D.x₃ ^ 2 := by group
    _ = H.C.D.x₁ * (H.C.D.x₁ * H.C.D.x₃) * H.C.D.x₃ ^ 2 := by rw [hc]
    _ = (H.C.D.x₁ * H.C.D.x₁) * (H.C.D.x₃ ^ 4 * H.C.D.x₃⁻¹) := by group
    _ = z * H.C.D.x₃⁻¹ := by rw [← sq, H.C.x₁_sq, h4, one_mul]

theorem hjJs : IsUniqueInvolution H.Js H.C.D.F.j := by
  have h := H.C.hjJ.conj H.rt
  rwa [H.rt_conj_j] at h

theorem Ts_syl : IsSylow2In H.Ts H.Js := H.hT.conj H.rt

theorem Ts_le : H.Ts ≤ Subgroup.centralizer ({H.a} : Set G) := by
  intro x hx
  rw [Ts, mem_conjSub_iff] at hx
  have h1 : H.rt⁻¹ * x * H.rt * H.a = H.a * (H.rt⁻¹ * x * H.rt) := H.comm_T hx
  have hr : H.rt * H.a = H.a * H.rt := H.comm_rt
  have hr' : H.rt⁻¹ * H.a = H.a * H.rt⁻¹ := by
    calc H.rt⁻¹ * H.a = H.rt⁻¹ * (H.a * H.rt) * H.rt⁻¹ := by group
      _ = H.rt⁻¹ * (H.rt * H.a) * H.rt⁻¹ := by rw [hr]
      _ = H.a * H.rt⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * H.a = H.rt * (H.rt⁻¹ * x * H.rt) * (H.rt⁻¹ * H.a) := by group
    _ = H.rt * (H.rt⁻¹ * x * H.rt) * (H.a * H.rt⁻¹) := by rw [hr']
    _ = H.rt * ((H.rt⁻¹ * x * H.rt) * H.a) * H.rt⁻¹ := by group
    _ = H.rt * (H.a * (H.rt⁻¹ * x * H.rt)) * H.rt⁻¹ := by rw [h1]
    _ = (H.rt * H.a) * (H.rt⁻¹ * x * H.rt) * H.rt⁻¹ := by group
    _ = (H.a * H.rt) * (H.rt⁻¹ * x * H.rt) * H.rt⁻¹ := by rw [hr]
    _ = H.a * x := by group

theorem zx₃_mem_Ts : z * H.C.D.x₃⁻¹ ∈ H.Ts := by
  rw [← H.rt_conj_x₃]
  exact conj_mem_conjSub H.x₃_mem_T

theorem Js_ne : H.Js ≠ H.C.D.F.ρ₃.K := by
  intro h
  have h1 : z * H.C.D.x₃⁻¹ ∈ H.C.D.F.ρ₃.K := h ▸ H.Ts_syl.1 H.zx₃_mem_Ts
  have h2 : z ∈ H.C.D.F.ρ₃.K := by
    have h3 := Subgroup.mul_mem _ h1 H.C.x₃_mem_J
    have e : z * H.C.D.x₃⁻¹ * H.C.D.x₃ = z := by group
    rwa [e] at h3
  have h3 : z ∈ Subgroup.zpowers H.C.D.x₃ := H.C.J_inf_W ▸ ⟨h2, H.C.hd.hzW⟩
  rcases eq_one_or_eq_sq_of_mem_zpowers H.C.orderOf_x₃ h3 H.C.hzK.sq with h4 | h4
  · exact H.C.hzK.ne_one h4
  · exact H.C.z_ne_j (h4.trans H.C.x₃_sq)

end HFrame
end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HFrame Ω K K' W S R R' z u)

namespace HFrame

theorem x₃_mul : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
  have hc : z * H.C.D.x₃⁻¹ = H.C.D.x₃⁻¹ * z :=
    Q3CL.Thompson.commutes_of_mem_WSet H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
      (W.inv_mem H.C.D.x₃_mem)
  rw [hc]; group

theorem B_le {L : Subgroup G} (h1 : H.C.D.F.j * H.a ∈ L) (h2 : H.C.D.F.j ∈ L) (h3 : z ∈ L) :
    H.B ≤ L := by
  rw [B, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  exacts [h1, h2, h3]

theorem closure_le_B {x y w : G} (hx : x ∈ H.B) (hy : y ∈ H.B) (hw : w ∈ H.B) :
    Subgroup.closure ({x, y, w} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h <;> rw [h]
  exacts [hx, hy, hw]

theorem B_eq_zja : H.B = Subgroup.closure ({z, H.C.D.F.j, H.a} : Set G) := by
  refine le_antisymm (H.B_le (Subgroup.mul_mem _ mem_closure₂ mem_closure₃) mem_closure₂
    mem_closure₁) (H.closure_le_B H.z_mem_B H.j_mem_B H.a_mem_B)

theorem B_eq_zjza : H.B = Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
  have ha : H.a ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
    have h := Subgroup.mul_mem _
      (Subgroup.inv_mem _ (mem_closure₁ : z ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G)))
      (mem_closure₃ : z * H.a ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G))
    rwa [inv_mul_cancel_left] at h
  refine le_antisymm (H.B_le (Subgroup.mul_mem _ mem_closure₂ ha) mem_closure₂ mem_closure₁)
    (H.closure_le_B H.z_mem_B H.j_mem_B (H.B.mul_mem H.z_mem_B H.a_mem_B))

theorem za_ne_one : z * H.a ≠ 1 := fun h =>
  H.a_ne_z (by
    have e : H.a = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_eq_of_mul_eq_one_right H.C.hzK.sq)

theorem ja_ne_one : H.C.D.F.j * H.a ≠ 1 := fun h =>
  H.a_ne_j (by
    have e : H.a = H.C.D.F.j⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_eq_of_mul_eq_one_right H.C.hjJ.sq)

theorem r_mem_normalizer_B : H.C.D.F.ρ.r ∈ Subgroup.normalizer (H.B : Set G) := by
  have hrz : H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem H.C.hzK H.C.r_mem_K).symm]; group
  have hra : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
  have hrj := H.C.r_conj_j
  refine mem_normalizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  · have e : H.C.D.F.ρ.r * (H.C.D.F.j * H.a) * H.C.D.F.ρ.r⁻¹ =
        (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹) := by
      group
    rw [e, hrj, hra]
    exact H.B.mul_mem (H.B.mul_mem H.j_mem_B H.z_mem_B) H.a_mem_B
  · rw [hrj]
    exact H.B.mul_mem H.j_mem_B H.z_mem_B
  · rw [hrz]
    exact H.z_mem_B

end HFrame
end
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
