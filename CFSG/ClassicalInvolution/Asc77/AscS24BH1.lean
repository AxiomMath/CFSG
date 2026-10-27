module

public import CFSG.ClassicalInvolution.Asc77.AscS24Elem
public import CFSG.ClassicalInvolution.Asc77.AscS24BNorm
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

theorem r_conj_j : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]

theorem t_conj_j : C.D.F.ρ'.r * C.D.F.j * C.D.F.ρ'.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.t₃, C.D.comm23.symm.mul_pow, C.x₂_sq]

theorem comm_jz : C.D.F.j * z = z * C.D.F.j :=
  Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW _
    (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2) z C.hd.hzW

theorem J_ne_K : C.D.F.ρ₃.K ≠ K := fun h => C.D.F.hne₁ (C.hK.trans h.symm)

theorem J_ne_K' : C.D.F.ρ₃.K ≠ K' := fun h => C.D.F.hne₂ (C.hK'.trans h.symm)

theorem J_inf_W : C.D.F.ρ₃.K ⊓ W = Subgroup.zpowers C.D.x₃ := by
  have hle : Subgroup.zpowers C.D.x₃ ≤ C.D.F.ρ₃.K ⊓ W :=
    Subgroup.zpowers_le.mpr ⟨C.x₃_mem_J, C.D.x₃_mem⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [C.card_J_inf_W, Nat.card_zpowers, C.orderOf_x₃]

end Ctx8

structure HCtx (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  C : Ctx8 p f Ω K K' W S R R' z u
  a : G
  T₃ : Subgroup G
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haR : R ≤ Subgroup.centralizer ({a} : Set G)
  haR' : R' ≤ Subgroup.centralizer ({a} : Set G)
  hT : IsSylow2In T₃ C.D.F.ρ₃.K
  hTN : T₃ ≤ Subgroup.normalizer (W : Set G)
  hTa : T₃ ≤ Subgroup.centralizer ({a} : Set G)

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

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

theorem comm_z : z * H.a = H.a * z := H.comm_W H.C.hd.hzW

theorem comm_j : H.C.D.F.j * H.a = H.a * H.C.D.F.j :=
  H.comm_W (H.C.x₃_sq ▸ W.pow_mem H.C.D.x₃_mem 2)

theorem comm_r : H.C.D.F.ρ.r * H.a = H.a * H.C.D.F.ρ.r := H.comm_R H.C.r_mem_R

theorem comm_t : H.C.D.F.ρ'.r * H.a = H.a * H.C.D.F.ρ'.r := H.comm_R' H.C.t_mem_R'

theorem not_le_centralizer_z : ¬ H.T₃ ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hc
  have hst := H.C.hs.stand
  have hΩ := hst.hyp
  have hJΩ : H.C.D.F.ρ₃.K ∈ Ω := H.C.D.F.ρ₃.hK
  have hTR : H.T₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ H.hT
  have h8 := hΩ.eight_le_of_mem_RSet hst.odd hTR
  have hTN := hΩ.le_normalizer_of_le_centralizer hst.odd hst.five hst.mem hJΩ
    (Ne.symm H.C.J_ne_K) H.C.hzK H.hT.1 H.hT.2.1 (by omega) hc
  have hnbr : H.C.D.F.ρ₃.K ∈ omegaNbr Ω K := ⟨hJΩ, H.C.J_ne_K, H.T₃, hTR, H.hT.1, hTN⟩
  have hperp : H.C.D.F.ρ₃.K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [H.C.hs.perp] at hperp
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

theorem B_isElemAbelian : IsElemAbelian 2 H.B :=
  S24.B_isElemAbelian_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz H.comm_j H.comm_z

theorem B_card : Nat.card ↥H.B = 8 :=
  S24.B_natCard_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.hjJ.ne_one H.C.hzK.ne_one H.C.z_ne_j.symm
    H.C.comm_jz H.comm_j H.comm_z H.a_not_mem

theorem ja_mem_B : H.C.D.F.j * H.a ∈ H.B := Subgroup.subset_closure (by simp)

theorem j_mem_B : H.C.D.F.j ∈ H.B := Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ H.B := Subgroup.subset_closure (by simp)

theorem a_mem_B : H.a ∈ H.B := by
  have e : H.a = H.C.D.F.j⁻¹ * (H.C.D.F.j * H.a) := by group
  rw [e]
  exact H.B.mul_mem (H.B.inv_mem H.j_mem_B) H.ja_mem_B

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
