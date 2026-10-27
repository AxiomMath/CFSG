module

public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.CGT.Stroth77.Sections34AssemblyAux
public import CFSG.CGT.Stroth77.Stroth34T200Normal

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

open Stroth34T200

namespace Stroth47Fus

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))

theorem t200_c_pow_ofInt (j : ℕ) :
    (dD.c : G) ^ j = dD.ofTorus (Torus.ofInt _ ![(j : ℤ), 0, 0]) := by
  rw [dD.c_eq, ← dD.ofTorus_nsmul, c_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_a_pow_ofInt (j : ℕ) :
    (dD.a : G) ^ j = dD.ofTorus (Torus.ofInt _ ![0, (j : ℤ), 0]) := by
  rw [dD.a_eq, ← dD.ofTorus_nsmul, a_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_b_pow_ofInt (j : ℕ) :
    (dD.b : G) ^ j = dD.ofTorus (Torus.ofInt _ ![0, 0, (j : ℤ)]) := by
  rw [dD.b_eq, ← dD.ofTorus_nsmul, b_eq_ofInt, ← natCast_zsmul, t200_zsmul_vec]
  simp only [mul_one, mul_zero]

theorem t200_rho_c₁ :
    dD.ρ⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * dD.ρ = (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [t200_c_pow_ofInt, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t200_φρ_vec]
  simp only [sub_zero, neg_zero]

theorem t200_rho_a₁ :
    dD.ρ⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) * dD.ρ = (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [t200_a_pow_ofInt, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t200_φρ_vec, t200_b_pow_ofInt]
  simp only [sub_zero, neg_zero]

theorem t200_u_a₁ :
    dD.u⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) * dD.u = (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [t200_a_pow_ofInt, dD.conj_ofTorus dD.u_mem dD.u_conj, t200_φu_vec, t200_b_pow_ofInt]

theorem t200_rho_b₁ :
    dD.ρ⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) * dD.ρ =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [t200_b_pow_ofInt, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t200_φρ_vec, t200_a_pow_ofInt,
    ← dD.ofTorus_add, t200_add_vec]
  congr 1
  rw [t200_vec_eq_iff]
  refine ⟨⟨2, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;> push_cast <;> ring

theorem t200_c₁_mul_self (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
  rw [t200_c_pow_ofInt, ← dD.ofTorus_add, t200_add_vec, dD.ofTorus_eq_one_iff,
    t200_vec_eq_zero_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨1, ?_⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  push_cast
  ring

theorem t200_c₁_ne_one (hm : 1 ≤ m) : (dD.c : G) ^ 2 ^ (m - 1) ≠ 1 := by
  rw [t200_c_pow_ofInt, Ne, dD.ofTorus_eq_one_iff, t200_vec_eq_zero_iff]
  rintro ⟨⟨k, hk⟩, -, -⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hk
  push_cast at hk
  have h2 : (2 : ℤ) ^ j * 1 = 2 ^ j * (2 * k) := by linear_combination hk
  have h1 := mul_left_cancel₀ (pow_ne_zero j (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

theorem t200_a₁_mul_self : (dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) = 1 := by
  rw [t200_a_pow_ofInt, ← dD.ofTorus_add, t200_add_vec, dD.ofTorus_eq_one_iff,
    t200_vec_eq_zero_iff]
  refine ⟨⟨0, by ring⟩, ⟨1, ?_⟩, ⟨0, by ring⟩⟩
  push_cast
  ring

theorem t200_b₁_mul_self : (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 := by
  rw [t200_b_pow_ofInt, ← dD.ofTorus_add, t200_add_vec, dD.ofTorus_eq_one_iff,
    t200_vec_eq_zero_iff]
  refine ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨1, ?_⟩⟩
  push_cast
  ring

theorem t200_a₁_ne_one : (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 := by
  rw [t200_a_pow_ofInt, Ne, dD.ofTorus_eq_one_iff, t200_vec_eq_zero_iff]
  rintro ⟨-, ⟨k, hk⟩, -⟩
  push_cast at hk
  have h2 : (2 : ℤ) ^ (m + 1) * 1 = 2 ^ (m + 1) * (2 * k) := by linear_combination hk
  have h1 := mul_left_cancel₀ (pow_ne_zero (m + 1) (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

theorem t200_u_conj_a : dD.u⁻¹ * (dD.a : G) * dD.u = dD.b := by
  rw [dD.a_eq, dD.conj_ofTorus dD.u_mem dD.u_conj, a_eq_ofInt, t200_φu_vec, ← b_eq_ofInt]
  rfl

theorem t200_u_conj_b : dD.u⁻¹ * (dD.b : G) * dD.u = dD.a := by
  rw [dD.b_eq, dD.conj_ofTorus dD.u_mem dD.u_conj, b_eq_ofInt, t200_φu_vec, ← a_eq_ofInt]
  rfl

theorem t200_d₂_eq : (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m =
    dD.ofTorus (Torus.ofInt _ ![0, (2 : ℤ) ^ m, (2 : ℤ) ^ m]) := by
  rw [t200_a_pow_ofInt, t200_b_pow_ofInt, ← dD.ofTorus_add, t200_add_vec]
  congr 1
  rw [t200_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> push_cast <;> ring

theorem t200_uv_conj_d₂ :
    dD.uv⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * dD.uv =
      ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)⁻¹ := by
  rw [t200_d₂_eq, dD.conj_ofTorus dD.uv_mem dD.uv_conj, t200_φuv_vec, ← dD.ofTorus_neg,
    t200_neg_vec]
  congr 1
  rw [t200_vec_eq_iff]
  refine ⟨⟨-2, ?_⟩, ⟨-1, ?_⟩, ⟨-1, ?_⟩⟩ <;> ring

theorem t200_conj_uv (m' : ℕ) (dE : StrothWeakTypeData D (.t200 (m' + 1))) :
    (dE.ofTorus (Torus.ofInt _ ![0, (2 : ℤ) ^ m', (2 : ℤ) ^ m']))⁻¹ * dE.uv *
        dE.ofTorus (Torus.ofInt _ ![0, (2 : ℤ) ^ m', (2 : ℤ) ^ m']) =
      (dE.a : G) ^ 2 ^ (m' + 1) * (dE.b : G) ^ 2 ^ (m' + 1) * dE.uv := by
  rw [Stroth43Fus.ofTorus_inv_mul_uv_mul, t200_d₂_eq dE, t200_φuv_vec, t200_sub_vec]
  congr 2
  rw [t200_vec_eq_iff]
  refine ⟨⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem t200_conj_uv' (m' : ℕ) (dE : StrothWeakTypeData D (.t200 (m' + 1))) :
    (dE.ofTorus (-Torus.ofInt _ ![0, (2 : ℤ) ^ m', (2 : ℤ) ^ m']))⁻¹ * dE.uv *
        dE.ofTorus (-Torus.ofInt _ ![0, (2 : ℤ) ^ m', (2 : ℤ) ^ m']) =
      ((dE.a : G) ^ 2 ^ (m' + 1) * (dE.b : G) ^ 2 ^ (m' + 1))⁻¹ * dE.uv := by
  rw [Stroth43Fus.ofTorus_inv_mul_uv_mul, t200_d₂_eq dE, ← dE.ofTorus_neg]
  simp only [t200_neg_vec, t200_φuv_vec, t200_sub_vec]
  congr 2
  rw [t200_vec_eq_iff]
  refine ⟨⟨1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

end Stroth47Fus

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t200 m)}

theorem t200_omega_eq (h : F.IsD D dD) :
    (dD.c : G) ^ 2 ^ (m - 1) = (F.dA.c : G) ∧ (dD.a : G) ^ 2 ^ (m + 1) = (F.dA.a : G) ^ 2 ∧
      (dD.b : G) ^ 2 ^ (m + 1) = (F.dA.b : G) ^ 2 := by
  have hm := h.one_le_of_t200
  have hc2 := Stroth47Fus.t200_c₁_mul_self dD hm
  have ha2 := Stroth47Fus.t200_a₁_mul_self dD
  have hb2 := Stroth47Fus.t200_b₁_mul_self dD
  obtain ⟨γ, hγ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.c.2 _) hc2)
  obtain ⟨α, hα⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.a.2 _) ha2)
  obtain ⟨β, hβ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.b.2 _) hb2)
  have hρA := F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj
  have huA := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj
  have hγ2 : γ + γ = 0 := by
    rw [hγ, ← F.dA.ofTorus_add] at hc2; exact F.dA.ofTorus_eq_one_iff.mp hc2
  have hγ1 : γ ≠ 0 := fun h0 =>
    Stroth47Fus.t200_c₁_ne_one dD hm (by rw [hγ, h0, F.dA.ofTorus_zero])
  have hγρ : (StrothTypeIndex.t100 1).action.φρ γ = γ := by
    have h1 := Stroth47Fus.t200_rho_c₁ dD
    rw [h.ρ_eq, hγ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hα2 : α + α = 0 := by
    rw [hα, ← F.dA.ofTorus_add] at ha2; exact F.dA.ofTorus_eq_one_iff.mp ha2
  have hα1 : α ≠ 0 := fun h0 =>
    Stroth47Fus.t200_a₁_ne_one dD (by rw [hα, h0, F.dA.ofTorus_zero])
  have hαu : (StrothTypeIndex.t100 1).action.φu α = β := by
    have h1 := Stroth47Fus.t200_u_a₁ dD
    rw [h.u_eq, hα, hβ, huA] at h1
    exact F.dA.ofTorus_inj h1
  have hαρ : (StrothTypeIndex.t100 1).action.φρ α = β := by
    have h1 := Stroth47Fus.t200_rho_a₁ dD
    rw [h.ρ_eq, hα, hβ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hβρ : (StrothTypeIndex.t100 1).action.φρ β = α + β := by
    have h1 := Stroth47Fus.t200_rho_b₁ dD
    rw [h.ρ_eq, hα, hβ, hρA, ← F.dA.ofTorus_add] at h1
    exact F.dA.ofTorus_inj h1
  have hαa := Stroth43Fus.t100_one_rho_u α hα2 hα1 (by rw [hαu, hαρ]) (by rw [hαρ, hβρ])
  have hβb : β = 2 • Torus.b := by rw [← hαρ, hαa, Stroth43Fus.t100_one_rho_two_a]
  refine ⟨?_, ?_, ?_⟩
  · rw [hγ, Stroth43Fus.t100_one_rho_fixed γ hγ2 hγ1 hγρ]; rfl
  · rw [hα, hαa, F.dA.ofTorus_nsmul]; rfl
  · rw [hβ, hβb, F.dA.ofTorus_nsmul]; rfl

theorem t200_a_half_mem (h : F.IsD D dD) : (dD.a : G) ^ 2 ^ m ∈ F.A := by
  haveI := dD.isMulCommutative
  set a' := (dD.a : G) ^ 2 ^ m with ha'
  have ha'D : a' ∈ D := D.pow_mem dD.a.2 _
  have haD : (F.dA.a : G) ∈ D := h.A_le F.dA.a.2
  have hsq : a' * a' = (F.dA.a : G) ^ 2 := by
    rw [← h.t200_omega_eq.2.1, ha', ← pow_two, ← pow_mul, ← pow_succ]
  have hc : a' * (F.dA.a : G)⁻¹ = (F.dA.a : G)⁻¹ * a' :=
    Subgroup.mul_comm_of_mem_isMulCommutative D ha'D (D.inv_mem haD)
  have hp2 : (F.dA.a : G)⁻¹ * a' * ((F.dA.a : G)⁻¹ * a') = 1 := by
    calc (F.dA.a : G)⁻¹ * a' * ((F.dA.a : G)⁻¹ * a')
        = (F.dA.a : G)⁻¹ * (a' * (F.dA.a : G)⁻¹) * a' := by group
      _ = (F.dA.a : G)⁻¹ * ((F.dA.a : G)⁻¹ * a') * a' := by rw [hc]
      _ = ((F.dA.a : G) ^ 2)⁻¹ * (a' * a') := by group
      _ = 1 := by rw [hsq, inv_mul_cancel]
  have hpA := h.mem_A_of_mul_self (D.mul_mem (D.inv_mem haD) ha'D) hp2
  rw [show a' = (F.dA.a : G) * ((F.dA.a : G)⁻¹ * a') by group]
  exact F.A.mul_mem F.dA.a.2 hpA

theorem t200_b_half_mem (h : F.IsD D dD) : (dD.b : G) ^ 2 ^ m ∈ F.A := by
  haveI := dD.isMulCommutative
  set b' := (dD.b : G) ^ 2 ^ m with hb'
  have hb'D : b' ∈ D := D.pow_mem dD.b.2 _
  have hbD : (F.dA.b : G) ∈ D := h.A_le F.dA.b.2
  have hsq : b' * b' = (F.dA.b : G) ^ 2 := by
    rw [← h.t200_omega_eq.2.2, hb', ← pow_two, ← pow_mul, ← pow_succ]
  have hc : b' * (F.dA.b : G)⁻¹ = (F.dA.b : G)⁻¹ * b' :=
    Subgroup.mul_comm_of_mem_isMulCommutative D hb'D (D.inv_mem hbD)
  have hp2 : (F.dA.b : G)⁻¹ * b' * ((F.dA.b : G)⁻¹ * b') = 1 := by
    calc (F.dA.b : G)⁻¹ * b' * ((F.dA.b : G)⁻¹ * b')
        = (F.dA.b : G)⁻¹ * (b' * (F.dA.b : G)⁻¹) * b' := by group
      _ = (F.dA.b : G)⁻¹ * ((F.dA.b : G)⁻¹ * b') * b' := by rw [hc]
      _ = ((F.dA.b : G) ^ 2)⁻¹ * (b' * b') := by group
      _ = 1 := by rw [hsq, inv_mul_cancel]
  have hpA := h.mem_A_of_mul_self (D.mul_mem (D.inv_mem hbD) hb'D) hp2
  rw [show b' = (F.dA.b : G) * ((F.dA.b : G)⁻¹ * b') by group]
  exact F.A.mul_mem F.dA.b.2 hpA

theorem t200_d₂_eq_xy (h : F.IsD D dD) :
    (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹)⁻¹ ∨
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ := by
  haveI := dD.isMulCommutative
  have hcp : ∀ (g x : G) (k : ℕ), (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := fun g x k => by
    simpa using conj_pow (a := g⁻¹) (b := x) (i := k)
  obtain ⟨-, ha₁, hb₁⟩ := h.t200_omega_eq
  have ha'A := h.t200_a_half_mem
  have hb'A := h.t200_b_half_mem
  set a' := (dD.a : G) ^ 2 ^ m with ha'
  set b' := (dD.b : G) ^ 2 ^ m with hb'
  have ha'D : a' ∈ D := D.pow_mem dD.a.2 _
  have hb'D : b' ∈ D := D.pow_mem dD.b.2 _
  obtain ⟨δ, hδ⟩ := F.dA.exists_ofTorus (F.A.mul_mem ha'A hb'A)
  have hδ2 : δ + δ = 2 • Torus.a + 2 • Torus.b := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_add, ← hδ, F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul,
      ← F.dA.a_eq, ← F.dA.b_eq, ← ha₁, ← hb₁]
    have hab : b' * a' = a' * b' := Subgroup.mul_comm_of_mem_isMulCommutative D hb'D ha'D
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [hab]
      _ = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
        rw [ha', hb', pow_succ, pow_mul, pow_mul, pow_two, pow_two]; group
  have hδu : (StrothTypeIndex.t100 1).action.φu δ = δ := by
    apply F.dA.ofTorus_inj
    rw [← F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj, ← hδ, ← h.u_eq]
    have hua : dD.u⁻¹ * a' * dD.u = b' := by
      rw [ha', ← hcp, Stroth47Fus.t200_u_conj_a]
    have hub : dD.u⁻¹ * b' * dD.u = a' := by
      rw [hb', ← hcp, Stroth47Fus.t200_u_conj_b]
    calc dD.u⁻¹ * (a' * b') * dD.u = (dD.u⁻¹ * a' * dD.u) * (dD.u⁻¹ * b' * dD.u) := by group
      _ = a' * b' := by
        rw [hua, hub]; exact Subgroup.mul_comm_of_mem_isMulCommutative D hb'D ha'D
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [← F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj, F.dA.ofTorus_neg, ← hδ, ← h.uv_eq]
    exact Stroth47Fus.t200_uv_conj_d₂ dD
  have hxy : (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ = F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg]; rfl
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδ' | hδ'
  · left
    rw [hδ, hδ', hxy, ← F.dA.ofTorus_neg, neg_neg]
  · right
    rw [hδ, hδ', hxy]

theorem t200_isConj_xyuv (h : F.IsD D dD) :
    IsConj F.dA.uv ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv) := by
  have hm := h.one_le_of_t200
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hd := h.t200_d₂_eq_xy
  rw [← h.uv_eq]
  rcases hd with hd | hd
  · have h1 := Stroth47Fus.t200_conj_uv' m' dD
    rw [hd, inv_inv] at h1
    exact isConj_iff.2 ⟨_, by rw [inv_inv]; exact h1⟩
  · have h1 := Stroth47Fus.t200_conj_uv m' dD
    rw [hd] at h1
    exact isConj_iff.2 ⟨_, by rw [inv_inv]; exact h1⟩

theorem t200_fusion (h : F.IsD D dD) :
    (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1))) ∧
    IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
    IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)) := by
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := Stroth76.frame_fusion F
  obtain ⟨hc₁, ha₁, hb₁⟩ := h.t200_omega_eq
  have hx2 : F.dA.toConfig.x ^ 2 = (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [StrothWeakTypeData.toConfig_x, inv_pow, ← ha₁]
    exact inv_eq_of_mul_eq_one_right (Stroth47Fus.t200_a₁_mul_self dD)
  have hy2 : F.dA.toConfig.y ^ 2 = (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [StrothWeakTypeData.toConfig_y, inv_pow, ← hb₁]
    exact inv_eq_of_mul_eq_one_right (Stroth47Fus.t200_b₁_mul_self dD)
  rw [hx2, hy2, StrothWeakTypeData.toConfig_uv, StrothWeakTypeData.toConfig_t, ← h.uv_eq,
    ← h.t_eq] at hfusE
  have ha₁E : (dD.a : G) ^ 2 ^ (m + 1) ∈
      Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t} :=
    Subgroup.subset_closure (by simp)
  have ha₁xy := hfusE _ ha₁E (Stroth47Fus.t200_a₁_ne_one dD)
  have huv1 : dD.uv ≠ 1 := fun h1 => F.uv_not_mem_centralizer_A (by
    rw [← h.uv_eq, h1]; exact Subgroup.one_mem _)
  have huvxy := hfusE dD.uv (Subgroup.subset_closure (by simp)) huv1
  refine ⟨fun y hy hy1 => (hfusE y hy hy1).trans ha₁xy.symm, ?_, ?_⟩
  · rw [h.u_eq, hc₁]; exact huw
  · rw [hc₁, h.u_eq]
    have huvxy' : IsConj F.dA.uv ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
      rw [← h.uv_eq]; exact huvxy
    exact hwu.trans (h.t200_isConj_xyuv.symm.trans (huvxy'.trans ha₁xy.symm))

end StrothFrame.IsD

theorem stroth_4_7_hfus200 :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  intro G _ _ F D m dD h hncD g hg
  obtain ⟨-, hu, hzu⟩ := h.t200_fusion
  have hca : IsConj ((dD.c : G) ^ 2 ^ (m - 1)) ((dD.a : G) ^ 2 ^ (m + 1)) :=
    hu.symm.trans ((isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hg⟩).trans hzu)
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  obtain ⟨hfusE, -, -, -, -, -⟩ := Stroth76.frame_fusion F
  obtain ⟨hc₁, ha₁, -⟩ := h.t200_omega_eq
  have hx2 : F.dA.toConfig.x ^ 2 = (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [StrothWeakTypeData.toConfig_x, inv_pow, ← ha₁]
    exact inv_eq_of_mul_eq_one_right (Stroth47Fus.t200_a₁_mul_self dD)
  have hx2E : F.dA.toConfig.x ^ 2 ∈ Subgroup.closure {F.dA.toConfig.x ^ 2,
      F.dA.toConfig.y ^ 2, F.dA.toConfig.uv, F.dA.toConfig.t} :=
    Subgroup.subset_closure (by simp)
  have hx21 : F.dA.toConfig.x ^ 2 ≠ 1 := by rw [hx2]; exact Stroth47Fus.t200_a₁_ne_one dD
  have hxy := hfusE _ hx2E hx21
  rw [hx2] at hxy
  apply F.not_isConj_w_xy_sq hnc
  rw [StrothWeakTypeData.toConfig_w, ← hc₁]
  exact hca.trans hxy

end CFSG.CGT.Stroth77
