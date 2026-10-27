module

public import CFSG.CGT.Stroth76.FrameFusion
public import CFSG.CGT.Stroth77.Section41
public import CFSG.CGT.Stroth77.Section42CoreSplit

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G] [Finite G]

open Stroth42Core

namespace Stroth43Fus

theorem t100_one_rho_fixed : ∀ γ : Torus (StrothTypeIndex.t100 1).k, γ + γ = 0 → γ ≠ 0 →
    (StrothTypeIndex.t100 1).action.φρ γ = γ → γ = Torus.c := by
  decide +kernel

theorem t100_one_rho_u : ∀ α : Torus (StrothTypeIndex.t100 1).k, α + α = 0 → α ≠ 0 →
    (StrothTypeIndex.t100 1).action.φu α = (StrothTypeIndex.t100 1).action.φρ α →
    (StrothTypeIndex.t100 1).action.φρ ((StrothTypeIndex.t100 1).action.φρ α) =
      α + (StrothTypeIndex.t100 1).action.φρ α → α = 2 • Torus.a := by
  decide +kernel

theorem t100_one_rho_two_a :
    (StrothTypeIndex.t100 1).action.φρ (2 • Torus.a) =
      (2 • Torus.b : Torus (StrothTypeIndex.t100 1).k) := by
  decide +kernel

theorem t100_one_xy : ∀ δ : Torus (StrothTypeIndex.t100 1).k,
    δ + δ = 2 • Torus.a + 2 • Torus.b → (StrothTypeIndex.t100 1).action.φu δ = δ →
    (StrothTypeIndex.t100 1).action.φuv δ = -δ →
    δ = Torus.a + Torus.b ∨ δ = -(Torus.a + Torus.b) := by
  decide +kernel

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t100 m))

theorem om100_add (ε ε' : Fin 3 → ℤ) : om100 m ε + om100 m ε' = om100 m (ε + ε') := by
  rw [om100, om100, om100, ← Torus.ofInt_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem t100_rho_c₁ (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * dD.ρ = (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [dD.t100_c_pow, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t100_φρ_om hm]
  exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))

theorem t100_rho_a₁ (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.a : G) ^ 2 ^ m * dD.ρ = (dD.b : G) ^ 2 ^ m := by
  rw [dD.t100_a_pow, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t100_φρ_om hm, dD.t100_b_pow]
  exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))

theorem t100_u_a₁ :
    dD.u⁻¹ * (dD.a : G) ^ 2 ^ m * dD.u = (dD.b : G) ^ 2 ^ m := by
  rw [dD.t100_a_pow, dD.conj_ofTorus dD.u_mem dD.u_conj, t100_φu_om, dD.t100_b_pow]
  rfl

theorem t100_rho_b₁ (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.b : G) ^ 2 ^ m * dD.ρ = (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m := by
  rw [dD.t100_b_pow, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t100_φρ_om hm, dD.t100_a_pow,
    ← dD.ofTorus_add, om100_add]
  exact congrArg dD.ofTorus ((om100_eq_iff hm _ _).mpr (by decide))

theorem t100_c₁_mul_self (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
  rw [dD.t100_c_pow, ← dD.ofTorus_add, om100_add_self hm, dD.ofTorus_zero]

theorem t100_a₁_mul_self (hm : 1 ≤ m) : (dD.a : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m = 1 := by
  rw [dD.t100_a_pow, ← dD.ofTorus_add, om100_add_self hm, dD.ofTorus_zero]

theorem t100_c₁_ne_one (hm : 1 ≤ m) : (dD.c : G) ^ 2 ^ (m - 1) ≠ 1 := by
  rw [dD.t100_c_pow, Ne, dD.ofTorus_eq_one_iff, ← om100_zero, om100_eq_iff hm]
  decide

theorem t100_a₁_ne_one (hm : 1 ≤ m) : (dD.a : G) ^ 2 ^ m ≠ 1 := by
  rw [dD.t100_a_pow, Ne, dD.ofTorus_eq_one_iff, ← om100_zero, om100_eq_iff hm]
  decide

theorem t100_b₁_mul_self (hm : 1 ≤ m) : (dD.b : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = 1 := by
  rw [dD.t100_b_pow, ← dD.ofTorus_add, om100_add_self hm, dD.ofTorus_zero]

private theorem conj_pow_eq (g x : G) (k : ℕ) : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := k)

theorem t100_u_conj_a : dD.u⁻¹ * (dD.a : G) * dD.u = dD.b := by
  rw [dD.a_eq, dD.conj_ofTorus dD.u_mem dD.u_conj,
    show (StrothTypeIndex.t100 m).action.φu Torus.a = Torus.b from
      (Type100.u_a m).trans (one_zsmul _)]
  rfl

theorem t100_u_conj_b : dD.u⁻¹ * (dD.b : G) * dD.u = dD.a := by
  rw [dD.b_eq, dD.conj_ofTorus dD.u_mem dD.u_conj,
    show (StrothTypeIndex.t100 m).action.φu Torus.b = Torus.a from
      (Type100.u_b m).trans (one_zsmul _)]
  rfl

theorem ofTorus_inv_mul_uv_mul {τ : StrothTypeIndex} (dE : StrothWeakTypeData D τ)
    (v : Torus τ.k) :
    (dE.ofTorus v)⁻¹ * dE.uv * dE.ofTorus v = dE.ofTorus (τ.action.φuv v - v) * dE.uv := by
  rw [mul_assoc, dE.uv_mul_ofTorus, ← mul_assoc, ← dE.ofTorus_neg, ← dE.ofTorus_add,
    neg_add_eq_sub]

theorem t100_d₂_eq (m' : ℕ) (dE : StrothWeakTypeData D (.t100 (m' + 1))) :
    (dE.a : G) ^ 2 ^ m' * (dE.b : G) ^ 2 ^ m' =
      dE.ofTorus (Torus.ofInt _ ![0, 2 ^ m', 2 ^ m']) := by
  rw [dE.a_eq, dE.b_eq, ← dE.ofTorus_nsmul, ← dE.ofTorus_nsmul, ← dE.ofTorus_add]
  congr 1
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply]

theorem t100_uv_conj_d₂ (m' : ℕ) (dE : StrothWeakTypeData D (.t100 (m' + 1))) :
    dE.uv⁻¹ * ((dE.a : G) ^ 2 ^ m' * (dE.b : G) ^ 2 ^ m') * dE.uv =
      ((dE.a : G) ^ 2 ^ m' * (dE.b : G) ^ 2 ^ m')⁻¹ := by
  rw [t100_d₂_eq m' dE, dE.conj_ofTorus dE.uv_mem dE.uv_conj, t100_φuv, ← dE.ofTorus_neg,
    ← Torus.ofInt_neg]
  congr 1
  rw [t100_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.neg_apply]
  refine ⟨⟨-2, by ring⟩, ⟨-1, by ring⟩, ⟨-1, by ring⟩⟩

theorem t100_conj_uv (m'' : ℕ) (dE : StrothWeakTypeData D (.t100 (m'' + 2))) :
    (dE.ofTorus (Torus.ofInt _ ![0, 2 ^ m'', 2 ^ m'']))⁻¹ * dE.uv *
        dE.ofTorus (Torus.ofInt _ ![0, 2 ^ m'', 2 ^ m'']) =
      (dE.a : G) ^ 2 ^ (m'' + 1) * (dE.b : G) ^ 2 ^ (m'' + 1) * dE.uv := by
  rw [ofTorus_inv_mul_uv_mul, t100_d₂_eq (m'' + 1) dE, t100_φuv, ← Torus.ofInt_sub]
  congr 2
  rw [t100_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.sub_apply]
  refine ⟨⟨-1, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_conj_uv' (m'' : ℕ) (dE : StrothWeakTypeData D (.t100 (m'' + 2))) :
    (dE.ofTorus (-Torus.ofInt _ ![0, 2 ^ m'', 2 ^ m'']))⁻¹ * dE.uv *
        dE.ofTorus (-Torus.ofInt _ ![0, 2 ^ m'', 2 ^ m'']) =
      ((dE.a : G) ^ 2 ^ (m'' + 1) * (dE.b : G) ^ 2 ^ (m'' + 1))⁻¹ * dE.uv := by
  rw [ofTorus_inv_mul_uv_mul, t100_d₂_eq (m'' + 1) dE, ← dE.ofTorus_neg, map_neg, t100_φuv,
    ← Torus.ofInt_neg, ← Torus.ofInt_neg, ← Torus.ofInt_sub, ← Torus.ofInt_neg]
  congr 2
  rw [t100_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.sub_apply, Pi.neg_apply]
  refine ⟨⟨1, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

end Stroth43Fus

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G}

theorem mem_A_of_mul_self {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    {z : G} (hz : z ∈ D) (h2 : z * z = 1) : z ∈ F.A :=
  omegaIn_le 1 F.A (h.omegaIn_one_eq ▸ mem_omegaIn_one_of_mul_self hz h2)

variable {m : ℕ} {dD : StrothWeakTypeData D (.t100 m)}

theorem t100_omega_eq (h : F.IsD D dD) (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) = (F.dA.c : G) ∧ (dD.a : G) ^ 2 ^ m = (F.dA.a : G) ^ 2 ∧
      (dD.b : G) ^ 2 ^ m = (F.dA.b : G) ^ 2 := by
  have hc2 := Stroth43Fus.t100_c₁_mul_self dD hm
  have ha2 := Stroth43Fus.t100_a₁_mul_self dD hm
  have hb2 := Stroth43Fus.t100_b₁_mul_self dD hm
  obtain ⟨γ, hγ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.c.2 _) hc2)
  obtain ⟨α, hα⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.a.2 _) ha2)
  obtain ⟨β, hβ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.b.2 _) hb2)
  have hρA := F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj
  have huA := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj
  have hγ2 : γ + γ = 0 := by
    rw [hγ, ← F.dA.ofTorus_add] at hc2; exact F.dA.ofTorus_eq_one_iff.mp hc2
  have hγ1 : γ ≠ 0 := fun h0 => Stroth43Fus.t100_c₁_ne_one dD hm (by rw [hγ, h0, F.dA.ofTorus_zero])
  have hγρ : (StrothTypeIndex.t100 1).action.φρ γ = γ := by
    have h1 := Stroth43Fus.t100_rho_c₁ dD hm
    rw [h.ρ_eq, hγ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hα2 : α + α = 0 := by
    rw [hα, ← F.dA.ofTorus_add] at ha2; exact F.dA.ofTorus_eq_one_iff.mp ha2
  have hα1 : α ≠ 0 := fun h0 => Stroth43Fus.t100_a₁_ne_one dD hm (by rw [hα, h0, F.dA.ofTorus_zero])
  have hαu : (StrothTypeIndex.t100 1).action.φu α = β := by
    have h1 := Stroth43Fus.t100_u_a₁ dD
    rw [h.u_eq, hα, hβ, huA] at h1
    exact F.dA.ofTorus_inj h1
  have hαρ : (StrothTypeIndex.t100 1).action.φρ α = β := by
    have h1 := Stroth43Fus.t100_rho_a₁ dD hm
    rw [h.ρ_eq, hα, hβ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hβρ : (StrothTypeIndex.t100 1).action.φρ β = α + β := by
    have h1 := Stroth43Fus.t100_rho_b₁ dD hm
    rw [h.ρ_eq, hα, hβ, hρA, ← F.dA.ofTorus_add] at h1
    exact F.dA.ofTorus_inj h1
  have hαa := Stroth43Fus.t100_one_rho_u α hα2 hα1 (by rw [hαu, hαρ]) (by rw [hαρ, hβρ])
  have hβb : β = 2 • Torus.b := by rw [← hαρ, hαa, Stroth43Fus.t100_one_rho_two_a]
  refine ⟨?_, ?_, ?_⟩
  · rw [hγ, Stroth43Fus.t100_one_rho_fixed γ hγ2 hγ1 hγρ]; rfl
  · rw [hα, hαa, F.dA.ofTorus_nsmul]; rfl
  · rw [hβ, hβb, F.dA.ofTorus_nsmul]; rfl

theorem t100_a_half_mem (h : F.IsD D dD) (hm : 1 ≤ m) : (dD.a : G) ^ 2 ^ (m - 1) ∈ F.A := by
  haveI := dD.isMulCommutative
  set a' := (dD.a : G) ^ 2 ^ (m - 1) with ha'
  have ha'D : a' ∈ D := D.pow_mem dD.a.2 _
  have haD : (F.dA.a : G) ∈ D := h.A_le F.dA.a.2
  have hsq : a' * a' = (F.dA.a : G) ^ 2 := by
    rw [← (h.t100_omega_eq hm).2.1, ha', ← pow_two, ← pow_mul, ← pow_succ,
      Nat.sub_add_cancel hm]
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

theorem t100_b_half_mem (h : F.IsD D dD) (hm : 1 ≤ m) : (dD.b : G) ^ 2 ^ (m - 1) ∈ F.A := by
  haveI := dD.isMulCommutative
  set b' := (dD.b : G) ^ 2 ^ (m - 1) with hb'
  have hb'D : b' ∈ D := D.pow_mem dD.b.2 _
  have hbD : (F.dA.b : G) ∈ D := h.A_le F.dA.b.2
  have hsq : b' * b' = (F.dA.b : G) ^ 2 := by
    rw [← (h.t100_omega_eq hm).2.2, hb', ← pow_two, ← pow_mul, ← pow_succ,
      Nat.sub_add_cancel hm]
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

theorem t100_d₂_eq_xy (h : F.IsD D dD) (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) =
        ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹)⁻¹ ∨
      (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ := by
  haveI := dD.isMulCommutative
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  obtain ⟨-, ha₁, hb₁⟩ := h.t100_omega_eq hm
  set a' := (dD.a : G) ^ 2 ^ m' with ha'
  set b' := (dD.b : G) ^ 2 ^ m' with hb'
  have ha'D : a' ∈ D := D.pow_mem dD.a.2 _
  have hb'D : b' ∈ D := D.pow_mem dD.b.2 _
  have ha'A : a' ∈ F.A := by simpa using h.t100_a_half_mem hm
  have hb'A : b' ∈ F.A := by simpa using h.t100_b_half_mem hm
  obtain ⟨δ, hδ⟩ := F.dA.exists_ofTorus (F.A.mul_mem ha'A hb'A)
  have hδ2 : δ + δ = 2 • Torus.a + 2 • Torus.b := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_add, ← hδ, F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul,
      ← F.dA.a_eq, ← F.dA.b_eq, ← ha₁, ← hb₁]
    have hab : b' * a' = a' * b' := Subgroup.mul_comm_of_mem_isMulCommutative D hb'D ha'D
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [hab]
      _ = (dD.a : G) ^ 2 ^ (m' + 1) * (dD.b : G) ^ 2 ^ (m' + 1) := by
        rw [ha', hb', pow_succ, pow_mul, pow_mul, pow_two, pow_two]; group
  have hδu : (StrothTypeIndex.t100 1).action.φu δ = δ := by
    apply F.dA.ofTorus_inj
    rw [← F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj, ← hδ, ← h.u_eq]
    have hua : dD.u⁻¹ * a' * dD.u = b' := by
      rw [ha', ← Stroth43Fus.conj_pow_eq, Stroth43Fus.t100_u_conj_a]
    have hub : dD.u⁻¹ * b' * dD.u = a' := by
      rw [hb', ← Stroth43Fus.conj_pow_eq, Stroth43Fus.t100_u_conj_b]
    calc dD.u⁻¹ * (a' * b') * dD.u = (dD.u⁻¹ * a' * dD.u) * (dD.u⁻¹ * b' * dD.u) := by group
      _ = a' * b' := by
        rw [hua, hub]; exact Subgroup.mul_comm_of_mem_isMulCommutative D hb'D ha'D
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [← F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj, F.dA.ofTorus_neg, ← hδ, ← h.uv_eq]
    exact Stroth43Fus.t100_uv_conj_d₂ m' dD
  have hxy : (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ = F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg]; rfl
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδ' | hδ'
  · left
    rw [hδ, hδ', hxy, ← F.dA.ofTorus_neg, neg_neg]
  · right
    rw [hδ, hδ', hxy]

theorem t100_isConj_xyuv (h : F.IsD D dD) (hm : 2 ≤ m) :
    IsConj F.dA.uv ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv) := by
  obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 2 := ⟨m - 2, by omega⟩
  have hd := h.t100_d₂_eq_xy (by omega)
  simp only [show m'' + 2 - 1 = m'' + 1 by omega] at hd
  rw [← h.uv_eq]
  rcases hd with hd | hd
  · have h1 := Stroth43Fus.t100_conj_uv' m'' dD
    rw [hd, inv_inv] at h1
    exact isConj_iff.2 ⟨_, by rw [inv_inv]; exact h1⟩
  · have h1 := Stroth43Fus.t100_conj_uv m'' dD
    rw [hd] at h1
    exact isConj_iff.2 ⟨_, by rw [inv_inv]; exact h1⟩

theorem t100_fusion (h : F.IsD D dD) (hm : 2 ≤ m) :
    (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ m)) ∧
    IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
    IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ m) := by
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := Stroth76.frame_fusion F
  obtain ⟨hc₁, ha₁, hb₁⟩ := h.t100_omega_eq (by omega)
  have ha₁2 := Stroth43Fus.t100_a₁_mul_self dD (by omega)
  have hb₁2 := Stroth43Fus.t100_b₁_mul_self dD (by omega)
  have hx2 : F.dA.toConfig.x ^ 2 = (dD.a : G) ^ 2 ^ m := by
    rw [StrothWeakTypeData.toConfig_x, inv_pow, ← ha₁]
    exact inv_eq_of_mul_eq_one_right ha₁2
  have hy2 : F.dA.toConfig.y ^ 2 = (dD.b : G) ^ 2 ^ m := by
    rw [StrothWeakTypeData.toConfig_y, inv_pow, ← hb₁]
    exact inv_eq_of_mul_eq_one_right hb₁2
  rw [hx2, hy2, StrothWeakTypeData.toConfig_uv, StrothWeakTypeData.toConfig_t, ← h.uv_eq,
    ← h.t_eq] at hfusE
  have ha₁E : (dD.a : G) ^ 2 ^ m ∈
      Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t} :=
    Subgroup.subset_closure (by simp)
  have ha₁xy := hfusE _ ha₁E (Stroth43Fus.t100_a₁_ne_one dD (by omega))
  have huv1 : dD.uv ≠ 1 := fun h1 => F.uv_not_mem_centralizer_A (by
    rw [← h.uv_eq, h1]; exact Subgroup.one_mem _)
  have huvxy := hfusE dD.uv (Subgroup.subset_closure (by simp)) huv1
  refine ⟨fun y hy hy1 => (hfusE y hy hy1).trans ha₁xy.symm, ?_, ?_⟩
  · rw [h.u_eq, hc₁]; exact huw
  · rw [hc₁, h.u_eq]
    have huvxy' : IsConj F.dA.uv ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
      rw [← h.uv_eq]; exact huvxy
    exact hwu.trans ((h.t100_isConj_xyuv hm).symm.trans (huvxy'.trans ha₁xy.symm))

end StrothFrame.IsD

theorem stroth_4_3_fusIII :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G},
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      2 ≤ m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ → e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ → e * e = 1 →
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t},
        y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ m)) ∧
      IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
      IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ m) :=
  by
  intro G _ _ F D m dD e h _ _ _ _ _ hm
  intros
  exact h.t100_fusion hm

end CFSG.CGT.Stroth77
