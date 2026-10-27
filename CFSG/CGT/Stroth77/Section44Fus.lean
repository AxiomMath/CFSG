module

public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.CGT.Stroth77.Section44CoreIII
public import CFSG.CGT.Stroth77.Section44Facts
public import CFSG.CGT.Stroth77.Section44FactsII
public import CFSG.CGT.Stroth77.Section44FactsIII
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.GroupTheory.FixedCosetCommutator

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

open Stroth44Core

namespace Stroth44Fus

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))

theorem t201_rho_c₁ (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * dD.ρ = (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [c_pow_om dD, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t201_φρ_om hm]
  exact congrArg dD.ofTorus ((om201_eq_iff hm _ _).mpr (by decide))

theorem t201_rho_za (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) * dD.ρ = (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [za_om dD, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t201_φρ_om hm, zb_om dD]
  exact congrArg dD.ofTorus ((om201_eq_iff hm _ _).mpr (by decide))

theorem t201_u_za : dD.u⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) * dD.u = (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [za_om dD, dD.conj_ofTorus dD.u_mem dD.u_conj, t201_φu_om, zb_om dD]
  rfl

theorem t201_rho_zb (hm : 1 ≤ m) :
    dD.ρ⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) * dD.ρ =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [zb_om dD, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t201_φρ_om hm, za_om dD, ← dD.ofTorus_add,
    om201_add]
  exact congrArg dD.ofTorus ((om201_eq_iff hm _ _).mpr (by decide))

theorem t201_u_conj_a : dD.u⁻¹ * (dD.a : G) * dD.u = dD.b := by
  rw [dD.a_eq, dD.conj_ofTorus dD.u_mem dD.u_conj,
    show (StrothTypeIndex.t201 m).action.φu Torus.a = Torus.b from
      (Type201.u_a m).trans (one_zsmul _)]
  rfl

theorem t201_u_conj_b : dD.u⁻¹ * (dD.b : G) * dD.u = dD.a := by
  rw [dD.b_eq, dD.conj_ofTorus dD.u_mem dD.u_conj,
    show (StrothTypeIndex.t201 m).action.φu Torus.b = Torus.a from
      (Type201.u_b m).trans (one_zsmul _)]
  rfl

theorem t201_d_eq :
    (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m, 2 ^ m]) := by
  rw [a_pow_eq, b_pow_eq, ofTorus_ofInt_mul]
  congr 2
  funext i
  fin_cases i <;> simp

theorem t201_uv_conj_d (hm : 1 ≤ m) :
    dD.uv⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * dD.uv =
      ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)⁻¹ := by
  rw [t201_d_eq dD, dD.conj_ofTorus dD.uv_mem dD.uv_conj, t201_φuv, ofTorus_ofInt_inv,
    dD.ofTorus_inj.eq_iff, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.neg_apply]
  refine ⟨⟨-2, by ring⟩, ⟨-(1 + 3 * 2 ^ k + 4 * (2 ^ k) ^ 2), by ring⟩, ⟨-(1 + 2 ^ k), by ring⟩⟩

theorem t201_φuv_sub (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φuv
        (Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)]) -
      Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)] =
    Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 2 ^ m, 2 ^ m] := by
  rw [t201_φuv, ← Torus.ofInt_sub, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.sub_apply]
  refine ⟨⟨-(1 + 2 * 2 ^ k), by ring⟩, ⟨-(2 * 2 ^ k + 5 * (2 ^ k) ^ 2 + 4 * (2 ^ k) ^ 3), by ring⟩,
    ⟨-(2 ^ k + (2 ^ k) ^ 2), by ring⟩⟩

theorem t201_conj_uv (hm : 1 ≤ m) :
    (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)]))⁻¹ *
        dD.uv *
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)]) =
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m * dD.uv := by
  rw [mul_assoc, dD.uv_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_neg, ← dD.ofTorus_add,
    neg_add_eq_sub, t201_φuv_sub hm, t201_d_eq dD]

theorem t201_conj_uv' (hm : 1 ≤ m) :
    dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)]) *
        dD.uv *
        (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ (m - 1) * (1 + 2 ^ m), 2 ^ (m - 1) * (1 + 2 ^ m)]))⁻¹ =
      ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)⁻¹ * dD.uv := by
  rw [← dD.ofTorus_neg, mul_assoc, dD.uv_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add, map_neg,
    ← sub_eq_add_neg, ← neg_sub, t201_φuv_sub hm, dD.ofTorus_neg, t201_d_eq dD]

end Stroth44Fus

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t201 m)}

theorem t201_omega_eq (h : F.IsD D dD) :
    (dD.c : G) ^ 2 ^ (m - 1) = (F.dA.c : G) ∧ (dD.a : G) ^ 2 ^ (m + 1) = (F.dA.a : G) ^ 2 ∧
      (dD.b : G) ^ 2 ^ (m + 1) = (F.dA.b : G) ^ 2 := by
  have hm := Stroth44.one_le h
  have hc2 : (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 := by
    rw [c_pow_om dD]; exact om201_mul_self dD hm _
  have hc1 : (dD.c : G) ^ 2 ^ (m - 1) ≠ 1 := by
    rw [c_pow_om dD]; exact om201_ne_one dD hm 0 (by decide)
  obtain ⟨ha2, hb2, ha1, -, -⟩ := za_zb dD hm
  obtain ⟨γ, hγ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.c.2 _) hc2)
  obtain ⟨α, hα⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.a.2 _) ha2)
  obtain ⟨β, hβ⟩ := F.dA.exists_ofTorus (h.mem_A_of_mul_self (D.pow_mem dD.b.2 _) hb2)
  have hρA := F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj
  have huA := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj
  have hγ2 : γ + γ = 0 := by
    rw [hγ, ← F.dA.ofTorus_add] at hc2; exact F.dA.ofTorus_eq_one_iff.mp hc2
  have hγ1 : γ ≠ 0 := fun h0 => hc1 (by rw [hγ, h0, F.dA.ofTorus_zero])
  have hγρ : (StrothTypeIndex.t100 1).action.φρ γ = γ := by
    have h1 := Stroth44Fus.t201_rho_c₁ dD hm
    rw [h.ρ_eq, hγ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hα2 : α + α = 0 := by
    rw [hα, ← F.dA.ofTorus_add] at ha2; exact F.dA.ofTorus_eq_one_iff.mp ha2
  have hα1 : α ≠ 0 := fun h0 => ha1 (by rw [hα, h0, F.dA.ofTorus_zero])
  have hαu : (StrothTypeIndex.t100 1).action.φu α = β := by
    have h1 := Stroth44Fus.t201_u_za dD
    rw [h.u_eq, hα, hβ, huA] at h1
    exact F.dA.ofTorus_inj h1
  have hαρ : (StrothTypeIndex.t100 1).action.φρ α = β := by
    have h1 := Stroth44Fus.t201_rho_za dD hm
    rw [h.ρ_eq, hα, hβ, hρA] at h1
    exact F.dA.ofTorus_inj h1
  have hβρ : (StrothTypeIndex.t100 1).action.φρ β = α + β := by
    have h1 := Stroth44Fus.t201_rho_zb dD hm
    rw [h.ρ_eq, hα, hβ, hρA, ← F.dA.ofTorus_add] at h1
    exact F.dA.ofTorus_inj h1
  have hαa := Stroth43Fus.t100_one_rho_u α hα2 hα1 (by rw [hαu, hαρ]) (by rw [hαρ, hβρ])
  have hβb : β = 2 • Torus.b := by rw [← hαρ, hαa, Stroth43Fus.t100_one_rho_two_a]
  refine ⟨?_, ?_, ?_⟩
  · rw [hγ, Stroth43Fus.t100_one_rho_fixed γ hγ2 hγ1 hγρ]; rfl
  · rw [hα, hαa, F.dA.ofTorus_nsmul]; rfl
  · rw [hβ, hβb, F.dA.ofTorus_nsmul]; rfl

theorem t201_a_half_mem (h : F.IsD D dD) : (dD.a : G) ^ 2 ^ m ∈ F.A := by
  have := dD.isMulCommutative
  set a' := (dD.a : G) ^ 2 ^ m with ha'
  have ha'D : a' ∈ D := D.pow_mem dD.a.2 _
  have haD : (F.dA.a : G) ∈ D := h.A_le F.dA.a.2
  have hsq : a' * a' = (F.dA.a : G) ^ 2 := by
    rw [← h.t201_omega_eq.2.1, ha', ← pow_two, ← pow_mul, ← pow_succ]
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

theorem t201_b_half_mem (h : F.IsD D dD) : (dD.b : G) ^ 2 ^ m ∈ F.A := by
  have := dD.isMulCommutative
  set b' := (dD.b : G) ^ 2 ^ m with hb'
  have hb'D : b' ∈ D := D.pow_mem dD.b.2 _
  have hbD : (F.dA.b : G) ∈ D := h.A_le F.dA.b.2
  have hsq : b' * b' = (F.dA.b : G) ^ 2 := by
    rw [← h.t201_omega_eq.2.2, hb', ← pow_two, ← pow_mul, ← pow_succ]
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

theorem t201_d_eq_xy (h : F.IsD D dD) :
    (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹)⁻¹ ∨
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ := by
  have := dD.isMulCommutative
  have hm := Stroth44.one_le h
  obtain ⟨-, ha₁, hb₁⟩ := h.t201_omega_eq
  have ha'A := h.t201_a_half_mem
  have hb'A := h.t201_b_half_mem
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
      rw [ha', ← Stroth42.conj_pow', Stroth44Fus.t201_u_conj_a]
    have hub : dD.u⁻¹ * b' * dD.u = a' := by
      rw [hb', ← Stroth42.conj_pow', Stroth44Fus.t201_u_conj_b]
    calc dD.u⁻¹ * (a' * b') * dD.u = (dD.u⁻¹ * a' * dD.u) * (dD.u⁻¹ * b' * dD.u) := by group
      _ = a' * b' := by
        rw [hua, hub]; exact Subgroup.mul_comm_of_mem_isMulCommutative D hb'D ha'D
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [← F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj, F.dA.ofTorus_neg, ← hδ, ← h.uv_eq]
    exact Stroth44Fus.t201_uv_conj_d dD hm
  have hxy : (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ = F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg]; rfl
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδ' | hδ'
  · left
    rw [hδ, hδ', hxy, ← F.dA.ofTorus_neg, neg_neg]
  · right
    rw [hδ, hδ', hxy]

theorem t201_isConj_xyuv (h : F.IsD D dD) :
    IsConj F.dA.uv ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv) := by
  have hm := Stroth44.one_le h
  rw [← h.uv_eq]
  rcases h.t201_d_eq_xy with hd | hd
  · have h1 := Stroth44Fus.t201_conj_uv' dD hm
    rw [hd, inv_inv] at h1
    exact isConj_iff.2 ⟨_, h1⟩
  · have h1 := Stroth44Fus.t201_conj_uv dD hm
    rw [hd] at h1
    exact isConj_iff.2 ⟨_, by rw [inv_inv]; exact h1⟩

theorem t201_fusion (h : F.IsD D dD) :
    (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1))) ∧
    IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
    IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)) := by
  have hm := Stroth44.one_le h
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := Stroth76.frame_fusion F
  obtain ⟨hc₁, ha₁, hb₁⟩ := h.t201_omega_eq
  obtain ⟨ha₁2, hb₁2, ha₁1, -, -⟩ := za_zb dD hm
  have hx2 : F.dA.toConfig.x ^ 2 = (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [StrothWeakTypeData.toConfig_x, inv_pow, ← ha₁]
    exact inv_eq_of_mul_eq_one_right ha₁2
  have hy2 : F.dA.toConfig.y ^ 2 = (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [StrothWeakTypeData.toConfig_y, inv_pow, ← hb₁]
    exact inv_eq_of_mul_eq_one_right hb₁2
  rw [hx2, hy2, StrothWeakTypeData.toConfig_uv, StrothWeakTypeData.toConfig_t, ← h.uv_eq,
    ← h.t_eq] at hfusE
  have ha₁E : (dD.a : G) ^ 2 ^ (m + 1) ∈
      Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t} :=
    Subgroup.subset_closure (by simp)
  have ha₁xy := hfusE _ ha₁E ha₁1
  have huv1 : dD.uv ≠ 1 := fun h1 => Stroth44.uv_not_mem h (h1 ▸ D.one_mem)
  have huvxy := hfusE dD.uv (Subgroup.subset_closure (by simp)) huv1
  refine ⟨fun y hy hy1 => (hfusE y hy hy1).trans ha₁xy.symm, ?_, ?_⟩
  · rw [h.u_eq, hc₁]; exact huw
  · rw [hc₁, h.u_eq]
    have huvxy' : IsConj F.dA.uv ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
      rw [← h.uv_eq]; exact huvxy
    exact hwu.trans (h.t201_isConj_xyuv.symm.trans (huvxy'.trans ha₁xy.symm))

end StrothFrame.IsD

theorem stroth_4_4_hfus201 :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t201 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  intro G _ _ F D m dD h hncD g hg
  have hm := Stroth44.one_le h
  obtain ⟨-, hu, hzu⟩ := h.t201_fusion
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  exact h.not_isConj_of_omega hnc (t201_h3 dD hm)
    (hu.symm.trans ((Stroth42.isConj_of_conj_eq hg).symm.trans hzu))

end CFSG.CGT.Stroth77
