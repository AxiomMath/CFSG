module

import CFSG.CGT.Stroth77.Section47InvOneE32Comm
import CFSG.CGT.Stroth77.Section47InvOneE32Conj
import CFSG.CGT.Stroth77.Section47InvOneE32Elab
import CFSG.CGT.Stroth77.Section47InvOneE32Gen
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Stroth77.Section47Core
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200_mul_mem_S₁ {d w : G} (hd : d ∈ D) (hw : w ∈ ({dD.uv, dD.t, dD.u} : Set G)) :
    d * w ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right (Subgroup.subset_closure hw))

theorem t200_E'_le_S₁ :
    Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.cab * dD.uv,
      (dD.a : G)⁻¹ * dD.t} ≤ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  t200_closure_le_S₁ dD
    (t200_mul_mem_S₁ dD (mul_mem (mul_mem dD.c.2 dD.a.2) dD.b.2) (by simp))
    (t200_mul_mem_S₁ dD (D.inv_mem dD.a.2) (by simp))

theorem t200inv1_elab_e [Finite G] (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 2) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t, e}, x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t, e}) = 32 := by
  have hE := dD.t200_elabE' hm
  obtain ⟨ha, hb⟩ := t200inv1_comm_a₁_b₁ dD hm (Or.inl rfl) hrel 0
  rw [dD.ofTorus_zero, one_mul] at ha hb
  obtain ⟨h₃, h₄⟩ := t200inv1_comm_E'_e dD hrel
  have hS := t200inv1_ofTorus_mul_e_not_mem dD hm (Or.inl rfl) hrel 0
  rw [dD.ofTorus_zero, one_mul] at hS
  obtain ⟨hsq, hcard⟩ := elab_closure_insert hE.1 hrel.e_sq ha hb h₃ h₄
    (fun h => hS (t200_E'_le_S₁ dD h))
  exact ⟨hsq, by rw [hcard, hE.2]⟩

theorem t200inv1_elab_c₁e [Finite G] (hm : 1 ≤ m) (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t, (dD.c : G) ^ 2 ^ (m - 1) * e}, x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.cab * dD.uv, (dD.a : G)⁻¹ * dD.t, (dD.c : G) ^ 2 ^ (m - 1) * e}) = 32 := by
  have hE := dD.t200_elabE' hm
  obtain ⟨ha, hb⟩ := t200inv1_comm_a₁_b₁ dD hm (Or.inr rfl) hrel (om200 m ![1, 0, 0])
  rw [← dD.t200_c_pow] at ha hb
  obtain ⟨h₃, h₄⟩ := t200inv1_comm_E'_c₁e dD hm hrel
  have hS := t200inv1_ofTorus_mul_e_not_mem dD hm (Or.inr rfl) hrel (om200 m ![1, 0, 0])
  rw [← dD.t200_c_pow] at hS
  obtain ⟨hsq, hcard⟩ := elab_closure_insert hE.1
    (t200inv1_c₁e_mul_self dD hm hrel) ha hb h₃ h₄
    (fun h => hS (t200_E'_le_S₁ dD h))
  exact ⟨hsq, by rw [hcard, hE.2]⟩

theorem t200_elabF [Finite G] (hm : 1 ≤ m) :
    ((∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t}, x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t}) = 16) ∧
      Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t} ≤
        D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  obtain ⟨hy₃, hy₄, h₃, h₄, h₃₄⟩ := t200_yF_facts dD
  exact ⟨t200_elab16 dD hm hy₃ hy₄ h₃ h₄ h₃₄, t200_closure_le_S₁ dD
    (t200_mul_mem_S₁ dD (dD.ofTorus_mem _) (by simp))
    (t200_mul_mem_S₁ dD (dD.ofTorus_mem _) (by simp))⟩

theorem t200inv1_elabF_c₁e [Finite G] (hm : 1 ≤ m) (hrel : Rel34inv dD e 0 1 2) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t, (dD.c : G) ^ 2 ^ (m - 1) * e},
        x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t, (dD.c : G) ^ 2 ^ (m - 1) * e}) =
        32 := by
  obtain ⟨hF, hle⟩ := t200_elabF dD hm
  obtain ⟨ha, hb⟩ := t200inv1_comm_a₁_b₁ dD hm (Or.inl rfl) hrel (om200 m ![1, 0, 0])
  rw [← dD.t200_c_pow] at ha hb
  obtain ⟨h₃, h₄⟩ := t200inv1_comm_F_c₁e dD hm hrel
  have hS := t200inv1_ofTorus_mul_e_not_mem dD hm (Or.inl rfl) hrel (om200 m ![1, 0, 0])
  rw [← dD.t200_c_pow] at hS
  obtain ⟨hsq, hcard⟩ := elab_closure_insert hF.1
    (t200inv1_c₁e_mul_self dD hm hrel) ha hb h₃ h₄ (fun h => hS (hle h))
  exact ⟨hsq, by rw [hcard, hF.2]⟩

theorem t200inv1_elabF_e [Finite G] (hm : 1 ≤ m) (hrel : Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t, e}, x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1),
        dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv,
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t, e}) = 32 := by
  obtain ⟨hF, hle⟩ := t200_elabF dD hm
  obtain ⟨ha, hb⟩ := t200inv1_comm_a₁_b₁ dD hm (Or.inr rfl) hrel 0
  rw [dD.ofTorus_zero, one_mul] at ha hb
  obtain ⟨h₃, h₄⟩ := t200inv1_comm_F_e dD hm hrel
  have hS := t200inv1_ofTorus_mul_e_not_mem dD hm (Or.inr rfl) hrel 0
  rw [dD.ofTorus_zero, one_mul] at hS
  obtain ⟨hsq, hcard⟩ := elab_closure_insert hF.1 hrel.e_sq ha hb h₃ h₄ (fun h => hS (hle h))
  exact ⟨hsq, by rw [hcard, hF.2]⟩

theorem t200inv1_elab32_e [Finite G] {j : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 2) :
    (∃ A : Subgroup G, A ≤ Subgroup.centralizer {e} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32) ∧
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * e} ∧
        (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32 := by
  rcases hj with rfl | rfl
  · have h₁ := t200inv1_elab_e dD hm hrel
    have h₂ := t200inv1_elabF_c₁e dD hm hrel
    exact ⟨⟨_, le_centralizer_of_mul_self h₁.1 (Subgroup.subset_closure (by simp)), h₁⟩,
      ⟨_, le_centralizer_of_mul_self h₂.1 (Subgroup.subset_closure (by simp)), h₂⟩⟩
  · have h₁ := t200inv1_elabF_e dD hm hrel
    have h₂ := t200inv1_elab_c₁e dD hm hrel
    exact ⟨⟨_, le_centralizer_of_mul_self h₁.1 (Subgroup.subset_closure (by simp)), h₁⟩,
      ⟨_, le_centralizer_of_mul_self h₂.1 (Subgroup.subset_closure (by simp)), h₂⟩⟩

theorem t200inv1_te_elab32_t [Finite G] {j : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 2) (v : Torus (StrothTypeIndex.t200 m).k)
    (h2 : dD.ofTorus v * dD.t * e * (dD.ofTorus v * dD.t * e) = 1) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer {dD.ofTorus v * dD.t * e} ∧
      (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32 := by
  rcases hj with rfl | rfl
  · obtain ⟨q, -, hq⟩ := t200inv1_conj_Dte_e dD hrel v h2
    have hA := t200inv1_elab_e dD hm hrel
    exact exists_elab_of_conj (g := q⁻¹) (by group) ⟨_, le_centralizer_of_mul_self hA.1 hq, hA⟩
  · obtain ⟨q, -, hq⟩ := t200inv1_conj_Dte_c₁e dD hm hrel v h2
    have hA := t200inv1_elab_c₁e dD hm hrel
    exact exists_elab_of_conj (g := q⁻¹) (by group) ⟨_, le_centralizer_of_mul_self hA.1 hq, hA⟩

theorem t200inv1_te_elab32 [Finite G] {j : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 2) (v : Torus (StrothTypeIndex.t200 m).k) (i : Bool)
    (h2 : dD.ofTorus v * dD.d8 i true false * e * (dD.ofTorus v * dD.d8 i true false * e) = 1) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer {dD.ofTorus v * dD.d8 i true false * e} ∧
      (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32 := by
  cases i
  · rw [dD.d8_ftf] at h2 ⊢
    exact t200inv1_te_elab32_t dD hm hj hrel v h2
  · set g := dD.ofTorus v * dD.d8 true true false * e with hg
    have hu := t200_u_conj_uvte dD (t200inv1_e_comm_u dD hrel).symm v
    rw [← hg, dD.d8_ftf] at hu
    have h2' : dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.t * e *
        (dD.ofTorus ((StrothTypeIndex.t200 m).action.φu v) * dD.t * e) = 1 := by
      rw [← hu, show dD.u⁻¹ * g * dD.u * (dD.u⁻¹ * g * dD.u) = dD.u⁻¹ * (g * g) * dD.u by group,
        h2]
      group
    exact exists_elab_of_conj (g := dD.u⁻¹) (by rw [← hu]; group)
      (t200inv1_te_elab32_t dD hm hj hrel _ h2')

end Stroth47Core

end CFSG.CGT.Stroth77
