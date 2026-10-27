module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Nm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84g4_swap_of_map (ht : t * t = 1) {A A2 : Subgroup G}
    (h : A2 = A.map (MulAut.conj t).toMonoidHom) :
    (∀ a ∈ A, t * a * t⁻¹ ∈ A2) ∧ ∀ b ∈ A2, t * b * t⁻¹ ∈ A := by
  subst h
  refine ⟨fun a ha => Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, fun b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  have e : t * (MulAut.conj t).toMonoidHom a * t⁻¹ = a := by
    show t * (t * a * t⁻¹) * t⁻¹ = a
    calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
      _ = a := by rw [ht, hti]; group
  rw [e]
  exact ha

theorem sec8t84g4_map_conj_mul {γ d : G} {X : Subgroup G} (hd : d ∈ normalizer (X : Set G)) :
    X.map (MulAut.conj (γ * d)).toMonoidHom = X.map (MulAut.conj γ).toMonoidHom := by
  have h1 : X.map (MulAut.conj (γ * d)).toMonoidHom =
      (X.map (MulAut.conj d).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have h2 : X.map (MulAut.conj d).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hd
  rw [h1, h2]

theorem sec8t84g4_V2_le (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : V2 ≤ T2 := by
  intro y hy
  rw [D.V2_eq] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact D.swap1 x (D.mod1.V_le hx)

theorem sec8t84g4_F2_le (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F2 ≤ T2 := by
  intro y hy
  rw [D.F2_eq] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact D.swap1 x (D.mod1.F_le hx)

theorem sec8t84g4_U_le (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    V1 ⊔ F1 ≤ T1 ∧ V2 ⊔ F2 ≤ T2 :=
  ⟨sup_le D.mod1.V_le D.mod1.F_le, sup_le (sec8t84g4_V2_le D) (sec8t84g4_F2_le D)⟩

theorem sec8t84g4_U2_eq (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    V2 ⊔ F2 = (V1 ⊔ F1).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_sup, D.V2_eq, D.F2_eq]

theorem sec8t84g4_U_swap (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (∀ a ∈ V1 ⊔ F1, t * a * t⁻¹ ∈ V2 ⊔ F2) ∧ ∀ b ∈ V2 ⊔ F2, t * b * t⁻¹ ∈ V1 ⊔ F1 :=
  sec8t84g4_swap_of_map D.t_sq (sec8t84g4_U2_eq D)

theorem sec8t84g4_norm_VF (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    ∀ d ∈ T1 ⊔ T2, d ∈ normalizer (V1 : Set G) ∧ d ∈ normalizer (V2 : Set G) ∧
      d ∈ normalizer (F1 : Set G) ∧ d ∈ normalizer (F2 : Set G) := by
  intro d hd
  obtain ⟨hV1, hV2⟩ := sec8t84g4_norm_prod D.wr D.mod1.V_le (sec8t84g4_V2_le D)
    D.mod1.V_norm (sec8t84g4_swap_of_map D.t_sq D.V2_eq).1
    (sec8t84g4_swap_of_map D.t_sq D.V2_eq).2 d hd
  obtain ⟨hF1, hF2⟩ := sec8t84g4_norm_prod D.wr D.mod1.F_le (sec8t84g4_F2_le D)
    D.mod1.F_norm (sec8t84g4_swap_of_map D.t_sq D.F2_eq).1
    (sec8t84g4_swap_of_map D.t_sq D.F2_eq).2 d hd
  exact ⟨hV1, hV2, hF1, hF2⟩

theorem sec8t84g4_diag_V1 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    sec8t84g4_diagSub D.wr V1 = E ⊓ centralizer ({t} : Set G) := by
  have h := sec8t84g4_sup_cent D.wr D.mod1.V_le (sec8t84g4_V2_le D)
    (sec8t84g4_swap_of_map D.t_sq D.V2_eq).1
  calc sec8t84g4_diagSub D.wr V1 = (V1 ⊔ V2) ⊓ centralizer ({t} : Set G) := h.symm
    _ = E ⊓ centralizer ({t} : Set G) := by rw [← D.E_eq]

theorem sec8t84g4_diag_F1 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    sec8t84g4_diagSub D.wr F1 = (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) :=
  (sec8t84g4_sup_cent D.wr D.mod1.F_le (sec8t84g4_F2_le D)
    (sec8t84g4_swap_of_map D.t_sq D.F2_eq).1).symm

theorem sec8t84g4_W_eq (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    E ⊔ (F1 ⊔ F2) = (V1 ⊔ F1) ⊔ (V2 ⊔ F2) := by
  rw [D.E_eq]
  exact sup_sup_sup_comm V1 V2 F1 F2

theorem sec8t84g4_diag_U1 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    sec8t84g4_diagSub D.wr (V1 ⊔ F1) = (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) := by
  rw [sec8t84g4_W_eq D]
  exact (sec8t84g4_sup_cent D.wr (sec8t84g4_U_le D).1 (sec8t84g4_U_le D).2
    (sec8t84g4_U_swap D).1).symm

end CFSG.OddStandard.SmallF3.Omega
