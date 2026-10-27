module

public import CFSG.Quasithin.H13.A6S1379a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1373

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V3_lt_UH_F4 (h13315 : Stmt13_3_15_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    S.V3 < conjClosure S.V3 H := by
  refine lt_of_le_of_ne (le_conjClosure _ _) fun h => hH.2.2 ?_
  have hN : H ≤ Subgroup.normalizer (S.V3 : Set G) := by
    rw [h]
    exact le_normalizer_conjClosure _ _
  exact ((le_inf hH.2.1 hN).trans (S.G1_inf_G3_le_F4 h13315)).trans S.NV_le_M

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem comm_conjSub_mem_V1_F4 {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) {x y : G} (hx : x ∈ conjSub a V) (hy : y ∈ conjSub b V) :
    x * y * x⁻¹ * y⁻¹ ∈ fsuV1 T V := by
  rw [mem_conjSub] at hx
  have hy' : a⁻¹ * y * a ∈ conjSub (a⁻¹ * b) V := by
    rw [mem_conjSub] at hy ⊢
    have e : (a⁻¹ * b)⁻¹ * (a⁻¹ * y * a) * (a⁻¹ * b) = b⁻¹ * y * b := by group
    rw [e]
    exact hy
  obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V_F4 hNS h13315 h1356two hH hab
    (H.mul_mem (H.inv_mem ha) hb) hy'
  have h1 := S.comm_mem_V1_of_rho (u := ⟨_, hwN⟩) hρ hx

  have h2 : (a⁻¹ * x * a) * (a⁻¹ * y * a) * (a⁻¹ * x * a)⁻¹ * (a⁻¹ * y * a)⁻¹ ∈ fsuV1 T V := by
    have e : (a⁻¹ * x * a) * (a⁻¹ * y * a) * (a⁻¹ * x * a)⁻¹ * (a⁻¹ * y * a)⁻¹ =
        ((a⁻¹ * y * a) * (a⁻¹ * x * a) * (a⁻¹ * y * a)⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
    rw [e]
    exact (fsuV1 T V).inv_mem h1
  have e : x * y * x⁻¹ * y⁻¹ =
      a * ((a⁻¹ * x * a) * (a⁻¹ * y * a) * (a⁻¹ * x * a)⁻¹ * (a⁻¹ * y * a)⁻¹) * a⁻¹ := by group
  rw [e, S.conj_V1_of_mem hH ha h2]
  exact h2

theorem comm_VH_mem_V1_F4 {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ conjClosure V H) : x * y * x⁻¹ * y⁻¹ ∈ fsuV1 T V := by

  let C : G → Subgroup G := fun y =>
    { carrier := {x | x ∈ H ∧ x * y * x⁻¹ * y⁻¹ ∈ fsuV1 T V}
      mul_mem' := by
        rintro x₁ x₂ ⟨h1H, h1⟩ ⟨h2H, h2⟩
        refine ⟨H.mul_mem h1H h2H, ?_⟩
        have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
            x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹ * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
        rw [e, S.conj_V1_of_mem hH h1H h2]
        exact (fsuV1 T V).mul_mem h2 h1
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hxH, h⟩
        refine ⟨H.inv_mem hxH, ?_⟩
        have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e, S.conj_V1_of_mem hH (H.inv_mem hxH) ((fsuV1 T V).inv_mem h)]
        exact (fsuV1 T V).inv_mem h }
  have hVH : conjClosure V H ≤ H :=
    conjClosure_le fun a ha v hv =>
      H.mul_mem (H.mul_mem ha ((S.hypF91_F4 hNS h13315 h1356two hH).V_le_H hv)) (H.inv_mem ha)

  have hgen : ∀ b ∈ H, ∀ w ∈ V, conjClosure V H ≤ C (b * w * b⁻¹) := by
    intro b hb w hw
    refine conjClosure_le fun a ha v hv => ⟨hVH (mem_conjClosure ha hv), ?_⟩
    exact S.comm_conjSub_mem_V1_F4 hNS h13315 h1356two hH hab ha hb (mul_mem_conjSub hv)
      (mul_mem_conjSub hw)

  let D : Subgroup G :=
    { carrier := {y | y ∈ H ∧ x * y * x⁻¹ * y⁻¹ ∈ fsuV1 T V}
      mul_mem' := by
        rintro y₁ y₂ ⟨h1H, h1⟩ ⟨h2H, h2⟩
        refine ⟨H.mul_mem h1H h2H, ?_⟩
        have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
            (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e, S.conj_V1_of_mem hH h1H h2]
        exact (fsuV1 T V).mul_mem h1 h2
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hyH, h⟩
        refine ⟨H.inv_mem hyH, ?_⟩
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e, S.conj_V1_of_mem hH (H.inv_mem hyH) ((fsuV1 T V).inv_mem h)]
        exact (fsuV1 T V).inv_mem h }
  have hD : conjClosure V H ≤ D :=
    conjClosure_le fun b hb w hw => ⟨hVH (mem_conjClosure hb hw), (hgen b hb w hw hx).2⟩
  exact (hD hy).2

theorem sq_VH_mem_V1_F4 {x : G} (hx : x ∈ conjClosure V H) :
    x * x ∈ fsuV1 T V := by
  let E : Subgroup G :=
    { carrier := {x | x ∈ conjClosure V H ∧ x * x ∈ fsuV1 T V}
      mul_mem' := by
        rintro x₁ x₂ ⟨h1U, h1⟩ ⟨h2U, h2⟩
        refine ⟨(conjClosure V H).mul_mem h1U h2U, ?_⟩
        have hc := S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab h2U h1U
        have hHx₁ : x₁ ∈ H := conjClosure_le (K := H) (fun a ha v hv => H.mul_mem
          (H.mul_mem ha ((S.hypF91_F4 hNS h13315 h1356two hH).V_le_H hv)) (H.inv_mem ha)) h1U

        have e : x₁ * x₂ * (x₁ * x₂) =
            x₁ * ((x₂ * x₁ * x₂⁻¹ * x₁⁻¹) * (x₁ * x₁)) * x₁⁻¹ * (x₂ * x₂) := by group
        rw [e, S.conj_V1_of_mem hH hHx₁ ((fsuV1 T V).mul_mem hc h1)]
        exact (fsuV1 T V).mul_mem ((fsuV1 T V).mul_mem hc h1) h2
      one_mem' := ⟨(conjClosure V H).one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hxU, h⟩
        refine ⟨(conjClosure V H).inv_mem hxU, ?_⟩
        have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        rw [e]
        exact (fsuV1 T V).inv_mem h }
  have hE : conjClosure V H ≤ E := by
    refine conjClosure_le fun a ha v hv => ⟨mem_conjClosure ha hv, ?_⟩
    have hv2 : v * v = 1 := by
      rw [← pow_two]
      exact S.elemAbelian_V.2 v hv
    have e : a * v * a⁻¹ * (a * v * a⁻¹) = a * (v * v) * a⁻¹ := by group
    rw [e, hv2, mul_one, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  exact (hE hx).2

theorem exists_conjSub_rho_45_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    ∃ h ∈ H, ∃ w ∈ conjSub h V, ∃ hwN : w ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨w, hwN⟩ = swap 4 5 := by
  by_contra hcon
  push Not at hcon
  apply hna
  refine HypF91.isElemAbelian_conjClosure_of_forall S.elemAbelian_V fun k hk v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V_F4 hNS h13315 h1356two hH hab hk hw
  rcases hρ with h1 | h45
  · exact (Subgroup.mem_centralizer_iff.mp ((S.rho_eq_one_iff ⟨w, hwN⟩).1 h1) v hv).symm
  · exact absurd h45 (hcon k hk w hw hwN)

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
