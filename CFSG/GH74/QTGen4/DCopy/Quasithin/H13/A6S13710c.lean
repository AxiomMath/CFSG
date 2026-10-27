module

public import CFSG.Quasithin.H13.A6S13710c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem UH_le_centralizer_V_F4 :
    conjClosure S.V3 H ≤ Subgroup.centralizer (V : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hV := hF.le_pCoreOf_iff_le_centralizer.1 (S.V_le_QH_F4 hNS h13315 h1356two hH hab)
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hV hv).2 u hu).symm

theorem UH_le_cLT_F4 :
    conjClosure S.V3 H ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
  le_inf ((S.UH_le_T_F4 hNS h1356two h13315 hH).trans le_sup_right)
    (S.UH_le_centralizer_V_F4 hNS h13315 h1356two hH hab)

omit hab in

theorem comm_VH_HC_F4 {x : G} (hxQ : x ∈ pCoreOf 2 H)
    (hxC : x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G)) {y : G}
    (hy : y ∈ conjClosure V H) : y * x * y⁻¹ * x⁻¹ ∈ fsuV1 T V := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H

  let K : Subgroup G :=
    { carrier := {y | y ∈ H ∧ y * x * y⁻¹ * x⁻¹ ∈ fsuV1 T V}
      mul_mem' := by
        rintro y₁ y₂ ⟨h1H, h1⟩ ⟨h2H, h2⟩
        refine ⟨H.mul_mem h1H h2H, ?_⟩
        have e : y₁ * y₂ * x * (y₁ * y₂)⁻¹ * x⁻¹ =
            y₁ * (y₂ * x * y₂⁻¹ * x⁻¹) * y₁⁻¹ * (y₁ * x * y₁⁻¹ * x⁻¹) := by group
        rw [e, S.conj_V1_of_mem hH h1H h2]
        exact (fsuV1 T V).mul_mem h2 h1
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hyH, h⟩
        refine ⟨H.inv_mem hyH, ?_⟩
        have e : y⁻¹ * x * y⁻¹⁻¹ * x⁻¹ = y⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e, S.conj_V1_of_mem hH (H.inv_mem hyH) ((fsuV1 T V).inv_mem h)]
        exact (fsuV1 T V).inv_mem h }
  have hle : conjClosure V H ≤ K := by
    refine conjClosure_le fun h hh v hv => ⟨H.mul_mem (H.mul_mem hh (hF.V_le_H hv))
      (H.inv_mem hh), ?_⟩

    have hx'Q : h⁻¹ * x * h ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hh)) x).mp hxQ
      simpa using this
    have hx'C : h⁻¹ * x * h ∈ Subgroup.centralizer (S.V3 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : h * w * h⁻¹ ∈ conjClosure S.V3 H := mem_conjClosure hh hw
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hw'
      calc w * (h⁻¹ * x * h) = h⁻¹ * ((h * w * h⁻¹) * x) * h := by group
        _ = h⁻¹ * (x * (h * w * h⁻¹)) * h := by rw [hc]
        _ = h⁻¹ * x * h * w := by group
    have hx'N : h⁻¹ * x * h ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le (hQT hx'Q)
    have hρ := fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨_, hx'N⟩) hx'C)
    have h1 := S.comm_mem_V1_of_rho (u := ⟨_, hx'N⟩) hρ hv
    have h2 : v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹ ∈ fsuV1 T V := by
      have e : v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹ =
          ((h⁻¹ * x * h) * v * (h⁻¹ * x * h)⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact (fsuV1 T V).inv_mem h1
    have e : h * v * h⁻¹ * x * (h * v * h⁻¹)⁻¹ * x⁻¹ =
        h * (v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ := by group
    rw [e, S.conj_V1_of_mem hH hh h2]
    exact h2
  exact (hle hy).2

theorem comm_VH_mem_V_F4 {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ conjClosure V H) : x * y * x⁻¹ * y⁻¹ ∈ V :=
  ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V)
    (S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab hx hy)

namespace Conf

variable (C : S.Conf H)

theorem UH_le_W_F4 : conjClosure S.V3 H ≤ C.W :=
  le_inf (conjClosure_mono S.V3_le_V le_rfl) (S.UH_le_centralizer_V_F4 hNS h13315 h1356two hH hab)

theorem UHg_le_cLT_F4 :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [mem_conjSub, inv_inv] at hx
  have h1 := S.UH_le_cLT_F4 hNS h13315 h1356two hH hab hx
  have hgN := S.le_normalizer_cLT ((L ⊔ T).inv_mem (le_sup_left (a := L) C.g_mem))
  have := (Subgroup.mem_normalizer_iff.mp hgN _).mp h1
  have e : (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * (C.g : G)⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem VHg_inf_QH_le_A_F4 {x : G} (hx : x ∈ C.VHg)
    (hxQ : x ∈ pCoreOf 2 H) : x ∈ C.A := by
  refine ⟨hx, ?_⟩
  obtain ⟨hxN, hR⟩ := S.rho_QH_mem_R8_F4 hNS h13315 h1356two hH hxQ
  obtain ⟨hxN', h⟩ := C.rho_VHg_F4 hNS h13315 h1356two hH hab hx
  refine (S.rho_eq_one_iff ⟨x, hxN⟩).1 ?_
  rcases h with h | h
  · exact h
  · have h' : S.frame.ρ ⟨x, hxN⟩ = swap 3 4 := h
    rw [h'] at hR
    exact absurd hR swap34_not_mem_R8

theorem comm_VHg_mem_V_F4 {x y : G} (hx : x ∈ C.VHg)
    (hy : y ∈ C.VHg) : x * y * x⁻¹ * y⁻¹ ∈ V := by
  have hV := S.comm_VH_mem_V_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx) ((C.mem_VHg).1 hy)
  have key : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ ∈ V := by
    have e : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) *
          ((C.g : G) * x * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact hV
  exact (Subgroup.mem_normalizer_iff.mp C.g.2 _).mpr key

theorem c3_mod_V_F4 {x : G} (hx : x ∈ C.ZI) :
    x⁻¹ * ((C.c3 : G) * x * (C.c3 : G)⁻¹) ∈ V := by

  have hmul : ∀ a b : G, a ∈ Subgroup.normalizer (V : Set G) → x⁻¹ * (a * x * a⁻¹) ∈ V →
      x⁻¹ * (b * x * b⁻¹) ∈ V → x⁻¹ * (a * b * x * (a * b)⁻¹) ∈ V := by
    intro a b ha h1 h2
    have e : x⁻¹ * (a * b * x * (a * b)⁻¹) =
        (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * (b * x * b⁻¹)) * a⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp ha _).mp h2)
  have hv : x⁻¹ * ((C.v : G) * x * (C.v : G)⁻¹) ∈ V := by
    have := S.comm_VH_mem_V_F4 hNS h13315 h1356two hH hab ((conjClosure V H).inv_mem hx.1) C.v_mem
    have e : x⁻¹ * ((C.v : G) * x * (C.v : G)⁻¹) = x⁻¹ * C.v * x⁻¹⁻¹ * (C.v : G)⁻¹ := by group
    rw [e]
    exact this
  have hw : x⁻¹ * ((C.w : G) * x * (C.w : G)⁻¹) ∈ V := by
    have := C.comm_VHg_mem_V_F4 hNS h13315 h1356two hH hab (C.VHg.inv_mem hx.2) C.w_mem
    have e : x⁻¹ * ((C.w : G) * x * (C.w : G)⁻¹) = x⁻¹ * C.w * x⁻¹⁻¹ * (C.w : G)⁻¹ := by group
    rw [e]
    exact this
  have hr : x⁻¹ * ((C.r : G) * x * (C.r : G)⁻¹) ∈ V := by
    rw [r_coe]
    exact hmul _ _ C.v.2 hv hw
  have hrN : (C.r : G) ∈ Subgroup.normalizer (V : Set G) := C.r.2
  have hpow : ∀ k : ℕ, x⁻¹ * ((C.r : G) ^ k * x * ((C.r : G) ^ k)⁻¹) ∈ V := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ _ (Subgroup.pow_mem _ hrN k) ih hr
  rw [c3_coe]
  exact hpow _

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem UHg_le_normalizer_UH_F4 :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤
      Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
  (C.UHg_le_cLT_F4 hNS h13315 h1356two hH hab).trans ((S.cLT_le_T hhat).trans
    ((S.hypF91_F4 hNS h13315 h1356two hH).T_le_H.trans (le_normalizer_conjClosure _ _)))

theorem comm_DH_UHg_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {d u : G} (hd : d ∈ conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H))
    (hu : u ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) : d * u = u * d := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hne : conjSub (C.g : G)⁻¹ (fsuV1 T V) ≠ fsuV1 T V := by
    intro h
    apply C.V1g_not_le_UH hab hna
    rw [h]
    exact S.V1_le_UH
  have h1 : ⁅d, u⁆ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) :=
    (hF.F96_3 hne).1 (Subgroup.commutator_mem_commutator
      ⟨conjClosure_mono S.V3_le_V le_rfl hd.1, hd.2⟩ hu)
  have h2 : ⁅d, u⁆ ∈ conjClosure S.V3 H := by
    rw [commutatorElement_def]
    have h3 : u * d⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (C.UHg_le_normalizer_UH_F4 hNS h13315 h1356two hH hab hhat
        hu) _).mp ((conjClosure S.V3 H).inv_mem hd.1)
    have e : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
    rw [e]
    exact (conjClosure S.V3 H).mul_mem hd.1 h3
  have h4 := C.V1g_inf_UH hab hna h1 h2
  rw [commutatorElement_def] at h4
  calc d * u = d * u * d⁻¹ * u⁻¹ * (u * d) := by group
    _ = u * d := by rw [h4, one_mul]

theorem comm_DHg_UH_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {x u : G} (hx : x ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H)
    (hu : u ∈ conjClosure S.V3 H) : x * u = u * x := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hsq := C.g_sq_mem hhat
  have h2 := (hF.F96_2 C.g_mem C.g_mem rfl hsq).1
  rw [← h2, mem_conjSub, inv_inv] at hx
  have hgu : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [mem_conjSub, inv_inv]
    have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H hsq
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hgg) u).mp hu
    have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * C.g * u * ((C.g : G) * C.g)⁻¹ := by group
    rw [e]
    exact this
  have h := C.comm_DH_UHg_F4 hNS h13315 h1356two hH hab hhat hna hx hgu
  have e1 : (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) =
      (C.g : G) * (x * u) * (C.g : G)⁻¹ := by group
  have e2 : (C.g : G) * u * (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) =
      (C.g : G) * (u * x) * (C.g : G)⁻¹ := by group
  rw [e1, e2] at h
  simpa using h

theorem DHg_le_ZI_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H ≤ C.ZI := by
  intro x hx
  have hxA := C.VHg_inf_QH_le_A_F4 hNS h13315 h1356two hH hab
    (C.UHg_le_VHg hx.1) hx.2
  have hxC : x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (C.comm_DHg_UH_F4 hNS h13315 h1356two hH hab hhat hna hx hu).symm
  have h1 := S.comm_VH_HC_F4 hNS h13315 h1356two hH hx.2 hxC C.v_mem
  exact (C.dmod_F4 hNS h13315 h1356two hH hab hhat).fix_v_A hxA
    (C.V_le_ZI (((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V) h1))

theorem EHg_le_ZI_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) : C.VHg ⊓ pCoreOf 2 H ≤ C.ZI := by
  intro x hx
  have hD := C.dmod_F4 hNS h13315 h1356two hH hab hhat
  have hxA := C.VHg_inf_QH_le_A_F4 hNS h13315 h1356two hH hab hx.1 hx.2

  have hu : (C.v : G) * x * (C.v : G)⁻¹ * x⁻¹ ∈ conjClosure S.V3 H := by
    rw [← S.comm_VH_QH_eq_F4 hNS h13315 h1356two hH h13314]
    exact Subgroup.commutator_mem_commutator C.v_mem hx.2
  have huW := C.UH_le_W_F4 hNS h13315 h1356two hH hab hu
  have hxu : ((C.v : G) * x * (C.v : G)⁻¹ * x⁻¹) * ((C.v : G) * x * (C.v : G)⁻¹ * x⁻¹)⁻¹ ∈
      C.ZI := by
    rw [mul_inv_cancel]; exact C.ZI.one_mem
  have h1 := hD.beta_eq huW hxA hxu
  set u := (C.v : G) * x * (C.v : G)⁻¹ * x⁻¹ with hu_def
  set d := ((C.v : G) * C.w * C.v)⁻¹ * u⁻¹ * ((C.v : G) * C.w * C.v) with hd_def

  have hdU : d ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [(C.F96_y_F4 hNS h13315 h1356two hH hab).2.2.1, mem_conjSub, inv_inv]
    have e : (C.y : G) * d * (C.y : G)⁻¹ = u⁻¹ := by rw [hd_def, y_coe]; group
    rw [e]
    exact (conjClosure S.V3 H).inv_mem hu
  have hdQ : d ∈ pCoreOf 2 H := by
    have e : d = (x * d⁻¹)⁻¹ * x := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem
      (S.VH_le_QH_F4 hNS h13315 h1356two hH hab (C.ZI_le_VH h1))) hx.2
  have hdZ := C.DHg_le_ZI_F4 hNS h13315 h1356two hH hab hhat hna ⟨hdU, hdQ⟩
  have e : x = (x * d⁻¹) * d := by group
  rw [e]
  exact C.ZI.mul_mem h1 hdZ

theorem A_inf_QH_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) : C.A ⊓ pCoreOf 2 H = C.ZI := by
  refine le_antisymm (fun x hx => C.EHg_le_ZI_F4 hNS h13315 h1356two hH hab hhat hna h13314
    ⟨hx.1.1, hx.2⟩) (le_inf (C.ZI_le_A_F4 hNS h13315 h1356two hH hab) ?_)
  exact C.ZI_le_VH.trans (S.VH_le_QH_F4 hNS h13315 h1356two hH hab)

theorem A_eq_F4 : C.A = C.VHg ⊓ pCoreOf 2 (L ⊔ T) := by
  rw [← S.cT]
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, S.cLT_le_T hhat ⟨C.VHg_le_LT_F4 hNS h13315 h1356two hH hab hx.1, hx.2⟩, hx.2⟩
  · intro x hx
    exact ⟨hx.1, hx.2.2⟩

theorem exists_card_N_F4 : ∃ e : ℕ, Nat.card C.N = 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.1 (C.isPGroup_N_F4 hNS h13315 h1356two hH hab hhat)

theorem rho_c3_F4 : S.frame.ρ C.c3 = swap 4 5 * swap 3 4 := by
  obtain ⟨e, he⟩ := C.exists_card_N_F4 hNS h13315 h1356two hH hab hhat
  have h3 : (swap (4 : Fin 6) 5 * swap 3 4) ^ 3 = 1 := by decide
  rw [c3, map_pow, C.rho_r, pow_eq_pow_mod _ h3, he, two_pow_sq_mod_three, pow_one]

theorem c3_fix_F4 {x : G} (hx : x ∈ C.N)
    (hc : (C.c3 : G) * x * (C.c3 : G)⁻¹ * x⁻¹ ∈ C.ZI) : x ∈ C.ZI := by
  have hD := C.dmod_F4 hNS h13315 h1356two hH hab hhat
  obtain ⟨e, he⟩ := C.exists_card_N_F4 hNS h13315 h1356two hH hab hhat

  obtain ⟨m, hm⟩ : ∃ m, Nat.card C.N ^ 2 = 3 * m + 1 := by
    refine ⟨Nat.card C.N ^ 2 / 3, ?_⟩
    have := Nat.div_add_mod (Nat.card C.N ^ 2) 3
    rw [he, two_pow_sq_mod_three] at this
    rw [he]
    omega
  have hr3 : (C.r : G) ^ 3 ∈ C.N := C.r_cube_mem_N
  have hNF : ∀ n ∈ C.N, n ∈ DMod.fixMod C.ZI x := fun n hn =>
    ⟨C.N_le_normalizer_ZI_F4 hNS h13315 h1356two hH hab hhat hn, hD.comm n hn x hx⟩
  have hrZ : (C.r : G) ∈ Subgroup.normalizer (C.ZI : Set G) := by
    rw [r_coe]; exact Subgroup.mul_mem _ hD.vZ hD.wZ
  have hcF : (C.c3 : G) ∈ DMod.fixMod C.ZI x := by
    refine ⟨?_, hc⟩
    rw [c3_coe]
    exact Subgroup.pow_mem _ hrZ _
  have hrF : (C.r : G) ∈ DMod.fixMod C.ZI x := by
    have e1 : (C.r : G) = (((C.r : G) ^ 3) ^ m)⁻¹ * C.c3 := by
      rw [c3_coe, hm, ← pow_mul, pow_succ]
      group
    rw [e1]
    exact (DMod.fixMod C.ZI x).mul_mem
      ((DMod.fixMod C.ZI x).inv_mem (hNF _ (C.N.pow_mem hr3 m))) hcF
  exact hD.fix_r hx hrF.2

theorem nu_c3_ZI_F4 : nu (C.c3 : G) C.ZI = 4 := by
  have hVZ := C.V_le_ZI
  have hZV : C.ZI ≤ Subgroup.normalizer (V : Set G) :=
    C.ZI_le_VH.trans (S.VH_le_NV_F4 hNS h13315 h1356two hH hab)
  rw [nu_mul (C.c3 : G) hVZ (inf_le_left.trans hZV),
    relIndex_cfix_sup_eq_one (C.c3_cube) hVZ
      (by rw [S.card_V]; decide)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp C.c3.2 y).mp hy)
      (fun x hx => C.c3_mod_V_F4 hNS h13315 h1356two hH hab hx),
    one_mul, nu_V C.c3 (C.rho_c3_F4 hNS h13315 h1356two hH hab hhat)]

theorem nu_c3_N_F4 :
    nu (C.c3 : G) C.N = C.ZI.relIndex C.N * 4 := by
  have hZN : C.ZI ≤ C.N := (C.ZI_le_W_F4 hNS h13315 h1356two hH hab).trans C.W_le_N
  rw [nu_mul (C.c3 : G) hZN (inf_le_left.trans (C.N_le_normalizer_ZI_F4 hNS h13315 h1356two hH hab
    hhat)), cfix_sup_eq_of_fpf (fun x hx h => C.c3_fix_F4 hNS h13315 h1356two hH hab hhat hx h),
    C.nu_c3_ZI_F4 hNS h13315 h1356two hH hab hhat]

omit hab in

theorem cLT_le_normalizer_N_F4 :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.N : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (C.cLT_le_normalizer_I_F4 hNS h13315 h1356two hH hhat hq) x).mp hx.1
  · exact A5.conj_mem_centralizer_of_mem_normalizer (S.frame.T_le (S.cLT_le_T hhat hq)) hx.2

theorem nu_c3_Q_N_F4 :
    nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) = nu (C.c3 : G) C.N := by
  have hNQ := C.N_le_cLT_F4 hNS h13315 h1356two hH hab
  have hc3I := C.c3_mem_I
  have hcN : ∀ n ∈ C.N, (C.c3 : G) * n * (C.c3 : G)⁻¹ ∈ C.N := by
    intro n hn
    refine ⟨C.I.mul_mem (C.I.mul_mem hc3I hn.1) (C.I.inv_mem hc3I), ?_⟩
    exact A5.conj_mem_centralizer_of_mem_normalizer C.c3.2 hn.2
  have h3 : ¬ 3 ∣ Nat.card C.N := by
    obtain ⟨e, he⟩ := C.exists_card_N_F4 hNS h13315 h1356two hH hab hhat
    rw [he]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hcX : ∀ q ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G),
      q⁻¹ * ((C.c3 : G) * q * (C.c3 : G)⁻¹) ∈ C.N := by
    intro q hq
    have hqI := C.cLT_le_normalizer_I_F4 hNS h13315 h1356two hH hhat
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)).inv_mem hq)
    have h1 : q⁻¹ * C.c3 * q⁻¹⁻¹ ∈ C.I := (Subgroup.mem_normalizer_iff.mp hqI _).mp hc3I
    refine ⟨?_, ?_⟩
    · have e : q⁻¹ * ((C.c3 : G) * q * (C.c3 : G)⁻¹) = (q⁻¹ * C.c3 * q⁻¹⁻¹) * (C.c3 : G)⁻¹ := by
        group
      rw [e]
      exact C.I.mul_mem h1 (C.I.inv_mem hc3I)
    · exact (Subgroup.centralizer (V : Set G)).mul_mem
        ((Subgroup.centralizer (V : Set G)).inv_mem hq.2)
        (A5.conj_mem_centralizer_of_mem_normalizer C.c3.2 hq.2)
  rw [nu_mul (C.c3 : G) hNQ (inf_le_left.trans (C.cLT_le_normalizer_N_F4 hNS h13315 h1356two hH
    hhat)), relIndex_cfix_sup_eq_one (C.c3_cube) hNQ h3 hcN hcX,
    one_mul]

theorem A_eq_conj_F4 : C.A = conjSub (C.y : G)⁻¹ C.W := by
  have hD := C.dmod_F4 hNS h13315 h1356two hH hab hhat
  ext x
  rw [mem_conjSub, inv_inv]
  constructor
  · intro hx
    exact hD.yA x hx
  · intro hx
    have := hD.yW _ hx
    have e : ((C.v : G) * C.w * C.v)⁻¹ * ((C.y : G) * x * (C.y : G)⁻¹) * ((C.v : G) * C.w * C.v) =
        x := by rw [y_coe]; group
    rwa [e] at this

theorem relIndex_ZI_N_F4 :
    C.ZI.relIndex C.N = (C.ZI.relIndex C.A) ^ 2 := by
  have hD := C.dmod_F4 hNS h13315 h1356two hH hab hhat
  have hWA : C.W ⊓ C.A = C.ZI :=
    le_antisymm (fun x hx => hD.WA x hx.1 hx.2) (le_inf hD.ZW hD.ZA)
  have hcardWA : Nat.card C.W = Nat.card C.A := by
    rw [C.A_eq_conj_F4 hNS h13315 h1356two hH hab hhat, A5.card_conjSub']
  have hprod := card_sup_mul_card_inf' (C.W_le_normalizer_A_F4 hNS h13315 h1356two hH hab hhat)
  rw [← C.N_eq_F4 hNS h13315 h1356two hH hab hhat, hWA, hcardWA] at hprod
  have r1 := Subgroup.relIndex_mul_card C.ZI C.N
  have r2 := Subgroup.relIndex_mul_card C.ZI C.A
  rw [inf_eq_left.2 (hD.ZW.trans hD.WN)] at r1
  rw [inf_eq_left.2 hD.ZA] at r2
  have hpos : 0 < Nat.card C.ZI := Nat.card_pos
  have key : C.ZI.relIndex C.N * (Nat.card C.ZI * Nat.card C.ZI) =
      (C.ZI.relIndex C.A) ^ 2 * (Nat.card C.ZI * Nat.card C.ZI) := by
    calc C.ZI.relIndex C.N * (Nat.card C.ZI * Nat.card C.ZI)
        = (C.ZI.relIndex C.N * Nat.card C.ZI) * Nat.card C.ZI := by ring
      _ = Nat.card C.A * Nat.card C.A := by rw [r1, hprod]
      _ = (C.ZI.relIndex C.A * Nat.card C.ZI) * (C.ZI.relIndex C.A * Nat.card C.ZI) := by
          rw [r2]
      _ = (C.ZI.relIndex C.A) ^ 2 * (Nat.card C.ZI * Nat.card C.ZI) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos) key

theorem nu_cQ_F4 :
    nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) =
      4 * (C.ZI.relIndex C.A) ^ 2 := by
  rw [C.nu_c3_Q_N_F4 hNS h13315 h1356two hH hab hhat, C.nu_c3_N_F4 hNS h13315 h1356two hH hab hhat,
    C.relIndex_ZI_N_F4 hNS h13315 h1356two hH hab hhat, mul_comm]

omit hhat in

theorem c3_mem_L_F4 : (C.c3 : G) ∈ L := by
  have hcLT : (C.c3 : G) ∈ L ⊔ T := C.I_le_LT_F4 hNS h13315 h1356two hH hab C.c3_mem_I
  have hx : (C.c3 : G) ∈ ((L : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL]
    exact hcLT
  obtain ⟨l, hl, t, ht, hlt⟩ := Set.mem_mul.mp hx
  obtain ⟨a, ha⟩ := S.h13.sylow.1 ⟨t, ht⟩
  have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨l', hl', he⟩ := A5.pow_mem_mul_of_normalizes hl (S.T_le_NL ht) (2 ^ a)
  rw [hta, mul_one, hlt] at he
  have h3 := C.c3_cube
  have h4 : (C.c3 : G) = ((C.c3 : G) ^ 2 ^ a) ^ 2 ^ a := by
    rw [← pow_mul, ← mul_pow, show (2 * 2 : ℕ) = 4 by norm_num, pow_eq_pow_mod _ h3,
      Nat.pow_mod]
    norm_num
  rw [h4, he]
  exact L.pow_mem hl' _

theorem exists_c1_F4 :
    ∃ c₁ : ↥(Subgroup.normalizer (V : Set G)), (c₁ : G) ∈ S.L1 ∧ (c₁ : G) ^ 3 = 1 ∧
      S.frame.ρ c₁ = swap 0 1 * swap 1 2 ∧
      nu (c₁ : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) =
        nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L _).2 conj_354_012.1
  refine ⟨l * C.c3 * l⁻¹, ?_, ?_, ?_, ?_⟩
  ·
    have hρ : S.frame.ρ (l * C.c3 * l⁻¹) = swap 0 1 * swap 1 2 := by
      rw [map_mul, map_mul, map_inv, hρl, C.rho_c3_F4 hNS h13315 h1356two hH hab hhat]
      exact conj_354_012.2
    have hc1L : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact L.mul_mem (L.mul_mem hlL (C.c3_mem_L_F4 hNS h13315 h1356two hH hab)) (L.inv_mem hlL)
    have hfix := fix_e0123_of (S.frame.ρ (l * C.c3 * l⁻¹)) (by rw [hρ]; exact c012_fix45.1)
      (by rw [hρ]; exact c012_fix45.2)
    have hz : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
        ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = S.z := by
      refine (S.conj_eq_iff _ ⟨S.z, S.z_mem_V⟩).2 ?_
      rw [S.psi_z]
      exact Subtype.ext hfix
    have hN : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
        Subgroup.normalizer (fsuV1 T V : Set G) := by
      rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
      calc ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z =
          ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
            ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ *
              ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) := by group
        _ = S.z * ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) := by rw [hz]
    refine Subgroup.subset_closure ⟨⟨hc1L, hN⟩, 3, by decide, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, C.c3_cube]
    group
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, C.c3_cube]
    group
  · rw [map_mul, map_mul, map_inv, hρl, C.rho_c3_F4 hNS h13315 h1356two hH hab hhat]
    exact conj_354_012.2
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact nu_conj (S.le_normalizer_cLT (le_sup_left (a := L) hlL))

end Hat

end Conf

end NonAb

variable (S)

end Setting4

end CFSG.Quasithin.H13.A6
