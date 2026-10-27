module

public import CFSG.Quasithin.H13.A6S13710a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1379c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem VH_le_QH_F4 : conjClosure V H ≤ pCoreOf 2 H :=
  conjClosure_le fun _ hh v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) v).mp
      (S.V_le_QH_F4 hNS h13315 h1356two hH hab hv)

theorem VH_le_T_F4 : conjClosure V H ≤ T :=
  (S.VH_le_QH_F4 hNS h13315 h1356two hH hab).trans
    (pCoreOf_le_of_sylow S.h13.sylow (S.hypF91_F4 hNS h13315 h1356two hH).T_le_H)

theorem isPGroup_VH_F4 : IsPGroup 2 (conjClosure V H) :=
  S.h13.sylow.1.to_le (S.VH_le_T_F4 hNS h13315 h1356two hH hab)

theorem exists_conf_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) : Nonempty (S.Conf H) := by
  obtain ⟨g, hgL, hρg⟩ := S.exists_g0135
  obtain ⟨h, hh, w, hw, hwN, hρw⟩ := S.exists_conjSub_rho_45_F4 hNS h13315 h1356two hH hab hna
  have hw' : h⁻¹ * w * h ∈ V := mem_conjSub.1 hw
  have hwVH : w ∈ conjClosure V H := by
    have e : w = h * (h⁻¹ * w * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh hw'
  have hsq : w * w = 1 := by
    have h2 : (h⁻¹ * w * h) ^ 2 = 1 := S.elemAbelian_V.2 _ hw'
    have e : w * w = h * (h⁻¹ * w * h) ^ 2 * h⁻¹ := by rw [pow_two]; group
    rw [e, h2]
    group
  exact ⟨⟨g, hgL, hρg, ⟨w, hwN⟩, hwVH, hsq, hρw⟩⟩

theorem VH_le_NV_F4 :
    conjClosure V H ≤ Subgroup.normalizer (V : Set G) :=
  (S.VH_le_T_F4 hNS h13315 h1356two hH hab).trans S.frame.T_le

omit hab in

theorem T_le_normalizer_VH_F4 :
    T ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
  (S.hypF91_F4 hNS h13315 h1356two hH).T_le_H.trans (le_normalizer_conjClosure V H)

omit hab in

theorem cLT_le_normalizer_VH_F4 (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
  (S.cLT_le_T hhat).trans (S.T_le_normalizer_VH_F4 hNS h13315 h1356two hH)

namespace Conf

variable {S} (C : S.Conf H)

theorem VHg_le_NV_F4 :
    C.VHg ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  have h1 := S.VH_le_NV_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have e : x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ C.g.2) h1) C.g.2

theorem I_le_NV_F4 : C.I ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (S.VH_le_NV_F4 hNS h13315 h1356two hH hab) (C.VHg_le_NV_F4 hNS h13315 h1356two hH hab)

theorem VHg_le_LT_F4 : C.VHg ≤ L ⊔ T := by
  intro x hx
  have h1 : (C.g : G) * x * (C.g : G)⁻¹ ∈ T :=
    S.VH_le_T_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have hgLT : (C.g : G) ∈ L ⊔ T := le_sup_left (a := L) C.g_mem
  have e : x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g := by group
  rw [e]
  exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hgLT) (le_sup_right (a := L) h1)) hgLT

theorem I_le_LT_F4 : C.I ≤ L ⊔ T :=
  sup_le ((S.VH_le_T_F4 hNS h13315 h1356two hH hab).trans le_sup_right)
    (C.VHg_le_LT_F4 hNS h13315 h1356two hH hab)

theorem rho_VHg_F4 {x : G} (hx : x ∈ C.VHg) :
    ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hxN⟩ = 1 ∨ S.frame.ρ ⟨x, hxN⟩ = swap 3 4 := by
  have hxN := C.VHg_le_NV_F4 hNS h13315 h1356two hH hab hx
  refine ⟨hxN, ?_⟩
  obtain ⟨hyN, hρ⟩ := S.rho_VH_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      C.g⁻¹ * ⟨(C.g : G) * x * (C.g : G)⁻¹, hyN⟩ * C.g := by
    apply Subtype.ext
    show x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g
    group
  rw [e, map_mul, map_mul, map_inv, C.rho_g]
  rcases hρ with h | h
  · left
    rw [h, mul_one, inv_mul_cancel]
  · right
    rw [h]
    exact conj_g0135_45

theorem ZI_le_centralizer_F4 :
    C.ZI ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  obtain ⟨hxN, h1⟩ := S.rho_VH_F4 hNS h13315 h1356two hH hab (C.ZI_le_VH hx)
  obtain ⟨hxN', h2⟩ := C.rho_VHg_F4 hNS h13315 h1356two hH hab (C.ZI_le_VHg hx)
  refine (S.rho_eq_one_iff ⟨x, hxN⟩).1 ?_
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) (by decide)

theorem ZI_le_W_F4 : C.ZI ≤ C.W :=
  le_inf C.ZI_le_VH (C.ZI_le_centralizer_F4 hNS h13315 h1356two hH hab)

theorem ZI_le_A_F4 : C.ZI ≤ C.A :=
  le_inf C.ZI_le_VHg (C.ZI_le_centralizer_F4 hNS h13315 h1356two hH hab)

theorem N_le_cLT_F4 :
    C.N ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
  inf_le_inf_right _ (C.I_le_LT_F4 hNS h13315 h1356two hH hab)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hab in

theorem cLT_le_normalizer_VHg_F4 :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.VHg : Set G) := by
  have hgN : (C.g : G) ∈ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    S.le_normalizer_cLT (le_sup_left (a := L) C.g_mem)
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
  rw [mem_VHg] at hx ⊢
  have hq' : (C.g : G) * q * (C.g : G)⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hgN q).mp hq
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (S.cLT_le_normalizer_VH_F4 hNS h13315 h1356two hH hhat hq') _).mp hx
  have e : (C.g : G) * (q * x * q⁻¹) * (C.g : G)⁻¹ =
      ((C.g : G) * q * (C.g : G)⁻¹) * ((C.g : G) * x * (C.g : G)⁻¹) *
        ((C.g : G) * q * (C.g : G)⁻¹)⁻¹ := by group
  rw [e]
  exact h1

omit hab in

theorem cLT_le_normalizer_I_F4 :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.I : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
  have h1 := S.cLT_le_normalizer_VH_F4 hNS h13315 h1356two hH hhat hq
  have h2 := C.cLT_le_normalizer_VHg_F4 hNS h13315 h1356two hH hhat hq
  have hle : conjClosure V H ⊔ C.VHg ≤ C.I.comap (MulAut.conj q).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.VH_le_I ((Subgroup.mem_normalizer_iff.mp h1 y).mp hy)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.VHg_le_I ((Subgroup.mem_normalizer_iff.mp h2 y).mp hy)
  have := hle hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem isPGroup_N_F4 : IsPGroup 2 C.N :=
  S.h13.sylow.1.to_le ((C.N_le_cLT_F4 hNS h13315 h1356two hH hab).trans (S.cLT_le_T hhat))

theorem W_le_normalizer_A_F4 :
    C.W ≤ Subgroup.normalizer (C.A : Set G) := by
  intro x hx
  have hxQ : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    C.N_le_cLT_F4 hNS h13315 h1356two hH hab (C.W_le_N hx)
  have h1 := C.cLT_le_normalizer_VHg_F4 hNS h13315 h1356two hH hhat hxQ
  have hxN := S.VH_le_NV_F4 hNS h13315 h1356two hH hab (C.W_le hx)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨ha1, ha2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 a).mp ha1,
      A5.conj_mem_centralizer_of_mem_normalizer hxN ha2⟩
  · rintro ⟨ha1, ha2⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h1 a).mpr ha1, ?_⟩
    have := A5.conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hxN) ha2
    simpa [mul_assoc] using this

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
