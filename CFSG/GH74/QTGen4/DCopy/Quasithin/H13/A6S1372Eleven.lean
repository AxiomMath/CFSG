module

public import CFSG.Quasithin.H13.A6S1372Eleven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

theorem VH_split_F4 {x : G} (hx : x ∈ conjClosure V H) :
    (C.v : G) * x ∈ C.W ∨ x ∈ C.W := by
  obtain ⟨hxN, h⟩ := S.rho_VH_F4 hNS h13315 h1356two hH hab hx
  rcases h with h | h
  · exact Or.inr ⟨hx, (S.rho_eq_one_iff ⟨x, hxN⟩).1 h⟩
  · refine Or.inl ⟨(conjClosure V H).mul_mem C.v_mem hx, ?_⟩
    have h1 : S.frame.ρ (C.v * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, C.rho_v, h]
      exact swap45_sq
    exact (S.rho_eq_one_iff _).1 h1

theorem relIndex_W_F4 : C.W.relIndex (conjClosure V H) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
  exact ⟨C.v, C.v_mem, C.v_not_mem_W, fun x hx => C.VH_split_F4 hNS h13315 h1356two hH hab hx⟩

theorem UHg_le_A_F4 :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ C.A :=
  fun _ hx => ⟨C.UHg_le_VHg hx, (C.UHg_le_cLT_F4 hNS h13315 h1356two hH hab hx).2⟩

theorem isElemAbelian_W_of_eq_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (hAW : C.A = C.W) : IsElemAbelian 2 C.W := by
  have key : ∀ x : G, x ∈ fsuV1 T V → (C.g : G) * x * (C.g : G)⁻¹ ∈ fsuV1 T V → x = 1 := by
    intro x hx hgx
    refine C.V1g_inf_UH hab hna ?_ (S.V1_le_UH hx)
    rw [mem_conjSub, inv_inv]
    exact hgx
  have hWA : ∀ {x : G}, x ∈ C.W → (C.g : G) * x * (C.g : G)⁻¹ ∈ conjClosure V H :=
    fun {x} hx => (C.mem_VHg).1 (show x ∈ C.A by rw [hAW]; exact hx).1
  rw [F7.isElemAbelian_iff]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab hx.1 hy.1
    have h2 := S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab (hWA hx) (hWA hy)
    have e : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) *
          ((C.g : G) * x * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹)⁻¹ := by group
    rw [← e] at h2
    have h3 := key _ h1 h2
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  · have h1 := S.sq_VH_mem_V1_F4 hNS h13315 h1356two hH hab hx.1
    have h2 := S.sq_VH_mem_V1_F4 hNS h13315 h1356two hH hab (hWA hx)
    have e : (C.g : G) * (x * x) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) := by group
    rw [← e] at h2
    rw [pow_two]
    exact key _ h1 h2

theorem not_comm_VH_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (hW : IsElemAbelian 2 C.W) :
    ∃ a ∈ conjClosure V H, ∃ b ∈ conjClosure V H, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  apply hna
  rw [F7.isElemAbelian_iff]
  refine ⟨hc, fun x hx => ?_⟩
  rcases C.VH_split_F4 hNS h13315 h1356two hH hab hx with h | h
  · have h1 : ((C.v : G) * x) ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hW h
    have hvx := hc _ C.v_mem _ hx
    have e : ((C.v : G) * x) ^ 2 = (C.v : G) * C.v * x ^ 2 := by
      rw [pow_two, pow_two]
      calc (C.v : G) * x * ((C.v : G) * x) = (C.v : G) * (x * C.v) * x := by group
        _ = (C.v : G) * (C.v * x) * x := by rw [← hvx]
        _ = (C.v : G) * C.v * (x * x) := by group
    rw [e, C.v_sq, one_mul] at h1
    exact h1
  · exact F7.isElemAbelian_pow_eq_one hW h

omit hab in

theorem T_le_normalizer_W_F4 :
    T ≤ Subgroup.normalizer (C.W : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  refine A5.le_normalizer_of_forall_conj_mem fun t ht x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (hF.T_le_H ht)) x).mp
      hx.1
  · exact A5.conj_mem_centralizer_of_mem_normalizer (S.frame.T_le ht) hx.2

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem A_le_T_F4 : C.A ≤ T := fun _ hx =>
  S.cLT_le_T hhat ⟨C.VHg_le_LT_F4 hNS h13315 h1356two hH hab hx.1, hx.2⟩

theorem comm_A_UH_of_le_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (hle : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H) {a u : G} (ha : a ∈ C.A)
    (hu : u ∈ conjClosure S.V3 H) : a * u * a⁻¹ * u⁻¹ = 1 := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H (C.g_sq_mem hhat)

  have hxU : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [mem_conjSub, inv_inv]
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hgg) u).mp hu
    have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * C.g * u * ((C.g : G) * C.g)⁻¹ := by group
    rw [e]
    exact this
  have hxQ := hle hxU
  have hxC : (C.g : G) * u * (C.g : G)⁻¹ ∈
      Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    exact (C.comm_DHg_UH_F4 hNS h13315 h1356two hH hab hhat hna ⟨hxU, hxQ⟩ hu').symm

  have hy : (C.g : G) * a * (C.g : G)⁻¹ ∈ conjClosure V H := (C.mem_VHg).1 ha.1
  have h1 := S.comm_VH_HC_F4 hNS h13315 h1356two hH hxQ hxC hy
  have h2 : a * u * a⁻¹ * u⁻¹ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) := by
    rw [mem_conjSub, inv_inv]
    have e : (C.g : G) * (a * u * a⁻¹ * u⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * a * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) *
          ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h1

  have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
  have h3 : a * u * a⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 H haH) u).mp hu) ((conjClosure S.V3 H).inv_mem hu)
  exact C.V1g_inf_UH hab hna h2 h3

theorem A_eq_W_of_le_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hle : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H) :
    C.A = C.W := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hAQ : C.A ≤ pCoreOf 2 H := by
    intro a ha
    have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
    rw [hF.pCoreOf_eq_centralizerMod, mem_centralizerMod]
    refine ⟨haH, hF.H_normalizes_V₁ haH, fun u hu => ?_⟩
    rw [C.comm_A_UH_of_le_F4 hNS h13315 h1356two hH hab hhat hna hle ha hu]
    exact (fsuV1 T V).one_mem
  have hAW : C.A ≤ C.W := by
    intro a ha
    have h1 : a ∈ C.ZI := by
      rw [← C.A_inf_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314]
      exact ⟨ha, hAQ ha⟩
    exact ⟨C.ZI_le_VH h1, ha.2⟩
  have hcard : Nat.card C.A = Nat.card C.W := by
    rw [C.A_eq_conj_F4 hNS h13315 h1356two hH hab hhat, A5.card_conjSub']
  exact Subgroup.eq_of_le_of_card_ge hAW hcard.ge

theorem not_UHg_le_QH_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) : ¬ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ pCoreOf 2 H := by
  intro hle
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hAW := C.A_eq_W_of_le_F4 hNS h13315 h1356two hH hab hhat hna h13314 hle
  have hW := C.isElemAbelian_W_of_eq_F4 hNS h13315 h1356two hH hab hna hAW
  have hW2 := C.relIndex_W_F4 hNS h13315 h1356two hH hab
  have hK := C.not_comm_VH_F4 hNS h13315 h1356two hH hab hna hW

  have hconj : ∀ h ∈ H, conjSub h C.W ≤ conjClosure V H ∧
      (conjSub h C.W).relIndex (conjClosure V H) = 2 ∧ IsElemAbelian 2 (conjSub h C.W) := by
    intro h hh
    have hN := le_normalizer_conjClosure V H hh
    exact ⟨A6Eleven.conjSub_le_of_mem_normalizer C.W_le hN,
      (A6Eleven.relIndex_conjSub hN).trans hW2, F7.isElemAbelian_conjSub hW⟩
  have hHW : H ≤ Subgroup.normalizer (C.W : Set G) := by
    refine A6Eleven.le_normalizer_of_conjSub hF.T_le_H
      (A5.isSylowTwoOf_of_le S.h13.sylow hF.T_le_H).2.2
      (C.T_le_normalizer_W_F4 hNS h13315 h1356two hH) fun h₁ hh₁ h hh hne1 hne => ?_
    obtain ⟨h1K, h12, hE1⟩ := hconj h hh
    obtain ⟨h2K, h22, hE2⟩ := hconj h₁ hh₁
    exact A6Eleven.eq_of_relIndex_two C.W_le h1K h2K hW2 h12 h22 hW hE1 hE2 hK hne hne1

  apply hna
  refine F7.isElemAbelian_mono hW (conjClosure_le fun h hh x hx => ?_)
  have hxW : x ∈ C.W := by
    rw [← hAW]
    exact C.ZI_le_A_F4 hNS h13315 h1356two hH hab (C.V_le_ZI hx)
  exact (Subgroup.mem_normalizer_iff.mp (hHW hh) x).mp hxW

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
