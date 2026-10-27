module

public import CFSG.Quasithin.H13.A5S1515b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1515a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

structure Pf1515_F4 (S : Setting G T L V) (H : Subgroup G) where

  h1323 : Input1323Two_F4

  hG248 : StmtG248

  hC113 : StmtC113c

  hH : H ∈ S.Hz

  hn : H ≤ Subgroup.normalizer (S.L1 : Set G)

  hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)

  g : G
  g_mem : g ∈ H

  hQ8 : IsQ8Sq ↥(S.V3 ⊔ conjSub g⁻¹ S.V3)

  hS3 : ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub g⁻¹ V)).Normal,
    Nonempty (↥(V ⊔ conjSub g⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub g⁻¹ V) ≃*
      Equiv.Perm (Fin 3))

  hUI : (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H = S.V3 ⊔ conjSub g⁻¹ S.V3

  C : Q8Coords (conjClosure S.V3 H)

  Cz : C.z = S.z

  c : ↥(Subgroup.normalizer (V : Set G))
  c_mem : (c : G) ∈ S.L1
  c_rho : S.frame.ρ c = c3p

  v : G
  v_mem : v ∈ V
  v_not : v ∉ pCoreOf 2 H

namespace Pf1515_F4
open CFSG.Quasithin.H13.A5.Setting.Pf1515_F4

variable {S : Setting G T L V} {H : Subgroup G} (P : Pf1515_F4 S H)
include P

theorem hF_F4 : HypF91 T V L S.V1 S.V3 H := S.hypF91_F4 P.h1323 P.hH

theorem L1_le_H_F4 : S.L1 ≤ H := le_sup_left.trans P.hH.1.1

theorem T_le_H_F4 : T ≤ H := le_sup_right.trans P.hH.1.1

theorem U_le_Q_F4 : conjClosure S.V3 H ≤ pCoreOf 2 H := P.hF_F4.conjClosure_Vp_le_pCoreOf

theorem Q_le_T_F4 : pCoreOf 2 H ≤ T := by
  obtain ⟨P', hP'⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have := pCoreOf_two_le_sylow H P' (hP' ▸ P.T_le_H_F4)
  rwa [hP'] at this

theorem comm_z_F4 {x : G} (hx : x ∈ H) : x * S.z = S.z * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (P.hH.2.1 hx)

theorem G248_F4 : IsShort2 L ∧ IsAltType L 5 ∧ pCoreOf 2 L = V ∧
    conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) := by
  obtain ⟨l, hl, hlN⟩ := S.exists_L_not_normalizer_V1
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := S.G248_data_F4 P.h1323 P.hG248 P.hH P.hn P.hna hl hlN
  exact ⟨h2, h3, h4, h5, h6⟩

theorem pCoreOf_L_F4 : pCoreOf 2 L = V := P.G248_F4.2.2.1

theorem U_eq_F4 : conjClosure S.V3 H = pCoreOf 2 S.L1 := P.G248_F4.2.2.2.1

theorem card_U_F4 : Nat.card (conjClosure S.V3 H) = 32 := P.G248_F4.2.2.2.2.1

theorem Idata_F4 : S.V3 ⊔ conjSub P.g⁻¹ S.V3 = conjClosure S.V3 H ∧
    pCoreOf 2 (V ⊔ conjSub P.g⁻¹ V) = conjClosure S.V3 H ∧
    Nat.card (pCoreOf 2 (V ⊔ conjSub P.g⁻¹ V)) = 32 ∧
    Nonempty (oTwoQuot ↥(V ⊔ conjSub P.g⁻¹ V) ≃* Equiv.Perm (Fin 3)) :=
  S.I_data_F4 P.h1323 P.hG248 P.hH P.hn P.hna P.g_mem P.hQ8 P.hS3 P.hUI

theorem I_inf_Q_F4 : (V ⊔ conjSub P.g⁻¹ V) ⊓ pCoreOf 2 H = conjClosure S.V3 H :=
  P.hUI.trans P.Idata_F4.1

theorem I_le_H_F4 : V ⊔ conjSub P.g⁻¹ V ≤ H := sup_le P.hF_F4.V_le_H (P.hF_F4.conjSub_inv_le_H P.g_mem)

theorem U_le_I_F4 : conjClosure S.V3 H ≤ V ⊔ conjSub P.g⁻¹ V := by
  rw [← P.I_inf_Q_F4]
  exact inf_le_left

theorem mem_Q_iff_F4 {x : G} (hx : x ∈ H) :
    x ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure S.V3 H, x * u * x⁻¹ * u⁻¹ ∈ S.V1 := by
  rw [P.hF_F4.F92_3.1, mem_centralizerMod]
  exact ⟨fun h => h.2.2, fun h => ⟨hx, P.hF_F4.H_normalizes_V₁ hx, h⟩⟩

theorem Q_le_NV_F4 : pCoreOf 2 H ≤ Subgroup.normalizer (V : Set G) := by
  intro q hq
  have h3 := P.hF_F4.F92_3
  rw [h3.1] at hq
  exact (h3.2.2 (h3.2.1 hq)).2

theorem Q_le_NI_F4 :
    pCoreOf 2 H ≤ Subgroup.normalizer ((V ⊔ conjSub P.g⁻¹ V : Subgroup G) : Set G) := by
  refine B2F.le_normalizer_sup P.Q_le_NV_F4 fun q hq => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hq' : P.g * q * P.g⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H P.g_mem) q).mp hq
  rw [mem_conjSub, mem_conjSub, inv_inv]
  have e : P.g * (q * x * q⁻¹) * P.g⁻¹ =
      (P.g * q * P.g⁻¹) * (P.g * x * P.g⁻¹) * (P.g * q * P.g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (P.Q_le_NV_F4 hq') _

theorem mem_V1_of_central_F4 {x : G} (hx : x ∈ conjClosure S.V3 H)
    (hc : ∀ u ∈ conjClosure S.V3 H, x * u = u * x) : x ∈ S.V1 := by
  have := P.C.center ⟨x, hx⟩ fun u => Subtype.ext (hc u u.2)
  rw [S.mem_V1, ← P.Cz]
  exact this

theorem H_le_Cz_F4 : H ≤ Subgroup.centralizer ({P.C.z} : Set G) := by
  rw [P.Cz]
  exact P.hH.2.1

@[expose] noncomputable def Φ_F4 : ↥H →* MulAut (Multiplicative V4) :=
  P.C.act H (le_normalizer_conjClosure _ _) P.H_le_Cz_F4

theorem Φ_mem_F4 (x : ↥H) : P.Φ_F4 x ∈ Oq := P.C.act_mem_Oq _ _ _ x

theorem Φ_eq_one_iff_F4 (x : ↥H) : P.Φ_F4 x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [P.mem_Q_iff_F4 x.2]
  unfold Φ_F4
  rw [Q8Coords.act_eq_one_iff]
  refine forall₂_congr fun u _ => ?_
  rw [S.mem_V1, P.Cz]

theorem Φ_eq_iff_F4 (x y : ↥H) : P.Φ_F4 x = P.Φ_F4 y ↔ (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 H := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, P.Φ_eq_one_iff_F4]
  rfl

theorem c_mem_H_F4 : (P.c : G) ∈ H := P.L1_le_H_F4 P.c_mem

@[expose] noncomputable def ch_F4 : MulAut (Multiplicative V4) := P.Φ_F4 ⟨P.c, P.c_mem_H_F4⟩

theorem mem_U_of_mem_L1_Q_F4 {x : G} (hx : x ∈ S.L1) (hq : x ∈ pCoreOf 2 H) :
    x ∈ conjClosure S.V3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [P.U_eq_F4]
  refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : S.L1 ⊓ pCoreOf 2 H ≤ S.L1)
    (B2F.le_normalizer_inf Subgroup.le_normalizer (P.L1_le_H_F4.trans (le_normalizer_pCoreOf 2 H)))
    ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨hx, hq⟩

theorem mem_U_of_mem_L1_rho_F4 {x : ↥(Subgroup.normalizer (V : Set G))} (hx : (x : G) ∈ S.L1)
    (hρ : S.frame.ρ x = 1) : (x : G) ∈ conjClosure S.V3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC := S.frame.mem_centralizer_of_rho x hρ
  have hxO : (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cLT]
    exact ⟨le_sup_left (a := L) (S.L1_le_L hx), hxC⟩
  rw [P.U_eq_F4]
  refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : S.L1 ⊓ pCoreOf 2 (L ⊔ T) ≤ S.L1)
    (B2F.le_normalizer_inf Subgroup.le_normalizer
      ((S.L1_le_L.trans le_sup_left).trans (le_normalizer_pCoreOf 2 _)))
    ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨hx, hxO⟩

theorem L1_trichotomy_F4 {x : G} (hx : x ∈ S.L1) :
    x ∈ conjClosure S.V3 H ∨ (P.c : G) * P.c * x ∈ conjClosure S.V3 H ∨
      (P.c : G) * x ∈ conjClosure S.V3 H := by
  obtain ⟨xn, rfl⟩ : ∃ xn : ↥(Subgroup.normalizer (V : Set G)), (xn : G) = x :=
    ⟨⟨x, S.frame.L_le (S.L1_le_L hx)⟩, rfl⟩
  have hs : (S.frame.ρ xn).sign = 1 := (S.frame.image_L _).1 ⟨xn, S.L1_le_L hx, rfl⟩
  have h4 : S.frame.ρ xn 4 = 4 :=
    S.rho_four_of_conj_z xn.2 (S.conj_z_of_normalizes (S.L1_le_NV1 hx))
  have hUL1 := S.UH_le_L1_F4 P.h1323 P.hH P.hn
  have hsurj := (S.lemma_13_5_14_two_F4 P.h1323 P.hH P.hna).2

  have key : ∀ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ S.L1 → InK4 (S.frame.ρ y) →
      (y : G) ∈ conjClosure S.V3 H := by
    intro y hy hK
    obtain ⟨u, hu, hρu⟩ := hsurj _ hK
    have hun : u ∈ Subgroup.normalizer (V : Set G) :=
      S.frame.T_le (S.conjClosure_V3_le_T_F4 P.h1323 P.hH hu)
    have h1 : S.frame.ρ ((⟨u, hun⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hρu, inv_mul_cancel]
    have h2 := P.mem_U_of_mem_L1_rho_F4
      (x := (⟨u, hun⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * y)
      (S.L1.mul_mem (S.L1.inv_mem (hUL1 hu)) hy) h1
    have h3 : u * (u⁻¹ * (y : G)) ∈ conjClosure S.V3 H := (conjClosure S.V3 H).mul_mem hu h2
    rwa [mul_inv_cancel_left] at h3
  rcases A4_decomp _ hs h4 with h | h | h
  · exact Or.inl (key xn hx h)
  · refine Or.inr (Or.inl ?_)
    exact key (P.c * P.c * xn) (S.L1.mul_mem (S.L1.mul_mem P.c_mem P.c_mem) hx)
      (by rw [map_mul, map_mul, P.c_rho]; exact h)
  · refine Or.inr (Or.inr ?_)
    exact key (P.c * xn) (S.L1.mul_mem P.c_mem hx) (by rw [map_mul, P.c_rho]; exact h)

theorem Φ_L1_F4 {x : ↥H} (hx : (x : G) ∈ S.L1) :
    P.Φ_F4 x = 1 ∨ P.ch_F4 * P.ch_F4 * P.Φ_F4 x = 1 ∨ P.ch_F4 * P.Φ_F4 x = 1 := by
  unfold ch_F4
  rcases P.L1_trichotomy_F4 hx with h | h | h
  · exact Or.inl ((P.Φ_eq_one_iff_F4 x).2 (P.U_le_Q_F4 h))
  · refine Or.inr (Or.inl ?_)
    rw [← map_mul, ← map_mul, P.Φ_eq_one_iff_F4]
    exact P.U_le_Q_F4 h
  · refine Or.inr (Or.inr ?_)
    rw [← map_mul, P.Φ_eq_one_iff_F4]
    exact P.U_le_Q_F4 h

theorem ch_ne_one_F4 : P.ch_F4 ≠ 1 := by
  intro h
  have hq := (P.Φ_eq_one_iff_F4 _).1 h
  have hu := P.mem_U_of_mem_L1_Q_F4 P.c_mem hq
  have := (S.lemma_13_5_14_two_F4 P.h1323 P.hH P.hna).1 _ hu
  apply not_InK4_c3p
  rw [← P.c_rho]
  exact this

theorem ch_cube_F4 : P.ch_F4 ^ 3 = 1 := by
  unfold ch_F4
  rw [← map_pow, P.Φ_eq_one_iff_F4]
  have h1 : S.frame.ρ (P.c ^ 3) = 1 := by rw [map_pow, P.c_rho]; exact c3p_cube
  have h2 := P.mem_U_of_mem_L1_rho_F4 (x := P.c ^ 3) (S.L1.pow_mem P.c_mem 3) h1
  exact P.U_le_Q_F4 h2

theorem ch_props_F4 : P.ch_F4 ∈ Oq ∧ P.ch_F4 ≠ 1 ∧ P.ch_F4 ^ 3 = 1 := ⟨P.Φ_mem_F4 _, P.ch_ne_one_F4, P.ch_cube_F4⟩

theorem Φ_normalizes_F4 (x : ↥H) :
    P.Φ_F4 x * P.ch_F4 = P.ch_F4 * P.Φ_F4 x ∨ P.Φ_F4 x * P.ch_F4 = P.ch_F4 * P.ch_F4 * P.Φ_F4 x := by
  have hy : ((x * ⟨P.c, P.c_mem_H_F4⟩ * x⁻¹ : ↥H) : G) ∈ S.L1 :=
    (Subgroup.mem_normalizer_iff.mp (P.hn x.2) _).mp P.c_mem
  have hΦ : P.Φ_F4 (x * ⟨P.c, P.c_mem_H_F4⟩ * x⁻¹) = P.Φ_F4 x * P.ch_F4 * (P.Φ_F4 x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rcases P.Φ_L1_F4 hy with h | h | h
  · rw [hΦ] at h
    exact absurd (by
      calc P.ch_F4 = (P.Φ_F4 x)⁻¹ * (P.Φ_F4 x * P.ch_F4 * (P.Φ_F4 x)⁻¹) * P.Φ_F4 x := by group
        _ = 1 := by rw [h]; group) P.ch_ne_one_F4
  · rw [hΦ] at h
    exact Or.inl (comm_of_conj_eq_inv_sq P.ch_cube_F4 h)
  · rw [hΦ] at h
    exact Or.inr (conj_eq_sq_of_conj_eq_inv P.ch_cube_F4 h)

theorem v_mem_H_F4 : P.v ∈ H := P.hF_F4.V_le_H P.v_mem

theorem v'_mem_F4 : P.g⁻¹ * P.v * P.g ∈ conjSub P.g⁻¹ V := by
  rw [mem_conjSub, inv_inv]
  simpa [mul_assoc] using P.v_mem

theorem v'_mem_H_F4 : P.g⁻¹ * P.v * P.g ∈ H :=
  H.mul_mem (H.mul_mem (H.inv_mem P.g_mem) P.v_mem_H_F4) P.g_mem

@[expose] noncomputable def t1_F4 : MulAut (Multiplicative V4) := P.Φ_F4 ⟨P.v, P.v_mem_H_F4⟩

@[expose] noncomputable def t2_F4 : MulAut (Multiplicative V4) :=
  P.Φ_F4 ⟨P.g⁻¹ * P.v * P.g, P.v'_mem_H_F4⟩

theorem comm_v_L1_F4 {x : G} (hx : x ∈ S.L1) : P.v * x * P.v⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  have h := Subgroup.commutator_mem_commutator P.v_mem hx
  rw [S.commutator_V_L1, commutatorElement_def] at h
  exact P.U_le_Q_F4 (le_conjClosure S.V3 H h)

theorem v'_not_F4 : P.g⁻¹ * P.v * P.g ∉ pCoreOf 2 H := fun h => by
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H P.g_mem) _).mp h
  exact P.v_not (by simpa [mul_assoc] using this)

theorem t1_props_F4 : P.t1_F4 ∈ Oq ∧ P.t1_F4 ≠ 1 ∧ P.t1_F4 * P.t1_F4 = 1 ∧ P.t1_F4 * P.ch_F4 = P.ch_F4 * P.t1_F4 := by
  refine ⟨P.Φ_mem_F4 _, fun h => P.v_not ((P.Φ_eq_one_iff_F4 _).1 h), ?_, ?_⟩
  · unfold t1_F4
    rw [← map_mul, P.Φ_eq_one_iff_F4]
    show P.v * P.v ∈ pCoreOf 2 H
    rw [← pow_two, S.elemAbelian_V.2 _ P.v_mem]
    exact Subgroup.one_mem _
  · unfold t1_F4 ch_F4
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, P.Φ_eq_one_iff_F4]
    exact P.comm_v_L1_F4 P.c_mem

theorem t2_props_F4 : P.t2_F4 ∈ Oq ∧ P.t2_F4 ≠ 1 ∧ P.t2_F4 * P.t2_F4 = 1 ∧ P.t2_F4 * P.ch_F4 = P.ch_F4 * P.t2_F4 := by
  refine ⟨P.Φ_mem_F4 _, fun h => P.v'_not_F4 ((P.Φ_eq_one_iff_F4 _).1 h), ?_, ?_⟩
  · unfold t2_F4
    rw [← map_mul, P.Φ_eq_one_iff_F4]
    show P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) ∈ pCoreOf 2 H
    have hv2 : P.v * P.v = 1 := by rw [← pow_two]; exact S.elemAbelian_V.2 _ P.v_mem
    have e : P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) = P.g⁻¹ * (P.v * P.v) * P.g := by group
    rw [e, hv2]
    simp
  · unfold t2_F4 ch_F4
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, P.Φ_eq_one_iff_F4]
    have hc' : P.g * P.c * P.g⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (P.hn P.g_mem) _).mp P.c_mem
    have h := P.comm_v_L1_F4 hc'
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
    show P.g⁻¹ * P.v * P.g * P.c * (P.g⁻¹ * P.v * P.g)⁻¹ * (P.c : G)⁻¹ ∈ pCoreOf 2 H
    have e : P.g⁻¹ * P.v * P.g * P.c * (P.g⁻¹ * P.v * P.g)⁻¹ * (P.c : G)⁻¹ =
        P.g⁻¹ * (P.v * (P.g * P.c * P.g⁻¹) * P.v⁻¹ * (P.g * P.c * P.g⁻¹)⁻¹) * P.g⁻¹⁻¹ := by
      group
    rw [e]
    exact this

theorem V_cases_F4 {w : G} (hw : w ∈ V) : w ∈ pCoreOf 2 H ∨ w * P.v⁻¹ ∈ pCoreOf 2 H := by
  by_cases h3 : w ∈ S.V3
  · exact Or.inl (P.U_le_Q_F4 (le_conjClosure S.V3 H h3))
  · right
    have hv3 : P.v ∉ S.V3 := fun h => P.v_not (P.U_le_Q_F4 (le_conjClosure S.V3 H h))
    refine P.U_le_Q_F4 (le_conjClosure S.V3 H ?_)
    have hwv : w * P.v⁻¹ ∈ V := V.mul_mem hw (V.inv_mem P.v_mem)
    refine S.mem_pre.2 ⟨hwv, mem_W3.2 ?_⟩
    have hw' : c4 (S.frame.ψ ⟨w, hw⟩) ≠ 1 := fun h => h3 (S.mem_pre.2 ⟨hw, mem_W3.2 h⟩)
    have hv' : c4 (S.frame.ψ ⟨P.v, P.v_mem⟩) ≠ 1 := fun h =>
      hv3 (S.mem_pre.2 ⟨P.v_mem, mem_W3.2 h⟩)
    have e : (⟨w * P.v⁻¹, hwv⟩ : ↥V) = ⟨w, hw⟩ * (⟨P.v, P.v_mem⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_mul, map_inv]
    exact mulZMod2_eq _ _ hw' hv'

theorem S3_facts_F4 : P.g⁻¹ * P.v * P.g * P.v⁻¹ ∉ pCoreOf 2 H ∧
    P.v * (P.g⁻¹ * P.v * P.g) ∉ pCoreOf 2 H ∧ (P.v * (P.g⁻¹ * P.v * P.g)) ^ 3 ∈ pCoreOf 2 H ∧
    ∃ y ∈ V ⊔ conjSub P.g⁻¹ V, y ^ 3 = 1 ∧ y ∉ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hN, ⟨e⟩⟩ := P.hS3
  set I := V ⊔ conjSub P.g⁻¹ V with hIdef
  set π := QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I) with hπ
  have hπ1 : ∀ y : ↥I, π y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ y y' : ↥I, π y = π y' ↔ (y : G) * (y' : G)⁻¹ ∈ pCoreOf 2 H := fun y y' => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hπ1]
    rfl
  have hvI : P.v ∈ I := le_sup_left (a := V) P.v_mem
  have hv'I : P.g⁻¹ * P.v * P.g ∈ I := le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem_F4
  set a : ↥I := ⟨P.v, hvI⟩
  set b : ↥I := ⟨P.g⁻¹ * P.v * P.g, hv'I⟩
  have ha2 : π a * π a = 1 := by
    rw [← map_mul, hπ1]
    show P.v * P.v ∈ pCoreOf 2 H
    rw [← pow_two, S.elemAbelian_V.2 _ P.v_mem]
    exact Subgroup.one_mem _
  have hb2 : π b * π b = 1 := by
    rw [← map_mul, hπ1]
    show P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) ∈ pCoreOf 2 H
    have hv2 : P.v * P.v = 1 := by rw [← pow_two]; exact S.elemAbelian_V.2 _ P.v_mem
    have e : P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) = P.g⁻¹ * (P.v * P.v) * P.g := by group
    rw [e, hv2]
    simp
  have ha1 : π a ≠ 1 := fun h => P.v_not ((hπ1 a).1 h)
  have hb1 : π b ≠ 1 := fun h => P.v'_not_F4 ((hπ1 b).1 h)

  have hVimg : ∀ w (hw : w ∈ V), π ⟨w, le_sup_left (a := V) hw⟩ = 1 ∨
      π ⟨w, le_sup_left (a := V) hw⟩ = π a := by
    intro w hw
    rcases P.V_cases_F4 hw with h | h
    · exact Or.inl ((hπ1 _).2 h)
    · exact Or.inr ((hπeq _ _).2 h)
  have hV'img : ∀ w (hw : w ∈ conjSub P.g⁻¹ V), π ⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩ = 1 ∨
      π ⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩ = π b := by
    intro w hw
    have hw2 := hw
    rw [mem_conjSub, inv_inv] at hw2
    rcases P.V_cases_F4 hw2 with h | h
    · left
      rw [hπ1]
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
      show w ∈ pCoreOf 2 H
      simpa [mul_assoc] using this
    · right
      rw [hπeq]
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
      show w * (P.g⁻¹ * P.v * P.g)⁻¹ ∈ pCoreOf 2 H
      have e : w * (P.g⁻¹ * P.v * P.g)⁻¹ =
          P.g⁻¹ * (P.g * w * P.g⁻¹ * P.v⁻¹) * P.g⁻¹⁻¹ := by group
      rw [e]
      exact this

  have hab : π a ≠ π b := by
    intro hab
    set K : Subgroup G := ((pairSub (π a) ha2).comap π).map I.subtype
    have hIK : I ≤ K := by
      refine sup_le (fun w hw => ⟨⟨w, le_sup_left (a := V) hw⟩, hVimg w hw, rfl⟩) fun w hw =>
        ⟨⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩, ?_, rfl⟩
      rcases hV'img w hw with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hab.symm)
    obtain ⟨ρ, hρ1, hρa⟩ := perm3_exists_ne (e (π a))
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm ρ)
    obtain ⟨y, hy, hyq⟩ := hIK q.2
    have hyq' : y = q := Subtype.ext hyq
    subst hyq'
    have hq' : e (π y) = ρ := by
      rw [show π y = (y : ↥I ⧸ (pCoreOf 2 H).subgroupOf I) from rfl, hq, MulEquiv.apply_symm_apply]
    rcases (show π y = 1 ∨ π y = π a from hy) with h | h
    · rw [h, map_one] at hq'
      exact hρ1 hq'.symm
    · rw [h] at hq'
      exact hρa hq'.symm

  have hστ := perm3_mul_of_ne (e (π a)) (e (π b)) (by rw [← map_mul, ha2, map_one])
    (by rw [← map_mul, hb2, map_one]) (fun h => ha1 (e.injective (h.trans (map_one e).symm)))
    (fun h => hb1 (e.injective (h.trans (map_one e).symm))) (fun h => hab (e.injective h))
  rw [← map_mul, ← map_mul] at hστ
  have hw1 : π (a * b) ≠ 1 := fun h => hστ.1 (by rw [h, map_one])
  have hw3 : π (a * b) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact hστ.2
  refine ⟨fun h => hab ((hπeq b a).2 h).symm, fun h => hw1 ((hπ1 (a * b)).2 h), ?_, ?_⟩
  · exact (hπ1 ((a * b) ^ 3)).1 (by rw [map_pow]; exact hw3)

  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw3Q : (((a * b) ^ 3 : ↥I) : G) ∈ pCoreOf 2 H := (hπ1 _).1 (by rw [map_pow]; exact hw3)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hw3Q⟩
  have hk' : (((a * b) ^ 3 : ↥I) : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    exact this
  obtain ⟨y, hy⟩ : ∃ y : ↥I, y = (a * b) ^ 2 ^ k := ⟨_, rfl⟩
  have hy3 : (y : G) ^ 3 = 1 := by
    rw [hy, ← SubgroupClass.coe_pow, ← pow_mul, mul_comm (2 ^ k) 3, pow_mul,
      SubgroupClass.coe_pow]
    exact hk'

  have hord : orderOf (e (π (a * b))) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hw3, map_one]) (fun h => hw1 (e.injective
      (h.trans (map_one e).symm)))
  have hρ1 : e (π y) ≠ 1 := by
    intro h
    rw [hy, map_pow, map_pow] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    have h3 := (Nat.prime_dvd_prime_iff_eq (Nat.prime_three) Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
    omega
  have hρ3 : e (π y) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : y ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one, map_one]
  refine ⟨y, y.2, hy3, fun hyN => ?_⟩

  have hc : (y : G) * P.v * (y : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN _).mp P.v_mem
  have hcon := perm3_conj_ne (e (π a)) (e (π y)) (by rw [← map_mul, ha2, map_one])
    (fun h => ha1 (e.injective (h.trans (map_one e).symm))) hρ3 hρ1
  have hyv : y * a * y⁻¹ = ⟨(y : G) * P.v * (y : G)⁻¹, le_sup_left (a := V) hc⟩ := rfl
  rcases hVimg _ hc with h | h
  · apply hcon.1
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hyv, h, map_one]
  · apply hcon.2
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hyv, h]

theorem t12_props_F4 : P.t1_F4 * P.t2_F4 ≠ 1 ∧ (P.t1_F4 * P.t2_F4) ^ 3 = 1 := by
  obtain ⟨-, h1, h3, -⟩ := P.S3_facts_F4
  unfold t1_F4 t2_F4
  rw [← map_mul, ← map_pow]
  exact ⟨fun h => h1 ((P.Φ_eq_one_iff_F4 _).1 h), (P.Φ_eq_one_iff_F4 _).2 h3⟩

theorem centralizer_T_L_F4 : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, y, hyI, hy3, hyN⟩ := P.S3_facts_F4
  set D := T ⊓ Subgroup.centralizer (L : Set G) with hDdef
  have hyH : y ∈ H := P.I_le_H_F4 hyI
  have hUL : conjClosure S.V3 H ≤ L :=
    (S.UH_le_L1_F4 P.h1323 P.hH P.hn).trans S.L1_le_L

  have hDQ : ∀ d ∈ D, d ∈ pCoreOf 2 H := by
    intro d hd
    refine (P.mem_Q_iff_F4 (P.T_le_H_F4 hd.1)).2 fun u hu => ?_
    have := Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)
    rw [← this, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

  have hyD : ∀ d ∈ D, y * d * y⁻¹ = d := by
    intro d hd
    have hdQ := hDQ d hd
    have hdN := P.Q_le_NI_F4 hdQ

    set k := y * d * y⁻¹ * d⁻¹ with hk
    have hkI : k ∈ V ⊔ conjSub P.g⁻¹ V := by
      have h1 : d * y⁻¹ * d⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        (Subgroup.mem_normalizer_iff.mp hdN _).mp ((V ⊔ conjSub P.g⁻¹ V).inv_mem hyI)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem hyI h1
      simpa [hk, mul_assoc] using this
    have hkC : ∀ u ∈ conjClosure S.V3 H, k * u = u * k := by
      intro u hu
      have hdu : ∀ x ∈ conjClosure S.V3 H, d * x = x * d := fun x hx =>
        (Subgroup.mem_centralizer_iff.mp hd.2 x (hUL hx)).symm
      have hy' : y⁻¹ * u * y ∈ conjClosure S.V3 H := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure S.V3 H (H.inv_mem hyH)) u).mp hu
        simpa using this
      have h1 := hdu _ hy'
      have h2 := hdu u hu
      have hdinv : d⁻¹ * u = u * d⁻¹ := by
        calc d⁻¹ * u = d⁻¹ * (u * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * u) * d⁻¹ := by rw [h2]
          _ = u * d⁻¹ := by group
      calc k * u = y * d * y⁻¹ * (d⁻¹ * u) := by rw [hk]; group
        _ = y * d * y⁻¹ * (u * d⁻¹) := by rw [hdinv]
        _ = y * (d * (y⁻¹ * u * y)) * y⁻¹ * d⁻¹ := by group
        _ = y * ((y⁻¹ * u * y) * d) * y⁻¹ * d⁻¹ := by rw [h1]
        _ = u * k := by rw [hk]; group
    have hkQ : k ∈ pCoreOf 2 H := by
      refine (P.mem_Q_iff_F4 (P.I_le_H_F4 hkI)).2 fun u hu => ?_
      rw [hkC u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hkU : k ∈ conjClosure S.V3 H := by
      rw [← P.I_inf_Q_F4]
      exact ⟨hkI, hkQ⟩
    have hkV1 := P.mem_V1_of_central_F4 hkU hkC
    rcases S.mem_V1.1 hkV1 with h | h
    · rw [hk] at h
      calc y * d * y⁻¹ = y * d * y⁻¹ * d⁻¹ * d := by group
        _ = d := by rw [h, one_mul]
    · exfalso
      apply S.z_ne_one
      refine eq_one_of_conj_eq_mul (d := d) hy3 (by rw [← pow_two]; exact S.z_sq)
        (P.comm_z_F4 hyH) ?_
      rw [← h, hk]
      group

  by_contra hD
  have hDp : IsPGroup 2 D := S.isPGroup_T.to_le inf_le_left
  have hloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hD, hDp, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLTD : L ⊔ T ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le ?_ ?_
    · intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := Subgroup.mem_centralizer_iff.mp hx.2 l hl
        rw [this, mul_inv_cancel_right]
        exact hx
      · intro hx
        have := Subgroup.mem_centralizer_iff.mp hx.2 l hl
        have e : x = l * x * l⁻¹ := by
          calc x = l⁻¹ * (l * x * l⁻¹ * l) := by group
            _ = l⁻¹ * (l * (l * x * l⁻¹)) := by rw [this]
            _ = l * x * l⁻¹ := by group
        rw [e]
        exact hx
    · exact B2F.le_normalizer_inf Subgroup.le_normalizer
        (S.T_le_NL.trans (normalizer_le_normalizer_centralizer' L))
  have hM'eq := S.uniqueM.2 M' ⟨hM', hLTD.trans hle⟩
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      rw [hyD d hd]
      exact hd
    · intro hd
      have := hyD _ hd
      have e : d = y * d * y⁻¹ := by
        calc d = y⁻¹ * (y * d * y⁻¹) * y := by group
          _ = y⁻¹ * (y * (y * d * y⁻¹) * y⁻¹) * y := by rw [this]
          _ = y * d * y⁻¹ := by group
      rw [e]
      exact hd
  have hyM : y ∈ Subgroup.normalizer (L : Set G) := hM'eq ▸ hle hyND
  apply hyN
  have := normalizer_le_normalizer_pCoreOf 2 L hyM
  rwa [P.pCoreOf_L_F4] at this

theorem pCoreOf_LT_F4 : pCoreOf 2 (L ⊔ T) = V := by
  obtain ⟨h1, -⟩ := P.hC113 G L T S.sylow_LT S.T_le_NL P.G248_F4.1 P.G248_F4.2.1
  rw [h1, P.centralizer_T_L_F4, sup_bot_eq]
  show ⁅pCoreOf 2 L, L⁆ = V
  rw [P.pCoreOf_L_F4]
  exact S.commutator_V_L

theorem V_le_L_F4 : V ≤ L := by
  rw [← P.pCoreOf_L_F4]
  exact pCoreOf_le 2 L

theorem normalizer_L_eq_F4 : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) := by
  apply le_antisymm
  · have := normalizer_le_normalizer_pCoreOf 2 L
    rwa [P.pCoreOf_L_F4] at this
  · exact S.NV_le_M

theorem centralizer_V_le_F4 : Subgroup.centralizer (V : Set G) ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G)
  have hMV : M = Subgroup.normalizer (V : Set G) := P.normalizer_L_eq_F4
  have hVM : V ≤ M := by rw [hMV]; exact Subgroup.le_normalizer
  have hVO : V ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 hVM hMV.le S.isPGroup_V
  have hTM : T ≤ M := S.T_le_NL
  have hInH : InH T M := ⟨hTM, fun h => S.V_ne_bot (le_bot_iff.1 (h ▸ hVO))⟩
  have hchar := S.charTwo_of_inH hInH
  have hOT : pCoreOf 2 M ≤ T := by
    obtain ⟨P', hP'⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
    have := pCoreOf_two_le_sylow M P' (hP' ▸ hTM)
    rwa [hP'] at this
  have hOV : pCoreOf 2 M ≤ V := by
    rw [← P.pCoreOf_LT_F4]
    exact le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer hTM).trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  have hOeq : pCoreOf 2 M = V := le_antisymm hOV hVO
  intro x hx
  have hxM : x ∈ M := by rw [hMV]; exact Subgroup.centralizer_le_normalizer _ hx
  have hx' : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by rw [hOeq]; exact hx
  have := hchar ⟨hxM, hx'⟩
  rwa [hOeq] at this

theorem normalizer_L_F4 : Subgroup.normalizer (L : Set G) = L ⊔ T := by
  set M := Subgroup.normalizer (L : Set G)
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := P.normalizer_L_eq_F4.le
  have hLTM : L ⊔ T ≤ M := sup_le Subgroup.le_normalizer S.T_le_NL
  refine le_antisymm ?_ hLTM

  set f : ↥M →* ℤˣ := Equiv.Perm.sign.comp (S.frame.ρ.comp (Subgroup.inclusion hMV))
  have hker : f.ker ≤ (L ⊔ T).subgroupOf M := by
    intro m hm
    have hm' : (S.frame.ρ (Subgroup.inclusion hMV m)).sign = 1 := hm
    obtain ⟨l, hlL, hl⟩ := (S.frame.image_L _).2 hm'
    rw [Subgroup.mem_subgroupOf]
    have hk : S.frame.ρ (l⁻¹ * Subgroup.inclusion hMV m) = 1 := by
      rw [map_mul, map_inv, hl, inv_mul_cancel]
    have hkV := P.centralizer_V_le_F4 (S.frame.mem_centralizer_of_rho _ hk)
    have hkL : ((l⁻¹ * Subgroup.inclusion hMV m :
        ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := P.V_le_L_F4 hkV
    have : (m : G) = l * ((l⁻¹ * Subgroup.inclusion hMV m :
        ↥(Subgroup.normalizer (V : Set G))) : G) := by
      simp [Subgroup.coe_inclusion]
    rw [this]
    exact le_sup_left (a := L) (L.mul_mem hlL hkL)
  have h2 : ((L ⊔ T).subgroupOf M).index ∣ 2 := by
    have h1 := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at h1
    have h3 : Nat.card f.range ∣ 2 := by
      have := Subgroup.card_subgroup_dvd_card f.range
      rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
      exact this
    exact h1.trans h3
  have hodd : ¬ 2 ∣ ((L ⊔ T).subgroupOf M).index := by
    have hT := isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
    intro h
    apply hT.2.2
    exact h.trans (Subgroup.index_dvd_of_le fun x hx => (le_sup_right : T ≤ L ⊔ T) hx)
  have h1 : ((L ⊔ T).subgroupOf M).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exact absurd (h ▸ dvd_rfl) hodd
  intro m hm
  have := Subgroup.index_eq_one.1 h1
  have hm' : (⟨m, hm⟩ : ↥M) ∈ (L ⊔ T).subgroupOf M := this ▸ Subgroup.mem_top _
  exact hm'

theorem Q_eq_U_F4 : pCoreOf 2 H = conjClosure S.V3 H := by
  symm
  refine Subgroup.eq_of_le_of_card_ge P.U_le_Q_F4 ?_
  rw [P.card_U_F4]
  have hQN := P.Q_le_NV_F4

  have hL1H := P.L1_le_H_F4
  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 →
      ∀ q (hq : q ∈ pCoreOf 2 H), ∃ hq' : (g : G) * q * (g : G)⁻¹ ∈ pCoreOf 2 H,
        S.frame.ρ ⟨_, hQN hq'⟩ = S.frame.ρ g * S.frame.ρ ⟨q, hQN hq⟩ * (S.frame.ρ g)⁻¹ := by
    intro g hg q hq
    have hq' := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hL1H hg)) q).mp hq
    refine ⟨hq', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hD : ∀ q (hq : q ∈ pCoreOf 2 H), InD (S.frame.ρ ⟨q, hQN hq⟩) := fun q hq =>
    S.frame.T_D _ (P.Q_le_T_F4 hq)
  obtain ⟨g', hg'L1, hg'⟩ := S.exists_L1_of_three c3q_props.1 c3q_props.2.1 c3q_props.2.2
  have hgi : ((P.c⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.L1 := S.L1.inv_mem P.c_mem
  have hK4 : ∀ q (hq : q ∈ pCoreOf 2 H), InK4 (S.frame.ρ ⟨q, hQN hq⟩) := by
    intro q hq
    obtain ⟨h1, e1⟩ := hconj P.c P.c_mem q hq
    obtain ⟨h2, e2⟩ := hconj P.c⁻¹ hgi q hq
    obtain ⟨h3, e3⟩ := hconj g' hg'L1 q hq
    have d1 := hD _ h1
    have d2 := hD _ h2
    have d3 := hD _ h3
    rw [e1, P.c_rho] at d1
    rw [e2, map_inv, P.c_rho, inv_inv] at d2
    rw [e3, hg'] at d3
    exact InK4_of_conj_D _ (hD q hq) d1 d2 d3

  set f : ↥(pCoreOf 2 H) →* Equiv.Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion hQN)
  have hfker : f.ker = (pCoreOf 2 H ⊓ V).subgroupOf (pCoreOf 2 H) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : S.frame.ρ (Subgroup.inclusion hQN q) = 1 := h
      have hC := S.frame.mem_centralizer_of_rho _ h'
      refine ⟨q.2, ?_⟩
      rw [← P.pCoreOf_LT_F4, ← S.cT]
      exact ⟨P.Q_le_T_F4 q.2, hC⟩
    · intro h
      show S.frame.ρ (Subgroup.inclusion hQN q) = 1
      refine S.frame.rho_eq_one_of_mem _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact B2F.isElemAbelian_comm S.elemAbelian_V hw h.2
  have hcard := card_le_of_range_subset inf_le_left f hfker {σ | InK4 σ} fun q =>
    hK4 q q.2
  have hX : Nat.card ({σ | InK4 σ} : Set (Equiv.Perm (Fin 5))) = 4 := by
    have : Nat.card ({σ | InK4 σ} : Set (Equiv.Perm (Fin 5))) =
        Nat.card {σ : Equiv.Perm (Fin 5) // InK4 σ} := rfl
    rw [this, Nat.card_eq_fintype_card, card_InK4]

  have hQV : Nat.card ↥(pCoreOf 2 H ⊓ V) ≤ 8 := by
    have hdvd : Nat.card ↥(pCoreOf 2 H ⊓ V) ∣ 16 := by
      rw [← S.card_V]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card ↥(pCoreOf 2 H ⊓ V) ≠ 16 := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge (inf_le_right : pCoreOf 2 H ⊓ V ≤ V)
        (by rw [h, S.card_V])
      have hv : P.v ∈ pCoreOf 2 H ⊓ V := by rw [this]; exact P.v_mem
      exact P.v_not hv.1
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(pCoreOf 2 H ⊓ V) = n at hdvd hne hle ⊢
    interval_cases n <;> omega
  rw [hX] at hcard
  omega

end Pf1515_F4

end Setting

end CFSG.Quasithin.H13.A5
