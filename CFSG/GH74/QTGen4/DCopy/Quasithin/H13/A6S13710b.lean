module

public import CFSG.Quasithin.H13.A6S13710b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

section NonAb

variable {S}
variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

theorem F96_y_F4 :
    conjSub (C.g : G)⁻¹ H = conjSub (C.y : G)⁻¹ H ∧
      conjSub (C.g : G)⁻¹ (pCoreOf 2 H) = conjSub (C.y : G)⁻¹ (pCoreOf 2 H) ∧
      conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) = conjSub (C.y : G)⁻¹ (conjClosure S.V3 H) ∧
      conjSub (C.g : G)⁻¹ (conjClosure V H) = conjSub (C.y : G)⁻¹ (conjClosure V H) :=
  (S.hypF91_F4 hNS h13315 h1356two hH).F96_1 C.g_mem
    (C.I_le_LT_F4 hNS h13315 h1356two hH hab C.y_mem_I) C.V1_g_eq_y

theorem VHg_eq_F4 :
    C.VHg = conjSub (C.y : G)⁻¹ (conjClosure V H) :=
  (C.F96_y_F4 hNS h13315 h1356two hH hab).2.2.2

theorem conj_y_mem_VHg_F4 {x : G} (hx : x ∈ conjClosure V H) :
    (C.y : G)⁻¹ * x * C.y ∈ C.VHg := by
  rw [C.VHg_eq_F4 hNS h13315 h1356two hH hab, mem_conjSub, inv_inv]
  have e : (C.y : G) * ((C.y : G)⁻¹ * x * C.y) * (C.y : G)⁻¹ = x := by group
  rw [e]
  exact hx

theorem conj_y_mem_VH_F4 {x : G} (hx : x ∈ C.VHg) :
    (C.y : G) * x * (C.y : G)⁻¹ ∈ conjClosure V H := by
  rw [C.VHg_eq_F4 hNS h13315 h1356two hH hab, mem_conjSub, inv_inv] at hx
  exact hx

theorem conj_y_v_mem_F4 :
    (C.w : G)⁻¹ * ((C.y : G)⁻¹ * C.v * C.y) ∈ C.W ⊔ C.A := by
  refine Subgroup.mem_sup_right ⟨C.VHg.mul_mem (C.VHg.inv_mem C.w_mem)
    (C.conj_y_mem_VHg_F4 hNS h13315 h1356two hH hab C.v_mem), ?_⟩
  have h : S.frame.ρ (C.w⁻¹ * (C.y⁻¹ * C.v * C.y)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, C.rho_w, C.rho_y, C.rho_v]
    decide
  have := (S.rho_eq_one_iff _).1 h
  simpa using this

theorem VH_cases_F4 {x : G} (hx : x ∈ conjClosure V H) :
    x ∈ C.W ⊔ C.A ∨ (C.v : G) * x ∈ C.W ⊔ C.A := by
  obtain ⟨hxN, h⟩ := S.rho_VH_F4 hNS h13315 h1356two hH hab hx
  rcases h with h | h
  · exact Or.inl (Subgroup.mem_sup_left ⟨hx, (S.rho_eq_one_iff ⟨x, hxN⟩).1 h⟩)
  · refine Or.inr (Subgroup.mem_sup_left ⟨(conjClosure V H).mul_mem C.v_mem hx, ?_⟩)
    have h1 : S.frame.ρ (C.v * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, C.rho_v, h]
      exact swap45_sq
    exact (S.rho_eq_one_iff _).1 h1

theorem VHg_cases_F4 {x : G} (hx : x ∈ C.VHg) :
    x ∈ C.W ⊔ C.A ∨ (C.w : G) * x ∈ C.W ⊔ C.A := by
  obtain ⟨hxN, h⟩ := C.rho_VHg_F4 hNS h13315 h1356two hH hab hx
  rcases h with h | h
  · exact Or.inl (Subgroup.mem_sup_right ⟨hx, (S.rho_eq_one_iff ⟨x, hxN⟩).1 h⟩)
  · refine Or.inr (Subgroup.mem_sup_right ⟨C.VHg.mul_mem C.w_mem hx, ?_⟩)
    have h1 : S.frame.ρ (C.w * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, C.rho_w, h]
      exact swap34_sq
    exact (S.rho_eq_one_iff _).1 h1

theorem comm_VH_mem_ZI_F4 {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ conjClosure V H) : x * y * x⁻¹ * y⁻¹ ∈ C.ZI :=
  C.V_le_ZI (((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V)
    (S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab hx hy))

theorem comm_VHg_mem_ZI_F4 {x y : G} (hx : x ∈ C.VHg)
    (hy : y ∈ C.VHg) : x * y * x⁻¹ * y⁻¹ ∈ C.ZI := by
  have h := S.comm_VH_mem_V1_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx) ((C.mem_VHg).1 hy)
  have hV := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V) h
  have key : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ ∈ V := by
    have e : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) *
          ((C.g : G) * x * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact hV
  exact C.V_le_ZI ((Subgroup.mem_normalizer_iff.mp C.g.2 _).mpr key)

theorem v_le_normalizer_ZI_F4 :
    (C.v : G) ∈ Subgroup.normalizer (C.ZI : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem (X := Subgroup.zpowers (C.v : G))
    (fun x hx z hz => ?_) (Subgroup.mem_zpowers _)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hvk : (C.v : G) ^ k ∈ conjClosure V H := (conjClosure V H).zpow_mem C.v_mem k
  have h := C.comm_VH_mem_ZI_F4 hNS h13315 h1356two hH hab hvk hz.1
  have e : (C.v : G) ^ k * z * ((C.v : G) ^ k)⁻¹ =
      ((C.v : G) ^ k * z * ((C.v : G) ^ k)⁻¹ * z⁻¹) * z := by group
  rw [e]
  exact C.ZI.mul_mem h hz

theorem w_le_normalizer_ZI_F4 :
    (C.w : G) ∈ Subgroup.normalizer (C.ZI : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem (X := Subgroup.zpowers (C.w : G))
    (fun x hx z hz => ?_) (Subgroup.mem_zpowers _)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hwk : (C.w : G) ^ k ∈ C.VHg := C.VHg.zpow_mem C.w_mem k
  have h := C.comm_VHg_mem_ZI_F4 hNS h13315 h1356two hH hab hwk hz.2
  have e : (C.w : G) ^ k * z * ((C.w : G) ^ k)⁻¹ =
      ((C.w : G) ^ k * z * ((C.w : G) ^ k)⁻¹ * z⁻¹) * z := by group
  rw [e]
  exact C.ZI.mul_mem h hz

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem comm_VH_N_F4 {x n : G} (hx : x ∈ conjClosure V H)
    (hn : n ∈ C.N) : x * n * x⁻¹ * n⁻¹ ∈ C.W := by
  have hnQ := C.N_le_cLT_F4 hNS h13315 h1356two hH hab hn
  have hnV := S.cLT_le_normalizer_VH_F4 hNS h13315 h1356two hH hhat hnQ
  have hxN := S.VH_le_NV_F4 hNS h13315 h1356two hH hab hx
  refine ⟨?_, ?_⟩
  · have h1 : n * x⁻¹ * n⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.mp hnV _).mp ((conjClosure V H).inv_mem hx)
    have e : x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) := by group
    rw [e]
    exact (conjClosure V H).mul_mem hx h1
  · exact (Subgroup.centralizer (V : Set G)).mul_mem
      (A5.conj_mem_centralizer_of_mem_normalizer hxN hnQ.2)
      ((Subgroup.centralizer (V : Set G)).inv_mem hnQ.2)

theorem comm_VHg_N_F4 {x n : G} (hx : x ∈ C.VHg)
    (hn : n ∈ C.N) : x * n * x⁻¹ * n⁻¹ ∈ C.A := by
  have hnQ := C.N_le_cLT_F4 hNS h13315 h1356two hH hab hn
  have hnV := C.cLT_le_normalizer_VHg_F4 hNS h13315 h1356two hH hhat hnQ
  have hxN := C.VHg_le_NV_F4 hNS h13315 h1356two hH hab hx
  refine ⟨?_, ?_⟩
  · have h1 : n * x⁻¹ * n⁻¹ ∈ C.VHg :=
      (Subgroup.mem_normalizer_iff.mp hnV _).mp (C.VHg.inv_mem hx)
    have e : x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) := by group
    rw [e]
    exact C.VHg.mul_mem hx h1
  · exact (Subgroup.centralizer (V : Set G)).mul_mem
      (A5.conj_mem_centralizer_of_mem_normalizer hxN hnQ.2)
      ((Subgroup.centralizer (V : Set G)).inv_mem hnQ.2)

theorem coe_W_sup_A_F4 :
    ((C.W ⊔ C.A : Subgroup G) : Set G) = (C.W : Set G) * (C.A : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right C.W C.A
    (C.W_le_normalizer_A_F4 hNS h13315 h1356two hH hab hhat)

theorem VH_le_normalizer_P_F4 :
    conjClosure V H ≤ Subgroup.normalizer ((C.W ⊔ C.A : Subgroup G) : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun x hx p hp => ?_
  have hp' : p ∈ (C.W : Set G) * (C.A : Set G) := by
    rw [← C.coe_W_sup_A_F4 hNS h13315 h1356two hH hab hhat]; exact hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hp'
  have hxN := S.VH_le_NV_F4 hNS h13315 h1356two hH hab hx
  have h1 : x * a * x⁻¹ ∈ C.W :=
    ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) a).mp ha.1,
      A5.conj_mem_centralizer_of_mem_normalizer hxN ha.2⟩
  have h2 := C.comm_VH_N_F4 hNS h13315 h1356two hH hab hhat hx (C.A_le_N hb)
  have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹ * b⁻¹) * b := by group
  rw [e]
  exact (C.W ⊔ C.A).mul_mem ((C.W ⊔ C.A).mul_mem (Subgroup.mem_sup_left h1)
    (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_right hb)

theorem VHg_le_normalizer_P_F4 :
    C.VHg ≤ Subgroup.normalizer ((C.W ⊔ C.A : Subgroup G) : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun x hx p hp => ?_
  have hp' : p ∈ (C.W : Set G) * (C.A : Set G) := by
    rw [← C.coe_W_sup_A_F4 hNS h13315 h1356two hH hab hhat]; exact hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hp'
  have hxN := C.VHg_le_NV_F4 hNS h13315 h1356two hH hab hx
  have h1 : x * b * x⁻¹ ∈ C.A :=
    ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) b).mp hb.1,
      A5.conj_mem_centralizer_of_mem_normalizer hxN hb.2⟩
  have h2 := C.comm_VHg_N_F4 hNS h13315 h1356two hH hab hhat hx (C.W_le_N ha)
  have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a * (x * b * x⁻¹) := by group
  rw [e]
  exact (C.W ⊔ C.A).mul_mem ((C.W ⊔ C.A).mul_mem (Subgroup.mem_sup_right h2)
    (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right h1)

theorem P_normal_F4 :
    ∀ x ∈ conjClosure V H ⊔ C.VHg, ∀ p ∈ C.W ⊔ C.A, x * p * x⁻¹ ∈ C.W ⊔ C.A := by
  intro x hx p hp
  have hle : conjClosure V H ⊔ C.VHg ≤ Subgroup.normalizer ((C.W ⊔ C.A : Subgroup G) : Set G) :=
    sup_le (C.VH_le_normalizer_P_F4 hNS h13315 h1356two hH hab hhat)
      (C.VHg_le_normalizer_P_F4 hNS h13315 h1356two hH hab hhat)
  exact (Subgroup.mem_normalizer_iff.mp (hle hx) p).mp hp

theorem r_six_mem_P_F4 : ((C.v : G) * C.w) ^ (6 : ℤ) ∈ C.W ⊔ C.A := by
  have h := C.comm_VH_N_F4 hNS h13315 h1356two hH hab hhat C.v_mem C.r_cube_mem_N
  rw [C.conj_v_r_cube] at h
  have e : ((C.v : G) * C.w) ^ (6 : ℤ) = (((C.r : G) ^ 3)⁻¹ * ((C.r : G) ^ 3)⁻¹)⁻¹ := by
    rw [r_coe, ← mul_inv_rev, inv_inv, ← pow_add,
      show (6 : ℤ) = ((3 + 3 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [e]
  exact Subgroup.mem_sup_left (C.W.inv_mem h)

theorem N_eq_F4 : C.N = C.W ⊔ C.A := by
  refine le_antisymm (fun x hx => ?_) (C.P_le_N)
  have hPn := C.P_normal_F4 hNS h13315 h1356two hH hab hhat
  have hgen := exists_dihedral_form hPn C.v_mem C.w_mem C.v_sq C.w_sq
    (fun x hx => C.VH_cases_F4 hNS h13315 h1356two hH hab hx)
    (fun x hx => C.VHg_cases_F4 hNS h13315 h1356two hH hab hx)
  have h3 : ((C.v : G) * C.w) ^ (3 : ℤ) ∈ C.W ⊔ C.A :=
    pow_three_mem_of_conj hPn (Subgroup.mem_sup_left C.v_mem) (Subgroup.mem_sup_right C.w_mem)
      C.v_sq C.w_sq hgen (C.r_six_mem_P_F4 hNS h13315 h1356two hH hab hhat) C.y_mem_I
      (C.conj_y_v_mem_F4 hNS h13315 h1356two hH hab)
  obtain ⟨i, p, hp, hxp⟩ := hgen x hx.1
  have hpN := C.P_le_N hp
  have hpV : p ∈ Subgroup.normalizer (V : Set G) := C.I_le_NV_F4 hNS h13315 h1356two hH hab hpN.1
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := C.I_le_NV_F4 hNS h13315 h1356two hH hab hx.1
  have hρx : S.frame.ρ ⟨x, hxV⟩ = 1 := (S.rho_eq_one_iff _).2 hx.2
  have hρp : S.frame.ρ ⟨p, hpV⟩ = 1 := (S.rho_eq_one_iff _).2 hpN.2
  rcases hxp with rfl | rfl
  ·
    have e' : (⟨_, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) = C.r ^ i * ⟨p, hpV⟩ :=
      Subtype.ext (by simp [r_coe])
    rw [e', map_mul, hρp, mul_one, map_zpow, C.rho_r] at hρx
    obtain ⟨k, hk⟩ := (r_pow_cases i).1 hρx
    rw [hk, zpow_mul]
    exact (C.W ⊔ C.A).mul_mem ((C.W ⊔ C.A).zpow_mem h3 k) hp
  ·
    exfalso
    have e' : (⟨_, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) = C.v * C.r ^ i * ⟨p, hpV⟩ :=
      Subtype.ext (by simp [r_coe])
    rw [e', map_mul, map_mul, hρp, mul_one, map_zpow, C.rho_r, C.rho_v] at hρx
    exact (r_pow_cases i).2 hρx

theorem N_prod_F4 {x : G} (hx : x ∈ C.N) :
    ∃ a ∈ C.W, ∃ b ∈ C.A, x = a * b := by
  rw [C.N_eq_F4 hNS h13315 h1356two hH hab hhat] at hx
  have hx' : x ∈ (C.W : Set G) * (C.A : Set G) := by
    rw [← C.coe_W_sup_A_F4 hNS h13315 h1356two hH hab hhat]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem comm_W_A_F4 {a b : G} (ha : a ∈ C.W) (hb : b ∈ C.A) :
    a * b * a⁻¹ * b⁻¹ ∈ C.ZI := by
  have h1 := C.comm_VH_N_F4 hNS h13315 h1356two hH hab hhat ha.1 (C.A_le_N hb)
  have h2 := C.comm_VHg_N_F4 hNS h13315 h1356two hH hab hhat hb.1 (C.W_le_N ha)
  refine ⟨h1.1, ?_⟩
  have e : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact C.VHg.inv_mem h2.1

theorem N_le_normalizer_ZI_F4 :
    C.N ≤ Subgroup.normalizer (C.ZI : Set G) := by
  intro n hn
  have hnQ := C.N_le_cLT_F4 hNS h13315 h1356two hH hab hn
  have h1 := S.cLT_le_normalizer_VH_F4 hNS h13315 h1356two hH hhat hnQ
  have h2 := C.cLT_le_normalizer_VHg_F4 hNS h13315 h1356two hH hhat hnQ
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨hz1, hz2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 z).mp hz1,
      (Subgroup.mem_normalizer_iff.mp h2 z).mp hz2⟩
  · rintro ⟨hz1, hz2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 z).mpr hz1,
      (Subgroup.mem_normalizer_iff.mp h2 z).mpr hz2⟩

theorem comm_N_F4 {x y : G} (hx : x ∈ C.N) (hy : y ∈ C.N) :
    x * y * x⁻¹ * y⁻¹ ∈ C.ZI := by
  have hZn := C.N_le_normalizer_ZI_F4 hNS h13315 h1356two hH hab hhat

  have hW : ∀ a ∈ C.W, ∀ y ∈ C.N, a * y * a⁻¹ * y⁻¹ ∈ C.ZI := by
    intro a ha y hy
    obtain ⟨c, hc, d, hd, rfl⟩ := C.N_prod_F4 hNS h13315 h1356two hH hab hhat hy
    have h1 := C.comm_VH_mem_ZI_F4 hNS h13315 h1356two hH hab ha.1 hc.1
    have h2 := C.comm_W_A_F4 hNS h13315 h1356two hH hab hhat ha hd
    have e : a * (c * d) * a⁻¹ * (c * d)⁻¹ =
        (a * c * a⁻¹ * c⁻¹) * (c * (a * d * a⁻¹ * d⁻¹) * c⁻¹) := by group
    rw [e]
    exact C.ZI.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp (hZn (C.W_le_N hc)) _).mp h2)
  have hA : ∀ b ∈ C.A, ∀ y ∈ C.N, b * y * b⁻¹ * y⁻¹ ∈ C.ZI := by
    intro b hb y hy
    obtain ⟨c, hc, d, hd, rfl⟩ := C.N_prod_F4 hNS h13315 h1356two hH hab hhat hy
    have h1 : b * c * b⁻¹ * c⁻¹ ∈ C.ZI := by
      have := C.comm_W_A_F4 hNS h13315 h1356two hH hab hhat hc hb
      have e : b * c * b⁻¹ * c⁻¹ = (c * b * c⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact C.ZI.inv_mem this
    have h2 := C.comm_VHg_mem_ZI_F4 hNS h13315 h1356two hH hab hb.1 hd.1
    have e : b * (c * d) * b⁻¹ * (c * d)⁻¹ =
        (b * c * b⁻¹ * c⁻¹) * (c * (b * d * b⁻¹ * d⁻¹) * c⁻¹) := by group
    rw [e]
    exact C.ZI.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp (hZn (C.W_le_N hc)) _).mp h2)
  obtain ⟨a, ha, b, hb, rfl⟩ := C.N_prod_F4 hNS h13315 h1356two hH hab hhat hx
  have h1 := hW a ha y hy
  have h2 := hA b hb y hy
  have e : a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by
    group
  rw [e]
  exact C.ZI.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn (C.W_le_N ha)) _).mp h2) h1

theorem dmod_F4 :
    DMod.Hyp C.N C.ZI C.W C.A (C.v : G) (C.w : G) where
  ZW := C.ZI_le_W_F4 hNS h13315 h1356two hH hab
  ZA := C.ZI_le_A_F4 hNS h13315 h1356two hH hab
  WN := C.W_le_N
  AN := C.A_le_N
  WA := fun x hx hx' => ⟨hx.1, hx'.1⟩
  prod := fun x hx => C.N_prod_F4 hNS h13315 h1356two hH hab hhat hx
  comm := fun x hx y hy => C.comm_N_F4 hNS h13315 h1356two hH hab hhat hx hy
  vN := fun x hx => C.comm_VH_N_F4 hNS h13315 h1356two hH hab hhat C.v_mem hx
  vW := fun x hx => C.comm_VH_mem_ZI_F4 hNS h13315 h1356two hH hab C.v_mem hx.1
  wN := fun x hx => C.comm_VHg_N_F4 hNS h13315 h1356two hH hab hhat C.w_mem hx
  wA := fun x hx => C.comm_VHg_mem_ZI_F4 hNS h13315 h1356two hH hab C.w_mem hx.1
  vZ := C.v_le_normalizer_ZI_F4 hNS h13315 h1356two hH hab
  wZ := C.w_le_normalizer_ZI_F4 hNS h13315 h1356two hH hab
  v2 := by rw [C.v_sq]; exact C.N.one_mem
  w2 := by rw [C.w_sq]; exact C.N.one_mem
  yA := fun a ha => ⟨C.conj_y_mem_VH_F4 hNS h13315 h1356two hH hab ha.1,
    A5.conj_mem_centralizer_of_mem_normalizer C.y.2 ha.2⟩
  yW := fun a ha => ⟨C.conj_y_mem_VHg_F4 hNS h13315 h1356two hH hab ha.1, by
    have := A5.conj_mem_centralizer_of_mem_normalizer (C.y⁻¹).2 ha.2
    rw [Subgroup.coe_inv, inv_inv] at this
    exact this⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
