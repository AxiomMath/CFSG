module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520gS331

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setting

variable {T L V H : Subgroup G}

theorem le_M_of_three_F4 (h331 : Stmt3_3_1_F4) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {W N : Subgroup G}
    (hWH : W ≤ H) (hWL : W ≤ Subgroup.normalizer (l1 T L V : Set G)) (hOT : pCoreOf 2 W ≤ T)
    (hQN : pCoreOf 2 W ≤ N) (hNW : N ≤ W) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ∀ k ∈ N, k ^ 3 ∈ pCoreOf 2 W) (h3 : (pCoreOf 2 W).relIndex N = 3) :
    N ≤ Subgroup.normalizer (L : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful).2.1.1
  have hO : oTwoUpper N ≤ Subgroup.normalizer (L : Set G) :=
    le_M_of_index_three_F4 h331 hThm h1222 h1332 h1334 S ((oTwoUpper_le N).trans (hNW.trans hWH))
      (oTwoUpper_oTwoUpper N) (hTN.trans (normalizer_le_normalizer_oTwoUpper N))
      (by rw [relIndex_oTwoUpper_eq hQN hNW hN3, h3])
      (Subgroup.set_mul_normalizer_comm _ _ (((oTwoUpper_le N).trans hNW).trans hWL))
  rw [← oTwoUpper_sup_pCoreOf_eq hQN hN3]
  exact sup_le hO (hOT.trans hTL)

end Setting

structure E9Ctx_F4 (T L V H Y : Subgroup G) : Prop where

  h331 : Stmt3_3_1_F4

  hThm : Thm14_5_3_F4

  h1222 : Stmt12_2_2_F4

  h1332 : Stmt13_3_2_F4

  h1334 : A6.Stmt13_3_4_F4

  S : Setting147 G T L V H

  YH : Y ≤ H

  HY : H ≤ Subgroup.normalizer (Y : Set G)

  Y3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y

  L1Y : l1 T L V ≤ Y

  E9 : IsElemAbelianOfRank 3 2 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)

namespace E9Ctx_F4
open CFSG.Quasithin.H13.L32A.E9Ctx

variable {T L V H Y : Subgroup G} (C : E9Ctx_F4 T L V H Y)
include C

theorem TH_F4 : T ≤ H := le_sup_right.trans C.S.hz.1.1

theorem TY_F4 : T ≤ Subgroup.normalizer (Y : Set G) := C.TH_F4.trans C.HY

theorem TL_F4 : T ≤ Subgroup.normalizer (L : Set G) :=
  (C.h1332 G T L C.S.hyp.hyp.h13 L C.S.hyp.hyp.h13.faithful).2.1.1

theorem Tl1_F4 : T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
  (l1_facts_F4 C.h1222 C.h1332 C.h1334 C.S C.YH C.HY).1

theorem QT_F4 : pCoreOf 2 Y ≤ T := (l1_facts_F4 C.h1222 C.h1332 C.h1334 C.S C.YH C.HY).2.1

theorem TQ_F4 : T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
  C.TY_F4.trans (normalizer_le_normalizer_pCoreOf 2 Y)

theorem HQ_F4 : H ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
  C.HY.trans (normalizer_le_normalizer_pCoreOf 2 Y)

theorem card_F4 : (pCoreOf 2 Y).relIndex Y = 9 := by
  obtain ⟨e⟩ := C.E9
  rw [relIndex_eq_card_quot, Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem comm_F4 : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 Y :=
  comm_mem_of_relIndex_le le_rfl C.Y3 (by rw [C.card_F4])

theorem L1Q_le_F4 : l1 T L V ⊔ pCoreOf 2 Y ≤ Y := sup_le C.L1Y (pCoreOf_le 2 Y)

theorem Y_le_N_L1Q_F4 : Y ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 Y : Subgroup G) : Set G) :=
  le_normalizer_of_comm_mem le_sup_right C.comm_F4 C.L1Q_le_F4

theorem T_le_N_L1Q_F4 : T ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 Y : Subgroup G) : Set G) :=
  fun _ ht => F6.mem_normalizer_sup (C.Tl1_F4 ht) (C.TQ_F4 ht)

theorem oTwoUpper_L1Q_F4 : oTwoUpper (l1 T L V ⊔ pCoreOf 2 Y) = l1 T L V :=
  le_antisymm (oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 Y) (C.QT_F4.trans C.Tl1_F4))
    (calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
      _ ≤ _ := oTwoUpper_mono le_sup_left)

theorem Y_le_N_l1_F4 : Y ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have := C.Y_le_N_L1Q_F4.trans (normalizer_le_normalizer_oTwoUpper (l1 T L V ⊔ pCoreOf 2 Y))
  rwa [C.oTwoUpper_L1Q_F4] at this

theorem lp3_F4 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 := by
  have hMod := stmtL32NModule_of_inputs_F4 C.h1332 C.h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 C.h1332) hMod C.h1222
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have h3 := S14.Lp3_F4
  rwa [hl1eq] at h3

theorem L1Q3_F4 : (pCoreOf 2 Y).relIndex (l1 T L V ⊔ pCoreOf 2 Y) = 3 := by
  have h := relIndex_oTwoUpper_eq (le_sup_right : pCoreOf 2 Y ≤ l1 T L V ⊔ pCoreOf 2 Y)
    C.L1Q_le_F4 fun k hk => C.Y3 k (C.L1Q_le_F4 hk)
  rw [C.oTwoUpper_L1Q_F4, C.lp3_F4] at h
  exact h.symm

theorem L1QY3_F4 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex Y = 3 := by
  have hm := Subgroup.relIndex_mul_relIndex _ _ _
    (le_sup_right : pCoreOf 2 Y ≤ l1 T L V ⊔ pCoreOf 2 Y) C.L1Q_le_F4
  rw [C.card_F4, C.L1Q3_F4] at hm
  omega

theorem coprime_T_F4 : Nat.Coprime 3 (Nat.card T) := by
  obtain ⟨k, hk⟩ := C.S.hyp.fsu.sylow.1.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem Y_le_M_F4 : Y ≤ Subgroup.normalizer (L : Set G) := by
  have hconj : ∀ {K : Subgroup G}, T ≤ Subgroup.normalizer (K : Set G) →
      ∀ d ∈ T, ∀ x ∈ K, d * x * d⁻¹ ∈ K := fun hK d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hK hd) x).mp hx
  obtain ⟨N₁, hQN₁, hN₁Y, hTN₁, hsup₁, hinf₁⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := Y)
      (Φ := pCoreOf 2 Y) (D := T) (T := l1 T L V ⊔ pCoreOf 2 Y) (pCoreOf_le 2 Y) C.comm_F4 C.Y3
      C.coprime_T_F4 (hconj C.TY_F4) (hconj C.TQ_F4) le_sup_right C.L1Q_le_F4 (hconj C.T_le_N_L1Q_F4)
  have hTN₁' : T ≤ Subgroup.normalizer (N₁ : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun x hx => hTN₁ d hd x hx
  have hN₁3 : (pCoreOf 2 Y).relIndex N₁ = 3 := by
    have hn := le_normalizer_of_comm_mem hQN₁ C.comm_F4 hN₁Y
    have := U3.relIndex_sup_eq (C.L1Q_le_F4.trans hn)
    rw [sup_comm N₁, hsup₁, inf_comm N₁, hinf₁, C.L1QY3_F4] at this
    exact this.symm
  have hN₁M := le_M_of_three_F4 C.h331 C.hThm C.h1222 C.h1332 C.h1334 C.S C.YH C.Y_le_N_l1_F4 C.QT_F4
    hQN₁ hN₁Y hTN₁' (fun k hk => C.Y3 k (hN₁Y hk)) hN₁3
  rw [← hsup₁]
  exact sup_le (sup_le (l1_le_M T L V) (C.QT_F4.trans C.TL_F4)) hN₁M

theorem mem_nX_F4 {g : G} (hgH : g ∈ H) (hgM : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ L32NSet14.nX T V := by
  have hMod := stmtL32NModule_of_inputs_F4 C.h1332 C.h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 C.h1332) hMod C.h1222
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 hV2
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have := S14.card_V1_F4
    rw [h, Subgroup.card_bot] at this
    exact absurd this (by norm_num)
  have h6 := lemma1433Six_of_inputs_F4 C.h1332 C.h1334 C.h1222 G T L V C.S.hyp.hyp C.S.hyp.fsu
    (fsuV1 T V) H inf_le_left hV1 C.S.hz.2.1
  have h2 : g ∈ H ⊓ Subgroup.normalizer (L : Set G) := ⟨hgH, hgM⟩
  rw [h6] at h2
  exact ⟨h2.2, C.S.hz.2.1 h2.1⟩

theorem Y_le_X_F4 : Y ≤ L32NSet14.nX T V := fun _ hy => C.mem_nX_F4 (C.YH hy) (C.Y_le_M_F4 hy)

theorem psi_facts_F4 :
    pCoreOf 2 Y ≤ L32NSet14.trivSub V (fsuV1 T V) ∧
      (∃ x ∈ l1 T L V, x ∉ L32NSet14.trivSub V (fsuV1 T V)) ∧
      Y ≤ kY T V Y ⊔ (l1 T L V ⊔ pCoreOf 2 Y) ∧
      ∀ g ∈ H, g ∈ Subgroup.normalizer (L : Set G) → ∀ n : ℕ, g ^ 3 ^ n = 1 →
        g ^ 3 ∈ L32NSet14.trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 C.h1332 C.h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 C.h1332) hMod C.h1222
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hQY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
  obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4

  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨x, hx, -, hxa, -⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
  have hxX : x ∈ L32NSet14.nX T V := S14.L1_le_X_F4 hx
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ fsuV1 T V := ((hψ _).mp h).2.2 a (S14.hV2.2.1 ha)
    rw [hxa] at h2
    apply hbV
    have := mul_mem (S14.hV2.1 h2) ha
    rwa [inv_mul_cancel_right] at this
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := S14.cube_eq_one_F4 ψ hx
  have hxY : x ∈ Y := C.L1Y (hl1eq ▸ hx)

  have h2el : ∀ r (hr : r ∈ pCoreOf 2 Y), ψ ⟨r, C.Y_le_X_F4 (hQY hr)⟩ ^ 2 = 1 := by
    intro r hr
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨r, hr⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have e : (⟨r, C.Y_le_X_F4 (hQY hr)⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [e, map_one]
  have hψQ : ∀ q (hq : q ∈ pCoreOf 2 Y), ψ ⟨q, C.Y_le_X_F4 (hQY hq)⟩ = 1 := by
    intro q hq
    have hxq : x * q * x⁻¹ ∈ pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hxY) q).mp hq
    refine L32NSet14.sl2_eq_one_of_conj _ _ hψx3 hψx (h2el q hq) ?_
    have h2 := h2el _ (mul_mem hq hxq)
    have e : ψ ⟨q * (x * q * x⁻¹), C.Y_le_X_F4 (hQY (mul_mem hq hxq))⟩ =
        ψ ⟨q, C.Y_le_X_F4 (hQY hq)⟩ * (ψ ⟨x, hxX⟩ * ψ ⟨q, C.Y_le_X_F4 (hQY hq)⟩ * (ψ ⟨x, hxX⟩)⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rwa [e] at h2
  refine ⟨fun q hq => (hψ ⟨q, C.Y_le_X_F4 (hQY hq)⟩).mp (hψQ q hq),
    ⟨x, hl1eq ▸ hx, fun h => hψx ((hψ _).mpr h)⟩, fun y hy => ?_, fun g hgH hgM n hgn => ?_⟩
  ·
    have hψy3 : ψ ⟨y, C.Y_le_X_F4 hy⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have e : (⟨y, C.Y_le_X_F4 hy⟩ : ↥(L32NSet14.nX T V)) ^ 3 =
          ⟨y ^ 3, C.Y_le_X_F4 (hQY (C.Y3 y hy))⟩ := Subtype.ext (by simp)
      rw [e]
      exact hψQ _ (C.Y3 y hy)
    have hxQ : x ∈ l1 T L V ⊔ pCoreOf 2 Y := Subgroup.mem_sup_left (hl1eq ▸ hx)
    have hK : ∀ m : ℕ, ψ ⟨y, C.Y_le_X_F4 hy⟩ = ψ ⟨x, hxX⟩ ^ m →
        y * (x ^ m)⁻¹ ∈ kY T V Y := fun m hm => by
      have hyx : y * (x ^ m)⁻¹ ∈ Y := mul_mem hy (inv_mem (pow_mem hxY m))
      refine ⟨hyx, (hψ ⟨_, C.Y_le_X_F4 hyx⟩).mp ?_⟩
      have e : (⟨y * (x ^ m)⁻¹, C.Y_le_X_F4 hyx⟩ : ↥(L32NSet14.nX T V)) =
          ⟨y, C.Y_le_X_F4 hy⟩ * (⟨x, hxX⟩ ^ m)⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_pow, hm, mul_inv_cancel]
    have hy' : ∀ m : ℕ, y * (x ^ m)⁻¹ ∈ kY T V Y → y ∈ kY T V Y ⊔ (l1 T L V ⊔ pCoreOf 2 Y) :=
      fun m hm => by
        rw [show y = y * (x ^ m)⁻¹ * x ^ m by group]
        exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right (pow_mem hxQ m))
    rcases L32A.sl2_mem_of_cube _ _ hψy3 hψx3 hψx with h | h | h
    · exact hy' 0 (hK 0 (by rw [h, pow_zero]))
    · exact hy' 1 (hK 1 (by rw [h, pow_one]))
    · exact hy' 2 (hK 2 (by rw [h, pow_two]))
  ·
    have hgX := C.mem_nX_F4 hgH hgM
    have hg3X := C.mem_nX_F4 (pow_mem hgH 3) (pow_mem hgM 3)
    refine (hψ ⟨g ^ 3, hg3X⟩).mp ?_
    have e : (⟨g ^ 3, hg3X⟩ : ↥(L32NSet14.nX T V)) = ⟨g, hgX⟩ ^ 3 := Subtype.ext (by simp)
    rw [e, map_pow]
    refine L32NSet14.sl2_cube_of_odd (m := 3 ^ n) (Odd.pow (by decide)) ?_
    rw [← map_pow]
    have e2 : (⟨g, hgX⟩ : ↥(L32NSet14.nX T V)) ^ 3 ^ n = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hgn)
    rw [e2, map_one]

theorem Q_le_K_F4 : pCoreOf 2 Y ≤ kY T V Y := le_inf (pCoreOf_le 2 Y) C.psi_facts_F4.1

theorem Y_le_N_K_F4 : Y ≤ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) := fun _ hy =>
  mem_normalizer_kY_F4 (C.Y_le_X_F4 hy) (Subgroup.le_normalizer hy)

theorem T_le_N_K_F4 : T ≤ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_kY_F4 (C.mem_nX_F4 (C.TH_F4 ht) (C.TL_F4 ht)) (C.TY_F4 ht)

theorem HM_le_N_K_F4 {g : G} (hgH : g ∈ H) (hgM : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) :=
  mem_normalizer_kY (C.mem_nX_F4 hgH hgM) (C.HY hgH)

theorem K_inf_F4 : kY T V Y ⊓ (l1 T L V ⊔ pCoreOf 2 Y) = pCoreOf 2 Y := by
  obtain ⟨x, hx, hxK⟩ := C.psi_facts_F4.2.1
  have hle : pCoreOf 2 Y ≤ kY T V Y ⊓ (l1 T L V ⊔ pCoreOf 2 Y) := le_inf C.Q_le_K_F4 le_sup_right
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right
  rw [C.L1Q3_F4] at hmul
  have hd : (pCoreOf 2 Y).relIndex (kY T V Y ⊓ (l1 T L V ⊔ pCoreOf 2 Y)) ∣ 3 :=
    ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at hmul
    have h1 : (kY T V Y ⊓ (l1 T L V ⊔ pCoreOf 2 Y)).relIndex (l1 T L V ⊔ pCoreOf 2 Y) = 1 := by
      omega
    exact hxK (Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left hx)).1.2

theorem K_sup_F4 : kY T V Y ⊔ (l1 T L V ⊔ pCoreOf 2 Y) = Y :=
  le_antisymm (sup_le (kY_le T V Y) C.L1Q_le_F4) C.psi_facts_F4.2.2.1

theorem K3_F4 : (pCoreOf 2 Y).relIndex (kY T V Y) = 3 := by
  have h := U3.relIndex_sup_eq (K := l1 T L V ⊔ pCoreOf 2 Y) (T := kY T V Y)
    ((kY_le T V Y).trans C.Y_le_N_L1Q_F4)
  rw [sup_comm (l1 T L V ⊔ pCoreOf 2 Y) (kY T V Y), C.K_sup_F4,
    inf_comm (l1 T L V ⊔ pCoreOf 2 Y) (kY T V Y), C.K_inf_F4, C.L1Q3_F4] at h
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ C.Q_le_K_F4 (kY_le T V Y)
  rw [C.card_F4, h] at hm
  omega

end E9Ctx_F4

end CFSG.Quasithin.H13.L32A
