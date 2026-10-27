module

public import CFSG.Quasithin.H13.L32A711c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure Ctx711_F4 (T L V H V₂ H₂ : Subgroup G) (z a l p : G) : Prop where

  S : Setting147 G T L V H

  h1222 : Stmt12_2_2_F4

  h1332 : Stmt13_3_2_F4

  h1334 : A6.Stmt13_3_4_F4

  hThm : Thm14_5_3_F4

  h4 : Lemma14_7_4_two_three_F4

  hV2 : A6.IsV2 T V V₂

  hz : z ∈ fsuV1 T V

  hz1 : z ≠ 1

  ha : a ∈ V₂

  haV : a ∉ fsuV1 T V

  hl : l ∈ L₁Of L V₂

  hl3 : l ^ 3 = 1

  hlz : l * z * l⁻¹ = a

  hp : p ∈ pCoreOf 2 (A6.g1 T V)

  hpa : p * a * p⁻¹ ≠ a

  TH₂ : T ≤ H₂

  H₂H : H₂ ≤ H

  idx : T.relIndex H₂ = 3

  nn : ¬ H₂ ≤ Subgroup.normalizer (T : Set G)

  inc : ¬ H₂ ≤ l1 T L V ⊔ T

  inc' : ¬ l1 T L V ⊔ T ≤ H₂

  cls : ∀ Y : Subgroup G, T ≤ Y → Y ≤ H → Y = T ∨ Y = l1 T L V ⊔ T ∨ Y = H₂ ∨ Y = H

namespace Ctx711_F4
open CFSG.Quasithin.H13.L32A.Ctx711_F4

variable {T L V H V₂ H₂ : Subgroup G} {z a l p : G} (C : Ctx711_F4 T L V H V₂ H₂ z a l p)
include C

theorem V_comm_F4 : IsMulCommutative ↥V :=
  (stmtL32NModule_of_inputs_F4 C.h1332 C.h1334 G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1

theorem V2_facts_F4 : (∀ v ∈ V₂, v = 1 ∨ v = z ∨ v = a ∨ v = a * z) ∧ z * z = 1 ∧ a * a = 1 ∧
    a * z = z * a ∧ z ∈ V₂ := by
  have := C.V_comm_F4
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have hzV : z ∈ V := (Subgroup.mem_inf.mp C.hz).1
  have haV' : a ∈ V := C.hV2.2.1 C.ha
  have haa : a * a = 1 := S14.mul_self_V_F4 haV'
  refine ⟨fun v hv => ?_, S14.mul_self_V_F4 hzV, haa, S14.comm_V_F4 haV' hzV, C.hV2.1 C.hz⟩
  rcases S14.mem_V2_F4 C.ha C.haV hv with h | h
  · rcases S14.eq_of_mem_V1_F4 C.hz C.hz1 h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases S14.eq_of_mem_V1_F4 C.hz C.hz1 h with h' | h'
    · right; right; left
      calc v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
        _ = a := by rw [h', mul_one]
    · right; right; right
      calc v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
        _ = a * z := by rw [h']

theorem T_fix_z_F4 {t : G} (ht : t ∈ T) : t * z * t⁻¹ = z := conj_fsuV1 C.hz ht

theorem mem_cent_F4 {g : G} (hgz : g * z * g⁻¹ = z) (hga : g * a * g⁻¹ = a) :
    g ∈ Subgroup.centralizer (V₂ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hfix : g * v * g⁻¹ = v := by
    rcases C.V2_facts_F4.1 v hv with rfl | rfl | rfl | rfl
    · group
    · exact hgz
    · exact hga
    · rw [show g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) by group, hga, hgz]
  calc v * g = (g * v * g⁻¹) * g := by rw [hfix]
    _ = g * v := by group

theorem conj_a_F4 {g : G} (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) (hgz : g * z * g⁻¹ = z) :
    g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a * z := by
  have hmem : g * a * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hgN a).mp C.ha
  rcases C.V2_facts_F4.1 _ hmem with h | h | h | h
  · exfalso
    apply C.haV
    have h' : g * a * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    rw [mul_left_cancel (mul_right_cancel h')]
    exact one_mem _
  · exfalso
    apply C.haV
    have h' : g * a * g⁻¹ = g * z * g⁻¹ := h.trans hgz.symm
    rw [mul_left_cancel (mul_right_cancel h')]
    exact C.hz
  · exact Or.inl h
  · exact Or.inr h

theorem inv_mul_mem_cent_F4 {g h : G} (hgN : g ∈ Subgroup.normalizer (V₂ : Set G))
    (hhN : h ∈ Subgroup.normalizer (V₂ : Set G)) (hgz : g * z * g⁻¹ = z) (hhz : h * z * h⁻¹ = z)
    (hga : g * a * g⁻¹ ≠ a) (hha : h * a * h⁻¹ ≠ a) :
    g⁻¹ * h ∈ Subgroup.centralizer (V₂ : Set G) := by
  have hg := (C.conj_a_F4 hgN hgz).resolve_left hga
  have hh := (C.conj_a_F4 hhN hhz).resolve_left hha
  refine C.mem_cent_F4 ?_ ?_
  · calc g⁻¹ * h * z * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * z * h⁻¹) * g := by group
      _ = z := by rw [hhz]; have := congrArg (fun u => g⁻¹ * u * g) hgz; simpa [mul_assoc] using
          this.symm
  · calc g⁻¹ * h * a * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * a * h⁻¹) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹) * g := by rw [hh, hg]
      _ = a := by group

theorem sq_mem_cent_F4 {g : G} (hgN : g ∈ Subgroup.normalizer (V₂ : Set G))
    (hgz : g * z * g⁻¹ = z) : g * g ∈ Subgroup.centralizer (V₂ : Set G) := by
  obtain ⟨-, hzz, haa, haz, -⟩ := C.V2_facts_F4
  refine C.mem_cent_F4 (by
    rw [show g * g * z * (g * g)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ by group, hgz, hgz]) ?_
  rcases C.conj_a_F4 hgN hgz with h | h
  · rw [show g * g * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ by group, h, h]
  · rw [show g * g * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ by group, h,
      show g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) by group, h, hgz, mul_assoc, hzz,
      mul_one]

theorem TH_F4 : T ≤ H := le_sup_right.trans C.S.hz.1.1

theorem L1H_F4 : l1 T L V ≤ H := le_sup_left.trans C.S.hz.1.1

theorem TL_F4 : T ≤ Subgroup.normalizer (L : Set G) :=
  (C.h1332 G T L C.S.hyp.hyp.h13 L C.S.hyp.hyp.h13.faithful).2.1.1

theorem L1T_le_M_F4 : l1 T L V ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)) C.TL_F4

theorem TV₂_F4 : T ≤ Subgroup.normalizer (V₂ : Set G) := C.hV2.2.2.1

theorem syl_F4 {X : Subgroup G} (hTX : T ≤ X) : IsSylowTwoOf T X :=
  isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow hTX

theorem T2_F4 : IsPGroup 2 T := C.S.hyp.fsu.sylow.1

theorem H_eq_F4 : l1 T L V ⊔ T ⊔ H₂ = H := by
  have hle : l1 T L V ⊔ T ⊔ H₂ ≤ H := sup_le (sup_le C.L1H_F4 C.TH_F4) C.H₂H
  have hT : T ≤ l1 T L V ⊔ T ⊔ H₂ := le_sup_right.trans le_sup_left
  have h₁ : l1 T L V ⊔ T ≤ l1 T L V ⊔ T ⊔ H₂ := le_sup_left
  have h₂ : H₂ ≤ l1 T L V ⊔ T ⊔ H₂ := le_sup_right
  rcases C.cls (l1 T L V ⊔ T ⊔ H₂) hT hle with h | h | h | h
  · exfalso
    apply C.inc
    exact h₂.trans (h.le.trans le_sup_right)
  · exact absurd (h₂.trans h.le) C.inc
  · exact absurd (h₁.trans h.le) C.inc'
  · exact h

theorem YT_F4 : oTwoUpper H₂ ⊔ T = H₂ := by
  have hS := C.syl_F4 C.TH₂
  refine le_antisymm (sup_le (oTwoUpper_le H₂) C.TH₂) ?_
  have h1 : (oTwoUpper H₂ ⊔ T).relIndex H₂ ∣ T.relIndex H₂ :=
    Subgroup.relIndex_dvd_of_le_left H₂ le_sup_right
  rw [C.idx] at h1
  have h2 : (oTwoUpper H₂ ⊔ T).relIndex H₂ ∣ (oTwoUpper H₂).relIndex H₂ :=
    Subgroup.relIndex_dvd_of_le_left H₂ le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper H₂).relIndex H₂ = 2 ^ m := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn : ((oTwoUpper H₂).subgroupOf H₂).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H₂)).mpr
        (fun x hx => normalizer_le_normalizer_oTwoUpper H₂ (Subgroup.le_normalizer hx))
    have hp : IsPGroup 2 (↥H₂ ⧸ (oTwoUpper H₂).subgroupOf H₂) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
      refine ⟨k, ?_⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      apply mem_oTwoUpper_of_odd (H₂.pow_mem x.2 _)
      have hord : orderOf ((x : G) ^ 2 ^ k) = m := by
        rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hkm,
          Nat.gcd_mul_right_left]
        exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
      rw [hord]
      exact hm
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  have h4 : (oTwoUpper H₂ ⊔ T).relIndex H₂ = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact h
    · rw [h] at hi
      exact absurd hi (by
        intro h'
        have : (2 : ℕ) ∣ 3 := by
          rcases i with _ | i
          · norm_num at h'
          · rw [h', pow_succ]; exact dvd_mul_left 2 _
        norm_num at this)
  exact Subgroup.relIndex_eq_one.mp h4

theorem TY_F4 : T ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := fun _ ht =>
  normalizer_le_normalizer_oTwoUpper H₂ (Subgroup.le_normalizer (C.TH₂ ht))

theorem H₂_S3_F4 : quasithinO2QuotientIso H₂ (Equiv.Perm (Fin 3)) :=
  U3.quot_S3_of_index_three (C.syl_F4 C.TH₂) C.idx C.nn

theorem Y_not_le_M_F4 : ¬ oTwoUpper H₂ ≤ Subgroup.normalizer (L : Set G) := fun h => by
  apply C.S.hz.2.2
  rw [← C.H_eq_F4, ← C.YT_F4]
  exact sup_le C.L1T_le_M_F4 (sup_le h C.TL_F4)

theorem V2_comm_F4 : ⁅V₂, oTwoUpper H₂⁆ = ⊥ := by
  have hYo : oTwoUpper (oTwoUpper H₂) = oTwoUpper H₂ :=
    le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
      mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2)
  have hYG : oTwoUpper H₂ ≤ A6.g1 T V := ((oTwoUpper_le H₂).trans C.H₂H).trans C.S.hz.2.1
  have hS3 : quasithinO2QuotientIso (oTwoUpper H₂ ⊔ T) (Equiv.Perm (Fin 3)) := by
    rw [C.YT_F4]
    exact C.H₂_S3_F4
  exact ((C.hThm G T L V C.S.hyp (oTwoUpper H₂) V₂ C.hV2 hYo hYG C.TY_F4 hS3).1).resolve_left
    C.Y_not_le_M_F4

theorem Y_cent_F4 : oTwoUpper H₂ ≤ Subgroup.centralizer (V₂ : Set G) := by
  have h := C.V2_comm_F4
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact Subgroup.le_centralizer_iff.mp h

theorem I2_eq_F4 : i2 T V V₂ = L₁Of L V₂ ⊔ pCoreOf 2 (A6.g1 T V) := (C.h4 G T L V V₂ C.S.hyp C.hV2).2.1

theorem NV2_le_NI2_F4 : Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i2 T V V₂ : Set G) :=
  (C.h4 G T L V V₂ C.S.hyp C.hV2).1.2

theorem I2_S3_F4 : quasithinO2QuotientIso (i2 T V V₂) (Equiv.Perm (Fin 3)) :=
  (quasithinO2QuotientIso_iff _ _).2 (C.h4 G T L V V₂ C.S.hyp C.hV2).2.2.1

theorem O2G1_le_T_F4 : pCoreOf 2 (A6.g1 T V) ≤ T :=
  pCoreOf_le_of_le C.S.hyp (C.TH_F4.trans C.S.hz.2.1)

theorem pT_F4 : p ∈ T := C.O2G1_le_T_F4 C.hp

theorem L2_le_I2_F4 : L₁Of L V₂ ≤ i2 T V V₂ := by
  rw [C.I2_eq_F4]
  exact le_sup_left

theorem NI2_le_NL2_F4 : Subgroup.normalizer (i2 T V V₂ : Set G) ≤
    Subgroup.normalizer (L₁Of L V₂ : Set G) := by
  rw [(C.h4 G T L V V₂ C.S.hyp C.hV2).2.2.2.1, oTwoRes_eq_oTwoUpper]
  exact normalizer_le_normalizer_oTwoUpper _

theorem T_le_NL2_F4 : T ≤ Subgroup.normalizer (L₁Of L V₂ : Set G) :=
  C.TV₂_F4.trans (C.NV2_le_NI2_F4.trans C.NI2_le_NL2_F4)

theorem Y_le_NL2_F4 : oTwoUpper H₂ ≤ Subgroup.normalizer (L₁Of L V₂ : Set G) :=
  (C.Y_cent_F4.trans (Subgroup.centralizer_le_normalizer _)).trans
    (C.NV2_le_NI2_F4.trans C.NI2_le_NL2_F4)

theorem l_moves_F4 : l * z * l⁻¹ ≠ z := by
  rw [C.hlz]
  exact fun h => C.haV (h ▸ C.hz)

theorem d1_le_NV2_F4 : d1 T L H₂ V₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
  sup_le (sup_le (C.Y_cent_F4.trans (Subgroup.centralizer_le_normalizer _)) (L2_le_NV2 L V₂)) C.TV₂_F4

theorem d1_le_NI2_F4 : d1 T L H₂ V₂ ≤ Subgroup.normalizer (i2 T V V₂ : Set G) :=
  C.d1_le_NV2_F4.trans C.NV2_le_NI2_F4

theorem I2_le_d1_F4 : i2 T V V₂ ≤ d1 T L H₂ V₂ := by
  rw [C.I2_eq_F4]
  exact sup_le (le_sup_right.trans le_sup_left) (C.O2G1_le_T_F4.trans le_sup_right)

theorem H₂_le_d1_F4 : H₂ ≤ d1 T L H₂ V₂ :=
  calc H₂ = oTwoUpper H₂ ⊔ T := C.YT_F4.symm
    _ ≤ d1 T L H₂ V₂ := sup_le (Y_le_d1 T L H₂ V₂) (T_le_d1 T L H₂ V₂)

theorem mem_d1_F4 {d : G} (hd : d ∈ d1 T L H₂ V₂) :
    ∃ l' ∈ L₁Of L V₂, ∃ y ∈ oTwoUpper H₂, ∃ t ∈ T, d = l' * y * t := by
  have hTN : T ≤ Subgroup.normalizer ((oTwoUpper H₂ ⊔ L₁Of L V₂ : Subgroup G) : Set G) :=
    fun _ ht => F6.mem_normalizer_sup (C.TY_F4 ht) (C.T_le_NL2_F4 ht)
  obtain ⟨e, he, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTN).mp hd
  rw [sup_comm] at he
  obtain ⟨l', hl', y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes C.Y_le_NL2_F4).mp he
  exact ⟨l', hl', y, hy, t, ht, rfl⟩

theorem L2T_idx_F4 : T.relIndex (L₁Of L V₂ ⊔ T) = 3 := by
  have hIT : i2 T V V₂ ⊔ T = L₁Of L V₂ ⊔ T := by
    rw [C.I2_eq_F4]
    exact le_antisymm (sup_le (sup_le le_sup_left (C.O2G1_le_T_F4.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hTN : T ≤ Subgroup.normalizer (i2 T V V₂ : Set G) := C.TV₂_F4.trans C.NV2_le_NI2_F4
  have hsyl : IsSylowTwoOf (T ⊓ i2 T V V₂) (i2 T V V₂) :=
    A4.isSylowTwoOf_inf_normal (C.syl_F4 (le_sup_right : T ≤ i2 T V V₂ ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTN)
  rw [← hIT, U3.relIndex_sup_eq hTN, inf_comm]
  exact U3.relIndex_eq_three_of_quot C.I2_S3_F4 hsyl

theorem cent_L2T_le_F4 : (L₁Of L V₂ ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C' := (L₁Of L V₂ ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) with hC'
  have hTC : T ≤ Subgroup.normalizer (C' : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right ht),
      mem_normalizer_centralizer' (C.TV₂_F4 ht)⟩
  have hle : C' ⊔ T ≤ L₁Of L V₂ ⊔ T := sup_le inf_le_left le_sup_right
  have hm := Subgroup.relIndex_mul_relIndex T (C' ⊔ T) (L₁Of L V₂ ⊔ T) le_sup_right hle
  rw [C.L2T_idx_F4] at hm
  have hd : T.relIndex (C' ⊔ T) ∣ 3 := Dvd.intro _ hm
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h3] at hm
    have h1 : (C' ⊔ T).relIndex (L₁Of L V₂ ⊔ T) = 1 := by omega
    have hlCT : l ∈ C' ⊔ T :=
      Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left C.hl)
    obtain ⟨c, hc, t, ht, hct⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTC).mp hlCT
    obtain ⟨k, hk⟩ := C.T2_F4 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hpow : l ^ 2 ^ k ∈ C' := by
      have := mul_pow_mul_inv_mem' hc (hTC ht) (2 ^ k)
      rwa [hk', inv_one, mul_one, ← hct] at this
    have hcop : Nat.Coprime (2 ^ k) (orderOf l) :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one C.hl3)
    have hlC : l ∈ C' := (Subgroup.zpowers_le.mpr hpow) (A4.mem_zpowers_pow_of_coprime hcop)
    apply C.l_moves_F4
    have := Subgroup.mem_centralizer_iff.mp hlC.2 z (C.V2_facts_F4.2.2.2.2)
    rw [← this]
    group

theorem Y_le_aD_F4 : oTwoUpper H₂ ≤ aD T L H₂ V₂ := le_inf (Y_le_d1 T L H₂ V₂) C.Y_cent_F4

theorem d1_le_NaD_F4 : d1 T L H₂ V₂ ≤ Subgroup.normalizer (aD T L H₂ V₂ : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
    mem_normalizer_centralizer' (C.d1_le_NV2_F4 hg)⟩

theorem aD_eq_F4 : aD T L H₂ V₂ = oTwoUpper H₂ ⊔ (aD T L H₂ V₂ ⊓ T) := by
  refine le_antisymm (fun d hd => ?_) (sup_le C.Y_le_aD_F4 inf_le_left)
  obtain ⟨l', hl', y, hy, t, ht, rfl⟩ := C.mem_d1_F4 hd.1
  have hdC := Subgroup.mem_centralizer_iff.mp hd.2
  have hyC := Subgroup.mem_centralizer_iff.mp (C.Y_cent_F4 hy)

  have hltC : l' * t ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have htv : t * v * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (C.TV₂_F4 ht) v).mp hv
    have h1 := hdC v hv
    have h2 := hyC _ htv
    have e1 : v * (l' * t) = v * (l' * y * t) * (y * t)⁻¹ * t := by group
    have e2 : l' * t * v = l' * (y * (t * v * t⁻¹) * y⁻¹) * t := by
      rw [← h2]
      group
    rw [e1, h1, e2]
    group
  have hl'T : l' ∈ T := by
    have h := C.cent_L2T_le_F4 ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hl')
      (Subgroup.mem_sup_right ht), hltC⟩
    rw [show l' = l' * t * t⁻¹ by group]
    exact mul_mem h (inv_mem ht)
  have hYT : l' * y * t ∈ oTwoUpper H₂ ⊔ T := by
    rw [show l' * y * t = (l' * y * l'⁻¹) * (l' * t) by group]
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (C.TY_F4 hl'T) y).mp hy))
      (Subgroup.mem_sup_right (mul_mem hl'T ht))
  obtain ⟨y', hy', t', ht', e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes C.TY_F4).mp hYT
  have ht'A : t' ∈ aD T L H₂ V₂ := by
    rw [show t' = y'⁻¹ * (l' * y * t) by rw [e]; group]
    exact mul_mem (inv_mem (C.Y_le_aD_F4 hy')) hd
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hy') (Subgroup.mem_sup_right ⟨ht'A, ht'⟩)

theorem aD_le_H₂_F4 : aD T L H₂ V₂ ≤ H₂ :=
  calc aD T L H₂ V₂ = oTwoUpper H₂ ⊔ (aD T L H₂ V₂ ⊓ T) := C.aD_eq_F4
    _ ≤ oTwoUpper H₂ ⊔ T := sup_le_sup_left inf_le_right _
    _ = H₂ := C.YT_F4

theorem aD_idx_F4 : (aD T L H₂ V₂ ⊓ T).relIndex (aD T L H₂ V₂) = 3 := by
  set P := aD T L H₂ V₂ ⊓ T with hP
  have hA : aD T L H₂ V₂ = oTwoUpper H₂ ⊔ P := C.aD_eq_F4
  have hPY : P ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := inf_le_right.trans C.TY_F4
  have hYP : oTwoUpper H₂ ⊓ P = oTwoUpper H₂ ⊓ T :=
    le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf (inf_le_left.trans C.Y_le_aD_F4) inf_le_right))
  calc P.relIndex (aD T L H₂ V₂) = P.relIndex (oTwoUpper H₂ ⊔ P) := by rw [← hA]
    _ = (oTwoUpper H₂ ⊓ P).relIndex (oTwoUpper H₂) := U3.relIndex_sup_eq hPY
    _ = (oTwoUpper H₂ ⊓ T).relIndex (oTwoUpper H₂) := by rw [hYP]
    _ = T.relIndex (oTwoUpper H₂ ⊔ T) := (U3.relIndex_sup_eq C.TY_F4).symm
    _ = 3 := by rw [C.YT_F4, C.idx]

theorem aD_syl_F4 : IsSylowTwoOf (aD T L H₂ V₂ ⊓ T) (aD T L H₂ V₂) := by
  refine ⟨inf_le_left, C.T2_F4.to_le inf_le_right, ?_⟩
  change ¬ 2 ∣ (aD T L H₂ V₂ ⊓ T).relIndex (aD T L H₂ V₂)
  rw [C.aD_idx_F4]
  norm_num

theorem T_aD_idx_F4 : (aD T L H₂ V₂ ⊓ T).relIndex T ≤ 2 := by
  classical
  have hle : aD T L H₂ V₂ ⊓ T ≤ T := inf_le_right
  have hmem : ∀ t ∈ T, t ∈ Subgroup.centralizer (V₂ : Set G) → t ∈ aD T L H₂ V₂ ⊓ T :=
    fun t ht hc => ⟨⟨(T_le_d1 T L H₂ V₂) ht, hc⟩, ht⟩
  have hpN := C.TV₂_F4 C.pT_F4
  have hpz := C.T_fix_z_F4 C.pT_F4
  let f : ↥T → Bool × ↥(aD T L H₂ V₂ ⊓ T) := fun t =>
    if h : (t : G) ∈ Subgroup.centralizer (V₂ : Set G) then (false, ⟨t, hmem t t.2 h⟩)
    else (true, ⟨p⁻¹ * t, hmem _ (mul_mem (inv_mem C.pT_F4) t.2) (C.inv_mul_mem_cent_F4 hpN
      (C.TV₂_F4 t.2) hpz (C.T_fix_z_F4 t.2) C.hpa (fun ha => h (C.mem_cent_F4 (C.T_fix_z_F4 t.2) ha)))⟩)
  have hf : Function.Injective f := by
    intro s t hst
    by_cases hs : (s : G) ∈ Subgroup.centralizer (V₂ : Set G) <;>
      by_cases ht : (t : G) ∈ Subgroup.centralizer (V₂ : Set G) <;>
      simp only [f, hs, ht, dite_true, dite_false, Prod.mk.injEq, Bool.false_eq_true,
        Bool.true_eq_false, false_and] at hst
    · exact Subtype.ext (congrArg (fun x : ↥(aD T L H₂ V₂ ⊓ T) => (x : G)) hst.2)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun x : ↥(aD T L H₂ V₂ ⊓ T) => (x : G))
        hst.2))
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  have h1 : (aD T L H₂ V₂ ⊓ T).relIndex T * Nat.card ↥(aD T L H₂ V₂ ⊓ T) = Nat.card T := by
    rw [Subgroup.relIndex, mul_comm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_mul_index]
  have hpos : 0 < Nat.card ↥(aD T L H₂ V₂ ⊓ T) := Nat.card_pos
  by_contra hc
  push Not at hc
  have : 3 * Nat.card ↥(aD T L H₂ V₂ ⊓ T) ≤ Nat.card T := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hc
  omega

theorem O2G1_le_O2H_F4 : pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 (C.O2G1_le_T_F4.trans C.TH_F4)
    (C.S.hz.2.1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem aD_nn_F4 : ¬ aD T L H₂ V₂ ≤ Subgroup.normalizer ((aD T L H₂ V₂ ⊓ T : Subgroup G) : Set G) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : aD T L H₂ V₂ ⊓ T ≤ pCoreOf 2 (aD T L H₂ V₂) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left h (C.T2_F4.to_le inf_le_right)
  have hN : H₂ ≤ Subgroup.normalizer (aD T L H₂ V₂ : Set G) := C.H₂_le_d1_F4.trans C.d1_le_NaD_F4
  have h2 : pCoreOf 2 (aD T L H₂ V₂) ≤ pCoreOf 2 H₂ := U3.pCoreOf_le_pCoreOf C.aD_le_H₂_F4 hN
  have hOT : pCoreOf 2 H₂ ≤ T := pCoreOf_le_of_le C.S.hyp C.TH₂
  have h3 : (pCoreOf 2 H₂).relIndex T = 2 := U3.relIndex_pCoreOf_T C.H₂_S3_F4 C.TH₂ C.idx hOT
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ (h1.trans h2) hOT
  rw [h3] at hm
  have hpos : (aD T L H₂ V₂ ⊓ T).relIndex (pCoreOf 2 H₂) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : (aD T L H₂ V₂ ⊓ T).relIndex (pCoreOf 2 H₂) = 1 := by
    have := C.T_aD_idx_F4
    omega
  have h5 : pCoreOf 2 H₂ ≤ aD T L H₂ V₂ ⊓ T := Subgroup.relIndex_eq_one.mp h4
  have h6 : pCoreOf 2 H ≤ pCoreOf 2 H₂ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le C.S.hyp C.TH_F4).trans C.TH₂)
      (C.H₂H.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hpA := h5 (h6 (C.O2G1_le_O2H_F4 C.hp))
  apply C.hpa
  have := Subgroup.mem_centralizer_iff.mp hpA.1.2 a C.ha
  rw [← this]
  group

end Ctx711_F4

end CFSG.Quasithin.H13.L32A
