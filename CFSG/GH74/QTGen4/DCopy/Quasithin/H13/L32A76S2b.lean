module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A706g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AStatements

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure Ctx_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H Y : Subgroup G) : Prop where
  S : Setting147 G T L V H
  h98 : HypF98 T V L (fsuV1 T V) V H
  h1222 : Stmt12_2_2_F4
  h1332 : Stmt13_3_2_F4
  h1334 : A6.Stmt13_3_4_F4
  hY2 : oTwoUpper Y = Y
  hYH : Y ≤ H
  hHY : H ≤ Subgroup.normalizer (Y : Set G)
  hexp : ∀ y ∈ Y, y ^ 5 ∈ pCoreOf 2 Y
  hYM : Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y
  hHYL : H = Y ⊔ (l1 T L V ⊔ T)
  hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)
  hmin : ∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
    N = modO2Image H Y
  h25 : (pCoreOf 2 Y).relIndex Y = 25

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable {T L V H Y : Subgroup G} (C : Ctx_F4 G T L V H Y)
include C

theorem h91_F4 : HypF91 T V L (fsuV1 T V) V H := C.h98.toHypF91

theorem fact_F4 : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H))) :=
  ⟨C.h91_F4.isElemAbelian_tilde⟩

theorem sq_eq_one_F4 (w : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : w ^ 2 = 1 :=
  Subtype.ext (by simpa using C.h91_F4.isElemAbelian_tilde.2 w w.2)

theorem pCoreOf_Y_F4 : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H :=
  S152Y.pCoreOf_eq_inf_of_normalizer C.hYH C.hHY

theorem rho_mem_X_F4 (x : ↥H) : FixR.rho C.h91_F4 x ∈
    autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) :=
  (FixR.mem_autOn_tilde_iff C.h91_F4 le_rfl).mpr ⟨x, x.2, rfl⟩

theorem rho_mem_E_F4 (y : ↥H) (hy : (y : G) ∈ Y) : FixR.rho C.h91_F4 y ∈
    autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) :=
  (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mpr ⟨y, hy, rfl⟩

theorem conj_mem_E_F4 {g e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hg : g ∈ autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)))
    (he : e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    g * e * g⁻¹ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) := by
  obtain ⟨x, -, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 le_rfl).mp hg
  obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mp he
  refine (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
  exact (Subgroup.mem_normalizer_iff.mp (C.hHY x.2) _).mp hyY

theorem E_le_X_F4 : autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) ≤
    autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) := fun e he => by
  obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mp he
  exact C.rho_mem_X_F4 y

theorem pow_five_E_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (he : e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    e ^ 5 = 1 := by
  obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mp he
  rw [← map_pow]
  refine (FixR.rho_eq_one_iff C.h91_F4 _).mpr ?_
  have := C.hexp y hyY
  rw [C.pCoreOf_Y_F4] at this
  simpa using this.2

theorem pCoreOf_lt_F4 : pCoreOf 2 Y < Y := by
  refine lt_of_le_of_ne (pCoreOf_le 2 Y) fun he => ?_
  have h := C.h25
  rw [he, Subgroup.relIndex_self] at h
  norm_num at h

theorem card_E_F4 :
    Nat.card (autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) = 25 := by
  rw [HypF91.card_autOn_tilde C.h91_F4 C.hYH, ← C.pCoreOf_Y_F4, C.h25]

theorem comm_E_F4 {a b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (ha : a ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hb : b ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hEp : IsPGroup 5
      (autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :=
    fun e => ⟨1, Subtype.ext (by simpa using C.pow_five_E_F4 e.2)⟩
  have hEne : autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) ≠ ⊥ := by
    intro hbot
    have := C.card_E_F4
    rw [hbot, Subgroup.card_bot] at this
    norm_num at this
  exact M76.comm_of_minimal C.h91_F4 C.hYH C.hHY C.hmin hEp hEne a ha b hb

theorem exists_lines_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] :
    ∃ d₁ d₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H)),
      d₁ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) ∧
      d₂ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) ∧
      Lines d₁ d₂ ∧
      ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
        Lines.InE d₁ d₂ e := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h91 := C.h91_F4
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  set ρ := FixR.rho h91 with hρ
  set X := autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) with hX
  set E := autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) with hEdef
  have hV : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), w ^ 2 = 1 := C.sq_eq_one_F4
  have hEp : IsPGroup 5 E := fun e => ⟨1, Subtype.ext (by simpa using C.pow_five_E_F4 e.2)⟩

  have hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    (qhatOf_le_qOf X).trans C.h98.lemma_14_5_18_three.1
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hq)

  by_cases hII : ∃ A ∈ QhatStar X, ∃ a ∈ A, ∃ y : ↥H, (y : G) ∈ Y ∧ a * ρ y ≠ ρ y * a
  swap
  · refine (M76.false_of_caseI_F4 C.S C.h1222 C.h1332 C.h1334 C.h98 (p := 5) (by norm_num) le_rfl
      C.hHY C.hHYL C.hexp C.pCoreOf_lt_F4 fun A hA a ha y hy => ?_).elim
    by_contra hne
    exact hII ⟨A, hA, a, ha, y, hy, hne⟩
  obtain ⟨A, hAQ, a, haA, y, hy, hne⟩ := hII
  have hEX : E ≤ X := C.E_le_X_F4
  have hEO : E ≤ pCoreOf 5 X := le_pCoreOf_of_le_normalizer 5 hEX
    (fun g hg => Subgroup.mem_normalizer_fintype fun e he => C.conj_mem_E_F4 hg he) hEp
  have hEA : ⁅E, A⁆ ≤ E := Subgroup.commutator_le.mpr fun e he b hb => by
    rw [commutatorElement_def, show e * b * e⁻¹ * b⁻¹ = e * (b * e⁻¹ * b⁻¹) by group]
    exact E.mul_mem he (C.conj_mem_E_F4 (QhatStar_le hAQ hb) (E.inv_mem he))
  have hcomm_ne : ⁅E, A⁆ ≠ ⊥ := by
    intro hbot
    have hmem := Subgroup.commutator_mem_commutator (C.rho_mem_E_F4 y hy) haA
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply hne
    calc a * ρ y = (ρ y * a * (ρ y)⁻¹ * a⁻¹)⁻¹ * ρ y * a := by group
      _ = ρ y * a := by rw [hmem, inv_one, one_mul]
  have hEAD : ⁅E, A⁆ ≤ ⁅pCoreOf 5 X, A⁆ := Subgroup.commutator_mono hEO le_rfl
  have hD : ⁅pCoreOf 5 X, A⁆ ≠ ⊥ := fun h => hcomm_ne (eq_bot_iff.mpr (h ▸ hEAD))
  obtain ⟨-, h5, -, -, -⟩ := D2_13 hV hr.symm hAQ (by norm_num : (5 : ℕ) ≠ 2) rfl hD
  obtain ⟨-, -, hDcard, hDcyc, -, hDrk⟩ := h5 rfl
  have hDE : ⁅E, A⁆ = ⁅pCoreOf 5 X, A⁆ := by
    apply Subgroup.eq_of_le_of_card_ge hEAD
    have hdvd : Nat.card ↥(⁅E, A⁆ : Subgroup _) ∣ Nat.card ↥(⁅pCoreOf 5 X, A⁆ : Subgroup _) :=
      Subgroup.card_dvd_of_le hEAD
    rw [hDcard] at hdvd ⊢
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hcomm_ne
    · exact h.ge
  obtain ⟨⟨d, hdD⟩, hgen⟩ := hDcyc.exists_generator
  have hDz : ⁅pCoreOf 5 X, A⁆ = Subgroup.zpowers d := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hdD)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hd1 : d ≠ 1 := by
    intro h1
    rw [hDz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hrk4 : rk (cw d) = 4 := by
    rw [cw, ← commV_zpowers_eq_map, ← hDz]; exact hDrk
  have hdE : d ∈ E := hEA (hDE ▸ hdD)
  have hd5 : d ^ 5 = 1 := C.pow_five_E_F4 hdE
  have hdord : orderOf d = 5 := orderOf_eq_prime hd5 hd1

  obtain ⟨x, hxX, hxd⟩ : ∃ x ∈ X, x * d * x⁻¹ ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have hN : X ≤ Subgroup.normalizer (Subgroup.zpowers d : Set _) := fun g hg =>
      Subgroup.mem_normalizer_fintype fun e he => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ (hcon g hg) j
    have heq := M76.eq_of_minimal h91 C.hYH C.hmin (Subgroup.zpowers_le.mpr hdE) hN
      (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hd1)
    have h1 := C.card_E_F4
    rw [← heq, Nat.card_zpowers, hdord] at h1
    norm_num at h1
  set d₂ := x * d * x⁻¹ with hd₂
  have hd₂E : d₂ ∈ E := C.conj_mem_E_F4 hxX hdE
  have hd₂5 : d₂ ^ 5 = 1 := C.pow_five_E_F4 hd₂E
  have hd₂1 : d₂ ≠ 1 := fun h1 => hxd (h1 ▸ Subgroup.one_mem _)
  have hrk₂ : rk (cw d₂) = 4 := by rw [hd₂, rk_cw_conj, hrk4]
  have hcomm : d * d₂ = d₂ * d := C.comm_E_F4 hdE hd₂E
  have hk : ∀ k : ℕ, d₂ * d ^ k ≠ 1 := fun k h1 =>
    hxd (by rw [eq_inv_of_mul_eq_one_left h1]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers _) _))
  have hk' : ∀ k : ℕ, d * d₂ ^ k ≠ 1 := by
    intro k h1
    have hdz : d ∈ Subgroup.zpowers d₂ := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    have hle : Subgroup.zpowers d ≤ Subgroup.zpowers d₂ := Subgroup.zpowers_le.mpr hdz
    have heq : Subgroup.zpowers d = Subgroup.zpowers d₂ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hdord, orderOf_eq_prime hd₂5 hd₂1]
    exact hxd (heq ▸ Subgroup.mem_zpowers d₂)
  have hL : Lines d d₂ :=
    ⟨hV, hd5, hd₂5, hcomm, hrk4, hrk₂,
      centralizes_of_rank_four hV hd5 hd₂5 hcomm hk hrk4 hrk₂,
      centralizes_of_rank_four hV hd₂5 hd5 hcomm.symm hk' hrk₂ hrk4⟩
  exact ⟨d, d₂, hdE, hd₂E, hL, fun e he => hL.inE_of_card hdE hd₂E C.card_E_F4 he⟩

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
