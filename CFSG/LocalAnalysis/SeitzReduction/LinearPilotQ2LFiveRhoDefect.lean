module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoRoot
import all CFSG.Fischer.F4

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer CFSG.LieType.Steinberg.CentralExt.SLClosed
open scoped commutatorElement

section Identities

variable {G : Type*} [Group G]

theorem conj_chain_identity {a b c g A B Δ : G} (hA : g * a * g⁻¹ = a * A)
    (hb : g * b * g⁻¹ = b) (hB : g * c * g⁻¹ = c * B) (hΔ : ⁅a, b⁆ = c * Δ) :
    c⁻¹ * (a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹) * c = B * (g * Δ * g⁻¹) * Δ⁻¹ := by
  have key : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have e1 : ⁅a * A, b⁆ = (a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹) * ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : g * (c * Δ) * g⁻¹ = (g * c * g⁻¹) * (g * Δ * g⁻¹) := by group
  rw [hA, hb, hΔ, e1, hΔ, e2, hB] at key
  have hP : a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹ = c * B * (g * Δ * g⁻¹) * Δ⁻¹ * c⁻¹ := by
    rw [key]
    group
  rw [hP]
  group

theorem conj_comm_identity {a b h α β : G} (hα : h * a * h⁻¹ = a * α)
    (hβ : h * b * h⁻¹ = b * β) :
    h * ⁅a, b⁆ * h⁻¹ = ⁅a, b⁆ * ((b * (a * (b⁻¹ * α * b) * a⁻¹) * b⁻¹) *
      (b * (a * β * a⁻¹) * b⁻¹) * (b * (a * α⁻¹ * a⁻¹) * b⁻¹) * (b * β⁻¹ * b⁻¹)) := by
  have key : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [key, hα, hβ]
  simp only [commutatorElement_def]
  group

end Identities

theorem commute_commutatorElement' {G : Type*} [Group G] {k x y : G} (hx : Commute k x)
    (hy : Commute k y) : Commute k ⁅x, y⁆ := by
  rw [commutatorElement_def]
  exact ((hx.mul_right hy).mul_right hx.inv_right).mul_right hy.inv_right

namespace RhoExt

variable {E : Type*} [Group E] (X : RhoExt E)

@[expose] noncomputable def ptK (m : Fin 4) : E := X.tor (rhoDiag (rhoPtVec m))

theorem π_ptK (m : Fin 4) :
    (X.π (X.ptK m) : Matrix (Fin 4) (Fin 4) F4) = diagonal (rhoPtVec m) := by
  rw [ptK, (X.tor_spec (coe_rhoDiag (rhoPtVec_prod m))).1, coe_rhoDiag (rhoPtVec_prod m)]

theorem rootLift_commute_ptK {i j m : Fin 4} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)
    (s : F4) : Commute (X.ptK m) (X.rootLift i j s) :=
  X.rootLift_commute_tor hij (coe_rhoDiag (rhoPtVec_prod m)) (by simp [rhoPtVec, him, hjm]) s

theorem ω_ne_one : F4.ω ≠ 1 := by decide +kernel

theorem βE_eq_zero_of_commute_ptK {m : Fin 4} {w : E} (hw1 : X.π w = 1)
    (hw : Commute (X.ptK m) w) {r : Fin 4} (hr : r ≠ m) : X.βE w r = 0 :=
  X.βE_eq_zero_of_commute (X.π_ptK m) hw1 hw.eq
    (by simp only [rhoPtVec, hr, ite_false]; exact ω_ne_one)

theorem π_commutator_rootLift {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s t : F4) : X.π ⁅X.rootLift i j s, X.rootLift k l t⁆ = 1 := by
  rw [map_commutatorElement, X.π_rootLift hij, X.π_rootLift hkl,
    commutatorElement_eq_one_iff_mul_comm]
  exact tv_commute hij hkl hjk hli s t

theorem rootLift_commute_disj {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hki : k ≠ i)
    (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (s t : F4) :
    X.rootLift i j s * X.rootLift k l t = X.rootLift k l t * X.rootLift i j s := by
  have h1 : Commute (X.rootK i j) (X.rootLift i j s) := (X.rootLift_spec hij s).2
  have h2 : Commute (X.rootK i j) (X.rootLift k l t) :=
    X.rootLift_commute_tor hkl (coe_rhoDiag (rhoPairVec_prod i j hij))
      (by simp [rhoPairVec, hki, hkj, hli, hlj]) t
  have hc := X.eq_one_of_commute (X.π_rootK hij) (rhoPairVec_ne_one i j)
    (X.π_commutator_rootLift hij hkl hkj.symm hli s t) (commute_commutatorElement' h1 h2).eq
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

theorem conj_eq_mul_commutator {i j : Fin 4} (hij : i ≠ j) (s : F4) (g : E) :
    g * X.rootLift i j s * g⁻¹ = X.rootLift i j s * ⁅X.rootLift i j s, g⁆ := by
  have h1 := X.rootLift_mul_self hij s
  have h2 := X.rootLift_inv hij s
  calc g * X.rootLift i j s * g⁻¹
      = (X.rootLift i j s * X.rootLift i j s) * g * (X.rootLift i j s)⁻¹ * g⁻¹ := by
        rw [h1, h2, one_mul]
    _ = X.rootLift i j s * ⁅X.rootLift i j s, g⁆ := by
        rw [commutatorElement_def]
        group

theorem row_chain_rel {i j l m : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) (s t u : F4) :
    X.βE ⁅X.rootLift i l (s * t), X.rootLift i m u⁆ j =
        t * X.βE ⁅X.rootLift i j s, X.rootLift i m u⁆ l ∧
      u * X.βE ((X.rootLift i l (s * t))⁻¹ * ⁅X.rootLift i j s, X.rootLift j l t⁆) m =
        s * t * X.βE ⁅X.rootLift i j s, X.rootLift i m u⁆ l := by
  set a := X.rootLift i j s with ha
  set b := X.rootLift j l t with hb
  set c := X.rootLift i l (s * t) with hc
  set g := X.rootLift i m u with hg
  set A := ⁅a, g⁆ with hAdef
  set B := ⁅c, g⁆ with hBdef
  set Δ := c⁻¹ * ⁅a, b⁆ with hΔdef
  have hA1 : X.π A = 1 := X.π_commutator_rootLift hij him hij.symm him.symm s u
  have hB1 : X.π B = 1 := X.π_commutator_rootLift hil him hil.symm him.symm (s * t) u
  have hΔ1 : X.π Δ = 1 := by
    rw [hΔdef, map_mul, map_inv, map_commutatorElement, X.π_rootLift hij, X.π_rootLift hjl,
      X.π_rootLift hil, tv_chain hij hjl hil, inv_mul_cancel]
  have hAl : ∀ r, r ≠ l → X.βE A r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hA1
    (commute_commutatorElement' (X.rootLift_commute_ptK hij hil hjl s)
      (X.rootLift_commute_ptK him hil hlm.symm u)) hr
  have hBj : ∀ r, r ≠ j → X.βE B r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hB1
    (commute_commutatorElement' (X.rootLift_commute_ptK hil hij hjl.symm (s * t))
      (X.rootLift_commute_ptK him hij hjm.symm u)) hr
  have hΔm : ∀ r, r ≠ m → X.βE Δ r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hΔ1
    (((X.rootLift_commute_ptK hil him hlm (s * t)).inv_right).mul_right
      (commute_commutatorElement' (X.rootLift_commute_ptK hij him hjm s)
        (X.rootLift_commute_ptK hjl hjm hlm t))) hr
  have hgb : g * b * g⁻¹ = b := by
    rw [hg, hb, X.rootLift_commute_disj him hjl hij.symm hjm hil.symm hlm u t,
      mul_inv_cancel_right]
  have key : c⁻¹ * (a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹) * c = B * (g * Δ * g⁻¹) * Δ⁻¹ :=
    conj_chain_identity (X.conj_eq_mul_commutator hij s g) hgb
      (X.conj_eq_mul_commutator hil (s * t) g)
      (show ⁅a, b⁆ = c * Δ by rw [hΔdef, mul_inv_cancel_left])
  have hci : c⁻¹ = c := X.rootLift_inv hil (s * t)
  have hAi1 : X.π A⁻¹ = 1 := by rw [map_inv, hA1, inv_one]
  have hbA : X.π (b * A⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, hAi1, mul_one, map_inv, mul_inv_cancel]
  have hQ : X.π (A * (b * A⁻¹ * b⁻¹)) = 1 := by rw [map_mul, hA1, hbA, one_mul]
  have hP : X.π (a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹) = 1 := by
    rw [map_mul, map_mul, hQ, mul_one, map_inv, mul_inv_cancel]
  have hgΔ : X.π (g * Δ * g⁻¹) = 1 := by
    rw [map_mul, map_mul, hΔ1, mul_one, map_inv, mul_inv_cancel]
  have hΔi1 : X.π Δ⁻¹ = 1 := by rw [map_inv, hΔ1, inv_one]
  have hBg : X.π (B * (g * Δ * g⁻¹)) = 1 := by rw [map_mul, hB1, hgΔ, one_mul]
  have hL : X.βE (c⁻¹ * (a * (A * (b * A⁻¹ * b⁻¹)) * a⁻¹) * c) =
      (tv F4 i l (s * t) : Matrix (Fin 4) (Fin 4) F4) *ᵥ
        ((tv F4 i j s : Matrix (Fin 4) (Fin 4) F4) *ᵥ
          (X.βE A + (tv F4 j l t : Matrix (Fin 4) (Fin 4) F4) *ᵥ (-X.βE A))) := by
    have h1 := X.βE_conj c⁻¹ hP
    rw [inv_inv] at h1
    rw [h1, hci, X.βE_conj a hQ, X.βE_mul hA1 hbA, X.βE_conj b hAi1, X.βE_inv hA1,
      X.π_rootLift hil, X.π_rootLift hij, X.π_rootLift hjl]
  have hR : X.βE (B * (g * Δ * g⁻¹) * Δ⁻¹) =
      X.βE B + (tv F4 i m u : Matrix (Fin 4) (Fin 4) F4) *ᵥ X.βE Δ + -X.βE Δ := by
    rw [X.βE_mul hBg hΔi1, X.βE_mul hB1 hgΔ, X.βE_conj g hΔ1, X.βE_inv hΔ1, X.π_rootLift him]
  rw [key, hR] at hL
  have hj := congrFun hL j
  have hi := congrFun hL i
  simp only [Pi.add_apply, tv_mulVec hil, tv_mulVec hij, tv_mulVec hjl, tv_mulVec him,
    ite_true, hij, hij.symm, hil.symm, hjl.symm, ite_false, hAl j hjl, hAl i hil, hBj i hij,
    hΔm i him, hΔm j hjm, add_zero, zero_add, CharTwo.neg_eq] at hj hi
  refine ⟨hj, ?_⟩
  rw [hi, CharTwo.add_self_eq_zero, mul_zero, add_zero, mul_assoc]

theorem row_hall_rel {i j l m : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) :
    X.βE ⁅X.rootLift i m 1, X.rootLift i j 1⁆ l =
      X.βE ⁅X.rootLift i m 1, X.rootLift i l 1⁆ j +
        X.βE ⁅X.rootLift i j 1, X.rootLift i l 1⁆ m := by
  set a := X.rootLift i m 1 with ha
  set b := X.rootLift i j 1 with hb
  set h := X.rootLift i l 1 with hh
  set α := ⁅a, h⁆ with hαdef
  set β := ⁅b, h⁆ with hβdef
  set P := ⁅a, b⁆ with hPdef
  have hα1 : X.π α = 1 := X.π_commutator_rootLift him hil him.symm hil.symm 1 1
  have hβ1 : X.π β = 1 := X.π_commutator_rootLift hij hil hij.symm hil.symm 1 1
  have hP1 : X.π P = 1 := X.π_commutator_rootLift him hij him.symm hij.symm 1 1
  have hαj : ∀ r, r ≠ j → X.βE α r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hα1
    (commute_commutatorElement' (X.rootLift_commute_ptK him hij hjm.symm 1)
      (X.rootLift_commute_ptK hil hij hjl.symm 1)) hr
  have hβm : ∀ r, r ≠ m → X.βE β r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hβ1
    (commute_commutatorElement' (X.rootLift_commute_ptK hij him hjm 1)
      (X.rootLift_commute_ptK hil him hlm 1)) hr
  have hPl : ∀ r, r ≠ l → X.βE P r = 0 := fun r hr => X.βE_eq_zero_of_commute_ptK hP1
    (commute_commutatorElement' (X.rootLift_commute_ptK him hil hlm.symm 1)
      (X.rootLift_commute_ptK hij hil hjl 1)) hr
  have key : h * P * h⁻¹ = P * ((b * (a * (b⁻¹ * α * b) * a⁻¹) * b⁻¹) *
      (b * (a * β * a⁻¹) * b⁻¹) * (b * (a * α⁻¹ * a⁻¹) * b⁻¹) * (b * β⁻¹ * b⁻¹)) :=
    conj_comm_identity (X.conj_eq_mul_commutator him 1 h) (X.conj_eq_mul_commutator hij 1 h)
  have hbi : b⁻¹ = b := X.rootLift_inv hij 1
  have hc1 : ∀ (e : E) {x : E}, X.π x = 1 → X.π (e * x * e⁻¹) = 1 := fun e x hx => by
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have hαi : X.π α⁻¹ = 1 := by rw [map_inv, hα1, inv_one]
  have hβi : X.π β⁻¹ = 1 := by rw [map_inv, hβ1, inv_one]
  have hT1 := hc1 a (hc1 b⁻¹ hα1)
  rw [inv_inv] at hT1
  have hT1' := hc1 b hT1
  have hT2 := hc1 b (hc1 a hβ1)
  have hT3 := hc1 b (hc1 a hαi)
  have hT4 := hc1 b hβi
  have hL := X.βE_conj h hP1
  rw [key, X.βE_mul hP1 (by rw [map_mul, map_mul, map_mul, hT1', hT2, hT3, hT4, one_mul,
      one_mul, one_mul]), X.βE_mul (by rw [map_mul, map_mul, hT1', hT2, hT3, one_mul, one_mul]) hT4,
    X.βE_mul (by rw [map_mul, hT1', hT2, one_mul]) hT3, X.βE_mul hT1' hT2] at hL
  have hT1v := X.βE_conj b⁻¹ hα1
  rw [inv_inv] at hT1v
  have hin : X.π (b⁻¹ * α * b) = 1 := by
    rw [map_mul, map_mul, hα1, mul_one, map_inv, inv_mul_cancel]
  rw [X.βE_conj b hT1, X.βE_conj a hin, hT1v, X.βE_conj b (hc1 a hβ1), X.βE_conj a hβ1,
    X.βE_conj b (hc1 a hαi), X.βE_conj a hαi, X.βE_conj b hβi, X.βE_inv hα1, X.βE_inv hβ1, hbi,
    X.π_rootLift him, X.π_rootLift hij, X.π_rootLift hil] at hL
  have hi := congrFun hL i
  simp only [Pi.add_apply, tv_mulVec hil, tv_mulVec hij, tv_mulVec him, ite_true,
    hij.symm, him.symm, ite_false, hαj i hij, hαj m hjm.symm,
    hβm i him, hβm j hjm, hPl i hil, add_zero, zero_add, one_mul, CharTwo.neg_eq] at hi
  rw [CharTwo.add_self_eq_zero, zero_add] at hi
  rw [← hi, add_comm]

theorem βE_commutator_symm {p q : E} (h : X.π ⁅p, q⁆ = 1) : X.βE ⁅q, p⁆ = X.βE ⁅p, q⁆ := by
  rw [← commutatorElement_inv, X.βE_inv h, CharTwo.neg_eq]

theorem row_one_eq_zero {i j l m : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) :
    X.βE ⁅X.rootLift i m 1, X.rootLift i j 1⁆ l = 0 := by
  have h1 := X.row_hall_rel hij hil him hjl hjm hlm
  have h2 := (X.row_chain_rel hij him hil hjm hjl hlm.symm 1 1 1).1
  rw [mul_one, one_mul] at h2
  rw [h1, h2, CharTwo.add_self_eq_zero]

theorem row_eq_zero {i x y z : Fin 4} (hix : i ≠ x) (hiy : i ≠ y) (hiz : i ≠ z) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (σ υ : F4) :
    X.βE ⁅X.rootLift i x σ, X.rootLift i y υ⁆ z = 0 := by
  have h1 := (X.row_chain_rel hiz hix hiy hxz.symm hyz.symm hxy 1 σ υ).1
  have h2 := (X.row_chain_rel hix hiy hiz hxy hxz hyz 1 υ 1).1
  have h3 := X.row_one_eq_zero hiz hiy hix hyz.symm hxz.symm hxy.symm
  have hs := X.βE_commutator_symm (X.π_commutator_rootLift hiz hiy hiz.symm hiy.symm 1 υ)
  rw [one_mul] at h1 h2
  rw [h1, ← hs, h2, h3, mul_zero, mul_zero]

theorem exists_fourth (i j l : Fin 4) : ∃ m : Fin 4, m ≠ i ∧ m ≠ j ∧ m ≠ l := by
  revert i j l
  decide

theorem rootLift_commute_row {i j l : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (s t : F4) : X.rootLift i j s * X.rootLift i l t = X.rootLift i l t * X.rootLift i j s := by
  obtain ⟨m, hmi, hmj, hml⟩ := exists_fourth i j l
  have hπ := X.π_commutator_rootLift hij hil hij.symm hil.symm s t
  refine commutatorElement_eq_one_iff_mul_comm.mp (X.eq_one_of_βE hπ (funext fun r => ?_))
  by_cases hr : r = m
  · subst hr
    exact X.row_eq_zero hij hil hmi.symm hjl hmj.symm hml.symm s t
  · exact X.βE_eq_zero_of_commute_ptK hπ (commute_commutatorElement'
      (X.rootLift_commute_ptK hij hmi.symm hmj.symm s)
      (X.rootLift_commute_ptK hil hmi.symm hml.symm t)) hr

theorem rootLift_chain {i j l : Fin 4} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t : F4) :
    ⁅X.rootLift i j s, X.rootLift j l t⁆ = X.rootLift i l (s * t) := by
  obtain ⟨m, hmi, hmj, hml⟩ := exists_fourth i j l
  have hΔ1 : X.π ((X.rootLift i l (s * t))⁻¹ * ⁅X.rootLift i j s, X.rootLift j l t⁆) = 1 := by
    rw [map_mul, map_inv, map_commutatorElement, X.π_rootLift hij, X.π_rootLift hjl,
      X.π_rootLift hil, tv_chain hij hjl hil, inv_mul_cancel]
  have hc : Commute (X.ptK m)
      ((X.rootLift i l (s * t))⁻¹ * ⁅X.rootLift i j s, X.rootLift j l t⁆) :=
    ((X.rootLift_commute_ptK hil hmi.symm hml.symm (s * t)).inv_right).mul_right
      (commute_commutatorElement' (X.rootLift_commute_ptK hij hmi.symm hmj.symm s)
        (X.rootLift_commute_ptK hjl hmj.symm hml.symm t))
  have hm := (X.row_chain_rel hij hil hmi.symm hjl hmj.symm hml.symm s t 1).2
  rw [X.row_eq_zero hij hmi.symm hil hmj.symm hjl hml s 1, mul_zero, one_mul] at hm
  have hΔ := X.eq_one_of_βE hΔ1 (funext fun r => by
    by_cases hr : r = m
    · subst hr
      exact hm
    · exact X.βE_eq_zero_of_commute_ptK hΔ1 hc hr)
  exact (inv_mul_eq_one.mp hΔ).symm

theorem rootLift_commute_col {i j k : Fin 4} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (s t : F4) : X.rootLift i j s * X.rootLift k j t = X.rootLift k j t * X.rootLift i j s := by
  obtain ⟨m, hmi, hmj, hmk⟩ := exists_fourth i j k
  have hπ := X.π_commutator_rootLift hij hkj hkj.symm hij.symm s t
  have hg1 : Commute (X.rootLift i m 1) (X.rootLift i j s) :=
    X.rootLift_commute_row hmi.symm hij hmj (1 : F4) s
  have hg2 : Commute (X.rootLift i m 1) (X.rootLift k j t) :=
    X.rootLift_commute_disj hmi.symm hkj hik.symm hmk.symm hij.symm hmj.symm 1 t
  have hc := X.βE_conj (X.rootLift i m 1) hπ
  rw [(commute_commutatorElement' hg1 hg2).eq, mul_inv_cancel_right,
    X.π_rootLift hmi.symm] at hc
  have hi := congrFun hc i
  rw [tv_mulVec hmi.symm, ite_eq_left rfl, one_mul, left_eq_add] at hi
  refine commutatorElement_eq_one_iff_mul_comm.mp (X.eq_one_of_βE hπ (funext fun r => ?_))
  by_cases hr : r = m
  · subst hr
    exact hi
  · exact X.βE_eq_zero_of_commute_ptK hπ (commute_commutatorElement'
      (X.rootLift_commute_ptK hij hmi.symm hmj.symm s)
      (X.rootLift_commute_ptK hkj hmk.symm hmj.symm t)) hr

end RhoExt

end CFSG.SeitzReduction.LinearPilot
