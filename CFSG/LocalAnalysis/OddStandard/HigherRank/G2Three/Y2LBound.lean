module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LLow
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup

variable {G : Type} [Group G]

@[expose] def y2l_lin {N : ℕ} (a0 a1 a2 x : Fin 3 → ZMod N) : Fin 3 → ZMod N :=
  x 0 • a0 + x 1 • a1 + x 2 • a2

@[expose] def y2l_actR (N : ℕ) : (Fin 3 → ZMod N) → Fin 3 → ZMod N :=
  y2l_lin ![0, 0, -1] ![0, -1, 0] ![-1, 0, 0]

@[expose] def y2l_actS (N : ℕ) : (Fin 3 → ZMod N) → Fin 3 → ZMod N :=
  y2l_lin ![0, 1, 0] ![0, 0, 1] ![1, -1, 1]

@[expose] def y2l_act8 (N : ℕ) (k : Fin 8) : (Fin 3 → ZMod N) → Fin 3 → ZMod N :=
  (y2l_actR N)^[k.val % 2] ∘ (y2l_actS N)^[k.val / 2]

theorem y2l_act8_dist2 : ∀ i j : Fin 8, y2l_act8 2 i ![1, 0, 0] = y2l_act8 2 j ![1, 0, 0] →
    y2l_act8 2 i ![0, 1, 0] = y2l_act8 2 j ![0, 1, 0] → i = j := by
  decide

theorem y2l_act8_dist4 : ∀ i j : Fin 8, y2l_act8 4 i ![1, 0, 0] = y2l_act8 4 j ![1, 0, 0] →
    y2l_act8 4 i ![0, 1, 0] = y2l_act8 4 j ![0, 1, 0] → i = j := by
  decide

section Psi

variable {N : ℕ} [NeZero N] {u v w : G} (hu : u ^ N = 1) (hv : v ^ N = 1) (hw : w ^ N = 1)
  (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w)
include hu hv hw huv huw hvw

theorem y2l_psi_nsmul (a : Fin 3 → ZMod N) (k : ℕ) :
    y2l_psi N u v w (k • a) = y2l_psi N u v w a ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, y2l_psi_zero]
  | succ k ih => rw [succ_nsmul, y2l_psi_add hu hv hw huv huw hvw, ih, pow_succ]

theorem y2l_psi_smul (c : ZMod N) (a : Fin 3 → ZMod N) :
    y2l_psi N u v w (c • a) = y2l_psi N u v w a ^ c.val := by
  rw [← y2l_psi_nsmul hu hv hw huv huw hvw, ← Nat.cast_smul_eq_nsmul (ZMod N),
    ZMod.natCast_zmod_val]

theorem y2l_psi_neg (a : Fin 3 → ZMod N) : y2l_psi N u v w (-a) = (y2l_psi N u v w a)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← y2l_psi_add hu hv hw huv huw hvw, add_neg_cancel, y2l_psi_zero]

theorem y2l_psi_conj (g : G) {a0 a1 a2 : Fin 3 → ZMod N}
    (h0 : g⁻¹ * u * g = y2l_psi N u v w a0) (h1 : g⁻¹ * v * g = y2l_psi N u v w a1)
    (h2 : g⁻¹ * w * g = y2l_psi N u v w a2) (x : Fin 3 → ZMod N) :
    g⁻¹ * y2l_psi N u v w x * g = y2l_psi N u v w (y2l_lin a0 a1 a2 x) := by
  have hc : ∀ y : G, g⁻¹ * y * g = MulAut.conj g⁻¹ y := fun y => by
    rw [MulAut.conj_apply, inv_inv]
  rw [y2l_lin, y2l_psi_add hu hv hw huv huw hvw, y2l_psi_add hu hv hw huv huw hvw,
    y2l_psi_smul hu hv hw huv huw hvw, y2l_psi_smul hu hv hw huv huw hvw,
    y2l_psi_smul hu hv hw huv huw hvw, ← h0, ← h1, ← h2, hc, hc u, hc v, hc w]
  simp only [y2l_psi, map_mul, map_pow]

theorem y2l_psi_injective (hN : ∀ z : ZMod N, z + z + (z + z) = 0)
    (h7 : ∀ d : Fin 3 → ZMod N, d ≠ 0 → d + d = 0 → y2l_psi N u v w d ≠ 1) :
    Function.Injective (y2l_psi N u v w) := by
  have hker : ∀ d, y2l_psi N u v w d = 1 → d = 0 := by
    intro d hd
    by_contra hne
    by_cases h2 : d + d = 0
    · exact h7 d hne h2 hd
    · refine h7 (d + d) h2 (funext fun i => hN (d i)) ?_
      rw [y2l_psi_add hu hv hw huv huw hvw, hd, one_mul]
  intro a b hab
  have h := hker (a - b) (by
    rw [sub_eq_add_neg, y2l_psi_add hu hv hw huv huw hvw, y2l_psi_neg hu hv hw huv huw hvw, hab,
      mul_inv_cancel])
  exact sub_eq_zero.mp h

end Psi

theorem y2l_conj_pow {A : Type} {ψ : A → G} {f : A → A} {g : G}
    (h : ∀ x, g⁻¹ * ψ x * g = ψ (f x)) (i : ℕ) (x : A) :
    (g ^ i)⁻¹ * ψ x * g ^ i = ψ (f^[i] x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [pow_succ, Function.iterate_succ_apply', ← h, ← ih]; group

theorem y2l_conj_mul {A : Type} {ψ : A → G} {f₁ f₂ : A → A} {g h : G}
    (h1 : ∀ x, g⁻¹ * ψ x * g = ψ (f₁ x)) (h2 : ∀ x, h⁻¹ * ψ x * h = ψ (f₂ x)) (x : A) :
    (g * h)⁻¹ * ψ x * (g * h) = ψ (f₂ (f₁ x)) := by
  rw [← h2, ← h1]; group

theorem y2l_psi_vec {N : ℕ} (u v w : G) (a b c : ZMod N) :
    y2l_psi N u v w ![a, b, c] = u ^ a.val * v ^ b.val * w ^ c.val := rfl

theorem y2l_card_ge {N : ℕ} [NeZero N] (hN1 : 1 < N) (hN : ∀ z : ZMod N, z + z + (z + z) = 0)
    (hdist : ∀ i j : Fin 8, y2l_act8 N i ![1, 0, 0] = y2l_act8 N j ![1, 0, 0] →
      y2l_act8 N i ![0, 1, 0] = y2l_act8 N j ![0, 1, 0] → i = j)
    {u v w r s : G} (hu : u ^ N = 1) (hv : v ^ N = 1) (hw : w ^ N = 1)
    (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w)
    (cru : r⁻¹ * u * r = w⁻¹) (crv : r⁻¹ * v * r = v⁻¹) (crw : r⁻¹ * w * r = u⁻¹)
    (csu : s⁻¹ * u * s = v) (csv : s⁻¹ * v * s = w) (csw : s⁻¹ * w * s = u * v⁻¹ * w)
    (h7 : ∀ d : Fin 3 → ZMod N, d ≠ 0 → d + d = 0 → y2l_psi N u v w d ≠ 1)
    [Finite (closure ({u, v, w, r, s} : Set G))] :
    8 * N ^ 3 ≤ Nat.card (closure ({u, v, w, r, s} : Set G)) := by
  haveI : Fact (1 < N) := ⟨hN1⟩
  set H := closure ({u, v, w, r, s} : Set G)
  have hmem : ∀ y ∈ ({u, v, w, r, s} : Set G), y ∈ H := fun y hy => subset_closure hy
  have huH := hmem u (by simp)
  have hvH := hmem v (by simp)
  have hwH := hmem w (by simp)
  have hrH := hmem r (by simp)
  have hsH := hmem s (by simp)
  have hneg : ∀ g : G, g ^ N = 1 → g ^ (-1 : ZMod N).val = g⁻¹ := fun g hg => by
    rw [y2l_pow_val_neg hg, ZMod.val_one, pow_one]
  have hR : ∀ x, r⁻¹ * y2l_psi N u v w x * r = y2l_psi N u v w (y2l_actR N x) :=
    y2l_psi_conj hu hv hw huv huw hvw r
      (by rw [cru, y2l_psi_vec, ZMod.val_zero, hneg w hw]; simp)
      (by rw [crv, y2l_psi_vec, ZMod.val_zero, hneg v hv]; simp)
      (by rw [crw, y2l_psi_vec, ZMod.val_zero, hneg u hu]; simp)
  have hS : ∀ x, s⁻¹ * y2l_psi N u v w x * s = y2l_psi N u v w (y2l_actS N x) :=
    y2l_psi_conj hu hv hw huv huw hvw s
      (by rw [csu, y2l_psi_vec, ZMod.val_zero, ZMod.val_one]; simp)
      (by rw [csv, y2l_psi_vec, ZMod.val_zero, ZMod.val_one]; simp)
      (by rw [csw, y2l_psi_vec, ZMod.val_one, hneg v hv, pow_one, pow_one])
  have h := y2l_card_ge_of_act (y2l_psi N u v w) (y2l_psi_add hu hv hw huv huw hvw)
    (y2l_psi_injective hu hv hw huv huw hvw hN h7) H
    (fun a => H.mul_mem (H.mul_mem (H.pow_mem huH _) (H.pow_mem hvH _)) (H.pow_mem hwH _))
    (fun k : Fin 8 => s ^ (k.val / 2) * r ^ (k.val % 2))
    (fun k => H.mul_mem (H.pow_mem hsH _) (H.pow_mem hrH _)) (y2l_act8 N)
    (fun k x => y2l_conj_mul (y2l_conj_pow hS _) (y2l_conj_pow hR _) x)
    (fun i j hij => hdist i j (hij _) (hij _))
  rwa [Nat.card_eq_fintype_card (α := Fin 3 → ZMod N), Fintype.card_fun, ZMod.card,
    Fintype.card_fin] at h

end CFSG.OddStandard.HigherRank.G2Three.Sec2
