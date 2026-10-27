module

public import Certificates.Data.Kernel.ThLet.Defs
public import CFSG.Certificates.Kernel.ThCent.PinSound

public section

namespace CFSG.KC.ThLet

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.SectionRank.Native

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem thLet_andB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem runK_eq (c rm ONE : ℕ) : ∀ (prog : List Op) (R : ℕ → ℕ) (k : (ℕ → ℕ) → Bool),
    runK c rm ONE prog R k = k (runPk c rm ONE prog R)
  | [], _, _ => rfl
  | op :: prog, R, k => by
    cases op with
    | mul i j t =>
      change strictF (mulB c rm (R i) (R j)) (fun v => runK c rm ONE prog (updN R t v) k) =
        k (strictF (mulB c rm (R i) (R j)) fun v => runPk c rm ONE prog (updN R t v))
      rw [strictF_eq, strictF_eq, runK_eq]
    | pow e i t =>
      change strictF (powB c rm ONE (R i) e 6) (fun v => runK c rm ONE prog (updN R t v) k) =
        k (strictF (powB c rm ONE (R i) e 6) fun v => runPk c rm ONE prog (updN R t v))
      rw [strictF_eq, strictF_eq, runK_eq]

theorem relsOK_spec {c rm ONE : ℕ} {E Ei : ℕ → ℕ} :
    ∀ {ws : List (List (Fin 6 × Bool))}, relsOK c rm ONE E Ei ws = true →
      ∀ r ∈ ws, relFrom c rm E Ei r ONE = ONE
  | [], _, _, hr => absurd hr List.not_mem_nil
  | w :: ws, h, r, hr => by
    obtain ⟨h1, h2⟩ := thLet_andB.1 h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact Nat.eq_of_beq_eq_true h1
    · exact relsOK_spec h2 r hr

theorem pairsOK_spec {c rm ONE S : ℕ} {E Ei : ℕ → ℕ} :
    ∀ {n : ℕ}, pairsOK c rm ONE S E Ei n = true → ∀ k < n,
      mulB c rm (E k) (Ei k) = ONE ∧ mulB c rm S (E k) = mulB c rm (E k) S
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := thLet_andB.1 h
    obtain ⟨h3, h4⟩ := thLet_andB.1 h1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact pairsOK_spec h2 k hk
    · exact ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

@[expose] def targetGe (m : ℕ) : Op → Bool
  | .mul _ _ k => Nat.ble m k
  | .pow _ _ k => Nat.ble m k

theorem foldl_opG_apply_of_lt {G : Type*} [Group G] (p : List Op) (m : ℕ) (R : ℕ → G)
    (h : p.all (targetGe m) = true) {r : ℕ} (hr : r < m) : p.foldl opG R r = R r := by
  induction p generalizing R with
  | nil => rfl
  | cons op p ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.foldl_cons, ih _ h.2]
    have hop := h.1
    cases op with
    | mul i j k =>
      have : m ≤ k := Nat.le_of_ble_eq_true hop
      exact Function.update_of_ne (by omega) _ _
    | pow e i k =>
      have : m ≤ k := Nat.le_of_ble_eq_true hop
      exact Function.update_of_ne (by omega) _ _

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem pkMat_relFrom (g : Fin 6 → J) {E Ei : ℕ → ℕ} (hE : ∀ i : Fin 6, pkMat (E i.val) = 𝕄 (g i))
    (hEi : ∀ i : Fin 6, pkMat (Ei i.val) = 𝕄 (g i)⁻¹) :
    ∀ (r : List (Fin 6 × Bool)) (acc : ℕ) (x : J), pkMat acc = 𝕄 x →
      pkMat (relFrom c rm E Ei r acc) = 𝕄 (x * (r.map fun y => cond y.2 (g y.1) (g y.1)⁻¹).prod)
  | [], acc, x, hx => by
    rw [List.map_nil, List.prod_nil, mul_one]
    exact hx
  | y :: r, acc, x, hx => by
    change pkMat (strictF (mulB c rm acc (letK E Ei y)) (relFrom c rm E Ei r)) = _
    have hy : pkMat (letK E Ei y) = 𝕄 (cond y.2 (g y.1) (g y.1)⁻¹) := by
      obtain ⟨i, s⟩ := y
      cases s
      · exact hEi i
      · exact hE i
    rw [strictF_eq, pkMat_relFrom g hE hEi r _ (x * cond y.2 (g y.1) (g y.1)⁻¹)
      (by rw [pkMat_mulB hk, hx, hy, mat_mul]), List.map_cons, List.prod_cons, mul_assoc]

end CFSG.KC.ThLet

end
