module

public import Certificates.Data.Kernel.E27Spor.SlpRec
public import CFSG.Certificates.Kernel.E27Spor.OrbRec

public section

namespace CFSG.KS.E27Spor

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS.E27Lie
open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27.OrbitF3

theorem mkL_length (f : ℕ → List ℕ) : ∀ n s, (mkL f n s).length = n
  | 0, _ => rfl
  | n + 1, s => by
    change (f s :: mkL f n (s + 1)).length = n + 1
    rw [List.length_cons, mkL_length f n (s + 1)]

theorem mkL_getD (f : ℕ → List ℕ) : ∀ n s r, r < n → (mkL f n s).getD r [] = f (s + r)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => rfl
  | n + 1, s, r + 1, h => by
    change (f s :: mkL f n (s + 1)).getD (r + 1) [] = f (s + (r + 1))
    rw [List.getD_cons_succ, mkL_getD f n (s + 1) r (by omega), Nat.add_assoc, Nat.add_comm 1 r]

theorem rowsR_length (d : ℕ) (R : ℕ → ℕ) (k : ℕ) : (rowsR d R k).length = d :=
  mkL_length _ d 0

theorem rowsR_getD {d : ℕ} (R : ℕ → ℕ) (k : ℕ) {r : ℕ} (hr : r < d) :
    (rowsR d R k).getD r [] = decD d (R (d * k + r)) := by
  rw [rowsR, mkL_getD _ d 0 r hr, Nat.zero_add]
  rfl

theorem nthM_eq : ∀ (L : List (List (List ℕ))) (k : ℕ), nthM L k = L.getD k []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => by
    rw [List.getD_cons_succ, ← nthM_eq L k]
    rfl

theorem nthR_eq : ∀ (L : List (List ℕ)) (r : ℕ), nthR L r = L.getD r []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, r + 1 => by
    rw [List.getD_cons_succ, ← nthR_eq L r]
    rfl

theorem ext_getD {l₁ l₂ : List (List ℕ)} (hl : l₁.length = l₂.length)
    (h : ∀ r < l₁.length, l₁.getD r [] = l₂.getD r []) : l₁ = l₂ :=
  List.ext_getElem hl fun r h1 h2 => by
    have := h r h1
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem lmulD_getD {d : ℕ} (X Y : List (List ℕ)) {r : ℕ} (hr : r < X.length) :
    (lmulD d X Y).getD r [] = lvecMul 3 d (X.getD r []) Y := by
  rw [lmulD, List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map,
    List.getD_eq_getElem _ _ hr]

variable {d : ℕ} {K : Subgroup (GL (Fin d) (ZMod 3))}

theorem slp_mem {base : List (List (List ℕ))} {nb : ℕ}
    (hbase : ∀ k < nb, (nthM base k).length = d ∧ (∀ r < d, ValidD d (nthR (nthM base k) r)) ∧
      ∃ g ∈ K, (g : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d (nthM base k))
    {R A B : ℕ → ℕ} {n : ℕ} (h : ∀ k < n, slpAt d base nb R A B k = true) :
    ∀ k < n, ∃ g ∈ K, (g : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d (rowsR d R k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hc := h k hk
    unfold slpAt at hc
    rw [bRec_eq] at hc
    split_ifs at hc with h1
    ·
      obtain ⟨hlen, hval, g, hg, e⟩ := hbase k (blt_of h1)
      refine ⟨g, hg, ?_⟩
      rw [e]
      congr 1
      refine (ext_getD (by rw [rowsR_length, hlen]) fun r hr => ?_).symm
      have hr' : r < d := by rwa [rowsR_length] at hr
      have e := beq_of (allN_spec hc r hr')
      change R (d * k + r) = lcode (nthR (nthM base k) r) at e
      rw [rowsR_getD R k hr', e, decD_lcode (hval r hr'), nthR_eq]
    ·
      rw [bRec_eq] at hc
      split_ifs at hc with h2
      rw [bRec_eq] at hc
      split_ifs at hc with h3
      have hA := blt_of h2
      have hB := blt_of h3
      obtain ⟨ga, hga, ea⟩ := ih (A k) hA (by omega)
      obtain ⟨gb, hgb, eb⟩ := ih (B k) hB (by omega)
      have hrows : rowsR d R k = lmulD d (rowsR d R (A k)) (rowsR d R (B k)) := by
        refine ext_getD (by rw [lmulD_length, rowsR_length, rowsR_length]) fun r hr => ?_
        have hr' : r < d := by rwa [rowsR_length] at hr
        have e := beq_of (allN_spec hc r hr')
        change R (d * k + r) =
          lcode (lvecMul 3 d (decD d (R (d * A k + r))) (rowsR d R (B k))) at e
        rw [rowsR_getD R k hr', lmulD_getD _ _ (by rwa [rowsR_length]), rowsR_getD R (A k) hr',
          e, decD_lcode (validD_lvecMul _ _)]
      refine ⟨ga * gb, mul_mem hga hgb, ?_⟩
      rw [hrows, rowsMat_lmulD (rowsR_length d R (A k)), Units.val_mul, ea, eb]

end CFSG.KS.E27Spor

end
