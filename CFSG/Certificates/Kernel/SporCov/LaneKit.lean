module

public import Certificates.Data.Kernel.SporCov.LaneKit
public import CFSG.Certificates.Kernel.SporCov.Words
public import CFSG.Certificates.Kernel.J4Hub.RegSound

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub

theorem forceR_eq (x : ℕ) (k : ℕ → Bool) : forceR x k = k x := by
  cases x <;> rfl

private theorem strictN_eqR (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

variable {G : Type} [Group G]

@[expose] def f4 (a b : G) (c : ℕ) : G :=
  if c = 0 then a else if c = 1 then a⁻¹ else if c = 2 then b else b⁻¹

@[expose] noncomputable def fLn (a b : G) (Ws : List (List ℕ)) (c : ℕ) : G :=
  if c < 4 then f4 a b c else wE (f4 a b) (nthW Ws (c - 4))

section Kit

variable {p w S d T L H CM RM ONE LV HV nb : ℕ}
  (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
  {ρ : G →* Matrix (Fin d) (Fin d) (ZMod p)}
include hc hnb

theorem mwLn_sound {lt : ℕ → ℕ} {f : ℕ → G}
    (hl : ∀ c, validM p nb L H (lt c) = true ∧ ordMat p d w S (lt c) = ρ (f c)) :
    ∀ (u : List ℕ) (acc : ℕ), validM p nb L H acc = true →
      validM p nb L H (mwLn (mulR p w S d T L H CM RM) lt u acc) = true ∧
        ordMat p d w S (mwLn (mulR p w S d T L H CM RM) lt u acc) =
          ρ (wE f u) * ordMat p d w S acc
  | [], acc, h => ⟨h, by rw [wE_nil, map_one, one_mul]; rfl⟩
  | c :: u, acc, h => by
    change validM p nb L H (CFSG.KC.Loop.strictN (mulR p w S d T L H CM RM (lt c) acc)
        (mwLn (mulR p w S d T L H CM RM) lt u)) = true ∧
      ordMat p d w S (CFSG.KC.Loop.strictN (mulR p w S d T L H CM RM (lt c) acc)
        (mwLn (mulR p w S d T L H CM RM) lt u)) = _
    rw [strictN_eqR]
    obtain ⟨v1, e1⟩ := mul_sound' hc hnb (hl c).1 h
    obtain ⟨v2, e2⟩ := mwLn_sound hl u _ v1
    refine ⟨v2, ?_⟩
    rw [e2, e1, (hl c).2, wE_cons, map_mul, mul_assoc]

theorem let4_sound {a b : G} {MA MAi MB MBi : ℕ}
    (hA : validM p nb L H MA = true ∧ ordMat p d w S MA = ρ a)
    (hAi : validM p nb L H MAi = true ∧ ordMat p d w S MAi = ρ a⁻¹)
    (hB : validM p nb L H MB = true ∧ ordMat p d w S MB = ρ b)
    (hBi : validM p nb L H MBi = true ∧ ordMat p d w S MBi = ρ b⁻¹) (c : ℕ) :
    validM p nb L H (let4 MA MAi MB MBi c) = true ∧
      ordMat p d w S (let4 MA MAi MB MBi c) = ρ (f4 a b c) := by
  unfold let4 f4
  rcases c with _ | _ | _ | c
  · exact hA
  · exact hAi
  · exact hB
  · have e0 : Nat.beq (c + 3) 0 = false := rfl
    have e1 : Nat.beq (c + 3) 1 = false := rfl
    have e2 : Nat.beq (c + 3) 2 = false := rfl
    rw [e0, e1, e2]
    simpa using hBi

theorem regR_sound {a b : G} {MA MAi MB MBi : ℕ}
    (hl : ∀ c, validM p nb L H (let4 MA MAi MB MBi c) = true ∧
      ordMat p d w S (let4 MA MAi MB MBi c) = ρ (f4 a b c)) :
    ∀ (Ws : List (List ℕ)) (k : List ℕ → Bool),
      regR (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws k = true →
      ∃ Rg, k Rg = true ∧ ∀ i, validM p nb L H (nthR ONE Rg i) = true ∧
        ordMat p d w S (nthR ONE Rg i) = ρ (wE (f4 a b) (nthW Ws i))
  | [], k, h => by
    refine ⟨[], h, fun i => ?_⟩
    obtain ⟨v1, e1⟩ := one_sound' hc hnb
    refine ⟨v1, ?_⟩
    change ordMat p d w S ONE = ρ (wE (f4 a b) [])
    rw [e1, wE_nil, map_one]
  | w' :: Ws, k, h => by
    change forceR (mwLn (mulR p w S d T L H CM RM) (let4 MA MAi MB MBi) w' ONE)
      (fun x => regR (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws fun xs => k (x :: xs)) =
        true at h
    rw [forceR_eq] at h
    obtain ⟨Rg, hk, hR⟩ := regR_sound hl Ws _ h
    refine ⟨_ :: Rg, hk, fun i => ?_⟩
    rcases i with _ | i
    · obtain ⟨v1, e1⟩ := one_sound' hc hnb
      obtain ⟨v2, e2⟩ := mwLn_sound hc hnb hl w' ONE v1
      refine ⟨v2, ?_⟩
      change ordMat p d w S (mwLn (mulR p w S d T L H CM RM) (let4 MA MAi MB MBi) w' ONE) =
        ρ (wE (f4 a b) w')
      rw [e2, e1, mul_one]
    · exact hR i

private theorem inv_of_mul {a : G} {X Y : ℕ}
    (hX : ordMat p d w S X = ρ a) (hXY : ordMat p d w S X * ordMat p d w S Y = 1) :
    ordMat p d w S Y = ρ a⁻¹ := by
  calc ordMat p d w S Y = ρ (a⁻¹ * a) * ordMat p d w S Y := by rw [inv_mul_cancel, map_one, one_mul]
    _ = ρ a⁻¹ * (ordMat p d w S X * ordMat p d w S Y) := by rw [map_mul, hX, mul_assoc]
    _ = ρ a⁻¹ := by rw [hXY, mul_one]

theorem kitLn_sound {a b : G} {MA MAi MB MBi : ℕ} (vA : validM p nb L H MA = true)
    (vAi : validM p nb L H MAi = true) (vB : validM p nb L H MB = true)
    (vBi : validM p nb L H MBi = true) (hA : ordMat p d w S MA = ρ a)
    (hB : ordMat p d w S MB = ρ b) {Ws : List (List ℕ)} {k : (List ℕ → ℕ) → Bool}
    (h : kitLn (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws k = true) :
    ∃ mw : List ℕ → ℕ, k mw = true ∧ ∀ u, validM p nb L H (mw u) = true ∧
      ordMat p d w S (mw u) = ρ (wE (fLn a b Ws) u) := by
  unfold kitLn at h
  rw [forceR_eq, forceR_eq, forceR_eq, forceR_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨vO, eO⟩ := one_sound' hc hnb
  have i1 : ordMat p d w S MA * ordMat p d w S MAi = 1 := by
    rw [← (mul_sound' hc hnb vA vAi).2, Nat.eq_of_beq_eq_true h1, eO]
  have i2 : ordMat p d w S MB * ordMat p d w S MBi = 1 := by
    rw [← (mul_sound' hc hnb vB vBi).2, Nat.eq_of_beq_eq_true h2, eO]
  have hl := let4_sound hc hnb ⟨vA, hA⟩ ⟨vAi, inv_of_mul hc hnb hA i1⟩ ⟨vB, hB⟩
    ⟨vBi, inv_of_mul hc hnb hB i2⟩
  obtain ⟨Rg, hk, hR⟩ := regR_sound hc hnb hl Ws _ h3
  refine ⟨_, hk, fun u => ?_⟩
  have hlt : ∀ c, validM p nb L H (letLn MA MAi MB MBi ONE Rg c) = true ∧
      ordMat p d w S (letLn MA MAi MB MBi ONE Rg c) = ρ (fLn a b Ws c) := by
    intro c
    unfold letLn fLn
    by_cases h4 : c < 4
    · have e : Nat.blt c 4 = true := Nat.ble_eq_true_of_le h4
      rw [e, if_pos h4]
      exact hl c
    · have e : Nat.blt c 4 = false := Bool.eq_false_iff.2 fun e => h4 (Nat.le_of_ble_eq_true e)
      rw [e, if_neg h4]
      exact hR (c - 4)
  obtain ⟨v, e⟩ := mwLn_sound hc hnb hlt u ONE vO
  exact ⟨v, by rw [e, eO, mul_one]⟩

theorem eqM_model (hρ : Function.Injective ρ) {f : ℕ → G} {mw : List ℕ → ℕ}
    (hmw : ∀ u, validM p nb L H (mw u) = true ∧ ordMat p d w S (mw u) = ρ (wE f u)) :
    Model letT (eqM mw) (wE f) ∧ ∀ u, chW letT u = true → wE f u = 1 → eqM mw u [] = true := by
  refine ⟨Model.of_wE _ fun u v _ _ h => hρ ?_, fun u _ h => ?_⟩
  · rw [← (hmw u).2, ← (hmw v).2, Nat.eq_of_beq_eq_true h]
  · have e : ordMat p d w S (mw u) = ordMat p d w S (mw []) := by
      rw [(hmw u).2, (hmw []).2, h, wE_nil]
    unfold eqM
    rw [ordMat_inj' hc hnb (hmw u).1 (hmw []).1 e]
    exact Nat.beq_refl _

end Kit

theorem trR_succ (w S n X : ℕ) :
    trR w S (n + 1) X = trR w S n X + X / 2 ^ (S * n + w * n) % 2 ^ w := by
  change Nat.add (trR w S n X) (Nat.land (Nat.shiftRight X (Nat.add (Nat.mul S n) (Nat.mul w n)))
    (Nat.sub (Nat.shiftLeft 1 w) 1)) = _
  have e1 : Nat.shiftLeft 1 w = 2 ^ w := by
    change 1 <<< w = 2 ^ w
    rw [Nat.shiftLeft_eq, one_mul]
  rw [e1, Nat.add_eq]
  congr 1
  change (X >>> (S * n + w * n)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem trR_eq_sum (w S X : ℕ) :
    ∀ n, trR w S n X = ∑ i ∈ Finset.range n, X / 2 ^ (S * i + w * i) % 2 ^ w
  | 0 => rfl
  | n + 1 => by rw [trR_succ, trR_eq_sum w S X n, Finset.sum_range_succ]

theorem trR_eq (p d w S X : ℕ) :
    ((trR w S d X : ℕ) : ZMod p) = Matrix.trace (ordMat p d w S X) := by
  rw [trR_eq_sum, Matrix.trace, Nat.cast_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ((X / 2 ^ (S * i + w * i) % 2 ^ w : ℕ) : ZMod p)) d]
  rfl

theorem trace_conj {K : Type} [Group K] {p d : ℕ} (ρ : K →* Matrix (Fin d) (Fin d) (ZMod p))
    {x y : K} (h : IsConj x y) : Matrix.trace (ρ x) = Matrix.trace (ρ y) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc, map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel,
    map_one, one_mul]

end CFSG.KD.SporCov

end
