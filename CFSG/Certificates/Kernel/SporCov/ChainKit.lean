module

public import Certificates.Data.Kernel.SporCov.ChainKit
public import CFSG.Certificates.Kernel.SporCov.LaneKit

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub

variable {G : Type} [Group G]

@[expose] def letG (a b : G) (E : List G) (c : ℕ) : G :=
  if c < 4 then f4 a b c else E.getD (c - 4) 1

@[expose] def regsG (a b : G) : List (List ℕ) → List G → List G
  | [], E => E
  | w :: Ws, E => regsG a b Ws (E ++ [wE (letG a b E) w])

@[expose] def fC (a b : G) (Ws : List (List ℕ)) : ℕ → G := letG a b (regsG a b Ws [])

theorem regsG_nil (a b : G) (E : List G) : regsG a b [] E = E := rfl

theorem regsG_cons (a b : G) (w : List ℕ) (Ws : List (List ℕ)) (E : List G) :
    regsG a b (w :: Ws) E = regsG a b Ws (E ++ [wE (letG a b E) w]) := rfl

theorem nthR_eq (d : ℕ) : ∀ (l : List ℕ) (i : ℕ), nthR d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nthR_eq d l i

theorem snocR_eq (x : ℕ) : ∀ Rg : List ℕ, snocR Rg x = Rg ++ [x]
  | [] => rfl
  | a :: Rg => congrArg (List.cons a) (snocR_eq x Rg)

theorem getD_snoc {α : Type*} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - l.length = k + 1 := ⟨i - l.length - 1, by omega⟩
    rw [hk]
    rfl

def RegInv (p d w S nb L H ONE : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) (ZMod p)) (Rg : List ℕ)
    (E : List G) : Prop :=
  Rg.length = E.length ∧ ∀ i, validM p nb L H (nthR ONE Rg i) = true ∧
    ordMat p d w S (nthR ONE Rg i) = ρ (E.getD i 1)

section Kit

variable {p w S d T L H CM RM ONE LV HV nb : ℕ}
  (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
  {ρ : G →* Matrix (Fin d) (Fin d) (ZMod p)}
include hc hnb

theorem letLn_soundC {a b : G} {MA MAi MB MBi : ℕ}
    (hl : ∀ c, validM p nb L H (let4 MA MAi MB MBi c) = true ∧
      ordMat p d w S (let4 MA MAi MB MBi c) = ρ (f4 a b c))
    {Rg : List ℕ} {E : List G}
    (hR : ∀ i, validM p nb L H (nthR ONE Rg i) = true ∧
      ordMat p d w S (nthR ONE Rg i) = ρ (E.getD i 1)) (c : ℕ) :
    validM p nb L H (letLn MA MAi MB MBi ONE Rg c) = true ∧
      ordMat p d w S (letLn MA MAi MB MBi ONE Rg c) = ρ (letG a b E c) := by
  unfold letLn letG
  by_cases h4 : c < 4
  · have e : Nat.blt c 4 = true := Nat.ble_eq_true_of_le h4
    rw [e, if_pos h4]
    exact hl c
  · have e : Nat.blt c 4 = false := Bool.eq_false_iff.2 fun e => h4 (Nat.le_of_ble_eq_true e)
    rw [e, if_neg h4]
    exact hR (c - 4)

theorem regC_sound {a b : G} {MA MAi MB MBi : ℕ}
    (hl : ∀ c, validM p nb L H (let4 MA MAi MB MBi c) = true ∧
      ordMat p d w S (let4 MA MAi MB MBi c) = ρ (f4 a b c)) :
    ∀ (Ws : List (List ℕ)) (Rg : List ℕ) (E : List G) (k : List ℕ → Bool),
      RegInv p d w S nb L H ONE ρ Rg E →
      regC (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws Rg k = true →
      ∃ Rg', k Rg' = true ∧ RegInv p d w S nb L H ONE ρ Rg' (regsG a b Ws E)
  | [], Rg, E, k, hI, h => ⟨Rg, h, hI⟩
  | w' :: Ws, Rg, E, k, hI, h => by
    change forceR (mwLn (mulR p w S d T L H CM RM) (letLn MA MAi MB MBi ONE Rg) w' ONE)
      (fun x => regC (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws (snocR Rg x) k) = true at h
    rw [forceR_eq] at h
    obtain ⟨vO, eO⟩ := one_sound' hc hnb
    obtain ⟨vx, ex⟩ := mwLn_sound hc hnb (letLn_soundC hc hnb hl hI.2) w' ONE vO
    rw [eO, mul_one] at ex
    refine regC_sound hl Ws _ _ k ⟨?_, fun i => ?_⟩ h
    · rw [snocR_eq, List.length_append, List.length_append, hI.1]
      rfl
    · rw [nthR_eq, snocR_eq, getD_snoc, getD_snoc, hI.1]
      split_ifs with h1 h2
      · rw [← nthR_eq]
        exact hI.2 i
      · exact ⟨vx, ex⟩
      · exact ⟨vO, by rw [eO, map_one]⟩

omit hc hnb in
private theorem inv_of_mulC {a : G} {X Y : ℕ}
    (hX : ordMat p d w S X = ρ a) (hXY : ordMat p d w S X * ordMat p d w S Y = 1) :
    ordMat p d w S Y = ρ a⁻¹ := by
  calc ordMat p d w S Y = ρ (a⁻¹ * a) * ordMat p d w S Y := by rw [inv_mul_cancel, map_one, one_mul]
    _ = ρ a⁻¹ * (ordMat p d w S X * ordMat p d w S Y) := by rw [map_mul, hX, mul_assoc]
    _ = ρ a⁻¹ := by rw [hXY, mul_one]

theorem kitC_sound {a b : G} {MA MAi MB MBi : ℕ} (vA : validM p nb L H MA = true)
    (vAi : validM p nb L H MAi = true) (vB : validM p nb L H MB = true)
    (vBi : validM p nb L H MBi = true) (hA : ordMat p d w S MA = ρ a)
    (hB : ordMat p d w S MB = ρ b) {Ws : List (List ℕ)} {k : (List ℕ → ℕ) → Bool}
    (h : kitC (mulR p w S d T L H CM RM) ONE MA MAi MB MBi Ws k = true) :
    ∃ mw : List ℕ → ℕ, k mw = true ∧ ∀ u, validM p nb L H (mw u) = true ∧
      ordMat p d w S (mw u) = ρ (wE (fC a b Ws) u) := by
  unfold kitC at h
  rw [forceR_eq, forceR_eq, forceR_eq, forceR_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨vO, eO⟩ := one_sound' hc hnb
  have i1 : ordMat p d w S MA * ordMat p d w S MAi = 1 := by
    rw [← (mul_sound' hc hnb vA vAi).2, Nat.eq_of_beq_eq_true h1, eO]
  have i2 : ordMat p d w S MB * ordMat p d w S MBi = 1 := by
    rw [← (mul_sound' hc hnb vB vBi).2, Nat.eq_of_beq_eq_true h2, eO]
  have hl := let4_sound hc hnb ⟨vA, hA⟩ ⟨vAi, inv_of_mulC hA i1⟩ ⟨vB, hB⟩ ⟨vBi, inv_of_mulC hB i2⟩
  have hI0 : RegInv p d w S nb L H ONE ρ [] ([] : List G) :=
    ⟨rfl, fun i => ⟨vO, by
      change ordMat p d w S ONE = ρ 1
      rw [eO, map_one]⟩⟩
  obtain ⟨Rg, hk, hR⟩ := regC_sound hc hnb hl Ws [] [] _ hI0 h3
  refine ⟨_, hk, fun u => ?_⟩
  obtain ⟨v, e⟩ := mwLn_sound hc hnb (letLn_soundC hc hnb hl hR.2) u ONE vO
  exact ⟨v, by rw [e, eO, mul_one]; rfl⟩

end Kit

end CFSG.KD.SporCov

end
