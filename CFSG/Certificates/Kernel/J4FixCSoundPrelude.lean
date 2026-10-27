module

public import CFSG.Certificates.Kernel.J4FixCSoundBase1

public import CFSG.Sporadic.Schreier.J4SKCent

public section

namespace CFSG.KC.J4FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.KS.SporSch.C11 CFSG.KC.Enum
open CFSG.Sporadic.SmallF2.Native

section Gen

variable {X XI Y YI : Nat} (hX : bindWK 11 11 xColumns.toList X = true)
  (hXI : bindWK 11 11 xInvColumns.toList XI = true) (hY : bindWK 11 11 yColumns.toList Y = true)
  (hYI : bindWK 11 11 yInvColumns.toList YI = true)
include hX hXI hY hYI

end Gen

theorem pairRep_mul {g h : J} {p q : ℕ} (hg : PairRep g p) (hh : PairRep h q) :
    PairRep (g * h) (pmulK p q) := by
  obtain ⟨k, hk, rfl, hkC⟩ := hg
  obtain ⟨k', hk', rfl, hkD⟩ := hh
  have hlt : paK p ^^^ appK (pcK p) (paK q) < 2 ^ 11 :=
    Nat.xor_lt_two_pow (paK_lt p) (appK_lt' _ _)
  have e : k * η (paK q) = η (appK (pcK p) (paK q)) * k := by
    rw [← app_eq, ← hkC (paK q)]
    group
  refine ⟨k * k', K.mul_mem hk hk', ?_, ?_⟩
  · simp only [pmulK, sN]
    change _ = η (paK (mkP (paK p ^^^ appK (pcK p) (paK q)) _)) * _
    rw [paK_mkP hlt, η_xor]
    calc η (paK p) * k * (η (paK q) * k') = η (paK p) * (k * η (paK q)) * k' := by group
      _ = _ := by rw [e]; group
  · simp only [pmulK, sN]
    change ActsBy _ (unpack11 (pcK (mkP (paK p ^^^ appK (pcK p) (paK q)) _)))
    rw [pcK_mkP hlt, ← comp_eq]
    exact actsBy_mul hkC hkD

theorem pairRep_evalW {gs : List J} {GP GIP : List ℕ}
    (hG : ∀ i, PairRep (nth 1 gs i) (nth pidP GP i))
    (hGI : ∀ i, PairRep (nth 1 gs i)⁻¹ (nth pidP GIP i)) :
    ∀ w, PairRep (wordE gs w) (evalW GP GIP w)
  | [] => by
    change PairRep 1 pidP
    exact pairRep_one
  | c :: w => by
    rw [wordE_cons]
    change PairRep _ (pmulK (letP GP GIP c) (evalW GP GIP w))
    refine pairRep_mul ?_ (pairRep_evalW hG hGI w)
    unfold letE letP
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      have e : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
      rw [e]
      exact hG _
    · rw [if_neg h]
      have e : Nat.beq (Nat.mod c 2) 0 = false :=
        Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
      rw [e]
      exact hGI _

theorem η_inv_self (a : ℕ) : (η a)⁻¹ = η a := by
  have h : η a * η a = 1 := by rw [← η_xor, Nat.xor_self, η_zero]
  exact inv_eq_of_mul_eq_one_right h

section GenI

variable {X XI Y YI : Nat} (hX : bindWK 11 11 xColumns.toList X = true)
  (hXI : bindWK 11 11 xInvColumns.toList XI = true) (hY : bindWK 11 11 yColumns.toList Y = true)
  (hYI : bindWK 11 11 yInvColumns.toList YI = true)
include hX hXI hY hYI

theorem pairRep_genI (g : List ℕ × ℕ) (ha : g.2 < 2 ^ 11) :
    PairRep (signedWord x y (toI g.1) * η g.2)⁻¹ (genIP X XI Y YI g) := by
  refine ⟨signedWord x y (invI g.1), signedWord_mem_K _, ?_, ?_⟩
  · rw [genIP, paK_mkP ha, mul_inv_rev, η_inv_self, signedWord_invI]
  · rw [genIP, pcK_mkP ha]
    exact actsBy_word hX hXI hY hYI _

end GenI

theorem peqK_of_eq {g : J} {p q : ℕ} (hp : PairRep g p) (hq : PairRep g q) : peqK p q = true := by
  obtain ⟨k, hk, e, hkC⟩ := hp
  obtain ⟨k', hk', e', hkD⟩ := hq
  have hn : k' * k⁻¹ ∈ K ⊓ N := by
    refine ⟨K.mul_mem hk' (K.inv_mem hk), ?_⟩
    have : k' * k⁻¹ = η (paK q) * η (paK p) := by
      calc k' * k⁻¹ = (η (paK q))⁻¹ * (η (paK q) * k') * k⁻¹ := by group
        _ = (η (paK q))⁻¹ * (η (paK p) * k) * k⁻¹ := by rw [← e', e]
        _ = η (paK q) * η (paK p) := by rw [η_inv_self]; group
    rw [this]
    exact N.mul_mem (η_mem_N _) (η_mem_N _)
  rw [K_inf_N, Subgroup.mem_bot] at hn
  have hkk : k' = k := by
    calc k' = k' * k⁻¹ * k := by group
      _ = k := by rw [hn, one_mul]
  subst hkk
  have ha : paK p = paK q := by
    have : η (paK p) = η (paK q) := mul_right_cancel (e.symm.trans e')
    exact η_injOn (paK_lt p) (paK_lt q) this
  refine peqK_of ha ?_
  have hb : ∀ b, app11 (unpack11 (pcK p)) b = app11 (unpack11 (pcK q)) b := fun b =>
    η_injOn (vecMulN_lt (cols_bdd _) b) (vecMulN_lt (cols_bdd _) b) ((hkC b).symm.trans (hkD b))
  have hs1 := (unpack11_bounded (pcK p)).1
  have hs2 := (unpack11_bounded (pcK q)).1
  refine Array.ext (by rw [hs1, hs2]) fun j h1 h2 => ?_
  have hj : j < 11 := by rwa [hs1] at h1
  have c1 := app11_two_pow (cols_bdd (pcK p)) hj
  have c2 := app11_two_pow (cols_bdd (pcK q)) hj
  rw [hb, c2, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at c1
  simpa using c1.symm

theorem η_comm' (a b : ℕ) : η a * η b = η b * η a := by
  rw [← η_xor, ← η_xor, Nat.xor_comm]

theorem actsBy_of_pairRep {g : J} {p : ℕ} (hg : PairRep g p) : ActsBy g (unpack11 (pcK p)) := by
  obtain ⟨k, -, rfl, hkC⟩ := hg
  intro a
  rw [← hkC a, mul_inv_rev, η_inv_self]
  calc η (paK p) * k * η a * (k⁻¹ * η (paK p)) = η (paK p) * (k * η a * k⁻¹) * η (paK p) := by
        group
    _ = (k * η a * k⁻¹) * (η (paK p) * η (paK p)) := by
        rw [hkC a, mul_assoc, η_comm' (app11 _ a), ← mul_assoc, ← η_xor (paK p) (paK p),
          Nat.xor_self, η_zero, one_mul, mul_one]
    _ = k * η a * k⁻¹ := by rw [← η_xor, Nat.xor_self, η_zero, mul_one]

theorem card_centralizer_N_eq {g : J} {p : ℕ} (hg : PairRep g p) :
    Nat.card (Subgroup.centralizer {g} ⊓ N : Subgroup J) = fixCount (unpack11 (pcK p)) := by
  obtain ⟨k, -, rfl, hkC⟩ := hg
  refine card_centralizer_N_of_actsBy (fun a => ?_) (cols_bdd _)
  rw [← hkC a, mul_inv_rev, η_inv_self]
  calc η (paK p) * k * η a * (k⁻¹ * η (paK p)) = η (paK p) * (k * η a * k⁻¹) * η (paK p) := by
        group
    _ = (k * η a * k⁻¹) * (η (paK p) * η (paK p)) := by
        rw [hkC a, mul_assoc, η_comm' (app11 _ a), ← mul_assoc, ← η_xor (paK p) (paK p),
          Nat.xor_self, η_zero, one_mul, mul_one]
    _ = k * η a * k⁻¹ := by rw [← η_xor, Nat.xor_self, η_zero, mul_one]

end CFSG.KC.J4FixC

end
