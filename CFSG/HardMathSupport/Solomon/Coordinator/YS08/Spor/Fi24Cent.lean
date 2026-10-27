module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
public import Certificates.Certificate214035

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
open CFSG.Sporadic.Fi24 (J)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi24Cent

section Seven

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven


noncomputable abbrev yA : J := g7 fi24SevenData.iy

noncomputable abbrev yB : J := g7 fi24SevenData.ic

theorem exists_conj_seven (s : J) (hs : orderOf s = 7) :
    ∃ t : J, t * s * t⁻¹ = yA ∨ t * s * t⁻¹ = yB :=
  fi24Seven_parts.conj s hs

section Cert


theorem cert_parts : CentFacts := Certificates.certificate214035

theorem three_fix_y {x : J} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hc : x * yA = yA * x) :
    (fixS x : Finset (Fin 306936)).card = 3240 ∨ (fixS x : Finset (Fin 306936)).card = 0 :=
  cert_parts.three_y x hx3 hx1 hc

theorem three_fix_c {x : J} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hc : x * yB = yB * x) :
    (fixS x : Finset (Fin 306936)).card = 378 :=
  cert_parts.three_c x hx3 hx1 hc

theorem no_root_y (g : J) : g ^ 7 ≠ yA := cert_parts.root_y g

theorem no_root_c (g : J) : g ^ 7 ≠ yB := cert_parts.root_c g

theorem card_fixS_yA : (fixS yA : Finset (Fin 306936)).card = 21 := cert_parts.fix_y

theorem card_fixS_yB : (fixS yB : Finset (Fin 306936)).card = 0 := cert_parts.fix_c

theorem three_seven {x s : J} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hs : orderOf s = 7)
    (hc : x * s = s * x) :
    ((fixS s : Finset (Fin 306936)).card = 21 ∧
        ((fixS x : Finset (Fin 306936)).card = 3240 ∨ (fixS x : Finset (Fin 306936)).card = 0)) ∨
      ((fixS s : Finset (Fin 306936)).card = 0 ∧ (fixS x : Finset (Fin 306936)).card = 378) := by
  obtain ⟨t, ht⟩ := exists_conj_seven s hs
  have hx3' : (t * x * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hx1' : t * x * t⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this, h]; group
  have hcomm : ∀ r : J, t * s * t⁻¹ = r → (t * x * t⁻¹) * r = r * (t * x * t⁻¹) := by
    intro r hr
    rw [← hr]
    calc t * x * t⁻¹ * (t * s * t⁻¹) = t * (x * s) * t⁻¹ := by group
      _ = t * (s * x) * t⁻¹ := by rw [hc]
      _ = t * s * t⁻¹ * (t * x * t⁻¹) := by group
  rcases ht with ht | ht
  · left
    refine ⟨?_, ?_⟩
    · rw [← card_fixS_conj t s, ht]
      exact card_fixS_yA
    · have := three_fix_y hx3' hx1' (hcomm yA ht)
      rwa [card_fixS_conj t x] at this
  · right
    refine ⟨?_, ?_⟩
    · rw [← card_fixS_conj t s, ht]
      exact card_fixS_yB
    · have := three_fix_c hx3' hx1' (hcomm yB ht)
      rwa [card_fixS_conj t x] at this

theorem pow_seven_eq_one {g : J} (hg : g ^ 49 = 1) : g ^ 7 = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra hne
  have h7 : (g ^ 7) ^ 7 = 1 := by rw [← pow_mul]; exact hg
  have hord : orderOf (g ^ 7) = 7 := orderOf_eq_prime h7 hne
  obtain ⟨t, ht⟩ := exists_conj_seven (g ^ 7) hord
  have hpow : (t * g * t⁻¹) ^ 7 = t * g ^ 7 * t⁻¹ := by rw [conj_pow]
  rcases ht with ht | ht
  · exact no_root_y (t * g * t⁻¹) (by rw [hpow, ht])
  · exact no_root_c (t * g * t⁻¹) (by rw [hpow, ht])

end Cert

end Seven

end Fi24Cent

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
