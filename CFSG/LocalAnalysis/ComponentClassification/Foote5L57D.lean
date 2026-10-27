module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57A

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem false_of_lin_conjugate_Q (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hMW : MacWilliamsStatement) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsT : s ∈ T) (hsN : s ∈ normalizer (S : Set G))
    (hss : s * s ∈ S) (hbot : Q ⊓ conjugate Q s = ⊥)
    (hnf : ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin) : False := by
  have htQs := h.t_mem_conjugate_Q ε hD hna hQ4 hQsq hsN hbot hnf
  have hRs := h.inf_conjugate_R_eq_bot_of_t_mem hna hsN htQs
  obtain ⟨e⟩ := h.nonempty_R_equiv_dihedral_four ε hD hna hQsq hsN hRs
  have hS64 := h.card_S_le_sixtyfour ε hD hQ4 hQsq hsN hbot hnf htQs e
  obtain ⟨r₀, hr₀, hr₀2, hr₀1, hr₀t, -⟩ := h.exists_r₀ ε hD hQ4 hQsq hsN hbot hnf htQs e
  have hR8 : Nat.card ↥(S ⊓ L) = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hRsS : conjugate (S ⊓ L) s ≤ S := conjugate_le_of_mem_normalizer hsN inf_le_left
  have hcomm : ∀ c ∈ S ⊓ L, ∀ d ∈ conjugate (S ⊓ L) s, c * d = d * c :=
    fun c hc d hd => (h.commute_of_inf_conjugate_eq_bot hsN hRs hc hd).symm
  have hcard : Nat.card ↥(S ⊓ L ⊔ conjugate (S ⊓ L) s) = 64 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (S ⊓ L)
      (conjugate (S ⊓ L) s) (le_normalizer_of_commute hcomm) (disjoint_iff.mpr hRs),
      card_conjugate_eq_card, hR8]
  have hSeq : S ⊓ L ⊔ conjugate (S ⊓ L) s = S :=
    eq_of_le_of_card_ge (sup_le inf_le_left hRsS) (by rw [hcard]; exact hS64)
  have hsX : ∀ c ∈ S ⊓ L, s⁻¹ * c * s ∈ conjugate (S ⊓ L) s := fun c hc => by
    rw [mem_conjugate_iff, show s * (s⁻¹ * c * s) * s⁻¹ = c by group]
    exact hc
  have hsX' : ∀ c ∈ conjugate (S ⊓ L) s, s⁻¹ * c * s ∈ S ⊓ L := fun c hc => by
    have h1 := h.conj_mem_R (inv_mem hss) (mem_conjugate_iff.mp hc)
    rwa [show (s * s)⁻¹ * (s * c * s⁻¹) * (s * s)⁻¹⁻¹ = s⁻¹ * c * s by group] at h1
  obtain ⟨c₁, hc₁, hinv, hsw, hsw'⟩ := exists_involution_swap hcomm hRs hsX hsX'
    (by rw [hSeq]; exact hss)
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hW : WreathCfg T (S ⊓ L) (conjugate (S ⊓ L) s) t r₀ (c₁⁻¹ * s) :=
    { isPGroup := h.sylT.isPGroup
      XT := inf_le_left.trans h.ST
      X'T := hRsS.trans h.ST
      comm := hcomm
      bot := hRs
      card := hR8
      xX := h.tR
      x2 := ht22
      x1 := h.t_ne_one
      xZ := fun d hd => h.tZ d (mem_inf.mp hd).1
      aX := hr₀
      a2 := hr₀2
      anc := by
        by_contra hno
        push Not at hno
        rcases h.center_R hna hr₀ (fun r hr => (hno r hr).symm) with h1 | h1
        · exact hr₀1 h1
        · exact hr₀t h1
      Cx := fun y hyT hyt => by
        rw [hSeq]
        exact h.mem_S_of_commute_t hsT hsN htQs hyT hyt
      sT := mul_mem (inv_mem (h.ST (mem_inf.mp hc₁).1)) hsT
      s2 := hinv
      sX := hsw
      sX' := hsw' }
  exact h.false_of_gen4 hGH hKG (hW.gen4 hMW h.sylT)

end Sec5

end CFSG.ComponentClassification.Foote5
