module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56K
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HaradaE16
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56H
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56I
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56J

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjugate_sq_eq_one {H : Subgroup G} {s c : G} (hHsq : ∀ q ∈ H, q * q = 1)
    (hc : c ∈ conjugate H s) : c * c = 1 := by
  rw [mem_conjugate_iff] at hc
  have h1 := hHsq _ hc
  calc c * c = s⁻¹ * (s * c * s⁻¹ * (s * c * s⁻¹)) * s := by group
    _ = 1 := by rw [h1]; group

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_s_of_lt (hSlt : S < T) :
    ∃ s ∈ T, s ∉ S ∧ s ∈ normalizer (S : Set G) ∧ s * s ∈ S ∧
      s ∉ normalizer (Q : Set G) ∧ Q ⊓ conjugate Q s = ⊥ ∧
      ∀ c ∈ Q, ∀ d ∈ conjugate Q s, c * d = d * c := by
  obtain ⟨s, hsT, hsS, hsN, hss⟩ := exists_mem_normalizer_sq_mem h.sylT.isPGroup hSlt
  have hsQ := h.not_mem_normalizer_Q hsT hsS
  exact ⟨s, hsT, hsS, hsN, hss, hsQ, h.inf_conjugate_eq_bot hsN hsQ,
    fun c hc d hd => h.commute_Q_conjugate hsN hsQ hc hd⟩

theorem conj_mem_Q_of_mem_conjugate {s c : G} (hss : s * s ∈ S) (hc : c ∈ conjugate Q s) :
    s⁻¹ * c * s ∈ Q := by
  rw [mem_conjugate_iff] at hc
  have h1 := h.conj_mem_Q (inv_mem hss) hc
  rwa [show (s * s)⁻¹ * (s * c * s⁻¹) * (s * s)⁻¹⁻¹ = s⁻¹ * c * s by group] at h1

theorem conj_z_center {s : G} (hsN : s ∈ normalizer (S : Set G)) :
    ∀ g ∈ S, g * (s⁻¹ * z * s) = s⁻¹ * z * s * g := by
  intro g hg
  have h1 := h.zS _ ((mem_normalizer_iff.mp hsN g).mp hg)
  calc g * (s⁻¹ * z * s) = s⁻¹ * ((s * g * s⁻¹) * z) * s := by group
    _ = s⁻¹ * (z * (s * g * s⁻¹)) * s := by rw [h1]
    _ = s⁻¹ * z * s * g := by group

theorem false_of_card_Q_eight (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hMW : MacWilliamsStatement) {s : G} (hsT : s ∈ T) (hsN : s ∈ normalizer (S : Set G))
    (hss : s * s ∈ S) (hbot : Q ⊓ conjugate Q s = ⊥)
    (hcomm : ∀ c ∈ Q, ∀ d ∈ conjugate Q s, c * d = d * c)
    (hSeq : Q ⊔ conjugate Q s = S) (hQ8 : Nat.card Q = 8)
    (hQna : ∃ c ∈ Q, ∃ d ∈ Q, c * d ≠ d * c) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by have := h.z2; rw [h1, orderOf_one] at this; omega
  obtain ⟨E, hEQ, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := Q) (k := 2) (by rw [h.open_pRank_Q])
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← sq]; exact hE.2 e he
  obtain ⟨a, haE, ha1, haz⟩ : ∃ a ∈ E, a ≠ 1 ∧ a ≠ z := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1, z} : Finset G) fun e he => by
      by_cases he1 : e = 1
      · rw [he1]
        exact Finset.mem_insert_self _ _
      · rw [hno e he he1]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
    rw [hEc] at h1
    norm_num at h1
    omega
  have haQ := hEQ haE
  have hanc : ∃ d ∈ Q, d * a ≠ a * d := by
    by_contra hno
    push Not at hno
    rcases eq_one_or_eq_of_mem_center_eight hQ8 hQna h.zQ hz1 (fun d hd => h.zS d (h.QS hd))
      haQ hno with h1 | h1
    · exact ha1 h1
    · exact haz h1
  obtain ⟨c₁, hc₁, hinv, hsw, hsw'⟩ := exists_involution_swap hcomm hbot
    (fun c hc => by rw [mem_conjugate_iff, show s * (s⁻¹ * c * s) * s⁻¹ = c by group]; exact hc)
    (fun c hc => h.conj_mem_Q_of_mem_conjugate hss hc) (by rw [hSeq]; exact hss)
  have hW : WreathCfg T Q (conjugate Q s) z a (c₁⁻¹ * s) :=
    { isPGroup := h.sylT.isPGroup
      XT := h.QS.trans h.ST
      X'T := (h.conjugate_Q_le hsN).trans h.ST
      comm := hcomm
      bot := hbot
      card := hQ8
      xX := h.zQ
      x2 := hz22
      x1 := hz1
      xZ := fun d hd => h.zS d (h.QS hd)
      aX := haQ
      a2 := hEsq a haE
      anc := hanc
      Cx := fun y hyT hyz => by rw [hSeq]; exact h.mem_S_of_commute hyT hyz
      sT := mul_mem (inv_mem (h.ST (h.QS hc₁))) hsT
      s2 := hinv
      sX := hsw
      sX' := hsw' }
  exact h.false_of_gen4 hGH hKG (hW.gen4 hMW h.sylT)

theorem false_of_card_S_thirtytwo {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
    (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {Lin : Subgroup (MulAut 𝕊)} (hD : Foote5AutData 𝕊 Lin)
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) (hMW : MacWilliamsStatement)
    {s : G} (hsN : s ∈ normalizer (S : Set G)) (hbot : Q ⊓ conjugate Q s = ⊥)
    (hcomm : ∀ c ∈ Q, ∀ d ∈ conjugate Q s, c * d = d * c) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) (hS32 : Nat.card S = 32) : False := by
  have hz1 : z ≠ 1 := fun h1 => by have := h.z2; rw [h1, orderOf_one] at this; omega
  have hQsS := h.conjugate_Q_le hsN
  have hAS : Q ⊔ conjugate Q s ≤ S := sup_le h.QS hQsS
  have hQs4 : Nat.card (conjugate Q s) = 4 := by rw [card_conjugate_eq_card, hQ4]
  have hQsq' : ∀ c ∈ conjugate Q s, c * c = 1 := fun c hc => conjugate_sq_eq_one hQsq hc
  have hA16 : Nat.card ↥(Q ⊔ conjugate Q s) = 16 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q (conjugate Q s)
      (le_normalizer_of_commute hcomm) (disjoint_iff.mpr hbot), hQ4, hQs4]
  have hidx : Nat.card S = 2 * Nat.card ↥(Q ⊔ conjugate Q s) := by rw [hS32, hA16]
  have hnotboth : ¬ ((∀ g ∈ S, ∀ c ∈ Q, g * c = c * g) ∧
      ∀ g ∈ S, ∀ c ∈ conjugate Q s, g * c = c * g) := by
    rintro ⟨hall, hall'⟩
    have hAZ : ∀ g ∈ S, ∀ c ∈ Q ⊔ conjugate Q s, g * c = c * g := by
      intro g hg c hc
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_mul_of_mem_sup_commute hcomm hc
      rw [← mul_assoc, hall g hg c₁ hc₁, mul_assoc, hall' g hg c₂ hc₂, mul_assoc]
    have hSab : ∀ y ∈ S, ∀ y' ∈ S, y * y' = y' * y := by
      intro y hy y' hy'
      by_cases hyA : y ∈ Q ⊔ conjugate Q s
      · exact (hAZ y' hy' y hyA).symm
      by_cases hy'A : y' ∈ Q ⊔ conjugate Q s
      · exact hAZ y hy y' hy'A
      have h1 := mul_mem_of_card_eq_two_mul hAS hidx (inv_mem hy) hy'
        (fun h2 => hyA (by have h3 := inv_mem h2; rwa [inv_inv] at h3)) hy'A
      calc y * y' = y * (y * (y⁻¹ * y')) := by group
        _ = y * ((y⁻¹ * y') * y) := by rw [hAZ y hy _ h1]
        _ = y' * y := by group
    have h2 := h.card_S_le_of_center_R ε hD fun y hy r hr => hSab y hy r (mem_inf.mp hr).1
    omega
  have hQZ : ∃ g ∈ S, ∃ c ∈ Q, g * c ≠ c * g := by
    by_contra hno
    push Not at hno
    refine hnotboth ⟨hno, fun g hg c hc => ?_⟩
    have h1 := hno _ ((mem_normalizer_iff.mp hsN g).mp hg) _ (mem_conjugate_iff.mp hc)
    calc g * c = s⁻¹ * ((s * g * s⁻¹) * (s * c * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * c * s⁻¹) * (s * g * s⁻¹)) * s := by rw [h1]
      _ = c * g := by group
  have hQ'Z : ∃ g ∈ S, ∃ c ∈ conjugate Q s, g * c ≠ c * g := by
    by_contra hno
    push Not at hno
    refine hnotboth ⟨fun g hg c hc => ?_, hno⟩
    have hgs : s⁻¹ * g * s ∈ S := conj_mem_of_mem_normalizer hsN hg
    have hcs : s⁻¹ * c * s ∈ conjugate Q s := by
      rw [mem_conjugate_iff, show s * (s⁻¹ * c * s) * s⁻¹ = c by group]
      exact hc
    have h1 := hno _ hgs _ hcs
    calc g * c = s * ((s⁻¹ * g * s) * (s⁻¹ * c * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * c * s) * (s⁻¹ * g * s)) * s⁻¹ := by rw [h1]
      _ = c * g := by group
  have hx'Q : s⁻¹ * z * s ∈ conjugate Q s := by
    rw [mem_conjugate_iff, show s * (s⁻¹ * z * s) * s⁻¹ = z by group]
    exact h.zQ
  have hx'1 : s⁻¹ * z * s ≠ 1 := fun h1 => hz1 (by
    calc z = s * (s⁻¹ * z * s) * s⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  exact h.false_of_gen4 hGH hKG (gen4_of_wreath_four hMW h.sylT h.ST h.QS hQsS hcomm hbot hQ4
    hQs4 hQsq hQsq' hS32 (fun g hg c hc => h.conj_mem_Q hg hc)
    (fun g hg c hc => h.conj_mem_conjugate_Q hsN hg hc) h.zQ hx'Q hz1 hx'1 h.zS
    (h.conj_z_center hsN) hQZ hQ'Z (fun y hyT hyz => h.mem_S_of_commute hyT hyz))

theorem nonabelian_R_of_not_sylow (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hST : ¬ IsSylowOf 2 S ⊤) : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  by_contra hna
  have hab : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a := by
    intro a ha b hb
    by_contra hab
    exact hna ⟨a, ha, b, hb, hab⟩
  have hSlt : S < T := lt_of_le_of_ne h.ST fun h1 => hST (by rw [h1]; exact h.sylT)
  obtain ⟨s, hsT, -, hsN, hss, -, hbot, hcomm⟩ := h.exists_s_of_lt hSlt
  have hQsS := h.conjugate_Q_le hsN
  have hAS : Q ⊔ conjugate Q s ≤ S := sup_le h.QS hQsS
  have hcardA : Nat.card ↥(Q ⊔ conjugate Q s) = Nat.card Q * Nat.card Q := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q (conjugate Q s)
      (le_normalizer_of_commute hcomm) (disjoint_iff.mpr hbot), card_conjugate_eq_card]
  have hS8 := h.card_S_le_of_abelian ε hD hab
  have hAcard := card_le_of_le hAS
  rw [hcardA] at hAcard
  obtain ⟨E, hEQ, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := Q) (k := 2) (by rw [h.open_pRank_Q])
  have hQ4 : 4 ≤ Nat.card Q := by
    have h1 := card_le_of_le hEQ
    rw [hEc] at h1
    norm_num at h1
    exact h1
  have hQ8 : Nat.card Q ≤ 8 := by nlinarith
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_Q
  have hk3 : k ≤ 3 := by
    by_contra hk3
    push Not at hk3
    have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    rw [← hk] at h1
    norm_num at h1
    omega
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    have h1 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk] at h1
    omega
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  ·
    have hQ4' : Nat.card Q = 4 := by rw [hk]; norm_num
    have hEeq : E = Q := eq_of_le_of_card_ge hEQ (by rw [hQ4', hEc]; norm_num)
    have hQsq : ∀ q ∈ Q, q * q = 1 := fun q hq => by
      rw [← sq]
      exact hE.2 q (hEeq ▸ hq)
    have hQsq' : ∀ c ∈ conjugate Q s, c * c = 1 := fun c hc => conjugate_sq_eq_one hQsq hc
    have hQs4 : Nat.card (conjugate Q s) = 4 := by rw [card_conjugate_eq_card, hQ4']
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h.isPGroup_S
    have hS16 : 16 ≤ Nat.card S := by rw [hQ4'] at hAcard; omega
    have hS32 : Nat.card S ≤ 32 := by rw [hQ4'] at hS8; omega
    have hj5 : j ≤ 5 := by
      by_contra hj5
      push Not at hj5
      have h1 : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj5
      rw [← hj] at h1
      norm_num at h1
      omega
    have hj4 : 4 ≤ j := by
      by_contra hj4
      push Not at hj4
      have h1 : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hj] at h1
      norm_num at h1
      omega
    have hS1632 : Nat.card S = 16 ∨ Nat.card S = 32 := by
      rcases (show j = 4 ∨ j = 5 by omega) with rfl | rfl
      · left
        rw [hj]
        norm_num
      · right
        rw [hj]
        norm_num
    rcases hS1632 with hj' | hj'
    ·
      have hSeq : Q ⊔ conjugate Q s = S :=
        eq_of_le_of_card_ge hAS (by rw [hcardA, hQ4', hj'])
      have hSab : ∀ y ∈ S, ∀ y' ∈ S, y * y' = y' * y := by
        intro y hy y' hy'
        rw [← hSeq] at hy hy'
        exact commute_of_mem_sup_abelian hcomm (fun c hc d hd => commute_of_sq_eq_one hQsq hc hd)
          (fun c hc d hd => commute_of_sq_eq_one hQsq' hc hd) hy hy'
      have hsyl : ∀ u ∈ Q, u ≠ 1 → IsSylowOf 2 S (centralizer ({u} : Set G)) :=
        fun u hu hu1 => h.isSylowOf_centralizer_of_center hu
          (orderOf_eq_prime (by rw [sq]; exact hQsq u hu) hu1) fun g hg => hSab g hg u (h.QS hu)
      have hSsq : ∀ y ∈ S, y * y = 1 := fun y hy => harE16_mul_self_of_mem_sup
        (fun a ha b hb => hSab a (hAS ha) b (hAS hb)) hQsq hQsq' (hSeq ▸ hy)
      exact h.false_of_gen4 hGH hKG (gen4_of_harada_e16 hMW hSab hSsq hj' h.QS hQ4' hsyl)
    · exact h.false_of_card_S_thirtytwo ε hD hGH hKG hMW hsN hbot hcomm hQ4' hQsq hj'
  ·
    have hQ8' : Nat.card Q = 8 := by rw [hk]; norm_num
    have hSeq : Q ⊔ conjugate Q s = S :=
      eq_of_le_of_card_ge hAS (by rw [hcardA, hQ8']; omega)
    have hQna : ∃ c ∈ Q, ∃ d ∈ Q, c * d ≠ d * c := by
      by_contra hQab
      push Not at hQab
      have hSab : ∀ y ∈ S, ∀ y' ∈ S, y * y' = y' * y := by
        intro y hy y' hy'
        rw [← hSeq] at hy hy'
        refine commute_of_mem_sup_abelian hcomm hQab (fun c hc d hd => ?_) hy hy'
        have h2 := hQab _ (mem_conjugate_iff.mp hc) _ (mem_conjugate_iff.mp hd)
        calc c * d = s⁻¹ * ((s * c * s⁻¹) * (s * d * s⁻¹)) * s := by group
          _ = s⁻¹ * ((s * d * s⁻¹) * (s * c * s⁻¹)) * s := by rw [h2]
          _ = d * c := by group
      have h1 := h.card_S_le_of_center_R ε hD fun y hy r hr => hSab y hy r (mem_inf.mp hr).1
      have h2 : Nat.card S = 64 := by rw [← hSeq, hcardA, hQ8']
      omega
    exact h.false_of_card_Q_eight hGH hKG hMW hsT hsN hss hbot hcomm hSeq hQ8' hQna

end Sec5

end CFSG.ComponentClassification.Foote5
