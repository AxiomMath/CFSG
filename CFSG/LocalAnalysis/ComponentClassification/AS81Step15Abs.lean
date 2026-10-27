module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15P0

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (centralizer (E : Set G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_centralizer hn
  · intro hc
    have := conj_mem_centralizer (inv_mem hn) hc
    simpa [mul_assoc] using this

theorem step15ii_of_data {R E H X : Subgroup G} {T : Subgroup (Equiv.Perm ↥(pointsIn R E))}
    (hD : PointsData R E H) (hT : TranslationData R E T)
    (hCEO : centralizer (E : Set G) = E ⊔ AS76b.oddCoreIn (centralizer (E : Set G)))
    (hCcard : Nat.card (centralizer (E : Set G)) =
      64 * Nat.card (AS76b.oddCoreIn (centralizer (E : Set G))))
    (hXN : X ≤ normalizer (E : Set G)) (hXR : ∀ x ∈ X, rightConjugate R x = R)
    (hXt : ∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ R → Q₂ ≠ R →
      ∃ x ∈ X, rightConjugate Q₁ x = Q₂)
    (hOX : AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (X : Set G)) :
    ∃ P₀ P : Subgroup G, P₀ ≤ normalizer (E : Set G) ∧
      normalizer (E : Set G) ≤ normalizer (P₀ : Set G) ∧
      normalizer (E : Set G) = P₀ ⊔ (normalizer (E : Set G) ⊓ normalizer (R : Set G)) ∧
      (∀ p ∈ P₀, ∀ q ∈ P₀, p * p ∈ centralizer (E : Set G) ∧
        p * q * p⁻¹ * q⁻¹ ∈ centralizer (E : Set G)) ∧
      (P₀ ⊓ centralizer (E : Set G)).relIndex P₀ = 16 ∧
      (∀ Q ∈ pointsIn R E, ∃ p ∈ P₀, rightConjugate R p = Q) ∧
      IsPGroup 2 P ∧ P ≤ P₀ ∧ P₀ = AS76b.oddCoreIn (centralizer (E : Set G)) ⊔ P ∧
      AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 := hT.card_points
  have hcomm := hD.comm
  obtain ⟨P₀, hP₀N, hNP₀, hCP₀, hP₀e, hP₀16, hP₀t, hP₀s⟩ := exists_translationSubgroup hD hT
  set C := centralizer (E : Set G) with hCdef
  set O := AS76b.oddCoreIn C with hOdef
  have hCfix : ∀ c ∈ C, ∀ Q ∈ pointsIn R E, rightConjugate Q c = Q := fun c hc Q hQ =>
    (rightConjugate_eq_self_iff Q c).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun q hq => mem_centralizer_iff.mp hc q (hQ.1 hq)))
  have hRpt : R ∈ pointsIn R E := self_mem_pointsIn hD.R_le
  have hNsup : normalizer (E : Set G) =
      P₀ ⊔ (normalizer (E : Set G) ⊓ normalizer (R : Set G)) := by
    refine le_antisymm (fun n hn => ?_) (sup_le hP₀N inf_le_left)
    obtain ⟨p, hp, hpn⟩ := hP₀t _ (rightConjugate_mem_pointsIn hRpt hn)
    have hnp : n * p⁻¹ ∈ normalizer (R : Set G) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← hpn, rightConjugate_mul,
        mul_inv_cancel, rightConjugate_one]
    have : n = (n * p⁻¹) * p := by group
    rw [this, sup_comm]
    exact mul_mem_sup (show n * p⁻¹ ∈ normalizer (E : Set G) ⊓ normalizer (R : Set G) from
      ⟨(normalizer (E : Set G)).mul_mem hn ((normalizer (E : Set G)).inv_mem (hP₀N hp)), hnp⟩) hp
  have hcommP : ⁅X, P₀⁆ ≤ P₀ := by
    rw [commutator_le]
    intro x hx p hp
    rw [commutatorElement_def]
    exact P₀.mul_mem ((mem_normalizer_iff.mp (hNP₀ (hXN hx)) p).mp hp) (P₀.inv_mem hp)
  have hcomm_pts : ∀ Q ∈ pointsIn R E, Q ≠ R → ∃ y ∈ ⁅X, P₀⁆, rightConjugate R y = Q := by
    intro Q hQ hQR
    obtain ⟨q, hq, hqQ⟩ := hP₀t Q hQ
    obtain ⟨Q', hQ', hQ'R, hQ'Q⟩ : ∃ Q' ∈ pointsIn R E, Q' ≠ R ∧ Q' ≠ Q := by
      by_contra hcon
      push Not at hcon
      have hsub : (pointsIn R E) ⊆ {R, Q} := fun Q' hQ' => by
        by_cases h : Q' = R
        · exact Or.inl h
        · exact Or.inr (hcon Q' hQ' h)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair (Ne.symm hQR), ← Nat.card_coe_set_eq, h16] at this
      omega
    obtain ⟨p, hp, hpQ'⟩ := hP₀t Q' hQ'
    have hRp : rightConjugate R p ≠ R := by rw [hpQ']; exact hQ'R
    have hQp : rightConjugate Q p ≠ R := by
      intro h
      apply hQ'Q
      have h1 : q * p ∈ C := hP₀s _ (P₀.mul_mem hq hp) (by rw [← rightConjugate_mul, hqQ, h])
      have hq2 : q * q ∈ C := (hP₀e q hq q hq).1
      have h2 : p = (q * q)⁻¹ * (q * (q * p)) := by group
      have h3 : rightConjugate R p = rightConjugate R q := by
        rw [h2, ← rightConjugate_mul, hCfix _ (C.inv_mem hq2) R hRpt, ← rightConjugate_mul]
        rw [hCfix _ h1 _ (rightConjugate_mem_pointsIn hRpt (hP₀N hq))]
      rw [← hpQ', h3, hqQ]
    obtain ⟨x, hx, hxQ⟩ := hXt _ (rightConjugate_mem_pointsIn hRpt (hP₀N hp))
      _ (rightConjugate_mem_pointsIn hQ (hP₀N hp)) hRp hQp
    refine ⟨⁅x⁻¹, p⁆, commutator_mem_commutator (X.inv_mem hx) hp, ?_⟩
    rw [commutatorElement_def, ← rightConjugate_mul, ← rightConjugate_mul, ← rightConjugate_mul,
      hXR _ (X.inv_mem hx), inv_inv, hxQ, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hP₀eq : P₀ = ⁅X, P₀⁆ ⊔ C := by
    refine le_antisymm (fun q hq => ?_) (sup_le hcommP hCP₀)
    by_cases hqR : rightConjugate R q = R
    · exact mem_sup_right (hP₀s q hq hqR)
    obtain ⟨y, hy, hyQ⟩ := hcomm_pts _ (rightConjugate_mem_pointsIn hRpt (hP₀N hq)) hqR
    have hqy : q * y⁻¹ ∈ C := hP₀s _ (P₀.mul_mem hq (P₀.inv_mem (hcommP hy))) (by
      rw [← rightConjugate_mul, ← hyQ, rightConjugate_mul, mul_inv_cancel, rightConjugate_one])
    have : q = (q * y⁻¹) * y := by group
    rw [this, sup_comm]
    exact mul_mem_sup hqy hy
  have hON : normalizer (E : Set G) ≤ normalizer (O : Set G) :=
    (normalizer_le_normalizer_centralizer E).trans (AS76b.normalizer_le_normalizer_oddCoreIn C)
  have hOX' : ⁅O, X⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact hOX
  have hPO : ⁅P₀, O⁆ ≤ O := by
    rw [commutator_le]
    intro p hp o ho
    rw [commutatorElement_def]
    exact O.mul_mem ((mem_normalizer_iff.mp (hON (hP₀N hp)) o).mp ho) (O.inv_mem ho)
  have h3 : ⁅⁅X, P₀⁆, O⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact eq_bot_iff.mpr ((commutator_mono_left hPO).trans hOX'.le)
    · rw [hOX', commutator_bot_left]
  set W := ⁅X, P₀⁆ ⊔ E with hW
  have hOW : O ≤ centralizer (W : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le (commutator_eq_bot_iff_le_centralizer.mp h3) ?_
    rw [← le_centralizer_iff]
    exact AS76b.oddCoreIn_le C
  have hEC : E ≤ C := fun x hx => mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  have hWP₀ : W ≤ P₀ := sup_le hcommP (hEC.trans hCP₀)
  have hOP₀ : O ≤ P₀ := (AS76b.oddCoreIn_le C).trans hCP₀
  have hWO : O ⊔ W = P₀ := by
    refine le_antisymm (sup_le hOP₀ hWP₀) ?_
    calc P₀ = ⁅X, P₀⁆ ⊔ C := hP₀eq
      _ ≤ O ⊔ W := by
        refine sup_le (le_sup_left.trans le_sup_right) ?_
        rw [hCEO]
        exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
  have hP₀card : Nat.card P₀ = 2 ^ 10 * Nat.card O := by
    have h := Subgroup.relIndex_mul_card C P₀
    rw [inf_eq_left.mpr hCP₀] at h
    have h16' : C.relIndex P₀ = 16 := by
      rw [← inf_relIndex_right, inf_comm]
      exact hP₀16
    rw [← h, h16', hCcard]
    ring
  have hWN : W ≤ normalizer (O : Set G) := hWP₀.trans (hP₀N.trans hON)
  have hsupW := card_sup_mul_card_inf hWN
  rw [hWO, hP₀card] at hsupW
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hWcard : Nat.card W = 2 ^ 10 * Nat.card (O ⊓ W : Subgroup G) := by
    have h : Nat.card O * Nat.card W = Nat.card O * (2 ^ 10 * Nat.card (O ⊓ W : Subgroup G)) := by
      rw [← hsupW]
      ring
    exact Nat.eq_of_mul_eq_mul_left hOpos h
  have hOWodd : Odd (Nat.card (O ⊓ W : Subgroup G)) :=
    (AS76b.odd_card_oddCoreIn C).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 W
  have hPcard : Nat.card P = 2 ^ 10 := by
    have hm0 : Nat.card (O ⊓ W : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    have hfac : (2 ^ 10 * Nat.card (O ⊓ W : Subgroup G)).factorization 2 = 10 := by
      rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd hOWodd.not_two_dvd_nat]
      rfl
    rw [hP.card_eq, hWcard, hfac]
  have hPW : P ≤ W := hP.le
  have hP2 : IsPGroup 2 P := hP.isPGroup
  have hOP : O ⊓ P = ⊥ := AS76b.oddCoreIn_inf_eq_bot hP2
  have hsupP := card_sup_mul_card_inf (hPW.trans hWN)
  rw [hOP, card_bot, mul_one, hPcard] at hsupP
  have hOPeq : O ⊔ P = P₀ := Subgroup.eq_of_le_of_card_ge (sup_le hOP₀ (hPW.trans hWP₀))
    (by rw [hsupP, hP₀card, mul_comm])
  exact ⟨P₀, P, hP₀N, hNP₀, hNsup, hP₀e, hP₀16, hP₀t, hP2, hPW.trans hWP₀, hOPeq.symm,
    hOW.trans (centralizer_le fun x hx => hPW hx)⟩

end CFSG.ComponentClassification.AS81
