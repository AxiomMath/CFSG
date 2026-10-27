module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem ordA_one_formula (m : ℕ) : Open.ordA 1 m = m * (m ^ 2 - 1) / Nat.gcd 2 (m - 1) := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]

theorem eq_five_or_seven_of_ordA_dvd {q c : ℕ} (hq : 5 ≤ q)
    (hc : c = 64 ∨ c = 168 ∨ c = 60 ∨ c = 72) (hd : Open.ordA 1 q ∣ c) : q = 5 ∨ q = 7 := by
  have hc0 : 0 < c := by omega
  have hle := Nat.le_of_dvd hc0 hd
  rw [ordA_one_formula] at hle hd
  have hq9 : q < 9 := by
    by_contra hge
    push Not at hge
    have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) :=
      Nat.div_le_div_left hg hgpos
    have h2 : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
    omega
  interval_cases q
  · exact Or.inl rfl
  · exfalso
    norm_num at hle
    omega
  · exact Or.inr rfl
  · exfalso
    norm_num at hle
    omega

theorem eq_of_pow_eq_prime {p f q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ^ f = q) :
    p = q ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact hq.one_lt.ne h
  have hpq : p ∣ q := h ▸ dvd_pow_self p hf
  have hpq' : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq)
  subst hpq'
  refine ⟨rfl, ?_⟩
  exact Nat.pow_right_injective hp.two_le (show p ^ f = p ^ 1 by rw [h, pow_one])

include hKa in
theorem card_oddBar_J_dvd_fixSub (hZJ : center (OddBar h.J) = ⊥) :
    Nat.card (OddBar h.J) ∣
      Nat.card (fixSub ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h))) := by
  obtain ⟨M₀, hM₀, ⟨eM⟩⟩ := exists_fix_component center_LK (inn_le_GAut hKa)
    (phi hKa (abar h)) (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  have h1 : Nat.card (OddBar h.J) ∣ Nat.card ↥(Jhat hKa) := by
    rw [← Nat.card_congr eJ.toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(Jhat hKa))]
    exact dvd_mul_right _ _
  rw [← Nat.card_congr eM.toEquiv] at h1
  exact h1.trans (Subgroup.card_dvd_of_le hM₀.1)

theorem card_centralizer_inf_S_of_isConj {x r : PSL3Four.R}
    (hxr : IsConj x r) :
    Nat.card ↥(centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) =
      Nat.card ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) := by
  obtain ⟨c, hc, hxc⟩ := PSL3Four.eq_conj_of_isConj hxr
  have hmap : (centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S).map
      (MulAut.conj c).toMonoidHom = centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨g', ⟨hg'c, hg'S⟩, rfl⟩
      refine ⟨?_, PSL3Four.conj_mem_S hc hg'S⟩
      rw [hxc]
      calc c * g' * c⁻¹ * (c * (r : Equiv.Perm (Fin 42)) * c⁻¹) = c * (g' * r) * c⁻¹ := by
            group
        _ = c * (r * g') * c⁻¹ := by rw [hg'c]
        _ = c * (r : Equiv.Perm (Fin 42)) * c⁻¹ * (c * g' * c⁻¹) := by group
    · rintro ⟨hgc, hgS⟩
      refine ⟨c⁻¹ * g * c, ⟨?_, ?_⟩, by group⟩
      · have hr : (r : Equiv.Perm (Fin 42)) = c⁻¹ * x * c := by rw [hxc]; group
        rw [hr]
        calc c⁻¹ * g * c * (c⁻¹ * (x : Equiv.Perm (Fin 42)) * c) = c⁻¹ * (g * x) * c := by
              group
          _ = c⁻¹ * (x * g) * c := by rw [hgc]
          _ = c⁻¹ * (x : Equiv.Perm (Fin 42)) * c * (c⁻¹ * g * c) := by group
      · have := PSL3Four.conj_mem_S (PSL3Four.R.inv_mem hc) hgS
        rwa [inv_inv] at this
  rw [← hmap, card_map_of_injective (MulAut.conj c).injective]

theorem card_centralizer_inf_S {x : PSL3Four.R}
    (hx : orderOf x = 2) :
    Nat.card ↥(centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 64 ∨
      Nat.card ↥(centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 168 ∨
      Nat.card ↥(centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 60 ∨
      Nat.card ↥(centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 72 := by
  obtain ⟨-, -, -, -, -, hcls, -, -, -, -, -, -, -, hC1, hC2, hC3, hC4, -⟩ :=
    PSL3Four.involution_enumeration
  rcases (hcls x).mp hx with hc | hc | hc | hc <;> rw [card_centralizer_inf_S_of_isConj hc]
  · exact Or.inl hC1
  · exact Or.inr (Or.inl hC2)
  · exact Or.inr (Or.inr (Or.inl hC3))
  · exact Or.inr (Or.inr (Or.inr hC4))

theorem card_fixSub_S {β : MulAut ↥PSL3Four.S}
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1) :
    Nat.card (fixSub β) = 64 ∨ Nat.card (fixSub β) = 168 ∨ Nat.card (fixSub β) = 60 ∨
      Nat.card (fixSub β) = 72 := by
  obtain ⟨eR, heR, -⟩ := PSL3Four.full_automorphism_action
  obtain ⟨x, rfl⟩ := eR.surjective β
  have hx2 : orderOf x = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      exact eR.injective (by rw [map_mul, hβ2, map_one])
    · rintro rfl
      exact hβ1 (map_one eR)
  have hmap : (fixSub (eR x)).map PSL3Four.S.subtype =
      centralizer {(x : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, mem_fixSub, coe_subtype]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, s.2⟩
      have h1 := congrArg Subtype.val hs
      rw [heR, Subgroup.coe_inv] at h1
      calc (s : Equiv.Perm (Fin 42)) * x = (x * s * (x : Equiv.Perm (Fin 42))⁻¹) * x := by
            rw [h1]
        _ = x * s := by group
    · rintro ⟨hgc, hgS⟩
      refine ⟨⟨g, hgS⟩, Subtype.ext ?_, rfl⟩
      rw [heR, Subgroup.coe_inv]
      calc (x : Equiv.Perm (Fin 42)) * g * (x : Equiv.Perm (Fin 42))⁻¹ =
          (g * x) * (x : Equiv.Perm (Fin 42))⁻¹ := by rw [hgc]
        _ = g := by group
  rw [← card_map_of_injective PSL3Four.S.subtype_injective, hmap]
  exact card_centralizer_inf_S hx2

include hKa in
theorem psl2_five_or_seven_of_psl34
    (hZJ : center (OddBar h.J) = ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hm : Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) :
    Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1 := by
  obtain ⟨eS⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hm
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eL, -⟩ : ∃ f : LK h ≃* ↥PSL3Four.S, f = eZ.trans eS := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ g : MulAut (LK h),
      g = ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h)) := ⟨_, rfl⟩
  have hdvd := card_oddBar_J_dvd_fixSub hKa hZJ
  rw [← hφ] at hdvd
  have hφ2 : φ * φ = 1 := by
    have h0 := pow_orderOf_eq_one (phi hKa (abar h))
    rw [orderOf_phi_abar' hKa, sq] at h0
    rw [hφ, ← Subgroup.coe_mul, h0, Subgroup.coe_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    have h0 := orderOf_phi_abar' hKa
    have h2 : phi hKa (abar h) = 1 := Subtype.ext (by rw [← hφ, h1, Subgroup.coe_one])
    rw [h2, orderOf_one] at h0
    exact absurd h0 (by norm_num)
  set β : MulAut ↥PSL3Four.S := (eL.symm.trans φ).trans eL with hβ
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun s => ?_
    have h1 := congrArg (fun g : MulAut (LK h) => g (eL.symm s)) hφ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    simp only [hβ, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1,
      MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hφ1
    refine MulEquiv.ext fun y => ?_
    have h2 := congrArg (fun g : MulAut ↥PSL3Four.S => g (eL y)) h1
    simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    rw [MulAut.one_apply]
    exact eL.injective h2
  have hcard : Nat.card (fixSub φ) = Nat.card (fixSub β) := by
    rw [hβ, ← fixSub_map_equiv eL φ, card_map_of_injective eL.injective]
  rw [hcard] at hdvd
  have hc := card_fixSub_S hβ2 hβ1
  rcases hJ with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, hq, hmJ⟩
  · exfalso
    have h7 : Nat.card (OddBar h.J) = 2520 :=
      (Nat.card_congr e7.toEquiv).trans card_alternatingGroup_seven
    rw [h7] at hdvd
    rcases hc with hc | hc | hc | hc <;> rw [hc] at hdvd <;> norm_num at hdvd
  · have hJc : Nat.card (OddBar h.J) = Open.ordA 1 (p ^ f) :=
      (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hmJ)).1 rfl
    rw [hJc] at hdvd
    have h57 : p ^ f = 5 ∨ p ^ f = 7 := by
      rcases hc with hc | hc | hc | hc <;> rw [hc] at hdvd
      · exact eq_five_or_seven_of_ordA_dvd hq (Or.inl rfl) hdvd
      · exact eq_five_or_seven_of_ordA_dvd hq (Or.inr (Or.inl rfl)) hdvd
      · exact eq_five_or_seven_of_ordA_dvd hq (Or.inr (Or.inr (Or.inl rfl))) hdvd
      · exact eq_five_or_seven_of_ordA_dvd hq (Or.inr (Or.inr (Or.inr rfl))) hdvd
    rcases h57 with h5 | h7
    · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_five h5
      exact Or.inl hmJ
    · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp (by norm_num) h7
      exact Or.inr hmJ

end CFSG.ComponentClassification.GSThmB.Cov
