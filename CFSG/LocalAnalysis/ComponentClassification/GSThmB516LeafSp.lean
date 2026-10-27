module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOddJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSp4C
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpHigh
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag CatFactsSp4 X10Sp4
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.CatLeafProof.X10Sp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Pump516

namespace Pump516

theorem psp_high_false {S : Type} [Group S] [Finite S] {n p e f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hadm : StatedLieAdmissible .PSp n p e) (hn : 3 ≤ n)
    (hm : Blueprint.LieModel S .PSp n p e) {t : S} (hct : orderOf (MulAut.conj t) = 2)
    {L : Subgroup (fixedSubgroup (MulAut.conj t))} (hL : IsComponent L) (hZ : NoCentralInv L)
    (hLm : Blueprint.LieModel (L ⧸ center L) .PSL 2 p (2 * f)) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have hα2 : MulAut.congr e (MulAut.conj t) * MulAut.congr e (MulAut.conj t) = 1 := by
    rw [← map_mul, ← pow_two, ← hct, pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.congr e (MulAut.conj t) ≠ 1 := fun h => by
    have h1 : MulAut.conj t = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at hct
    omega
  let Φ := CatLeafProof.fixedSubgroupCongrEquiv e (MulAut.conj t)
  have hL0 : IsComponent (L.map Φ.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Φ hL
  let eL : L ≃* L.map Φ.toMonoidHom := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  have hback : ∀ {τ' : StatedLieTag} {n' e' : ℕ},
      CentralModel p τ' n' e' (L.map Φ.toMonoidHom) → CentralModel p τ' n' e' L :=
    fun h => h.of_mulEquiv eL
  rcases fixed_component_models hp hp2 hK hadm hn hα2 hα1 hL0 (hZ.map Φ) with
    h | h | ⟨-, h⟩ | ⟨j, -, h⟩
  · obtain ⟨had, h⟩ := hback h
    exact false_of_two_lieModels_l2 hp hp2 hf (Or.inl ⟨rfl, hn⟩) had h hLm
  · obtain ⟨had, h⟩ := hback h
    exact false_of_two_lieModels_l2 hp hp2 hf (Or.inr (Or.inl rfl)) had h hLm
  · obtain ⟨had, h⟩ := hback h
    exact false_of_two_lieModels_l2 hp hp2 hf (Or.inr (Or.inr rfl)) had h hLm
  · obtain ⟨had, h⟩ := hback h
    exact false_of_two_lieModels_l2 hp hp2 hf (Or.inr (Or.inr rfl)) had h hLm

theorem sl_le_psl_sq {Q : ℕ} (hQ : 2 ≤ Q) : 2 * (Q * (Q ^ 2 - 1)) ≤ Q ^ 2 * ((Q ^ 2) ^ 2 - 1) := by
  have h1 : 2 * Q ≤ Q ^ 2 := by nlinarith
  have h2 : Q ^ 2 - 1 ≤ (Q ^ 2) ^ 2 - 1 := by
    have : Q ^ 2 ≤ (Q ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  calc 2 * (Q * (Q ^ 2 - 1)) = (2 * Q) * (Q ^ 2 - 1) := by ring
    _ ≤ Q ^ 2 * ((Q ^ 2) ^ 2 - 1) := Nat.mul_le_mul h1 h2

theorem psp_sqrt_le {k Q : ℕ} (hk : 1 ≤ k) (hkQ : k ^ 2 = Q) :
    k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) ≤ Q ^ 2 * ((Q ^ 2) ^ 2 - 1) := by
  subst hkQ
  have e4 : k ^ 4 = (k ^ 2) ^ 2 := by ring
  rw [e4]
  refine Nat.mul_le_mul_left _ ?_
  have h2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have h4 : (k ^ 2) ^ 2 ≤ ((k ^ 2) ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  calc (k ^ 2 - 1) * ((k ^ 2) ^ 2 - 1) ≤ (k ^ 2) ^ 2 * ((k ^ 2) ^ 2 - 1) :=
        Nat.mul_le_mul_right _ (by
          have : k ^ 2 ≤ (k ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    _ ≤ ((k ^ 2) ^ 2) ^ 2 - 1 := by
        have h1 : 1 ≤ (k ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
        have e : ((k ^ 2) ^ 2) ^ 2 = (k ^ 2) ^ 2 * (k ^ 2) ^ 2 := by ring
        rw [e, Nat.mul_sub_one]
        omega

end Pump516

theorem leafAt_psp4
    {S : Type} [Group S] [Finite S] {r e₀ : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible .PSp 2 r e₀) (hm : Blueprint.LieModel S .PSp 2 r e₀) :
    CF516LeafAt S := by
  intro hs hna _ σ P hP p f hp hp2 hf hPm t _ ht2 J hJC hJ hJm _ _ _ _ _ _
  have : IsSimpleGroup S := hs
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨.PSp, 2, r, e₀, hr, hr2, hadm, hm⟩
  obtain ⟨hct, hJc, -, hJm'⟩ := leaf_J_data hQ hna ht2 hJC hJ hJm
  have hrp : r = p := by
    rcases CatLeafProof.gls3OddFamilyInput_PSp_holds S 2 r e₀ hr hr2 hadm hm _ hct _ hJc with
      ⟨τ', n', f', -, h⟩ | ⟨-, -, hnot, -⟩
    · exact char_eq_of_psl_two_sq hp hp2 hf hr2 hJm' h
    · exact absurd ⟨t, rfl⟩ hnot
  subst hrp
  have hq3 : 3 ≤ r ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) r)
  have he₀ : 1 ≤ e₀ := hadm.2.1
  have hX4 := l4u4_card_lower hp2 hPm
  have hXP : Nat.card (P ⧸ pPrimeCore 2 P) ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  rcases Nat.lt_or_ge f e₀ with hlt | hle
  swap
  ·
    have hS2 := two_mul_card_of_lieModel_psp hp2 hm
    have hmono : (r ^ e₀) ^ 4 * (((r ^ e₀) ^ 2 - 1) * ((r ^ e₀) ^ 4 - 1)) ≤
        (r ^ f) ^ 4 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 4 - 1)) := by
      rcases Nat.eq_or_lt_of_le hle with h | h
      · rw [h]
      · exact (psp_lt_psp (Nat.one_le_pow _ _ hp.pos) (Nat.pow_lt_pow_right hp.one_lt h)).le
    have hlt' := two_mul_psp4_lt hq3
    exact false_of_card_le_quotient hP.2.2.2 (by omega)
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hm
  have h9 : 9 ≤ r ^ e₀ :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ r ^ e₀ := Nat.pow_le_pow_right hp.pos (by omega)
  have hτ : ∀ β : MulAut S, β * β = 1 → β ≠ 1 →
      MulAut.congr e β * MulAut.congr e β = 1 ∧ MulAut.congr e β ≠ 1 := fun β h2 h1 =>
    ⟨by rw [← map_mul, h2, map_one], fun h =>
      h1 ((MulAut.congr e).injective (h.trans (map_one _).symm))⟩
  have hcβ : ∀ (β : MulAut S) x, e (β x) = MulAut.congr e β (e x) := fun β x => by
    simp [MulAut.congr_apply]
  have hc2 : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← pow_two, ← hct, pow_orderOf_eq_one]
  have hc1 : MulAut.conj t ≠ 1 := fun h => by
    rw [h, orderOf_one] at hct
    omega
  have hJX : J ≤ fixOf (MulAut.conj t) := by
    change J ≤ fixedSubgroup (MulAut.conj t)
    rw [fixedSubgroup_conj]
    exact hJC
  have hJX' : IsPComponent 2 (J.subgroupOf (fixOf (MulAut.conj t))) := by
    change IsPComponent 2 (J.subgroupOf (fixedSubgroup (MulAut.conj t)))
    rw [fixedSubgroup_conj]
    exact hJ
  obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf (hcβ _) hJX hJX'
  obtain ⟨hα2, hα1⟩ := hτ _ hc2 hc1
  let eJ : J ≃* J.map e.toMonoidHom := J.equivMapOfInjective e.toMonoidHom e.injective
  have hJq : Blueprint.LieModel (↥(J.map e.toMonoidHom) ⧸ pPrimeCore 2 ↥(J.map e.toMonoidHom))
      .PSL 2 r (2 * f) :=
    OddQuot.lieModel_of_equiv (CatalogueBAlternating.primeCoreQuotientEquiv 2 eJ) hJm
  have hJcard : pPrimeCore 2 ↥(J.map e.toMonoidHom) = ⊥ →
      Nat.card (J.map e.toMonoidHom) * 2 = r ^ (2 * f) * ((r ^ (2 * f)) ^ 2 - 1) := by
    intro hO
    rw [← card_psl2_mul_two hp hp2 hJq,
      (pPrimeCore 2 ↥(J.map e.toMonoidHom)).card_eq_card_quotient_mul_card_subgroup, hO,
      Subgroup.card_bot, mul_one]
  have hJnt : Nontrivial (↥(J.map e.toMonoidHom) ⧸ pPrimeCore 2 ↥(J.map e.toMonoidHom)) :=
    (Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) hJq).toNontrivial
  have he₀2f : e₀ = 2 * f := by
    rcases psp4_fixed_cases hp hp2 he₀ hF (by omega) hα2 hα1 hJ0X hJ0 with
      ⟨hO, hc⟩ | ⟨hsimp, hc⟩ | ⟨hsimp, hc⟩ | ⟨hsimp, k, hk, hc⟩
    · have h1 := hJcard hO
      rw [hc] at h1
      obtain ⟨-, h2⟩ := eq_of_sl_card (a := e₀) (b := 2 * f) hp hp2 he₀ (by omega) (Or.inr rfl)
        (by rw [← h1]; ring)
      omega
    · have h1 := hJcard (pPrimeCore_eq_bot_of_simple hJnt)
      exact (eq_of_sl_card (a := e₀) (b := 2 * f) hp hp2 he₀ (by omega) (Or.inl rfl)
        (by rw [one_mul, ← hc, h1])).1
    · have h1 := hJcard (pPrimeCore_eq_bot_of_simple hJnt)
      have h2 := (eq_of_sl_card (a := e₀ * 2) (b := 2 * f) hp hp2 (by omega) (by omega)
        (Or.inl rfl) (by rw [one_mul, pow_mul, ← hc, h1])).1
      omega
    · have h1 := hJcard (pPrimeCore_eq_bot_of_simple hJnt)
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ Dvd.intro k (sq k).symm)
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, pow_zero, one_pow] at hk
          omega
        · exact h0
      exact (false_of_psp_eq_sl (g := 2 * f) hp hp2 hj (by omega) (Or.inl rfl)
        (by rw [one_mul, ← hc, h1])).elim
  obtain ⟨hσ2', hPF, hPp, hPtop⟩ := hP
  have hσ1 : σ ≠ 1 := ProperFixedComponent.ne_one ⟨hσ2', hPF, hPp, hPtop⟩
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => hσ2' y
  obtain ⟨hσ₀2, hσ₀1⟩ := hτ σ hσ2 hσ1
  obtain ⟨hP0X, hP0⟩ := isPComponent_map_fixOf (hcβ σ) hPF hPp
  have hPc : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hQ2 : 2 ≤ r ^ e₀ := by omega
  have hbound : Nat.card (P.map e.toMonoidHom) * 2 ≤
      (r ^ e₀) ^ 2 * (((r ^ e₀) ^ 2) ^ 2 - 1) := by
    rcases psp4_fixed_cases hp hp2 he₀ hF (by omega) hσ₀2 hσ₀1 hP0X hP0 with
      ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, k, hk, hc⟩
    · rw [hc, mul_comm]
      exact sl_le_psl_sq hQ2
    · rw [hc]
      exact le_trans (by omega) (sl_le_psl_sq hQ2)
    · exact hc.le
    · rw [hc]
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0] at hk
          omega
        · exact h0
      exact psp_sqrt_le hk1 hk
  have hlt' := two_mul_psp4_sq_lt hq3
  rw [he₀2f, mul_comm 2 f, pow_mul] at hbound
  omega

theorem cf516SpRow :
    CF516SpRow := by
  intro S _ _ τ n r e hr hr2 hτ hadm hm
  subst hτ
  rcases (by have := hadm.2.2.1; omega : n = 2 ∨ 3 ≤ n) with rfl | hn
  · exact leafAt_psp4 hr hr2 hadm hm
  · intro hs hna _ σ P hP p f hp hp2 hf hPm t _ ht2 J hJC hJ hJm _ _ _ _ _ _
    have : IsSimpleGroup S := hs
    have hQ : FixedTwoComponentsQuasisimple S :=
      fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨.PSp, n, r, e, hr, hr2, hadm, hm⟩
    obtain ⟨hct, hJc, hJZ, hJm'⟩ := leaf_J_data hQ hna ht2 hJC hJ hJm
    have hrp : r = p := by
      rcases CatLeafProof.gls3OddFamilyInput_PSp_holds S n r e hr hr2 hadm hm _ hct _ hJc with
        ⟨τ', n', f', -, h⟩ | ⟨-, -, hnot, -⟩
      · exact char_eq_of_psl_two_sq hp hp2 hf hr2 hJm' h
      · exact absurd ⟨t, rfl⟩ hnot
    subst hrp
    exact psp_high_false hp hp2 hf hadm hn hm hct hJc hJZ hJm'

end CFSG.ComponentClassification.GSThmB
