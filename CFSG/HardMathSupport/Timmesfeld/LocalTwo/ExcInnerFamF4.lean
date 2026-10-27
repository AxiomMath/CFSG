module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamE

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false

theorem degCount_F4_ge_two {e : ℕ} (h : 2 ≤ degCount Tag.F4 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ degCount Tag.F4 e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_F4_pos_of_dvd_ordF4 {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (h : p ∣ ordF4 q) : 0 < degCount Tag.F4 (orderOf ((q : ℕ) : ZMod p)) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((q : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he]
  have key : ∀ d ∈ degreesW Tag.F4, p ∣ q ^ d - 1 → 0 < degCount Tag.F4 e := by
    intro d hd hdvd
    have hed : e ∣ d := (dvd_pow_sub_one_iff_orderOf hq he).1 hdvd
    exact List.length_pos_of_mem (List.mem_filter.2 ⟨hd, by simpa using hed⟩)
  unfold ordF4 at h
  simp only [hp.dvd_mul] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact absurd (hp.dvd_of_dvd_pow h) hpq
  · exact key 12 (by decide) h
  · exact key 8 (by decide) h
  · exact key 6 (by decide) h
  · exact key 2 (by decide) h



theorem crossCharTwoFamCat_F4_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (p : ℕ), p.Prime →
      7 ≤ p → p ≠ q.p → 2 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) →
      InnerPlaneBalance p (CatT ⟨.F4 q, hv⟩)) :
    CrossCharTwoFamCat .F4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have := hKc
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  have hin : InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
    by_cases h2 : 2 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · rw [← hK] at h2
      exact innerPlaneBalance_of_rankLE1 hp hinj (rankLE1_F4 K hp hpK (by omega))
  have hout : OuterFields p (adjointGroup Tag.F4 K) := by
    obtain ⟨Q, _, _, Θ, -, hker⟩ := exists_hom_cyclic_F4 q K hK
    refine outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx) ?_
    by_cases hdvd : p ∣ Nat.card (adjointGroup Tag.F4 K)
    · rw [card_adjointGroup_F4] at hdvd
      exact Or.inr fun x hxp hxo => fieldCoreAt_adjointF4 q.prime_p q.exponent_pos K hK' hp
        (by omega) (degCount_F4_pos_of_dvd_ordF4 hp Nat.card_pos hpK hdvd)
        (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
    · exact Or.inl (elemAbelian_card_eq_one_of_not_dvd hp hdvd)
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_F4_of_classes
    (h : ∀ e ∈ [1, 2, 3, 4, 6], InnerPlaneBalanceAt .F4 e) : CrossCharTwoFamCat .F4 := by
  refine crossCharTwoFamCat_F4_of_planes fun q hv p hp hp7 hpq h2 => ?_
  have := degCount_F4_ge_two h2
  rcases this with he | he | he | he | he <;>
    exact h _ (by simp) q hv p hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
