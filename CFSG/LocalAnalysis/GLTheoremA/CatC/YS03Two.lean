module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Core
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbAlt
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

section Alt


theorem ys03_strongBal_alt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hpn : p ∣ n) (h73 : ¬ (p = 3 ∧ n = 7)) {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* alternatingGroup (Fin n)) : StrongBalAt p S := by
  intro X _ _ K B hcore hcomp ⟨eK⟩ hB hBN
  haveI := hS
  haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hncK : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eK.symm a, eK.symm b, fun h => hab (eK.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hZK : Subgroup.center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hncK
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm)
  let eKZ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans (QuotientGroup.quotientBot.trans (eK.trans e))
  exact CFSG.HardMathSupport.Dickson.I271.Amb.altCore hp hp2 hcore hcomp hB hBN hn hn6 hpn h73 eKZ

end Alt

theorem ys03_card_mulAut_alt5 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

section TwoAlt


theorem ys03_two_alt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (hk : (p = 3 ∧ (n = 5 ∨ n = 9)) ∨ (p = 7 ∧ n = 7)) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* alternatingGroup (Fin n))
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcardS : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rcases hk with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · refine ys03_weak_of_card_le hp ?_
    have hcardAut : Nat.card (MulAut S) = 120 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact ys03_card_mulAut_alt5
    have hp3 : IsPGroup 3 A := isPGroup_of_isElemAbelian hA
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card A ∣ 120 := hcardAut ▸ Subgroup.card_subgroup_dvd_card A
    rw [hk] at hdvd ⊢
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> norm_num
    · exfalso
      have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk2
      have := h9.trans hdvd
      norm_num at this
  · refine ys03_weak_of_coreFree hp (fun x hx hx1 H hH hxH => ?_) hA
    exact ys03_coreFree_of_strongBal hS hnc hp (by rw [hcardS]; decide)
      (ys03_strongBal_alt hp hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hS hnc e)
      hx hH hxH
  · refine ys03_weak_of_coreFree hp (fun x hx hx1 H hH hxH => ?_) hA
    exact ys03_coreFree_of_strongBal hS hnc hp (by rw [hcardS]; decide)
      (ys03_strongBal_alt hp hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hS hnc e)
      hx hH hxH

end TwoAlt

end CFSG.LocalAnalysis.GLTheoremA
