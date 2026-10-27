module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

theorem factorial_div_two_ne_D42_card {m : ℕ} :
    Nat.factorial m / 2 ≠ 174182400 := by
  by_cases h : m ≤ 11
  · have h1 : Nat.factorial m ≤ Nat.factorial 11 := Nat.factorial_le h
    have h2 : Nat.factorial m / 2 ≤ Nat.factorial 11 / 2 := Nat.div_le_div_right h1
    have h3 : Nat.factorial 11 / 2 = 19958400 := by norm_num [Nat.factorial]
    omega
  · have h1 : Nat.factorial 12 ≤ Nat.factorial m := Nat.factorial_le (by omega)
    have h2 : Nat.factorial 12 / 2 ≤ Nat.factorial m / 2 := Nat.div_le_div_right h1
    have h3 : Nat.factorial 12 / 2 = 239500800 := by norm_num [Nat.factorial]
    omega

theorem not_isD42Type_of_isAltType {K : Type} [Group K] [Finite K]
    (h : CFSG.ComponentClassification.CatLeaf.IsAltType K) :
    ¬ IsCatalogLieIso K IsD42Index := by
  intro hD42
  obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := h
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcardK : Nat.card K = 174182400 := card_of_isD42Type hD42
  have hcardA : Nat.card K = (Fintype.card Ω).factorial / 2 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  rw [hcardA] at hcardK
  exact factorial_div_two_ne_D42_card hcardK

theorem upD42AltLeaf_holds : UpD42AltLeaf := by
  intro S _ _ n hn ⟨e⟩ α hpump
  obtain ⟨hα3, hα1, I, hI, hI42⟩ := hpump
  let ψ : MulAut (alternatingGroup (Fin n)) := MulAut.congr e α
  have hψ3 : ψ ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hψ1 : ψ ≠ 1 := by
    intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  have hker : (e : S →* alternatingGroup (Fin n)).ker ≤ Subgroup.center S := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨A, hA, hAT⟩ := isD42Type_barOf_of_central (e : S →* alternatingGroup (Fin n))
    e.surjective hker α ψ (fun y => by simp [ψ, MulAut.congr_apply]) hI hI42
  obtain ⟨m, hm5, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn Nat.prime_three (by decide) ψ hψ3 hψ1 A hA
  obtain ⟨hsimp, hnab⟩ := isSimpleGroup_of_isD42Type hAT
  have hcen : Subgroup.center (barOf 3 A) = ⊥ := up34_center_eq_bot_of_simple hnab
  let e2 : PSimple 3 A ≃* barOf 3 A :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hAlt' : CFSG.ComponentClassification.CatLeaf.IsAltType (barOf 3 A) :=
    ⟨Fin m, inferInstance, inferInstance, by simpa using (le_trans (le_max_left 5 3) hm5),
      ⟨e2.symm.trans f⟩⟩
  exact not_isD42Type_of_isAltType hAlt' hAT

end CFSG.HardMathSupport.Dickson.Sec6

end
