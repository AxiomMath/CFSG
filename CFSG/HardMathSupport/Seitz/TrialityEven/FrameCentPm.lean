module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ThreeLiftProved

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KEXC
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Seitz.TrialityOdd
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator


variable {L : Type} [Field L] {G : Type} [Group G] {ι : G →* ModGL TwistTag.D4.tag L}
  {g0 : ModGL TwistTag.D4.tag L}

theorem exists_centralizer_le_of_frameTuples_pm [IsAlgClosed L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hι : Function.Injective ι)
    (hιC : ∀ g, ι g ∈ adjointGroup TwistTag.D4.tag L) (hg0 : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hL3 : ringChar L ≠ 3) {Fr : L →+* L} {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hEtor : ∀ x ∈ E, ∃ b ∈ fixedCharTuples (d4T36M ε) Fr,
      rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι x * g0)
    {r' : ℕ} (hr' : r'.Prime) (hr'5 : 5 ≤ r') (hr'L : ringChar L ≠ r') {y : G} (hy1 : y ≠ 1)
    (hyr : y ^ r' = 1) {by' : Fin TwistTag.D4.tag.rank → Lˣ}
    (hbyF : by' ∈ fixedCharTuples (d4T36M ε) Fr)
    (hby : rootDiagUnit TwistTag.D4.tag by' = g0⁻¹ * ι y * g0) :
    ∃ x ∈ E, x ≠ 1 ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  have : Fact r'.Prime := ⟨hr'⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) x.2)
  have hE9 : Nat.card E = 9 := by rw [hEcard]; norm_num
  have hordy : orderOf (rootDiagUnit TwistTag.D4.tag by') = r' := by
    rw [hby, orderOf_conj_apply hι, orderOf_eq_prime hyr hy1]
  have hby1 : by' ≠ 1 := ne_one_of_orderOf_rootDiagUnit hr' hordy
  obtain ⟨β, hβ⟩ := exists_tupleHom_of_forall
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp E.subtype)) fun x => by
      obtain ⟨b, -, hb⟩ := hEtor x x.2
      exact ⟨b, by rw [hb]; simp⟩
  have hβx : ∀ x : E, rootDiagUnit TwistTag.D4.tag (β x) = g0⁻¹ * ι x * g0 := fun x => by
    rw [hβ]
    simp
  have hβF : ∀ x : E, β x ∈ fixedCharTuples (d4T36M ε) Fr := fun x => by
    obtain ⟨b, hbF, hb⟩ := hEtor x x.2
    have : b = β x := CFSG.LieType.Chevalley.rootDiagUnit_injective (hb.trans (hβx x).symm)
    exact this ▸ hbF
  have hβord : ∀ x : E, x ≠ 1 → orderOf (rootDiagUnit TwistTag.D4.tag (β x)) = 3 := fun x hx => by
    rw [hβx, orderOf_conj_apply hι]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) x.2)
      fun h => hx (Subtype.ext h)
  rcases d4T36_rootCharKernel_cases hε hbyF hby1 with hker | ⟨i, hi⟩
  ·
    obtain ⟨x, hx1, -⟩ := exists_ne_one_map_eq_one_of_card_nine (L := L) hE9 hE3 1
    have hbp : rootDiagUnit Tag.D4 by' ^ r' = 1 := by
      have := pow_orderOf_eq_one (rootDiagUnit TwistTag.D4.tag by')
      rwa [hordy] at this
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), centralizer_le_of_rootCharKernel_empty hι hιC hg0
      (hβx x) hby hker (Proving.stab_one_of_rootDiagUnit_pow hr' hr'5 hbp hker)⟩
  ·
    have hα : trialityU i ∈ rootCharKernel by' := by
      rw [hi]
      exact ⟨0, by norm_num, Or.inl (by rw [pow_zero, Matrix.one_mulVec])⟩
    obtain ⟨x, hx1, hxα⟩ := exists_ne_one_map_eq_one_of_card_nine (L := L) hE9 hE3
      ((MonoidHom.mk' (fun a => FourGroupChevalley.rootChar a (trialityU i))
        fun a b => CTTorus.rootChar_mul a b _).comp β)
    have hordx := hβord x hx1
    have hbx1 : β x ≠ 1 := ne_one_of_orderOf_rootDiagUnit Nat.prime_three hordx
    have hαx : trialityU i ∈ rootCharKernel (β x) := ⟨hα.1, hxα⟩
    have hix : rootCharKernel (β x) = trialitySigma i := by
      rcases d4T36_rootCharKernel_cases hε (hβF x) hbx1 with h | ⟨j, hj⟩
      · rw [h] at hαx
        exact absurd hαx (Set.notMem_empty _)
      · rcases eq_or_ne i j with rfl | hij
        · exact hj
        · exfalso
          rw [hi] at hα
          rw [hj] at hαx
          exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hij) hα hαx
    obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
        (fun α : Fin Tag.D4.rank → ℤ => v • α) '' d4A2Sigma = trialitySigma i := by
      obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
      obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
      exact ⟨w, by rw [d4A2Sigma_eq_trialityStdA2, ← hw]⟩
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), centralizer_le_of_rootCharKernel_eq hι hιC hg0
      (hβx x) hby Nat.prime_three (by norm_num) hL3 hr' (by omega) hr'L hordx hordy
      (hix.trans hv.symm) (hi.trans hv.symm)⟩

end CFSG.HardMathSupport.Seitz.TrialityEven
