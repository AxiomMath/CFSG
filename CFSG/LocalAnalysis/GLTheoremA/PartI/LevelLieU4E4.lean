module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E3
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
  (SU4 μ3 fieldFactor4 equivSU4 mem_range_conj_of_fieldFactor4_eq_one exists_isPrimitiveRoot_three)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)

theorem zetaU_ne_one (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : ((zetaU ζ hζ : μ3) : Kˣ) ≠ 1 := by
  intro h
  have h' : ζ = 1 := by
    have := congrArg Units.val h
    rw [zetaU_val] at this
    simpa using this
  exact hζ.ne_one (by norm_num) h'

theorem zetaU_sq_ne_one (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ((zetaU ζ hζ ^ 2 : μ3) : Kˣ) ≠ 1 := by
  intro h
  have h2 : ζ ^ 2 = 1 := by
    have := congrArg Units.val h
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, zetaU_val] at this
    simpa using this
  apply hζ.ne_one (by norm_num)
  linear_combination hζ.pow_eq_one - ζ * h2

theorem goodCent_of_pow_three (hk : kLevel 3 SU4 ≤ 2)
    (hc : ∀ (ζ : K) (hζ : IsPrimitiveRoot ζ 3), GoodCent (c022 ζ hζ)) (s : SU4) (hs : s ^ 3 = 1) :
    GoodCent s := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  obtain ⟨h, hcases⟩ := normal_form s hs ζ hζ
  apply goodCent_of_conj h s
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · rw [h1]
    exact goodCent_one hk
  · rw [h2]
    exact goodCent_yStd _ (zetaU_ne_one ζ hζ)
  · rw [h3]
    exact goodCent_yStd _ (zetaU_sq_ne_one ζ hζ)
  · rw [h4]
    exact goodCent_c211 ζ hζ
  · rw [h5]
    exact hc ζ hζ

theorem catalogIs_of_mulEquiv_left {S T : Type} [Group S] [Group T] (e : S ≃* T) {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs T Q) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem downLe_SU4 (hk : kLevel 3 SU4 ≤ 2)
    (hc : ∀ (ζ : K) (hζ : IsPrimitiveRoot ζ 3), GoodCent (c022 ζ hζ)) : DownLe 3 2 SU4 := by
  intro α hα I hI
  by_cases hf : fieldFactor4 α = 1
  · obtain ⟨s, rfl⟩ := mem_range_conj_of_fieldFactor4_eq_one hf
    have hs : s ^ 3 = 1 := by
      have h3 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact hα
      have hz : s ^ 3 ∈ Subgroup.center SU4 := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut SU4 => φ g) h3
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.center_SU4, Subgroup.mem_bot] at hz
      exact hz
    exact goodCent_of_pow_three hk hc s hs I (by rw [CFSG.LocalAnalysis.GLTheoremA.LevelLieU.fixSubgroup_conj_eq] at hI; exact hI)
  ·
    obtain ⟨hcat, hcard⟩ := catalogIs_fixSub hα hf
    have hH : fixSubgroup α = CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α := by
      ext x
      exact Iff.rfl
    rw [hH] at hI
    have hsimp : IsSimpleGroup ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) :=
      CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two hcat
    haveI := hsimp
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hI.2.1 hsimp with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · rw [h]
      have hnc : ¬ IsMulCommutative ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) := by
        intro hcomm
        have hp := (Group.is_simple_iff_prime_card
          (α := ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α))).mp hsimp
        rw [hcard] at hp
        norm_num at hp
      obtain ⟨e⟩ := pSimple_equiv_of_simple (CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) hnc
        (by rw [hcard]; norm_num)
      rw [CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 e]
      exact CFSG.LocalAnalysis.GLTheoremA.LevelLieU.kLevel_le_two_of_chev
        (Or.inr (CFSG.LocalAnalysis.GLTheoremA.LevelLieU.catalog_ambiguous_of_u4two hcat))

theorem kdLieRowU4Eight_of_c022
    (hc : ∀ (ζ : K) (hζ : IsPrimitiveRoot ζ 3), GoodCent (c022 ζ hζ)) : KDLieRowU4Eight := by
  intro q hv hq
  have hcatU : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group
      S9.isU4eight :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩, show q.card = 8 from hq,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e0⟩ := bridge_u4eight hcatU
  let eS : SU4 ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group :=
    equivSU4.symm.trans e0.symm
  have hk2 : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group
      (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩,
      show (3 : ℕ) = 3 ∧ q.card = 8 from ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  have hk : kLevel 3 SU4 ≤ 2 :=
    CFSG.LocalAnalysis.GLTheoremA.LevelLieU.kLevel_le_two_of_k2 (catalogIs_of_mulEquiv_left eS hk2)
  exact downLe_of_mulEquiv eS (downLe_SU4 hk hc)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
