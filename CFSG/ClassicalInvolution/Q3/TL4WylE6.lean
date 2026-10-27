module

public import CFSG.ClassicalInvolution.Q3.TL4WylE
public import CFSG.ClassicalInvolution.Q3.TL4SecClqLie
public import CFSG.ClassicalInvolution.Q3.Q3T8P26P01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26P02
public import CFSG.ClassicalInvolution.Asc77.AscC22N5
public import CFSG.ClassicalInvolution.Asc77.AscC5O12
public import CFSG.ClassicalInvolution.Asc77.AscC5OM21
public import CFSG.ClassicalInvolution.Asc77.AscCX9Y
public import CFSG.ClassicalInvolution.Asc77.AscS24BHEnd
public import CFSG.ClassicalInvolution.Asc77.AscT8ZB3
public import CFSG.ClassicalInvolution.Asc77.AscT8ZC7
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign
public import CFSG.ClassicalInvolution.Balance.CentralizedDeltaBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.Q3AMBadFin
public import CFSG.ClassicalInvolution.Q3.Q3AMBadStand
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.Q3.Q3ExD
public import CFSG.ClassicalInvolution.Q3.Q3IntrSat
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DAEmpty
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Plug
public import CFSG.ClassicalInvolution.Q3.Q3T6DVFinal
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenProved
public import CFSG.ClassicalInvolution.Q3.Q3T7Assembly
public import CFSG.ClassicalInvolution.Q3.Q3T7ExitD4Phan
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2215
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Fin2
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22M11Proof
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Chain
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Fin2
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Res
public import CFSG.ClassicalInvolution.Q3.Q3T8B01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26Top
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4SecIdFam
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.Q3.TL4WylD7
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.GH74.BNPair.Defs
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform

theorem Wyl.isUniqueInvolution_of_le {X : Type} [Group X] [Finite X] {Λ : Set (Subgroup X)}
    (hΛ : HypOmegaGen Λ) {N J : Subgroup X} (hN : N ∈ Λ) (hJN : J ≤ N) {u : X}
    (hu : IsUniqueInvolution J u) : IsUniqueInvolution N u := by
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΛ hN
  rcases hw.unique u (hJN hu.mem) hu.sq with h | h
  · exact absurd h hu.ne_one
  · rw [h]
    exact hw

section Cit3


theorem secIdLieFrame_proved : SecIdLieFrame := by
  classical
  intro n hA hP Y _ _ hn R S t hd hc hl hnc B₁ hB₁ B₂ hB₂ hB₂K
  have hΩ := hd.hypOmegaGen
  have h2 := hl.isPGroup_members hc.2.2
  have hlifts := hl.hasLifts hd
  have hex := hl.exactSylow hc.2.2
  obtain ⟨hΦ, hgen, hAE⟩ := hl.liftFam_hyp hd hc
  have hΦg : HypOmegaGen (liftFam (CoreAssembly.conjClass (tightCore R))) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  let T : Fin 3 → Subgroup Y := ![tightCore R, B₁, B₂]
  have hT : ∀ i, T i ∈ CoreAssembly.conjClass (tightCore R) := by
    intro i
    fin_cases i
    · exact hK
    · exact hB₁.1
    · exact hB₂K.1
  have hTadj : ∀ i j, i ≠ j → T j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (T i) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hB₁
    · exact hB₂K
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hB₁.1 hB₁
    · exact absurd rfl hij
    · exact hB₂
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hB₂K.1 hB₂K
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hB₁.1 hB₂K.1 hB₂
    · exact absurd rfl hij
  have hTinj : Function.Injective T := by
    intro i j hij
    by_contra hne
    exact (hTadj i j hne).2.1 hij.symm
  obtain ⟨Mt, hMt, hTM, hMinj, hMadj⟩ := exists_lift_clique hΩ h2 hlifts hex T hT hTinj hTadj
  have hncΛ : ¬ DConnected (liftFam (CoreAssembly.conjClass (tightCore R))) := fun h =>
    hnc (dConnected_of_liftFam hΩ h2 hlifts hex h)
  have hcit : CITBelowT (.sl2 3 1) n := (citBelowT_three_iff (by norm_num) n).mpr hA
  obtain ⟨e, ⟨M⟩⟩ := Q3T8.Asc77.T8X.exists_spin8_datum_of_triangle
    (Disc3.ih8T_three_proved n hcit) hcit hn hΦ hc.2.2 hgen hAE Mt hMt hMinj hMadj hncΛ
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = 1 := M.exp_eq_f hD4
  subst he
  have hF := Q3T8.Asc77.T8ZZ.plusModelFacts
  have hne : (liftFam (CoreAssembly.conjClass (tightCore R))).Nonempty := ⟨_, hMt 0⟩
  obtain ⟨R₀, hR₀, hN₀⟩ := (M.mem_iff _).mp (hMt 0)
  have hK₀N : tightCore R ≤ R₀.map M.ψ := hN₀ ▸ hTM 0
  have hN₀Λ : R₀.map M.ψ ∈ liftFam (CoreAssembly.conjClass (tightCore R)) := M.map_mem hR₀
  have hnbrΛ : ∀ {N J : Subgroup Y}, N ∈ liftFam (CoreAssembly.conjClass (tightCore R)) →
      J ∈ CoreAssembly.conjClass (tightCore R) → J ≤ N →
        (J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ↔
          N ∈ omegaNbr (liftFam (CoreAssembly.conjClass (tightCore R))) (R₀.map M.ψ)) :=
    fun hN hJ hJN => (hex.mem_omegaNbr_liftFam_iff hΩ h2 hlifts hN₀Λ hK hK₀N hN hJ hJN).symm
  refine ⟨fun B hB v hv => ?_, ?_⟩
  ·
    obtain ⟨L, u, h⟩ := hlifts B hB.1
    have hNB := satU_mem_liftFam hB.1 h
    obtain ⟨RB, hRB, hNBe⟩ := (M.mem_iff _).mp hNB
    have hadj := (hnbrΛ hNB hB.1 h.le_sat).mp hB
    rw [hNBe] at hadj
    have hcomm := ((Q3MT.omegaNbr_iff3 M hΦ hG2 hD4 hR₀ hRB).mp hadj).2
    have ht0 : IsUniqueInvolution (R₀.map M.ψ) t :=
      Wyl.isUniqueInvolution_of_le hΦg hN₀Λ hK₀N hd.isUniqueInvolution_core
    have hvB : IsUniqueInvolution (RB.map M.ψ) v := by
      have := Wyl.isUniqueInvolution_of_le hΦg hNB h.le_sat hv
      rwa [hNBe] at this
    obtain ⟨ζ₀, hζ₀, hψ₀⟩ := T8ZZ.datum_exists_involution_lift M hF hR₀ ht0
    obtain ⟨ζB, hζB, hψB⟩ := T8ZZ.datum_exists_involution_lift M hF hRB hvB
    have hcen := T8ZZ.datum_mul_mem_center M hF hR₀ hRB hcomm hζ₀ hζB
    rwa [hψ₀, hψB] at hcen
  ·
    obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n02, n03, n04, n23, n24, n34, c02, c03, c04, -, -, -, hall⟩ :=
      Q3MT.clique_plus3 (M.cls_sub hR₀)
    have m₂ := M.fund_subset_cls hne hG2 hD4 h₂
    have m₃ := M.fund_subset_cls hne hG2 hD4 h₃
    have m₄ := M.fund_subset_cls hne hG2 hD4 h₄
    have hcore : ∀ {Rj}, Rj ∈ M.cls → R₀ ≠ Rj → Commutes R₀ Rj →
        ∃ C ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), C ≤ Rj.map M.ψ := by
      intro Rj hRj hn hc'
      obtain ⟨C, hC, hCN⟩ := exists_core_of_mem_liftFam (M.map_mem hRj)
      exact ⟨C, (hnbrΛ (M.map_mem hRj) hC hCN).mpr
        ((Q3MT.omegaNbr_iff3 M hΦ hG2 hD4 hR₀ hRj).mpr ⟨hn, hc'⟩), hCN⟩
    obtain ⟨C₂, hC₂, hC₂N⟩ := hcore m₂ n02 c02
    obtain ⟨C₃, hC₃, hC₃N⟩ := hcore m₃ n03 c03
    obtain ⟨C₄, hC₄, hC₄N⟩ := hcore m₄ n04 c04
    have hdist : ∀ {Rj Rk C C' : Subgroup _}, Rj ∈ M.cls → Rk ∈ M.cls → Rj ≠ Rk →
        C ∈ CoreAssembly.conjClass (tightCore R) → C ≤ Rj.map M.ψ → C' ≤ Rk.map M.ψ →
          C ≠ C' := by
      intro Rj Rk C C' hRj hRk hjk hC hCj hC'k e
      subst e
      have hCs : IsSylow2In C C := ⟨le_rfl, h2 C hC, fun V' hV' _ hle => le_antisymm hV' hle⟩
      have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hC hCs)
      have heq := Sec6Gen.eq_of_le_of_le hΦg (M.map_mem hRj) (M.map_mem hRk) (h2 C hC)
        (by omega) hCj hC'k
      exact hjk (Q3MT.map_inj3 M hG2 hD4 hRj hRk heq)
    have hall' : omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        {C₂, C₃, C₄} := by
      ext C
      refine ⟨fun hC => ?_, fun hC => ?_⟩
      · obtain ⟨L, u, h⟩ := hlifts C hC.1
        have hNC := satU_mem_liftFam hC.1 h
        obtain ⟨R', hR', hNCe⟩ := (M.mem_iff _).mp hNC
        have hadj := (hnbrΛ hNC hC.1 h.le_sat).mp hC
        rw [hNCe] at hadj
        obtain ⟨hn', hc'⟩ := (Q3MT.omegaNbr_iff3 M hΦ hG2 hD4 hR₀ hR').mp hadj
        have hCR' : C ≤ R'.map M.ψ := hNCe ▸ h.le_sat
        rcases hall R' (M.cls_sub hR') (Ne.symm hn') hc' with rfl | rfl | rfl
        · exact Or.inl (hex.core_unique hΩ h2 (M.map_mem m₂) hC.1 hC₂.1 hCR' hC₂N)
        · exact Or.inr (Or.inl (hex.core_unique hΩ h2 (M.map_mem m₃) hC.1 hC₃.1 hCR' hC₃N))
        · exact Or.inr (Or.inr (hex.core_unique hΩ h2 (M.map_mem m₄) hC.1 hC₄.1 hCR' hC₄N))
      · rcases hC with rfl | rfl | rfl
        · exact hC₂
        · exact hC₃
        · exact hC₄
    rw [hall']
    exact Set.ncard_eq_three.mpr ⟨C₂, C₃, C₄, hdist m₂ m₃ n23 hC₂.1 hC₂N hC₃N,
      hdist m₂ m₄ n24 hC₂.1 hC₂N hC₄N, hdist m₃ m₄ n34 hC₃.1 hC₃N hC₄N, rfl⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
