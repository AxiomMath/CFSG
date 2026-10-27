module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)

theorem lemma123_of_inputs
    (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (h122 : Lemma122_i_iiStatement) (h1116 : Prop1116StrongStatement)
    (hI185 : Sec12a.Input18_5) (hI191 : Lemma136c.Input19_1_O2) (hI191img : Lemma123.Input19_1_O2_img)
    (hI22 : Input22_3_2) (hDiag : Lemma123.InputDiagBalance)
    (hI196 : Lemma123.Input19_6_4) (hI2317 : Lemma123.Input23_17)
    (hI1917a : Lemma123.Input19_17_1c) (hI234 : Lemma123.Input23_4) (hSchurAlt : Lemma123.InputSchurAlt')
    (hL27 : Prop1116.InputNotL27Pi)
    (hI1917s : Lemma123.Input19_17_2) (hI2324 : Lemma123.Input23_24) (hSchurFi : Lemma123.InputSchurFi22)
    (hCore : CFSG.LieType.ChevTwo.Chev2CoreCent) (hKD : CFSG.LieType.ChevTwo.Chev2KDOut)
    (hI1916 : Lemma123.Input19_16_two)
    (hI7L : Input7_L34)
    (hI197 : Lemma123.Input19_7_3) (hI1918 : Lemma123.Input19_18) (hI272 : Lemma123.Input27_2) :
    Lemma123Statement := by
  intro G _ _ m p B M E A a h
  obtain ⟨K, D, r, P⟩ := Lemma123.prep123 (prop111_of_prop112 h112) h122 h115 hI191 hI22 hDiag h
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  have hSec : Sec11 G m p B M E A := h.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hiv : Tof p M a ≤ Lstar p (Cg a) := Sec12a.tof_le_lstar_of_inputs h hp hp2 (h122 h).1 hI185
  have key : p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K)) ∧
      Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner p (E ⊓ A) K ∧
      ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
        ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut p K ⟨u, hu⟩) := by
    rcases Lemma123.type_trichotomy123 h P.hK with ⟨q, hq, hchev⟩ | ⟨n, hn5, hn⟩ | ⟨s, hs⟩
    · by_cases hqp : q = p
      · rw [hqp] at hchev
        exact (Lemma123.case_chevp h112 hI196 hI2317 P hchev).elim
      · by_cases hq2 : q = 2
        · rw [hq2] at hchev
          by_cases hr1 : r = 1
          · exact (Lemma123.case_chev2_one hI191img h122 (Lemma123.input19_20_1_of_chev2 hCore)
            (Lemma123.input7_12_2_of_chev2 hKD) P hr1 hchev).elim
          · exact Lemma123.case_chev2_ge2 h122 hI191img hI1916 hI7L P (by have := P.hr; omega) hchev
        · exact (Lemma123.case_chev_odd h112 h1116 hI191img h122 hI1918 hI197 hI272 P hq hq2 hqp hchev).elim
    · exact (Lemma123.case_alt h112 h115 h117 hI1917a hI234 hSchurAlt hL27 P hn5 hn).elim
    · exact (Lemma123.case_spor h112 h117 hI191img h122 hI1917s hI2324 hSchurFi P hs).elim
  obtain ⟨hp3, hL34, hcard9, hfaith, hu⟩ := key
  subst hp3
  refine ⟨rfl, K, P.hK, ⟨hL34, ?_⟩, hu, ⟨hcard9, hfaith⟩, hiv⟩
  intro hcov
  have hcore : GLAPPrimeCoreOf 3 (Cg a) ≤ M ⊓ Cg a :=
    le_inf ((prop111_of_prop112 h112) hSec ha ha1) (Subgroup.map_subtype_le _)
  exact P.hKM ((Lemma123.le_M_of_barX_le P.hK.1 hcov hcore).trans inf_le_left)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
