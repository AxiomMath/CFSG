module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightLin
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL2
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightBT

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem three_eight_natSL_block [Finite Γ] (hmult : SL2EvenMultiplierTrivial)
    (hn2 : PushUpPerfectTwo) {G T V : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowTwoOf T G)
    (hne : cStarIn G T ≠ G) (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVT : omegaOneCenterOf T ≤ V) (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G)) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNatSL G V n) :
    ∃ E : Subgroup Γ, IsBTBlock G T E ∧
      G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ∧
      ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V := by
  classical
  obtain ⟨α, β, hαs, hαk, hβs, hβk, hβe⟩ := hnat
  rw [Subgroup.inf_subgroupOf_left] at hαk
  rw [Subgroup.inf_subgroupOf_left] at hβk
  have hβe' : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (β v)) := by
    intro g v v' hv'
    have hw : (g : Γ) * v * (g : Γ)⁻¹ ∈ V := hv' ▸ v'.2
    have h1 : v' = ⟨(g : Γ) * v * (g : Γ)⁻¹, hw⟩ := Subtype.ext hv'
    rw [h1, hβe g v hw]
    rfl
  obtain ⟨E, P', hP'G, hBP', hVP', hSyl, hmin, hcharP, hαP', hnc, hTSC, hJS, hEeq, hchi, hnex,
    hcomm2, hEY, hnotC, hGfin⟩ :=
    three_eight_linear_ext hG hT hne hVn hVT hVQ α hαs hαk β hβs hβe' hβk
  obtain ⟨n', hn', hcard, hlin, halt⟩ := hnex
  have hnn : n' = n := by
    have h1 : (2 : ℕ) ^ n' = 2 ^ n := by
      rw [← hcard]
      have : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      exact this
    exact Nat.pow_right_injective (le_refl 2) h1
  subst hnn
  have hshort : IsShort2 E := hchi.1.1
  refine ⟨E, ?_, hGfin, hEY⟩
  rcases Nat.lt_or_ge n' 2 with hlt | hge
  ·
    have hn1 : n' = 1 := by omega
    exact (isBTBlock_of_alt_three hP'G hmin hEeq hshort (halt hn1) hnotC).1
  · have hlin' : IsLin2Type E n' := hlin (by omega)
    have hGF : IsLin2TypeGF E n' := isLin2TypeGF_of_isLin2Type (by omega) hlin'
    have hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E := by
      rcases Nat.lt_or_ge n' 3 with h2 | h3
      · have h22 : n' = 2 := by omega
        subst hEeq
        subst h22
        exact hn2 Γ G T V P' α β hG hT hne hVn hVT hVQ hαs hαk hβs hβe' hβk hP'G hBP' hVP' hSyl
          hmin hcharP hαP' hnc hTSC hJS hchi hlin'
      · exact perfect_of_isLin2TypeGF hmult h3 hshort hGF
    have hcomm : ⁅E, baum T⁆ = E := by
      obtain ⟨α', hα's, hα'k, -⟩ := hGF
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n')) :=
        isSimpleGroup_sl2_galoisField hge
      exact commutator_eq_of_isShort2 hmin hEeq hshort α' hα's hα'k
    have hEG : E ≤ G := by
      rw [hEeq]
      exact (twoResidual_le P').trans hP'G
    exact isBTBlock_of_short hEG hshort hperf hcomm
      (Or.inl ⟨n', hge, isNaturalSLTwoModule_of_isLin2TypeGF hGF⟩) hnotC

end CFSG.CGT.PushingUpLit.BHS6
