module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueVert
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGLS3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P8

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_of_psp43 {X : Type} [Group X] (h : Blueprint.LieModel X .PSp 2 3 1) :
    Nat.card X = 25920 := by
  rw [GH74.card_of_lieModel_PSp (by norm_num) (by norm_num) h]
  decide

theorem factorial_div_two_ne (m : ℕ) : m.factorial / 2 ≠ 25920 := by
  rcases Nat.lt_or_ge m 9 with h | h
  · interval_cases m <;> decide
  · have h1 : (9 : ℕ).factorial ≤ m.factorial := Nat.factorial_le h
    have h2 : (9 : ℕ).factorial = 362880 := by decide
    omega

variable {Y : Type} [Group Y] [Finite Y]

theorem isSimpleChevalleyOver_three_of_fixed
    (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y)) (hY : TypC Y) (β : MulAut Y)
    (hβ : ∀ y, β (β y) = y) {T : Subgroup Y} (hTC : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β)))
    (hTL : Blueprint.LieModel (↥T ⧸ Open.fusionZStar ↥T) .PSp 2 3 1) :
    HarrisLit.IsSimpleChevalleyOver 3 (Y ⧸ Open.fusionZStar Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (pPrimeCore 2 ↥T).index ≤ (pPrimeCore 2 Y).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.le_of_dvd Nat.card_pos (Residue.card_quot_dvd T)
  rcases hle.lt_or_eq with hlt | heq
  swap
  ·
    obtain ⟨e⟩ := Residue.nonempty_quot_equiv_of_map_eq_top (Residue.map_eq_top_of_index_eq heq)
    exact ⟨.PSp, 2, 1, Blueprint.LieModel.of_mulEquiv (Sol78.fusionZStarQuotOfCore e) hTL⟩
  obtain ⟨σ, -, hσ, hPF, hP, hPne, ⟨eP⟩⟩ :=
    GrSLit.exists_simple_fixed_component_image hYq β hβ hTC hT hlt
  haveI hS : IsSimpleGroup ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := hYq.2.1
  have hPFC : CatLeaf.ProperFixedComponent σ _ := ⟨hσ, hPF, hP, hPne⟩
  have hPL := Blueprint.LieModel.of_mulEquiv eP hTL
  rcases hY with hodd | ⟨n, hn, -, -, ⟨θ⟩⟩ | ⟨hL, -⟩
  ·
    obtain ⟨τ, m, p, f, hp, hp2, hadm, hm⟩ := hodd
    have hmS := Blueprint.LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv Y).symm hm
    have hσ1 : σ ≠ 1 := hPFC.ne_one
    have hσσ : σ * σ = 1 := by
      ext y
      rw [MulAut.mul_apply, hσ, MulAut.one_apply]
    have hq := CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hYq.2.2
      ⟨τ, m, p, f, hp, hp2, hadm, hmS⟩ σ hσσ hσ1 _ hP
    obtain ⟨hcomp, ⟨eK⟩⟩ := hPFC.fusionZStar_equiv_of_quasisimple hq
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
    have hp3 : p = 3 := by
      rcases GrSLit.gls3OddLieAutComponentsInput_holds _ τ m p f hp hp2 hadm hmS σ hσ2 _ hcomp
        with ⟨τ', n', f', -, hm'⟩ | ⟨hp3, -, -, -⟩
      · exact (oddLieCharUnique_holds _ .PSp 2 3 1 τ' n' p f' (by norm_num) hp2
          (Blueprint.LieModel.of_mulEquiv eK hPL) hm').symm
      · exact hp3
    subst hp3
    exact ⟨τ, m, f, hm⟩
  ·
    exfalso
    obtain ⟨h', ⟨e⟩⟩ := hPFC.map θ
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ :=
      CatLeaf.isAltType_of_properFixedComponent_alternating (by omega) (by omega) h'
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 := Nat.card_congr (e.trans eA).toEquiv
    rw [card_of_psp43 hPL, nat_card_alternatingGroup] at h1
    exact factorial_div_two_ne _ h1.symm
  ·
    exfalso
    rcases GrSLit.simpleFixedComponents_l34 _ hS hYq.2.2 hL σ hσ _ hPF hP hPne with h | h
    · have h5 := oddLieCharUnique_holds _ .PSp 2 3 1 .PSL 2 5 1 (by norm_num) (by norm_num) hPL h
      omega
    · have h7 := oddLieCharUnique_holds _ .PSp 2 3 1 .PSL 2 7 1 (by norm_num) (by norm_num) hPL h
      omega

end CFSG.ComponentClassification.GS82PumpInputs.P8

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

theorem spFourThreeCentralPumpInput_of_typPump
    (hP : TypPumpInput) : SpFourThreeCentralPumpInput := by
  intro H _ _ hH M hM x hx hxN T hTM hTC hTpc hTL w hw hwT hwZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hT'C, hT'p⟩ := Residue.exists_conj_mulAut hx hxN hTM hTC hTpc
  obtain ⟨hZM, hZT⟩ := Residue.center_ne_bot_of_mem hTM hw hwT hwZ
  obtain ⟨eT⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hTM).symm
  have hTL' := Blueprint.LieModel.of_mulEquiv eT hTL
  have hTC' : TypC ↥(T.subgroupOf M) :=
    Or.inl ⟨.PSp, 2, 3, 1, by norm_num, by norm_num, hTL'.admissible, hTL'⟩
  have hMq2 : HarrisLit.IsTwoQuasisimple ↥M :=
    ((HarrisLit.isTwoComponent_iff_isPComponent M).mpr hM).2
  exact P8.isSimpleChevalleyOver_three_of_fixed hMq2.2
    (hP ↥M (hH.subgroup M) hMq2 hZM c hc _ hT'C hT'p hZT hTC') c hc hT'C hT'p hTL'

end CFSG.ComponentClassification.GS82PumpInputs
