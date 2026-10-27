module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNG2Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.Ree (ReeTag)

open scoped commutatorElement

theorem kay_G2 :
    KAY FG2 := by
  refine kay_of_kaAll ?_
  intro Y _ _ hY _ α hα2 hα1
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hY
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_mulEquiv_target e CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    kn_conj_injective_of_center_bot hZ
  have hout : KAOutCyc Y ∧ ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y := by
    by_cases hp3 : p = 3
    · subst hp3
      have : CharP F ReeTag.G2.prime :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
      obtain ⟨-, -, ⟨Θ₀, -, -, hker₀⟩, -⟩ :=
        CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf F hcard
      obtain ⟨Θ, hΘ⟩ := kn_hom_of_mulEquiv e Θ₀ hker₀
      exact ⟨kaOutCyc_of_hom Θ hΘ, ka_hOut_of_hom Θ hΘ α⟩
    · obtain ⟨-, Θ₀, -, -, hker₀, -⟩ :=
        CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf F
          hcard .G2 (Or.inr ⟨rfl, hp3⟩)
      have : IsCyclic (F ≃+* F) :=
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hcard).2
      obtain ⟨Θ, hΘ⟩ := kn_hom_of_mulEquiv e Θ₀ hker₀
      exact ⟨kaOutCyc_of_hom Θ hΘ, ka_hOut_of_hom Θ hΘ α⟩
  have hNoP : KANoP α := by
    by_cases h3 : p = 3 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := h3
      exact kaNoP_of_fixOddFree (g2_three_fixOddFree hm α hα2 hα1)
    · have hq5 : 5 ≤ p ^ f := five_le_pow_of_ne_three_one hp hp2 hf h3
      by_cases hin : α ∈ innSub Y
      · have hadm : StatedLieAdmissible .G2 0 p f := ⟨hp, hf, rfl, by omega⟩
        obtain ⟨ψ⟩ := equiv_modelUniv_g2 hp hp2 hf (by omega) hm
        have hO : InvOddCore Y := invOddCore_of_equiv ψ
          (fun u hu2 hu1 N hN hNn hNodd =>
            CFSG.ClassicalInvolution.Asc77.thm5IH_g2_oddCoreTrivial hp2 hadm u hu2 hu1 N hN hNn
              hNodd)
        exact kaNoP_of_fixOddFree (fixOddFree_of_inner hZ hO hin hα2 hα1)
      · have hodd : Odd (Nat.card F) := by
          rw [hcard]
          exact (hp.odd_of_ne_two hp2).pow
        have h5 : 5 ≤ Nat.card F := by rw [hcard]; exact hq5
        have hα'2 : MulAut.congr e α ^ 2 = 1 := by
          rw [sq, ← map_mul, hα2, map_one]
        have hnot : MulAut.congr e α ∉
            (MulAut.conj : Ivk47ab.G2g F →* MulAut (Ivk47ab.G2g F)).range := by
          rintro ⟨g', hg'⟩
          apply hin
          refine kn_mem_innSub.2 ⟨e.symm g', (MulAut.congr e).injective ?_⟩
          rw [kn_congr_conj, e.apply_symm_apply]
          exact hg'
        have hfix : IsSimpleGroup ↥(fixSub (MulAut.congr e α)) ∧
            ∃ x y : ↥(fixSub (MulAut.congr e α)), x * y ≠ y * x :=
          kn_g2_outer_fixed hodd h5 hα'2 hnot
        obtain ⟨hs, x, y, hxy⟩ := hfix
        obtain ⟨eT⟩ := kn_fixSub_congr e α
        exact kaNoP_of_simple ((MulEquiv.isSimpleGroup_congr eT).2 hs)
          ⟨eT.symm x, eT.symm y,
            fun h => hxy (eT.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact ka_all_of_noP hinj hNoP hout.1 hout.2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
