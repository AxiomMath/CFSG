module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MBender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
  CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem noN1_Sz8 {Y : Type} [Group Y]
    (hY : LieModel Y .twistedB2 0 2 3) {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} :
    ¬ N1Config Y p b R₀ := by
  intro h
  have hS : SuzukiModel Y 2 3 := by
    rcases hY with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_szModel_equiv hS
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  let e' : Y ≃* CFSG.Open.Sz 1 := e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz 1))
  have hBT : BenderType Y 3 2 1 := .suzuki 1 le_rfl e
  have : IsSimpleGroup Y := hBT.isSimple
  have hL := isBenderGroup_of_mulEquiv_sz le_rfl e'
  have hp : p.Prime := h.1
  have hbo : orderOf b = p := h.2.2.1
  by_cases hp3 : p = 3
  · have hcard : Nat.card Y = 29120 := by rw [hBT.card_eq]; norm_num
    refine noN1_of_bender_coprime hL (center_eq_bot_of_fusionBenderBorel
      (fusionBenderBorel_of_mulEquiv_sz le_rfl e') (by norm_num) le_rfl) ?_ h
    rw [hcard, hp3]
    norm_num
  · have hO : Nat.card (Outer Y) ∣ 3 := hBT.outer_suzuki.2.1
    have hb : b ∈ innSub Y := by
      refine mem_innSub_of_pow_coprime (n := p) (hbo ▸ pow_orderOf_eq_one b) ?_
      exact Nat.Coprime.coprime_dvd_right hO
        ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    exact noN1_of_bender_inner (fusionBenderBorel_of_mulEquiv_sz le_rfl e')
      (by norm_num) le_rfl hL (card_sylow_of_mulEquiv_sz le_rfl e') hb h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
