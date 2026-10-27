module

public import CFSG.ClassicalInvolution.Q3.Q3OFCov
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusThree
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusFour
public import CFSG.LieType.Steinberg.CentralExt.SpinOddThree
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeF4Multiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeMultiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeE7Multiplier
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Three
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3NTAlpha
public import CFSG.ClassicalInvolution.Q3.Q3OFAlg
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3TY1
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy CFSG.LieType.Universal
open scoped MatrixGroups

section Transport

theorem kindClosed3_of_equiv {c : CompData} {G' : Type} [Group G'] (e : c.G ≃* G')
    (h : ∀ (E : Type) [Group E] [Finite E] (π : E →* G'), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : G' →* E, ∀ x, π (σ x) = x) : KindClosed3 c := by
  intro E _ _ π hπ hcen
  have hπ' : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hπ
  have hcen' : (e.toMonoidHom.comp π).ker ≤ Subgroup.center E := by
    intro x hx
    apply hcen
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.injective (by simpa using hx)
  obtain ⟨σ, hσ⟩ := h E (e.toMonoidHom.comp π) hπ' hcen'
  exact ⟨σ.comp e.toMonoidHom, fun x => e.injective (hσ (e x))⟩

theorem closed_of_univ_eq {M : LieUniversal} {K' : Type} [Group K'] {D' : UniversalRootDatum K'}
    (hM : M = ⟨K', D'⟩)
    (h : ∀ (E : Type) [Group E] [Finite E] (π : E →* K'), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : K' →* E, ∀ x, π (σ x) = x) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* M.K), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : M.K →* E, ∀ x, π (σ x) = x := by
  subst hM
  exact h

end Transport

section Kinds

theorem kindClosed3_psu_odd {n : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n 3 1) (ho : ¬ Even n) :
    KindClosed3 (CompData.model .PSU n) := by
  refine kindClosed3_of_equiv (G' := CFSG.Assembly.LowTwoRank.StatedSU n (3 ^ 1) (GaloisField 3 2))
    (CFSG.LieType.Universal.Unitary.equivStatedSU (F := GaloisField 3 2) (p := 3) (f := 1)
      card_gf9 n) ?_
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
    card_gf9 le_rfl hadm.2.2.1 ho (by intro h; have := congrArg Prod.snd h; norm_num at this)
    hπ hcen

theorem kindClosed3_pomegaOdd {n : ℕ} (hn4 : 4 ≤ n) :
    KindClosed3 (CompData.model .POmegaOdd n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_three_exists_section_of_central
    (K := GaloisField 3 1) card_gf3 hn4 hπ hcen

theorem kindClosed3_pomegaPlus {n : ℕ} (hn4 : 4 ≤ n) :
    KindClosed3 (CompData.model .POmegaPlus n) := by
  have hn : 3 ≤ n := by omega
  refine closed_of_univ_eq (ModelFacts.modelUniv_POmegaPlus (n := n) (p := 3) (f := 1) hn) ?_
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_three_exists_section_of_central
    (K := GaloisField 3 1) hn card_gf3 hn4 hπ hcen

theorem kindClosed3_pomegaMinus {n : ℕ} (hn4 : 4 ≤ n) :
    KindClosed3 (CompData.model .POmegaMinus n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_three_exists_section_of_central'
    (minusCoeffs_irr 3 1) card_gf3 hn4 hπ hcen

theorem kindClosed3_f4 (n : ℕ) : KindClosed3 (CompData.model .F4 n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.FieldThree.f4_three_exists_section_of_central
    (K := GaloisField 3 1) card_gf3 hπ hcen

theorem kindClosed3_e8 (n : ℕ) : KindClosed3 (CompData.model .E8 n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.FieldThree.e8_three_exists_section_of_central
    (K := GaloisField 3 1) card_gf3 hπ hcen

theorem kindClosed3_e6 (n : ℕ) : KindClosed3 (CompData.model .E6 n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.FieldThree.e6_three_exists_section_of_central
    (K := GaloisField 3 1) card_gf3 hπ hcen

theorem kindClosed3_e7 (n : ℕ) : KindClosed3 (CompData.model .E7 n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.FieldThree.e7_three_exists_section_of_central
    (K := GaloisField 3 1) card_gf3 hπ hcen

theorem kindClosed3_twistedE6 (n : ℕ) : KindClosed3 (CompData.model .twistedE6 n) := by
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_three_exists_section_of_central
    (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) (card_gf9.trans (by norm_num))
    (fun c => by rw [CFSG.LieType.Steinberg.Exceptional.frobQ_apply, pow_one]) hπ hcen

end Kinds

end CFSG.ClassicalInvolution.Q3.Q3OF
