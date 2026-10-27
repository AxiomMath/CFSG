module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeModelDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

theorem I294Large.exists_sylow_not_comm_of_mulEquiv {r : ℕ} (hr : r.Prime) {L M : Type} [Group L]
    [Finite L] [Group M] [Finite M] (e : L ≃* M)
    (hS : ∃ S : Sylow r L, ¬ IsMulCommutative (S : Subgroup L)) :
    ∃ S : Sylow r M, ¬ IsMulCommutative (S : Subgroup M) := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨S, hS'⟩ := hS
  exact hS' (WeakClosureHeis.sylow_comm_of_surjective e.symm.toMonoidHom e.symm.surjective
    (fun T => hcon T) S)

theorem I294Large.rank_of_classical_model
    (hL : I294LargeModelPSL) (hU : I294LargeModelPSU) (hSp : I294LargeModelPSp)
    (hOo : I294LargeModelPOmegaOdd) (hOp : I294LargeModelPOmegaPlus)
    (hOm : I294LargeModelPOmegaMinus) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    {L : Type} [Group L] [Finite L] {t : StatedLieTag} {n p f : ℕ}
    (hm : StatedClassicalModel L t n p f) (hrp : r ≠ p) (hLU : ¬ IsLinearOrUnitaryAt r L)
    (hS : ∃ S : Sylow r L, ¬ IsMulCommutative (S : Subgroup L)) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  obtain ⟨hadm, hrest⟩ := id hm
  obtain ⟨hp, hf, hadm⟩ := hadm
  have hrq : ¬ r ∣ p ^ f := fun h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  cases t with
  | PSL =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hrK : ¬ r ∣ Nat.card K := by rw [hK]; exact hrq
    have hLU' : ¬ (r ∣ n ∧ r ∣ Nat.card K - 1) := fun h => hLU (Or.inl
      ⟨n, K, inferInstance, inferInstance, h.1, h.2, ⟨e⟩⟩)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hL r hr h5 K hrK n hLU' (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | PSU =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hLU' : ¬ (r ∣ n ∧ r ∣ p ^ f + 1) := fun h => hLU (Or.inr
      ⟨n, p ^ f, K, inferInstance, inferInstance, hK, h.1, h.2, ⟨e⟩⟩)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hU r hr h5 p f hp hf K hK hrq n hadm.1 hLU'
      (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | PSp =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hrK : ¬ r ∣ Nat.card K := by rw [hK]; exact hrq
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hSp r hr h5 K hrK n (by have := hadm.1; omega)
      (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | POmegaOdd =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hrK : ¬ r ∣ Nat.card K := by rw [hK]; exact hrq
    have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hp.odd_of_ne_two hadm.2).pow
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hOo r hr h5 K hrK hodd n hadm.1 (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | POmegaPlus =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have hrK : ¬ r ∣ Nat.card K := by rw [hK]; exact hrq
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hOp r hr h5 K hrK n hadm (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | POmegaMinus =>
    obtain ⟨K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hrest
    have hrK : ¬ r ∣ Nat.card K := by rw [hK]; exact hrq
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hOm r hr h5 K hrK n hadm b c hbc (I294Large.exists_sylow_not_comm_of_mulEquiv hr e hS)
  | G2 => exact hrest.elim
  | F4 => exact hrest.elim
  | E6 => exact hrest.elim
  | E7 => exact hrest.elim
  | E8 => exact hrest.elim
  | twistedE6 => exact hrest.elim
  | trialityD4 => exact hrest.elim
  | twistedB2 => exact hrest.elim
  | twistedG2 => exact hrest.elim
  | twistedF4 => exact hrest.elim
  | Tits => exact hrest.elim

theorem i294CrossLargePrimeOn_classical_of_models
    (hL : I294LargeModelPSL) (hU : I294LargeModelPSU) (hSp : I294LargeModelPSp)
    (hOo : I294LargeModelPOmegaOdd) (hOp : I294LargeModelPOmegaPlus)
    (hOm : I294LargeModelPOmegaMinus) : I294CrossLargePrimeOn I294CrossIsClassical := by
  intro r hr h5 L _ _ _ _ d hd hcr hLe hLU hS
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hLe
  cases idx with
  | A m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_A] at this; exact fun h => this h.symm
    exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e) hrp hLU hS
  | twistedA m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at this
      exact fun h => this h.symm
    exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e) hrp hLU hS
  | B m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_B] at this
      exact fun h => this h.symm
    have hr2 : 2 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases Nat.lt_or_ge m 3 with hm | hm
    · obtain rfl : m = 2 := by omega
      exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hrp hLU hS
    · by_cases hq2 : q.p = 2
      · exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even m q hv hq2 hm e)
          hrp hLU hS
      · exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd m q hv hq2 hm e)
          hrp hLU hS
  | C m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_C] at this
      exact fun h => this h.symm
    exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC m q hv e) hrp hLU hS
  | D m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_D] at this
      exact fun h => this h.symm
    exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m q hv e) hrp hLU hS
  | twistedD m q =>
    have hrp : r ≠ q.p := by
      have := hcr; simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at this
      exact fun h => this h.symm
    exact I294Large.rank_of_classical_model hL hU hSp hOo hOp hOm hr h5
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv e) hrp hLU hS
  | _ => exact (hd : False).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
