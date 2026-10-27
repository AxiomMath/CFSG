module

public import CFSG.Quasithin.EmptyFaithful.S152He17A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_five_element_F4 (hC27 : ASC27Statement_F4 G) {T Mc M H K₁ K₂ : Subgroup G}
    {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G}
    (tail : Tail15204 c Lc) (hYL : yOf152 T Mc M ≤ Lc)
    (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)) :
    ∃ y ∈ yOf152 T Mc M,
      ∃ hy : y ∈ Subgroup.normalizer
          (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)) : Set G),
        orderOf (conjAct (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) ⟨y, hy⟩) = 5 := by
  by_contra hno
  push Not at hno
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨⟨-, h12, -⟩, -, -⟩ := hC27 (g0Of T Mc M K₁) R (M ⊓ g0Of T Mc M K₁) Lc V tail.hyp tail.comp
    (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hYC : yOf152 T Mc M ≤ (Lc ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := by
    rw [yOf152_eq_oTwoUpper T Mc M]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyY, hyodd⟩ := hy
    have hyLR : y ∈ Lc ⊔ R := Subgroup.mem_sup_left (hYL hyY)
    have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
      A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R))
        (le_normalizer_pCoreOf 2 (Lc ⊔ R) hyLR)
    have hy5 : y ^ 5 = 1 := He10.pow_five_of_odd c y hyY hyodd
    have hord : orderOf (conjAct V ⟨y, hyN⟩) ∣ 5 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [this, map_one]
    rcases (Nat.dvd_prime Nat.prime_five).mp hord with h1 | h5
    · exact ⟨hyLR, A4.conjAct_eq_one_iff.mp (orderOf_eq_one_iff.mp h1)⟩
    · exact absurd h5 (hno y hyY hyN)
  have hcomm : ⁅yOf152 T Mc M, Lc⁆ ≤ pCoreOf 2 (g0Of T Mc M K₁) :=
    commutator_le_of_le_O2_oTwoZ hLG (subnormal_of_mem_cComp tail.comp) hRG hRN (hYC.trans h12)
  exact c.false_of_commutator_le tail.le hLG tail.sylow hcomm

end CFSG.Quasithin.He17
