module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem l154_subnormal_eq_or_le_center {G : Type*} [Group G] {J S : Subgroup G}
    (h : CFSG.Open.IsSubnormal J S) (hS : CFSG.Open.IsQuasisimple ↥S) :
    J = S ∨ J ≤ (Subgroup.center ↥S).map S.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hS with hMB | hM
    · subst hMB
      have hS' : CFSG.IsQuasisimple _ :=
        ⟨⟨hS.1⟩, hS.2,
          CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hS⟩
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hS' hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · exact Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h hx, rfl⟩
    · exact Or.inr (hAM.trans hM)

theorem l154_eq_of_subnormal_quasisimple {G : Type*} [Group G] {J S : Subgroup G}
    (h : CFSG.Open.IsSubnormal J S) (hS : CFSG.Open.IsQuasisimple ↥S) (hperf : ⁅J, J⁆ = J)
    (hne : J ≠ ⊥) : J = S := by
  rcases l154_subnormal_eq_or_le_center h hS with h1 | h1
  · exact h1
  · exfalso
    apply hne
    have hcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := h1 ha
      obtain ⟨b', -, rfl⟩ := h1 hb
      have := Subgroup.mem_center_iff.1 ha' b'
      simp only [Subgroup.coe_subtype]
      exact congrArg Subtype.val this.symm
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a ha b hb

section Field


theorem l154_of_centMod {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    {J : Subgroup Ω} (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcm : CentMod p S x) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J) :
    NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
  have hcore : GLAPPrimeCoreOf p S = ⊥ := by
    unfold GLAPPrimeCoreOf
    unfold GLAPPrimeCore at hSp
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).2 hSp
  have hcen : S ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro s hs
    have h1 := (mem_centModSubgroup.1 (centMod_iff.1 hcm)).2 s hs
    rw [hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 h1
  have hJS : GLAPComponent p S J := by rwa [inf_eq_left.2 hcen] at hJ
  have hJeq : J = S :=
    l154_eq_of_subnormal_quasisimple hJS.2.1 hqS (glaPComponent_perfect hJS)
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJS)
  subst hJeq
  exact ⟨MI.field_nonInnDiag_any hJS hF, fun ⟨hp3, hT⟩ => MI.td4_not_field_holds (hp3 ▸ hT)
    (hp3 ▸ hF)⟩

end Field

end CFSG.LocalAnalysis.GLTheoremA.K155X
