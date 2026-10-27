module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Triv

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem not_isPGroup_two_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ IsPGroup 2 Q := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := isQuasisimple_nontrivial hQ
  haveI : Group.IsNilpotent Q := h2.isNilpotent
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)
  rw [hQ.1] at h1
  exact lt_irrefl _ h1

theorem glaPPrimeCoreOf_eq_bot {p : ℕ} {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) :
    GLAPPrimeCoreOf p S = ⊥ := by
  unfold GLAPPrimeCoreOf
  show (GLAPPrimeCore p ↥S).map S.subtype = ⊥
  rw [hSp, Subgroup.map_bot]

theorem isQuasisimple_pQuot_of_core_eq_bot {p : ℕ} {S : Subgroup Ω} (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) : CFSG.Open.IsQuasisimple (↥S ⧸ GLAPPrimeCore p ↥S) :=
  hSq.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot)

theorem eq_of_glaPComponent_of_le_centMod {p : ℕ} {S D J : Subgroup Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hDS : D ≤ centModSubgroup p S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) J) : J = S := by
  have hcore : GLAPPrimeCoreOf p S = ⊥ := glaPPrimeCoreOf_eq_bot hSp
  have hSD : S ⊓ Subgroup.centralizer (D : Set Ω) = S := by
    apply inf_eq_left.2
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := (hDS hd).2 s hs
    rw [hcore, Subgroup.mem_bot, commutatorElement_def] at h
    calc d * s = (s * d * s⁻¹ * d⁻¹) * d * s := by rw [h]; group
      _ = s * d := by group
  rw [hSD] at hJ
  obtain ⟨hlayer, hall, hbar⟩ := glaPLayer_of_isQuasisimple (p := p) (Y := S)
    (isQuasisimple_pQuot_of_core_eq_bot hSq hSp)
  have hJl : J = GLAPLayer p S := hall J hJ
  have hsup := sup_glaPPrimeCoreOf_eq_of_barX_eq_top (p := p) (Y := S) (I := GLAPLayer p S)
    hlayer.1 hbar
  rw [hcore, sup_bot_eq] at hsup
  rw [hJl, hsup]

theorem commutator_eq_bot_of_normalizer_self {S T : Subgroup Ω} (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hTS : T ≤ S) (hT2 : IsPGroup 2 T) (hST : S ≤ Subgroup.normalizer (T : Set Ω)) :
    ⁅T, S⁆ = ⊥ := by
  haveI hTn : (T.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).2 hST
  have hne : T.subgroupOf S ≠ ⊤ := by
    intro htop
    have hST' : S ≤ T := by
      intro s hs
      have : (⟨s, hs⟩ : ↥S) ∈ T.subgroupOf S := htop ▸ Subgroup.mem_top _
      exact this
    have hTS' : T = S := le_antisymm hTS hST'
    subst hTS'
    exact not_isPGroup_two_of_isQuasisimple hSq hT2
  have hcen := le_center_of_normal_of_isQuasisimple hSq hTn hne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h := Subgroup.mem_center_iff.1 (hcen (show (⟨t, hTS ht⟩ : ↥S) ∈ T.subgroupOf S from ht))
    ⟨s, hs⟩
  exact (congrArg Subtype.val h).symm

end Triv

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
