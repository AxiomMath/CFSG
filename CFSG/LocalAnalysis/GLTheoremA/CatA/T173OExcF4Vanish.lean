module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4Kernel2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.T173X

variable {τ : Tag} {F : Type} [Field F] [Finite F]

section F4

theorem stdVanishes_torusPow_exc_F4
    [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    {d : ↥(adjointGroup .F4 F)} (hd : IsStdElt p (TableBExc.torusPow .F4 F p) d) :
    StdVanishes (TableBExc.torusPow .F4 F p) d := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite ↥(adjointGroup .F4 F) := generated_group_finite .F4 F
  obtain ⟨a, ha, hda⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusPow (τ := .F4) (F := F) (p := p) hd.1
  have hker : ∀ b : Fin Tag.F4.rank → Fˣ, (∀ i, b i ^ p = 1) →
      (∀ α ∈ rootCharKernel (τ := .F4) a, rootChar b α = 1) →
      rootDiagUnit .F4 b ∈ Subgroup.zpowers (rootDiagUnit .F4 a) := by
    intro b hb hbKer
    exact rootDiagUnit_mem_zpowers_of_rootChar_eq_one_of_exc hn hp hpq hda hd (Or.inl rfl)
      (fun h => by cases h) hb hbKer
  obtain ⟨⟨α, hαker, hαL⟩, ⟨β, hβker, hβS⟩⟩ :=
    exists_long_short_mem_rootCharKernel_F4 hp hp2 ha hker
  have hvac : (.F4 : Tag) = .E6 → p ≠ 3 := fun h => by cases h
  have hαU : (rootSubgroup .F4 F α).subgroupOf (adjointGroup .F4 F) ≤
      innerClosure (TableBExc.torusPow .F4 F p) d :=
    (rootSubgroup_le_stdLayer (τ := .F4) hn hp hp2 hpq hda hd (Or.inl rfl) hαker).trans
      (CFSG.LocalAnalysis.GLTheoremA.S9.Cl.le_closureIn_self _ _)
  have hβU : (rootSubgroup .F4 F β).subgroupOf (adjointGroup .F4 F) ≤
      innerClosure (TableBExc.torusPow .F4 F p) d :=
    (rootSubgroup_le_stdLayer (τ := .F4) hn hp hp2 hpq hda hd (Or.inl rfl) hβker).trans
      (CFSG.LocalAnalysis.GLTheoremA.S9.Cl.le_closureIn_self _ _)
  have hN : Subgroup.normalizer
      ((TableBExc.torusPow .F4 F p : Subgroup ↥(adjointGroup .F4 F)) :
        Set ↥(adjointGroup .F4 F)) ≤
      Subgroup.normalizer (innerClosure (TableBExc.torusPow .F4 F p) d :
        Set ↥(adjointGroup .F4 F)) :=
    CFSG.LocalAnalysis.GLTheoremA.S12.le_normalizer_closureIn_self _ _
  have htop : innerClosure (TableBExc.torusPow .F4 F p) d = ⊤ :=
    eq_top_of_rootSubgroup_le_F4 F p hN hαL hβS hαU hβU
  have hsimple : IsSimpleGroup ↥(adjointGroup .F4 F) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type (by simp)
  have h2 : ¬ IsPGroup 2 (⊤ : Subgroup ↥(adjointGroup .F4 F)) := by
    refine not_isPGroup_two_top_of_subgroup hp hp2 (TableBExc.torusPow .F4 F p) ?_
    rw [card_torusPow_exc hn hp hpq (Or.inl rfl) hvac]
    exact dvd_pow_self p (by have := two_le_rank_exc (Or.inl rfl); omega)
  exact stdVanishes_of_innerClosure_eq_top hsimple h2 htop

theorem modelFactExcSplit_F4 : ModelFactExcSplit .F4 := by
  intro F _ _ _ n p hn hp hp2 hpq hp3
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hn)
  refine modelFactV_of_frame (TableBExc.torusPow .F4 F p) ?_ ?_
  · intro A hA
    exact exists_conj_eq_torusPow_of_isBmax_exc (τ := .F4) hn hp hp2 hpq (Or.inl rfl)
      (fun h => by cases h) hA
  · intro d hd
    exact stdVanishes_torusPow_exc_F4 hn hp hp2 hpq hd

end F4

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
