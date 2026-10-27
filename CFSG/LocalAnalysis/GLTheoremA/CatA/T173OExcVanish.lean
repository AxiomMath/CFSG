module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcWeyl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcTorus
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag
public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.T173X

variable {τ : Tag} {F : Type} [Field F] [Finite F]

section Bmax


theorem exists_conj_eq_torusPow_of_isBmax_exc
    [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hp3 : τ = .E6 → p ≠ 3) {A : Subgroup ↥(adjointGroup τ F)} (hA : GLAIsBmax p A) :
    ∃ g : ↥(adjointGroup τ F), A.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow τ F p := by
  haveI : Fintype F := Fintype.ofFinite F
  have hpq' : p ∣ Nat.card F - 1 := by rw [hn]; exact hpq
  have hrank : 0 < τ.rank := by have := two_le_rank_exc hτ; omega
  have hVle : TableBExc.torusPow τ F p ≤ (torusGroup τ F).subgroupOf (adjointGroup τ F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow τ F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hVle hVp
      (isRoot_single τ ⟨0, hrank⟩)
  have hEcard' : Nat.card E = p ^ τ.rank :=
    hEcard.trans (card_torusPow_exc hn hp hpq hτ hp3)
  have hAle : p ^ τ.rank ≤ Nat.card A := by
    rw [hA.2.1, ← hEcard']
    exact card_le_pow_glaTwoLocalRank hp hE hX hX2 hXE
  rcases hτ with rfl | rfl | rfl | rfl
  · exact CFSG.StandardType.ggF4ToralRankInput_of_three (K := F) hp hp2 hpq'
      (fun _ => CFSG.StandardType.ggF4ThreeRankInput_holds) A hA.1 hAle
  · exact TableBExc.ggExcToralRankInput_E6_of_ne_three (K := F) hp hp2 (hp3 rfl) hpq' A hA.1 hAle
  · exact IOneRest.ggExcToralRankInput_E7E8 (K := F) (Or.inl rfl) hp hp2 hpq' A hA.1 hAle
  · exact IOneRest.ggExcToralRankInput_E7E8 (K := F) (Or.inr rfl) hp hp2 hpq' A hA.1 hAle

end Bmax

section Vanishing


theorem stdVanishes_torusPow_exc_E6_E7_E8
    [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp3 : τ = .E6 → p ≠ 3)
    {d : ↥(adjointGroup τ F)} (hd : IsStdElt p (TableBExc.torusPow τ F p) d) :
    StdVanishes (TableBExc.torusPow τ F p) d := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite ↥(adjointGroup τ F) := generated_group_finite τ F
  obtain ⟨a, -, hda⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusPow (τ := τ) (F := F) (p := p) hd.1
  obtain ⟨α, hα⟩ :=
    rootCharKernel_nonempty_of_isStdElt_of_exc hn hp hpq hda hd (Or.inr hτ) hp3
  have hU : (rootSubgroup τ F α).subgroupOf (adjointGroup τ F) ≤
      innerClosure (TableBExc.torusPow τ F p) d :=
    (rootSubgroup_le_stdLayer hn hp hp2 hpq hda hd (Or.inr hτ) hα).trans
      (CFSG.LocalAnalysis.GLTheoremA.S9.Cl.le_closureIn_self _ _)
  have hN : Subgroup.normalizer
      ((TableBExc.torusPow τ F p : Subgroup ↥(adjointGroup τ F)) :
        Set ↥(adjointGroup τ F)) ≤
      Subgroup.normalizer (innerClosure (TableBExc.torusPow τ F p) d :
        Set ↥(adjointGroup τ F)) :=
    CFSG.LocalAnalysis.GLTheoremA.S12.le_normalizer_closureIn_self _ _
  have htop : innerClosure (TableBExc.torusPow τ F p) d = ⊤ :=
    eq_top_of_rootSubgroup_le hτ F p hN hα.1 hU
  have hsimple : IsSimpleGroup ↥(adjointGroup τ F) := by
    refine CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type ?_
    rcases hτ with rfl | rfl | rfl <;> simp
  have h2 : ¬ IsPGroup 2 (⊤ : Subgroup ↥(adjointGroup τ F)) := by
    refine not_isPGroup_two_top_of_subgroup hp hp2 (TableBExc.torusPow τ F p) ?_
    rw [card_torusPow_exc hn hp hpq (Or.inr hτ) hp3]
    exact dvd_pow_self p (by have := two_le_rank_exc (Or.inr hτ); omega)
  exact stdVanishes_of_innerClosure_eq_top hsimple h2 htop

theorem modelFactExcSplit_E6 : ModelFactExcSplit .E6 := by
  intro F _ _ _ n p hn hp hp2 hpq hp3
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hn)
  refine modelFactV_of_frame (TableBExc.torusPow .E6 F p) ?_ ?_
  · intro A hA
    exact exists_conj_eq_torusPow_of_isBmax_exc (τ := .E6) hn hp hp2 hpq
      (Or.inr (Or.inl rfl)) hp3 hA
  · intro d hd
    exact stdVanishes_torusPow_exc_E6_E7_E8 (τ := .E6) hn hp hp2 hpq (Or.inl rfl) hp3 hd

theorem modelFactExcSplit_E7 : ModelFactExcSplit .E7 := by
  intro F _ _ _ n p hn hp hp2 hpq hp3
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hn)
  refine modelFactV_of_frame (TableBExc.torusPow .E7 F p) ?_ ?_
  · intro A hA
    exact exists_conj_eq_torusPow_of_isBmax_exc (τ := .E7) hn hp hp2 hpq
      (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h) hA
  · intro d hd
    exact stdVanishes_torusPow_exc_E6_E7_E8 (τ := .E7) hn hp hp2 hpq
      (Or.inr (Or.inl rfl)) (fun h => by cases h) hd

theorem modelFactExcSplit_E8 : ModelFactExcSplit .E8 := by
  intro F _ _ _ n p hn hp hp2 hpq hp3
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hn)
  refine modelFactV_of_frame (TableBExc.torusPow .E8 F p) ?_ ?_
  · intro A hA
    exact exists_conj_eq_torusPow_of_isBmax_exc (τ := .E8) hn hp hp2 hpq
      (Or.inr (Or.inr (Or.inr rfl))) (fun h => by cases h) hA
  · intro d hd
    exact stdVanishes_torusPow_exc_E6_E7_E8 (τ := .E8) hn hp hp2 hpq
      (Or.inr (Or.inr rfl)) (fun h => by cases h) hd

end Vanishing

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
