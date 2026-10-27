module

public import CFSG.GH74.Uniqueness.SU.SU14Basic
public import CFSG.GH74.Uniqueness.SU.SU14Hbar
public import CFSG.GH74.Uniqueness.SU.SU14Walter
public import CFSG.GH74.Uniqueness.SU.KInputsR3
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup CFSG.Blueprint

@[expose] def S_Thm182_rank3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    ∀ S : Sylow 2 G, Open.pRank 2 (S : Subgroup G) = 3 → gammaElem (S : Subgroup G) ≠ ⊤ →
      NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G

@[expose] def Prop189Rank3Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G),
    SU4.Conf18H S M V x z → SU4.Hyp184 S U M → Open.pRank 2 (S : Subgroup G) ≠ 3

@[expose] def Prop211Rank3Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) (z : G),
    SU10.Hyp21 S M z → Open.pRank 2 (S : Subgroup G) = 3 →
      (centralizer ({z} : Set G) ≤ M ∨
        K.IsTwoAlt (SU8.Hbar (centralizer ({z} : Set G))) 9 ∨
        ∃ (Y : Type) (_ : Group Y), SU8.IsL24 Y ∧
          Nonempty (SU8.Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y))

theorem S_Thm182_rank3_of_stmts
    (h183 : SU4.Lemma183Stmt) (h186 : SU4.Lemma186Stmt)
    (h18H : SU4.Lemma18HStmt) (h189 : Prop189Rank3Stmt) (h211 : Prop211Rank3Stmt)
    (h213 : SU10.Cor213Stmt) (hKI7b : K.KI7b9) : S_Thm182_rank3 := by
  intro G _ _ hsimple hnonab hkgh S hrank3 hgamma
  have hrank : 3 ≤ Open.pRank 2 (S : Subgroup G) := hrank3.ge
  obtain ⟨U, hsetup, hUS, hUc⟩ := exists_setup18 hsimple hnonab hkgh S hrank
  obtain ⟨M, hHyp⟩ := exists_hyp184 h183 hsetup hgamma
  have hno : SU4.Concl184b M := by
    intro V hV
    obtain ⟨V', x, z, hconf⟩ := h18H G S U M hHyp ⟨V, hV⟩
    exact h189 G S U M V' x z hconf hHyp hrank3
  have hΓ : SU4.Concl184a S M := h186 G S U M hHyp hno
  obtain ⟨z, hzord, hzc⟩ := exists_central_involution_sylow S hUS hUc
  have hH21 : SU10.Hyp21 S M z := hyp21_of hHyp hΓ hno hzord hzc
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hzc s hs)
  have hcases := h211 G S M z hH21 hrank3
  by_cases hC : centralizer ({z} : Set G) ≤ M
  · exact Or.inr (h213 G S M z hH21 hC)
  · have hshape := hcases.resolve_left hC
    rcases hshape with hb | hA
    ·
      exfalso
      have h1 := hKI7b (SU8.Hbar (centralizer ({z} : Set G))) hb
      have h2 := pRank_sylow_eq_twoRank_hbar S hSC
      omega
    ·
      obtain ⟨Y, _, hY, ⟨e⟩⟩ := hA
      obtain ⟨eY⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Y hY
      obtain ⟨hcomm, h8, h5⟩ := sylow_facts_of_hbar S hSC eY e
      exact Or.inl (isSporadic_J1_of_abelian_sylow hsimple hnonab S hcomm h8
        (h5.trans (Subgroup.card_subgroup_dvd_card _)))

end CFSG.GH74.Uniqueness.SU.SU14
