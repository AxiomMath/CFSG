module

public import CFSG.GF2Type.SmithTypeE.Parts
public import CFSG.LargeExtraspecial.S14Defs
import CFSG.GF2Type.Entry
public import CFSG.LargeExtraspecial.BridgeSetting

public section

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.LargeExtraspecial.Bridge
open scoped MatrixGroups

@[expose] def SmithL62LocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
        orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
          (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2))

@[expose] def SmithL62PathInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
        Commute x S.z → Commute S.z w → Commute w y →
          ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
            ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

@[expose] def SmithL62ThreeFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      (∀ a b : G, IsConj S.z a → IsConj S.z b →
        orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
          (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2))) ∧
      ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4

@[expose] def SmithL62Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) → ChevalleyExceptionalModel G .E6 2 1

theorem partB_of_smithL62Input (h : SmithL62Input) : PartB := by
  intro G _ _ _ _ z hz hext hcard Mbar _ hMbar hL
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 10 := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  obtain ⟨g⟩ := hL
  have g' : timmesfeldFStar Mbar ≃* PSL(6, ZMod 2) :=
    (MulEquiv.subgroupCongr (generalizedFitting_eq_timmesfeldFStar Mbar).symm).trans g
  have hE := h G (Setting.ofFStar z hz hext') hw
    ⟨(equivOfMapEq e (timmesfeldFStar_map e)).trans g'⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, hE⟩)

end CFSG.GF2Type.SmithTypeE
