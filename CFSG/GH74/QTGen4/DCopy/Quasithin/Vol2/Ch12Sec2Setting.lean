module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem stmt12_2_13_iff_F4 : Stmt12_2_13_F4 ↔
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ v ∈ V, v ≠ 1 ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        LieModel G .PSL (n + 1) 2 1) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nonempty (G ≃* NativeSporadic.M24)) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_4_2_iff_F4 : Stmt12_4_2_F4 ↔
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        Nat.card V = 2 ^ 10 →
        ¬ Subgroup.centralizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) ≤
          Subgroup.normalizer (L : Set G)) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_6_34_iff_F4 : Stmt12_6_34_F4 ↔
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) →
        Nat.card V = 2 ^ 4 ∧ L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 4 1 := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem stmt12_7_1_iff_F4 : Stmt12_7_1_F4 ↔
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
      (∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal,
        CFSG.IsQuasisimple (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
        Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3 ∧
        Nonempty ((↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
            Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
          alternatingGroup (Fin 6))) →
        Nonempty (G ≃* NativeSporadic.M24) ∨ Nonempty (G ≃* NativeSporadic.He) := by
  constructor
  · intro h G _ _ T L V hH
    exact h G T L V hH.simple hH.nonabelian hH.qtke hH.sylow hH.notAlt hH.maximal hH.faithful
      hH.quasisimple hH.normalizes hH.irrPlus
  · intro h G _ _ T L V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h G T L V ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] def Asc94_M24He_L52Type_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (z : G), IsSimpleGroup G → orderOf z = 2 →
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      g⁻¹ * z * g ≠ z) →
      (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) ∨
          Nonempty (G ≃* NativeSporadic.He)) ∧
        ((∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
            ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* GL (Fin 4) (ZMod 2),
              Function.Surjective φ ∧
              φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
                (Subgroup.normalizer (E : Set G))) →
          ¬ Nonempty (G ≃* NativeSporadic.He) ∧
            (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24)))

end CFSG.Quasithin.H13
