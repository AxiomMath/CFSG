module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.GH74.QTGen4.Leaves.SL5Rank

public section

namespace CFSG.GH74.QTGen4.Leaves.KGFactVac

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Asc94_M24He_L52Type_Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.Gen4 G →
    ∀ (z : G), IsSimpleGroup G → orderOf z = 2 →
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

theorem asc94_M24He_L52Type_gen4 : Asc94_M24He_L52Type_Gen4 := by
  intro G _ _ hG z _ _ hiso _
  obtain ⟨e⟩ := hiso
  exfalso
  let f : ↥(Subgroup.centralizer ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) →*
      G :=
    (Subgroup.centralizer ({z} : Set G)).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  exact (CFSG.GH74.QTGen4.Leaves.SL5Rank.not_gen4_of_centralizer_tvec f hf) hG

end CFSG.GH74.QTGen4.Leaves.KGFactVac
