module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Main
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2TNormal
public import CFSG.GH74.GLS.Stage1.Thm6.Assembly
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Rank
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conv
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Asc03
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Struct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Glue

variable {G : Type} [Group G] [Finite G]

theorem hnonab_of_std (h : Stage12.Std G) :
    ∀ S : Subgroup G, IsSylow2In S ⊤ → ¬ (IsElemAb2 S ∧ Nat.card S = 8) := by
  rintro S hS ⟨hE, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G := hS.2.1.toSylow (not_two_dvd_index_of_isSylow2In hS)
  exact h.nonab S' ⟨⟨fun a b => Subtype.ext ((hE a a.2).2 b b.2)⟩⟩

omit [Finite G] in
theorem orderOf_two_aux {x : G} (hx : orderOf x = 2) : x ≠ 1 ∧ x * x = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hx
    omega
  · rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hx])

@[expose] def S_stage1_thm6_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
    L2Meets G (fun K _ => Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      HasL2Model K (fun q => Odd q ∧ 3 < q)) → Stage12.Asc03Data G

end CFSG.GH74.GLS.Stage1.Thm6
