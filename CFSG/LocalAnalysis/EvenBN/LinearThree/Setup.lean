module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint

structure Hyp (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  standard : standardComponentIsStandard A
  center_eq_bot : center A = ⊥
  cyc : ∀ S : Sylow 2 (centralizer (A : Set G)),
    IsCyclic (S : Subgroup (centralizer (A : Set G)))
  core : ∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥
  three_le : 3 ≤ f
  model : LieModel A .PSL 3 2 f

theorem isCyclic_of_isCyclic_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (hS : IsCyclic (S : Subgroup H)) (T : Sylow p H) :
    IsCyclic (T : Subgroup H) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H S T
  rw [Sylow.coe_subgroup_smul]
  exact isCyclic_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap (S : Subgroup H))
    (MonoidHom.subgroupMap_surjective _ _)

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem even_card_centralizer (h : Hyp G A f) : Even (Nat.card (centralizer (A : Set G))) :=
  h.standard.2.1

theorem inf_centralizer_eq_bot (h : Hyp G A f) : A ⊓ centralizer (A : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxC⟩
  have hx : (⟨x, hxA⟩ : A) ∈ center A :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq_bot, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
