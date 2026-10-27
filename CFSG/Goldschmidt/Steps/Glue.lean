module

public import CFSG.Open.Defs
public import CFSG.Assembly.Defs
import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem glue_ne_bot {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {A : Subgroup G}
    (h : Subgroup.normalClosure (A : Set G) = ⊤) : A ≠ ⊥ := by
  rintro rfl
  have hle : Subgroup.normalClosure ((⊥ : Subgroup G) : Set G) ≤ ⊥ :=
    Subgroup.normalClosure_le_normal le_rfl
  exact bot_ne_top (h ▸ le_bot_iff.mp hle).symm

theorem glue_twoRank {G : Type} [Group G] [Finite G] {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (h4 : 4 ≤ Nat.card U) : 2 ≤ CFSG.Assembly.twoRank G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 U := fun x =>
    ⟨1, by simpa only [pow_one] using Subtype.ext (hU.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hUp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk2.trans (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G U hU k hk)

theorem glue_nonabelian {G : Type} [Group G] {K : Subgroup G} (hK : IsComponentOf K ⊤) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, -, -, hs⟩ := hK
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_center_iff.mpr fun y => h y g))

theorem glue_quasisimple {G : Type} [Group G] (h : IsComponentOf (⊤ : Subgroup G) ⊤) :
    CFSG.Open.IsQuasisimple G := by
  obtain ⟨-, -, hc, hs⟩ := h
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let f : (⊤ : Subgroup G) ⧸ Subgroup.center (⊤ : Subgroup G) ≃* G ⧸ Subgroup.center G :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  refine ⟨?_, ?_⟩
  · have : Group.IsPerfect (⊤ : Subgroup G) := Group.isPerfect_def.mpr hc
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  · have : Nontrivial (G ⧸ Subgroup.center G) := f.injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective f.toMonoidHom f.surjective

theorem glue_center {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (h : ((Subgroup.centralizer ((⊤ : Subgroup G) : Set G)).subgroupOf
      ((⊤ : Subgroup G) ⊔ A)).index < Nat.card G) : Subgroup.center G ≠ ⊥ := by
  intro hZ
  rw [top_sup_eq, Subgroup.coe_top, Subgroup.centralizer_univ, hZ, Subgroup.bot_subgroupOf,
    Subgroup.index_bot, Subgroup.card_top] at h
  exact lt_irrefl _ h

end CFSG.Goldschmidt
