module

public import CFSG.CGT.HaradaParrott80.Prop6
public import CFSG.GF2Type.Smith1979CharTwoKP

public section

namespace CFSG.CGT.Harada80

open CFSG CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique

theorem Setting.smithList_of_not_le (hS : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP)
    {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
    (hH1 : H1Natural m) (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)}
    (ha1 : a ≠ 1) (ha : quadQ m (Multiplicative.toAdd (S.beta a)) = 0)
    (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    (m = 2 ∧
        (LieModel G .PSL 6 2 1 ∨ LieModel G .PSU 6 2 1 ∨ LieModel G .POmegaPlus 4 2 1 ∨
          LieModel G .POmegaMinus 4 2 1 ∨ LieModel G .trialityD4 0 2 1 ∨
          LieModel G .POmegaPlus 4 3 1 ∨ NativeSporadic.IsSporadic G .Co2 ∨
          NativeSporadic.IsSporadic G .Co1 ∨ NativeSporadic.IsSporadic G .Th ∨
          NativeSporadic.IsSporadic G .HN)) ∨
      (m = 3 ∧
        (LieModel G .PSL 8 2 1 ∨ LieModel G .PSU 8 2 1 ∨ LieModel G .POmegaPlus 5 2 1 ∨
          LieModel G .POmegaMinus 5 2 1 ∨ NativeSporadic.IsSporadic G .J4 ∨
          NativeSporadic.IsSporadic G .Fi24Prime)) := by
  haveI := S.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hext, hcard⟩ := S.isExtraspecial_of_not_le hH1 hC ha1 ha hnot
  have hord : orderOf (a : G) = 2 :=
    orderOf_eq_prime (S.elemU.2 a a.2) fun h => ha1 (Subtype.ext h)
  have h := hS G S.nonab S.charTwo S.kProper (a : G) hord hext (2 * m) hcard
  rcases S.m_eq with rfl | rfl
  · exact Or.inl ⟨rfl, h.1 rfl⟩
  · exact Or.inr ⟨rfl, h.2 rfl⟩

end CFSG.CGT.Harada80
