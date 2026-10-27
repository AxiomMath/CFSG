module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module CFSG.LargeExtraspecial.S4

section Weak

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem mem_normalizer_of_forall_conj {X O : Subgroup S.O}
    (hOn : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O) {x : S.O} (hx : x ∈ X) :
    x ∈ normalizer (O : Set S.O) :=
  mem_normalizer_iff.mpr fun o => ⟨fun ho => hOn x hx o ho, fun ho => by
    have := hOn x⁻¹ (inv_mem hx) _ ho
    rwa [show x⁻¹ * (x * o * x⁻¹) * x⁻¹⁻¹ = o by group] at this⟩

theorem map_conj_eq_of_le_normalizer {j : G} (Hj : Hyp4 S j) (Cj : Cons311 S j)
    {X O : Subgroup S.O} (hXM : X ≤ S.Mbar) (hLX : S.Lbar j ≤ X) (hOX : O ≤ X)
    (hOn : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O) (hO : IsPGroup 2 O) {x : S.O} (hx : x ∈ X)
    (hle : (S.Lbar j).map (MulAut.conj x).toMonoidHom ≤
      normalizer ((S.Lbar j ⊔ O : Subgroup S.O) : Set S.O)) :
    (S.Lbar j).map (MulAut.conj x).toMonoidHom = S.Lbar j := by
  have hL2 : IsPGroup 2 (S.Lbar j) := isPGroup_Lbar S Hj.conj_mem
  have hLO : IsPGroup 2 ↥(S.Lbar j ⊔ O) :=
    hL2.to_sup_of_normal_right' hO fun l hl => mem_normalizer_of_forall_conj hOn (hLX hl)
  have hP : IsPGroup 2 ↥((S.Lbar j).map (MulAut.conj x).toMonoidHom ⊔ (S.Lbar j ⊔ O)) :=
    (hL2.map _).to_sup_of_normal_right' hLO hle
  have hLxX : (S.Lbar j).map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hx (hLX hl)) (inv_mem hx)
  have hPN := le_normalizer_of_weaklyClosed Cj.weaklyClosed hP
    (sup_le (hLxX.trans hXM) (sup_le (hLX.trans hXM) (hOX.trans hXM)))
    (le_sup_left.trans le_sup_right)
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hXM hx)
  rw [← hm, ← Lbar_mul S m j] at hPN ⊢
  exact Cj.weaklyClosed m m.2 (le_sup_left.trans hPN)

end Weak

end CFSG.LargeExtraspecial.S9
