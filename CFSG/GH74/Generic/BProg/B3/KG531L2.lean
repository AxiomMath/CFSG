module

public import CFSG.GH74.Generic.BProg.B3.KG531Crit
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Quasithin.Background.DicksonPerfectBasic

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace KG531L2

theorem isSolvable_centralizer_involution {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {u : PSL(2, F)} (hu : orderOf u = 2) :
    Group.IsSolvable (centralizer ({u} : Set PSL(2, F))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution F hF hodd (by omega) hu
  have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hodd.pow (n := f))
    omega
  rcases hq with hq | hq
  · obtain ⟨-, ⟨d⟩⟩ := h1 hq
    have := CFSG.Quasithin.Dickson.isSolvable_dihedral ((p ^ f - 1) / 2)
    exact Group.isSolvable_of_surjective (f := d.symm.toMonoidHom) d.symm.surjective
  · obtain ⟨-, ⟨d⟩⟩ := h3 hq
    have := CFSG.Quasithin.Dickson.isSolvable_dihedral ((p ^ f + 1) / 2)
    exact Group.isSolvable_of_surjective (f := d.symm.toMonoidHom) d.symm.surjective

theorem not_mem_of_perfect {S L : Type} [Group S] [Group L] (e : S ≃* L) {t : S} (ht : t ≠ 1)
    (hsolv : Group.IsSolvable (centralizer ({e t} : Set L))) {P : Subgroup S}
    (hPle : P ≤ centralizer ({t} : Set S)) (hP : Group.IsPerfect ↥P) : t ∉ P := by
  intro htP
  let φ : ↥P →* ↥(centralizer ({e t} : Set L)) :=
    (e.toMonoidHom.comp P.subtype).codRestrict _ fun x => by
      have hx : (x : S) * t = t * (x : S) :=
        Subgroup.mem_centralizer_singleton_iff.1 (hPle x.2)
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      change e (x : S) * e t = e t * e (x : S)
      rw [← map_mul, ← map_mul, hx]
  have hφ : Function.Injective φ := fun x y hxy =>
    Subtype.ext (e.injective (congrArg Subtype.val hxy))
  have : Group.IsSolvable ↥P := Group.isSolvable_of_isSolvable_injective hφ
  have : Nontrivial ↥P := ⟨⟨⟨t, htP⟩, 1, fun h => ht (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥P ‹_›

end KG531L2

theorem kg531_l2 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  have hst : StatedClassicalModel S .PSL 2 p f := by
    rcases hL with ⟨-, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hm
    all_goals exact absurd ht (by decide)
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hst
  let e : S ≃* PSL(2, F) := e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hu : orderOf (e t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.t_ord
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.t_ord
    rw [h1, orderOf_one] at this
    omega
  exact h.false_of_perfect fun P hPle hP =>
    KG531L2.not_mem_of_perfect e ht1
      (KG531L2.isSolvable_centralizer_involution hp hp2 hf hF hu) hPle hP

end CFSG.GH74.Generic.BProg.B3
