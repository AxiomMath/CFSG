module

public import CFSG.CGT.PushingUpLit.LIT.A4.Setup

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly

theorem centralizer_le_normalizer' {G : Type} [Group G] (P : Subgroup G) :
    Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hg' : ∀ q ∈ P, g * q * g⁻¹ = q := fun q hq => by
    have := (Subgroup.mem_centralizer_iff.1 hg q hq).symm
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  constructor
  · intro hh
    rw [hg' h hh]
    exact hh
  · intro hh
    have hq : (g * h * g⁻¹) * g = g * (g * h * g⁻¹) := Subgroup.mem_centralizer_iff.1 hg _ hh
    have e : h = g * h * g⁻¹ :=
      calc h = g⁻¹ * ((g * h * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [hq]
        _ = g * h * g⁻¹ := by group
    rw [e]
    exact hh

namespace A4Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (c : A4Cfg G M X)
include c

theorem centralizer_le {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) {m : G} (hm : m ∈ M)
    (hPX : P ≤ Subgroup.centralizer ((conjSub m X : Subgroup G) : Set G)) :
    Subgroup.centralizer (P : Set G) ≤ M := by
  have hXC : conjSub m X ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.1 (hPX hp) x hx).symm
  exact (centralizer_le_normalizer' P).trans
    (c.normalizer_le hP hP1 hm (hXC.trans (centralizer_le_normalizer' P)))

theorem exists_conj_ne (hnot : ¬ (X.subgroupOf M).Normal) : ∃ m ∈ M, conjSub m X ≠ X := by
  by_contra hall
  push Not at hall
  apply hnot
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.le]
  intro m hm
  have h := mem_normalizer_of_conjSub_eq (hall m hm |>.trans (conjSub_one X).symm)
  simpa using h

end A4Cfg

end CFSG.CGT.PushingUpLit.A4
