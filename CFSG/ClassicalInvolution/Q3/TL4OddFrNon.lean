module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem mem_closure_three_cases {a b d g : G} (hd : d * d = 1) (had : a * d = d * a)
    (hbd : b * d = d * b) (hg : g ∈ Subgroup.closure ({a, b, d} : Set G)) :
    g ∈ Subgroup.closure ({a, b} : Set G) ∨
      ∃ e ∈ Subgroup.closure ({a, b} : Set G), g = e * d := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.closure_le]
    rintro v (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr had
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hbd
  rw [T8T.closure_three_eq_sup] at hg
  obtain ⟨e, he, w, hw, rfl⟩ := exists_mul_of_mem_sup_central hle (fun w hw h hh => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hh) m).eq).symm) hg
  rcases Balance.Bootstrap.mem_zpowers_involution hd hw with rfl | rfl
  · left
    rwa [mul_one]
  · exact Or.inr ⟨e, he, rfl⟩

theorem card_centralizer_lt_of_center [Finite G] (hZ : Subgroup.center G = ⊥) {c : G}
    (hc1 : c ≠ 1) : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
    intro htop
    apply hc1
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rwa [hZ, Subgroup.mem_bot] at hcZ
  have h3 := Subgroup.card_le_card_group (Subgroup.centralizer ({c} : Set G))
  have h4 : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) ≠ Nat.card G :=
    fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h)
  omega

end Gen

end CFSG.ClassicalInvolution.Q3.TL4
