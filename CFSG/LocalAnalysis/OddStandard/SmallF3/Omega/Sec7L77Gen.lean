module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec7l77_solvable_of_odd_le {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Group.IsSolvable N) (hodd : ∀ x : H, Odd (orderOf x) → x ∈ N) :
    Group.IsSolvable H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (H ⧸ N) :=
    CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem N fun x hx =>
      hodd x (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hx))
  haveI : Group.IsNilpotent (H ⧸ N) := hQ.isNilpotent
  haveI : Group.IsSolvable (H ⧸ N) := inferInstance
  haveI := hN
  exact Group.isSolvable_of_subgroup_quotient N

theorem sec7l77_solvable_sup {G : Type*} [Group G] {D C : Subgroup G}
    (hDC : D ≤ Subgroup.centralizer (C : Set G)) (hD : Group.IsSolvable D)
    (hC : Group.IsSolvable C) : Group.IsSolvable ↥(D ⊔ C) := by
  haveI := hD
  haveI := hC
  let φ : ↥D × ↥C →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := by
        rintro ⟨d, c⟩ ⟨d', c'⟩
        have hcomm : (c : G) * (d' : G) = (d' : G) * (c : G) :=
          (Subgroup.mem_centralizer_iff.mp (hDC d'.2) (c : G) c.2)
        calc ((d * d' : ↥D) : G) * ((c * c' : ↥C) : G)
            = (d : G) * ((d' : G) * (c : G)) * (c' : G) := by
              simp only [Subgroup.coe_mul]; group
          _ = (d : G) * ((c : G) * (d' : G)) * (c' : G) := by rw [hcomm]
          _ = ((d : G) * (c : G)) * ((d' : G) * (c' : G)) := by group }
  have hrange : φ.range = D ⊔ C := by
    apply le_antisymm
    · rintro x ⟨⟨d, c⟩, rfl⟩
      exact Subgroup.mul_mem_sup d.2 c.2
    · refine sup_le ?_ ?_
      · intro d hd
        exact ⟨(⟨d, hd⟩, 1), by simp [φ]⟩
      · intro c hc
        exact ⟨(1, ⟨c, hc⟩), by simp [φ]⟩
  have hsol : Group.IsSolvable φ.range := solvable_of_surjective φ.rangeRestrict_surjective
  rw [hrange] at hsol
  exact hsol

end CFSG.OddStandard.SmallF3.Omega
