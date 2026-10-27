module

public import CFSG.ClassicalInvolution.Q3.Q3TIVDefs
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinE
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution.Asc77.S28 (TwinProductCentral fund_central_involution
  mem_center_of_equiv mul_involutions_scalar mul_involutions_scalar_su mul_involutions_scalar_sp)
open scoped MatrixGroups commutatorElement



section SL4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  Matrix Module

variable {p f : ℕ} [Fact p.Prime]

theorem twinProductCentral_psl4_of_odd (hp2 : p ≠ 2) (hodd : Odd (Nat.card (GaloisField p f)))
    (hadm : StatedLieAdmissible .PSL 4 p f) : TwinProductCentral p f .PSL 4 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have e : fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D =
      longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) :=
    fundamentalSubgroups_psl_eq (p := p) (f := f) (m := 3) (by omega)
  have hRL : R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) := e ▸ hR
  have hR'L : R' ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) := e ▸ hR'
  obtain ⟨i, hi⟩ := hRL
  obtain ⟨i', hi'⟩ := hR'L
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hR'
  have hci := hi.isClassicalSL2 h2
  have hci' := hi'.isClassicalSL2 h2
  have hri : r = i :=
    ((fund_central_involution hodd eR hrR hrc hr1).2 i hci.mem hci.orderOf_eq_two).symm
  have hr'i' : r' = i' :=
    ((fund_central_involution hodd eR' hr'R hr'c hr'1).2 i' hci'.mem hci'.orderOf_eq_two).symm
  rw [hri, hr'i']
  exact mul_involutions_scalar h2 hi hi' hne hc

end SL4

section SU4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix Module

variable {p f : ℕ} [Fact p.Prime]

theorem twinProductCentral_psu4_of_odd (hp2 : p ≠ 2) (hodd : Odd (Nat.card (GaloisField p f)))
    (hadm : StatedLieAdmissible .PSU 4 p f) : TwinProductCentral p f .PSU 4 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have hf : 1 ≤ f := hadm.2.1
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  obtain ⟨i, hi⟩ := (he R).mp hR
  obtain ⟨i', hi'⟩ := (he R').mp hR'
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU)
    trivial hadm (by decide) (by decide) hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hri : e r = i :=
    hi.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hrR)
      (by rw [MulEquiv.orderOf_eq]; exact ord)
  have hr'i' : e r' = i' :=
    hi'.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hr'R)
      (by rw [MulEquiv.orderOf_eq]; exact ord')
  have hcen := mul_involutions_scalar_su hp2 hK hi hi'
    (fun h => hne (Subgroup.map_injective e.injective h))
    ((CFSG.ClassicalInvolution.RouteD.Exotic.commutes_map_equiv e).mpr hc)
  refine mem_center_of_equiv e ?_
  rw [map_mul, hri, hr'i']
  exact hcen

end SU4

section Sp4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank Matrix Module

variable {p f : ℕ} [Fact p.Prime]

theorem twinProductCentral_psp2_of_odd (hp2 : p ≠ 2) (hodd : Odd (Nat.card (GaloisField p f)))
    (hadm : StatedLieAdmissible .PSp 2 p f) : TwinProductCentral p f .PSp 2 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have e : fundamentalSubgroups .PSp (modelUniv .PSp 2 p f Fact.out).D =
      planeGroupSet (GaloisField p f) 2 := fundamentalSubgroups_psp_eq hadm
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hRP : R ∈ planeGroupSet (GaloisField p f) 2 := e ▸ hR
  have hR'P : R' ∈ planeGroupSet (GaloisField p f) 2 := e ▸ hR'
  obtain ⟨P₀, hP₀, rfl⟩ := hRP
  obtain ⟨P₁, hP₁, rfl⟩ := hR'P
  obtain ⟨i₀, hi₀, hm₀⟩ := exists_inv_planeGroup h2 hP₀
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroup h2 hP₁
  have hri : r = i₀ := hi₀.eq_of_orderOf_eq_two h2 hrR ord
  have hr'i' : r' = i₁ := hi₁.eq_of_orderOf_eq_two h2 hr'R ord'
  have hne' : P₀ ≠ P₁ := fun h => hne (by rw [h])
  have horth := (commutes_planeGroup_iff h2 hP₀ hP₁ hne').mp hc
  rw [hri, hr'i']
  exact mul_involutions_scalar_sp h2 hP₀ hP₁ hi₀ hm₀ hi₁ hm₁ horth

end Sp4

section Three

open CFSG.Assembly.LowTwoRank

theorem twinProductCentral3_psl4 : TwinProductCentral3 .PSL 4 :=
  twinProductCentral_psl4_of_odd (p := 3) (f := 1) (by norm_num) Q3W.odd_gf3
    ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide, by decide⟩

theorem twinProductCentral3_psu4 : TwinProductCentral3 .PSU 4 :=
  twinProductCentral_psu4_of_odd (p := 3) (f := 1) (by norm_num) Q3W.odd_gf3
    ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide⟩

theorem twinProductCentral3_psp2 : TwinProductCentral3 .PSp 2 :=
  twinProductCentral_psp2_of_odd (p := 3) (f := 1) (by norm_num) Q3W.odd_gf3
    Q3Z.statedLieAdmissible_psp2

end Three

end CFSG.ClassicalInvolution.Q3.Q3TIV
