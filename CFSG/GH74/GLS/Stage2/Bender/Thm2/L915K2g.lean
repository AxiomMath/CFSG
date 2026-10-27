module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C6
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2a
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2e
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2f

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag
open CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
open scoped commutatorElement

theorem noL3InPSp4_thm : NoL3InPSp4 := by
  intro K _ _ q hqodd hq5 hpsp X _ _ f hf hZodd p n hp hp2 hn hLie
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ := hpsp
  obtain ⟨F₃, _, _, hF₃card, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hF₃odd : Odd (Nat.card F₃) := by
    rw [hF₃card]
    exact (hp.odd_of_ne_two hp2).pow
  have hFodd : Odd (Nat.card F) := hFcard ▸ hqodd
  have h2F : (2 : F) ≠ 0 := CFSG.ComponentClassification.CatFactsSp4.two_ne_zero_of_odd_card hFodd
  obtain ⟨x₁, x₂, hx₁, hx₂, hcomm, hne, hne1, hne2, hd1, hd2, hd12⟩ := l3_facts hZodd hF₃odd ι
  let f' : X →* StatedProj (StatedSp 2 F) := e.toMonoidHom.comp f
  have hf' : Function.Injective f' := e.injective.comp hf
  have hmul : ∀ x : X, x * x = 1 → f' x * f' x = 1 := fun x hx => by
    rw [← map_mul, hx, map_one]
  have hord : ∀ x : X, x * x = 1 → x ≠ 1 → orderOf (f' x) = 2 := by
    intro x hx hx1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact hmul x hx) ?_
    intro h
    exact hx1 (hf' (h.trans (map_one f').symm))
  have hu1 : ∀ x : X, x * x = 1 → x ≠ 1 →
      x ∈ ⁅⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆,
        ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆⁆ →
      ∃ g, g⁻¹ * f' x * g = CFSG.ComponentClassification.CatFactsSp4.u1 F := by
    intro x hx hx1 hxd
    obtain ⟨g, hg | hg⟩ :=
      CFSG.ComponentClassification.CatFactsSp4.exists_conj_of_orderOf_eq_two hFodd (hord x hx hx1)
    · exact ⟨g, hg⟩
    · exfalso
      refine not_conj_u2_of_mem_derived2 h2F (Y := (centralizer ({x} : Set X)).map f') ?_ ?_ ⟨g, hg⟩
      · rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp hy]
      · have e1 : ⁅⁅(centralizer ({x} : Set X)).map f', (centralizer ({x} : Set X)).map f'⁆,
            ⁅(centralizer ({x} : Set X)).map f', (centralizer ({x} : Set X)).map f'⁆⁆ =
            (⁅⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆,
              ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆⁆).map f' := by
          rw [Subgroup.map_commutator, Subgroup.map_commutator, ← Subgroup.map_commutator,
            ← Subgroup.map_commutator]
        rw [e1]
        exact Subgroup.mem_map_of_mem f' hxd
  have hx12 : (x₁ * x₂) * (x₁ * x₂) = 1 := by
    calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hcomm]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [hx₁, hx₂, one_mul]
  have hne12 : x₁ * x₂ ≠ 1 := by
    intro h
    apply hne
    have : x₁⁻¹ = x₁ := inv_eq_of_mul_eq_one_right hx₁
    calc x₁ = x₁ * (x₁ * x₂) := by rw [h, mul_one]
      _ = x₂ := by rw [← mul_assoc, hx₁, one_mul]
  have c1 := hu1 x₁ hx₁ hne1 hd1
  have c2 := hu1 x₂ hx₂ hne2 hd2
  have c3 := hu1 (x₁ * x₂) hx12 hne12 hd12
  rw [map_mul] at c3
  exact not_conj_u1_mul hFodd (by rw [← map_mul, ← map_mul, hcomm]) (fun h => hne (hf' h))
    (hord x₁ hx₁ hne1) (hord x₂ hx₂ hne2) c1 c2 c3

end CFSG.GH74.GLS.Stage2.Bender.Thm2
