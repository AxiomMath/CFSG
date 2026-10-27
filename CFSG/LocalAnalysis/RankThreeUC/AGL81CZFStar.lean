module

public import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem pCore_le_centralizer_of_isComponent {p : ℕ} [Fact p.Prime] {C : Subgroup X}
    (hC : CFSG.IsComponent C) : CFSG.pCore p X ≤ centralizer (C : Set X) := by
  haveI : Group.IsNilpotent (CFSG.pCore p X) := (CFSG.pCore_isPGroup (p := p) (G := X)).isNilpotent
  have hsub : (CFSG.pCore p X).IsSubnormal := (CFSG.pCore_normal (p := p) (G := X)).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer (G := X) inferInstance hsub).1 C hC
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem eq_bot_of_le_centralizer_pCore_of_isComponent {d : ℕ} (hd : d.Prime) (hd3 : d ≠ 3)
    (hO : CFSG.pPrimeCore 3 X = ⊥) {T : Subgroup X} (hT : IsPGroup d T)
    (hTA : T ≤ centralizer (CFSG.pCore 3 X : Set X))
    (hTC : ∀ C : Subgroup X, CFSG.IsComponent C → T ≤ centralizer (C : Set X)) : T = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgf : CFSG.generalizedFitting X = CFSG.pCore 3 X ⊔ CFSG.layer X := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore X 3 hO]
  have h1 : CFSG.pCore 3 X ≤ centralizer (T : Set X) := Subgroup.le_centralizer_iff.mp hTA
  have h2 : CFSG.layer X ≤ centralizer (T : Set X) := by
    refine sSup_le fun C hC => ?_
    exact Subgroup.le_centralizer_iff.mp (hTC C hC)
  have hgfle : CFSG.generalizedFitting X ≤ centralizer (T : Set X) := by
    rw [hgf]
    exact sup_le h1 h2
  have hT1 : T ≤ centralizer (CFSG.generalizedFitting X : Set X) :=
    Subgroup.le_centralizer_iff.mpr hgfle
  have hT2 : T ≤ CFSG.fittingSubgroup X :=
    hT1.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup X)
  rw [CFSG.Fitting_eq_pcore X 3 hO] at hT2
  have hT3 : IsPGroup 3 T := (CFSG.pCore_isPGroup (p := 3) (G := X)).to_le hT2
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  obtain ⟨n, hn⟩ := hT3 ⟨t, ht⟩
  obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
  have hn' : t ^ 3 ^ n = 1 := congrArg Subtype.val hn
  have hm' : t ^ d ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (3 ^ n) (d ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_three hd).mpr (Ne.symm hd3))
  have h3 : orderOf t ∣ Nat.gcd (3 ^ n) (d ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hm')
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
