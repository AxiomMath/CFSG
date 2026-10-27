module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn ThreeTen)

section SylowInHull

variable {H : Type} [Group H] {p : ℕ}

theorem p_sylow_le_oPPrimeHull (hp : p.Prime) {P : Subgroup H}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    P ≤ oPPrimeHull p (⊤ : Subgroup H) := by
  intro x hx
  obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_dvd_pow (⟨x, hx⟩ : P)
  have hk' : orderOf x ∣ p ^ k := by rwa [Subgroup.orderOf_mk] at hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hk'
  rw [oPPrimeHull]
  exact Subgroup.subset_closure ⟨Subgroup.mem_top x, m, hm⟩

theorem p_sylow_le_of_oPPrimeHull_eq (hp : p.Prime) {P I : Subgroup H}
    (hI : I = oPPrimeHull p (⊤ : Subgroup H))
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) : P ≤ I := by
  rw [hI]
  exact p_sylow_le_oPPrimeHull hp hP

end SylowInHull

section ResidualNormal

variable {H : Type} [Group H] [Finite H] {p : ℕ}

theorem normal_of_oPPrimeHull_eq {I : Subgroup H}
    (hI : I = oPPrimeHull p (⊤ : Subgroup H)) : I.Normal := by
  rw [hI]
  exact oPPrimeHull_top_normal p

end ResidualNormal

section OrderBasics

variable {H : Type} [Group H] {I D Y : Subgroup H}

theorem Y_lt_of_le (hDI : D ≤ I) (hY : Y < I ⊔ D) : Y < I := by
  rwa [sup_eq_left.mpr hDI] at hY

theorem Y_ne_left_of_le (hDI : D ≤ I) (hY : Y < I ⊔ D) : Y ≠ I :=
  ne_of_lt (Y_lt_of_le hDI hY)

theorem Y_le_left_of_le (hDI : D ≤ I) (hY : Y < I ⊔ D) : Y ≤ I :=
  (Y_lt_of_le hDI hY).le

end OrderBasics

section CaseSplit

@[expose] def ThreeTenHyp {H : Type} [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ) :
    Prop :=
  p.Prime ∧ p ≠ 2 ∧ d.Prime ∧ d ≠ 2 ∧ d ≠ p ∧
    I = oPPrimeHull p (⊤ : Subgroup H) ∧
    CFSG.ABGLocalTools.IsSylowOf d D ⊤ ∧ D ≠ ⊥ ∧
    CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧
    Y < I ⊔ D ∧ gammaIn 1 d D (I ⊔ D) ≤ Y ∧
    Subgroup.normalizer (P : Set H) ⊓ I ≤ Y

@[expose] def ThreeTenConcl {H : Type} [Group H] (I D Y : Subgroup H) (p d : ℕ) : Prop :=
  IsCyclic ↥D ∧ D ≤ I ∧ IsSLType 3 (ZMod p) ↥I ∧ d ∣ p + 1 ∧ IsMaxParabolicP p I Y

@[expose] def ThreeTenCase1 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    ThreeTenHyp I D P Y p d →
      (IsSLType 2 (ZMod p) ↥I ∨ IsPSLType 2 (ZMod p) ↥I ∨ IsSLType 3 (ZMod p) ↥I) →
        ThreeTenConcl I D Y p d

@[expose] def ThreeTenCase2 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    ThreeTenHyp I D P Y p d →
      (p = 7 ∧
        IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
          (fun B _ => Nat.card B = 2) ↥I) →
        ThreeTenConcl I D Y p d

@[expose] def ThreeTenCase3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    ThreeTenHyp I D P Y p d →
      (p = 5 ∧
        (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
            (fun B _ => Nat.card B = 2) ↥I ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) ↥I ∨
          IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) ↥I)) →
        ThreeTenConcl I D Y p d

@[expose] def ThreeTenCase4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    ThreeTenHyp I D P Y p d →
      (p = 3 ∧
        (IsSLType 2 (ZMod 5) ↥I ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) ↥I)) →
        ThreeTenConcl I D Y p d

theorem threeTen_of_cases (h1 : ThreeTenCase1) (h2 : ThreeTenCase2) (h3 : ThreeTenCase3)
    (h4 : ThreeTenCase4) : ThreeTen := by
  intro H _ _ I D P Y p d hp hp2 hd hd2 hdp hI hD hDne hP hY hγ hN hcase
  have hbase : ThreeTenHyp I D P Y p d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hY, hγ, hN⟩
  rcases hcase with h | h | h | h
  · exact h1 H I D P Y p d hbase h
  · exact h2 H I D P Y p d hbase h
  · exact h3 H I D P Y p d hbase h
  · exact h4 H I D P Y p d hbase h

end CaseSplit

end CFSG.LocalAnalysis.AGL81I.Section3
