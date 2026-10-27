module

public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk4Basic

open Subgroup

variable {G : Type} [Group G]

theorem exists_comm_involution [Finite G] {M : Subgroup G} {y : G} (hy : y * y = 1)
    (hyM : ∀ m ∈ M, y * m * y⁻¹ ∈ M) (hM : 2 ∣ Nat.card ↥M) :
    ∃ v ∈ M, v * v = 1 ∧ v ≠ 1 ∧ y * v = v * y := by
  classical
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let f : Function.End ↥M := fun m => ⟨y * m * y⁻¹, hyM m m.2⟩
  have hff : ∀ m : ↥M, f (f m) = m := by
    intro m
    apply Subtype.ext
    show y * (y * (m : G) * y⁻¹) * y⁻¹ = m
    calc y * (y * (m : G) * y⁻¹) * y⁻¹ = (y * y) * (m : G) * (y * y)⁻¹ := by group
      _ = m := by rw [hy]; group
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext m
    exact hff m
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥M := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥M) (f := f) (p := 2) (n := 1) hf
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at hmod
  let C : Subgroup G := M ⊓ centralizer ({y} : Set G)
  have hCfix : Nat.card ↥C = Nat.card (Function.fixedPoints f) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.1 c.2).1⟩, ?_⟩
        invFun := fun s => ⟨(s.1 : G), Subgroup.mem_inf.2 ⟨s.1.2, ?_⟩⟩
        left_inv := fun c => rfl
        right_inv := fun s => rfl }
    · have h1 : (c.1 : G) * y = y * (c.1 : G) :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2
      apply Subtype.ext
      show y * (c.1 : G) * y⁻¹ = c.1
      rw [← h1]; group
    · have h1 : y * ((s.1 : ↥M) : G) * y⁻¹ = ((s.1 : ↥M) : G) := congrArg Subtype.val s.2
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc ((s.1 : ↥M) : G) * y = (y * ((s.1 : ↥M) : G) * y⁻¹) * y := by rw [h1]
        _ = y * ((s.1 : ↥M) : G) := by group
  have hdvd : 2 ∣ Nat.card ↥C := by
    rw [hCfix]
    have h0 : Nat.card ↥M ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.2 hM
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans h0)
  have : Finite ↥C := inferInstance
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hc2 : (c : G) * c = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc, pow_two] at this
    exact congrArg Subtype.val this
  have hc1 : (c : G) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc
    omega
  exact ⟨c, (Subgroup.mem_inf.1 c.2).1, hc2, hc1,
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2).symm⟩

theorem exists_two_invol {P : Type} [Group P] [Finite P] (h : 2 ≤ CFSG.pRank 2 P) :
    ∃ a b : P, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := hE.2 e he
    rwa [sq] at this
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    have := hE.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  have h4 : Nat.card ↥E = 4 := by rw [hcard]; norm_num
  have hnt : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥E)
  have haE : (a : P) ∈ E := a.2
  have ha1' : (a : P) ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have hord : orderOf (a : P) = 2 := orderOf_eq_prime (by rw [sq]; exact hsq a a.2) ha1'
  obtain ⟨b, hbE, hb⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers (a : P) := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers (a : P) := hcon
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, h4] at this
    omega
  have hb1 : b ≠ 1 := fun h' => hb (h' ▸ one_mem _)
  have hba : (a : P) ≠ b := fun h' => hb (h' ▸ Subgroup.mem_zpowers _)
  exact ⟨a, b, hsq a a.2, hsq b hbE, ha1', hb1, hba, hcomm a a.2 b hbE⟩

theorem pRank_range_eq {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q] (φ : P →* Q)
    (hker : ¬ 2 ∣ Nat.card φ.ker) : CFSG.pRank 2 φ.range = CFSG.pRank 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two φ.ker hker,
    CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_two.one_lt
    (QuotientGroup.quotientKerEquivRange φ)).symm

end S3Rk4Basic

end CFSG.GH74.Generic.BProg.B3
