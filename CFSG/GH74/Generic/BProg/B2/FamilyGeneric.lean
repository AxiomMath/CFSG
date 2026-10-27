module

public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseB
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace FamilyGeneric

open scoped Pointwise

theorem nc2_of_isQuasisimple {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) : NC2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hs, hnab⟩ := hq
  have := hs
  have hev : Even (Nat.card (J ⧸ center J)) :=
    (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨P⟩ : Nonempty (Sylow 2 J) := inferInstance
  have hPnot : ¬ (P : Subgroup J) ≤ center J := by
    intro hle
    have hdvd : Nat.card P ∣ Nat.card (center J) := Subgroup.card_dvd_of_le hle
    have hcardJ : Nat.card J = Nat.card (J ⧸ center J) * Nat.card (center J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center J)
    obtain ⟨k, hk⟩ := hev
    have hJne : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have hP : Nat.card P = 2 ^ (Nat.card J).factorization 2 := Sylow.card_eq_multiplicity P
    have h1 : 2 ^ ((Nat.card J).factorization 2 + 1) ∣ Nat.card J := by
      rw [pow_succ, ← hP, mul_comm]
      exact (Nat.mul_dvd_mul (dvd_refl 2) hdvd).trans ⟨k, by rw [hcardJ, hk]; ring⟩
    exact Nat.pow_succ_factorization_not_dvd hJne Nat.prime_two h1
  obtain ⟨x, hxP, hxZ⟩ : ∃ x ∈ (P : Subgroup J), x ∉ center J := by
    by_contra hcon
    push Not at hcon
    exact hPnot hcon
  refine ⟨x, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hxP⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · by_contra hcon
    push Not at hcon
    exact hxZ (Subgroup.mem_center_iff.2 fun g => (hcon g))

theorem exists_fixed_two_element {J A : Type} [Group J] [Finite J] [Group A] [Finite A]
    (hA : IsPGroup 2 A) (α : A →* MulAut J) (hev : 2 ∣ Nat.card J) :
    ∃ x : J, x ≠ 1 ∧ (∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ ∀ a : A, α a x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction A (Sylow 2 J) := MulAction.compHom (Sylow 2 J) α
  have hfix : (MulAction.fixedPoints A (Sylow 2 J)).Nonempty := by
    have h1 := hA.card_modEq_card_fixedPoints (Sylow 2 J)
    have h2 := not_dvd_card_sylow 2 J
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints A (Sylow 2 J)) = 0 := by rw [hne]; simp
    rw [h0] at h1
    exact h2 ((Nat.modEq_zero_iff_dvd).1 h1)
  obtain ⟨P, hP⟩ := hfix
  have hinv : ∀ (a : A) (x : J), x ∈ (P : Subgroup J) → α a x ∈ (P : Subgroup J) := by
    intro a x hx
    have h1 : (α a) • P = P := hP a
    have h2 : (α a) • (P : Subgroup J) = (P : Subgroup J) := by
      rw [← Sylow.pointwise_smul_def, h1]
    have h3 : (α a) • x ∈ (α a) • (P : Subgroup J) := smul_mem_pointwise_smul x (α a) _ hx
    rw [h2] at h3
    exact h3
  let _ : MulAction A (P : Subgroup J) :=
    { smul := fun a x => ⟨α a x, hinv a x x.2⟩
      one_smul := fun x => Subtype.ext (by show (α 1) (x : J) = x; rw [map_one]; rfl)
      mul_smul := fun a b x => Subtype.ext (by
        show α (a * b) (x : J) = α a (α b (x : J))
        rw [map_mul]; rfl) }
  have hmod := hA.card_modEq_card_fixedPoints (P : Subgroup J)
  have hPcard : Nat.card (P : Subgroup J) = 2 ^ (Nat.card J).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hfac : 1 ≤ (Nat.card J).factorization 2 := by
    have hJne : Nat.card J ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hJne).1 hev
  have hPeven : 2 ∣ Nat.card (P : Subgroup J) := by
    rw [hPcard]
    exact dvd_pow_self 2 (by omega)
  have hone : (1 : (P : Subgroup J)) ∈ MulAction.fixedPoints A (P : Subgroup J) := fun a =>
    Subtype.ext (by
      show α a 1 = 1
      simp)
  by_contra hcon
  push Not at hcon
  have huniq : ∀ y ∈ MulAction.fixedPoints A (P : Subgroup J), y = 1 := by
    intro y hy
    by_contra hy1
    obtain ⟨n, hn⟩ := P.isPGroup' y
    obtain ⟨a, ha⟩ := hcon (y : J) (fun h => hy1 (Subtype.ext h)) ⟨n, congrArg Subtype.val hn⟩
    exact ha (congrArg Subtype.val (hy a))
  have hcardfix : Nat.card (MulAction.fixedPoints A (P : Subgroup J)) = 1 := by
    have : Unique (MulAction.fixedPoints A (P : Subgroup J)) :=
      ⟨⟨⟨1, hone⟩⟩, fun y => Subtype.ext (huniq y.1 y.2)⟩
    exact Nat.card_unique
  rw [hcardfix] at hmod
  have h1 : Nat.card (P : Subgroup J) % 2 = 1 % 2 := hmod
  have h2 : Nat.card (P : Subgroup J) % 2 = 0 := Nat.mod_eq_zero_of_dvd hPeven
  omega

theorem locE3_of_trivial_center {J : Type} [Group J] [Finite J]
    (hZ : ∀ z : J, (∀ y : J, y * z = z * y) → z = 1) (hev : 2 ∣ Nat.card J) :
    ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → LocE3 α := by
  intro A _ _ α hA
  have hpg : IsPGroup 2 A := by
    have := hA.1
    exact CFSG.IsElementaryAbelian.isPGroup 2 A
  obtain ⟨x, hx1, hx2, hxfix⟩ := exists_fixed_two_element hpg α hev
  refine ⟨⊤, ?_, x, ?_, hx2, ?_⟩
  · have h := GenLocBasic.pRank_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
    omega
  · rw [mem_fixedIn]
    rintro φ ⟨a, -, rfl⟩
    exact hxfix a
  · by_contra hcon
    push Not at hcon
    exact hx1 (hZ x fun y => hcon y)

theorem weakSig2NormG4_of_genLoc4_qs {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : GenLoc4 J) : WeakSig2NormG4 J :=
  weakSig2NormG4_of_genLoc4 hq (WeakSigCaseB.two_dvd_natCard_of_nc2 (nc2_of_isQuasisimple hq))
    (nc2_of_isQuasisimple hq) h

theorem weakSig2TwoG4_of_genLoc4_simple {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J)
    (hq : IsQuasisimple J) (h : GenLoc4 J) : WeakSig2TwoG4 J :=
  weakSig2TwoG4_of_genLoc4 hs hq (nc2_of_isQuasisimple hq)
    (locE3_of_trivial_center (WeakSigCaseB.center_trivial_of_simple hs hq)
      (WeakSigCaseB.two_dvd_natCard_of_nc2 (nc2_of_isQuasisimple hq))) h

end FamilyGeneric

end CFSG.GH74.Generic.BProg.B2
