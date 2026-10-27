module

public import Mathlib
public import CFSG.LinearAlgebra.LinearGroups.RegularPermutationSign
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalInvolutions
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem exists_signHom_of_cyclic_sylow_two {G : Type*} [Group G] [Finite G]
    (h2 : 2 ∣ Nat.card G) (P : Sylow 2 G) (hP : IsCyclic P) :
    ∃ (φ : G →* ℤˣ) (g : G), φ g ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := hP.exists_generator
  have hord : orderOf (g : G) = Nat.card P := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hP2 : Nat.card P = 2 ^ (Nat.card G).factorization 2 := P.card_eq_multiplicity
  have hk : 1 ≤ (Nat.card G).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have hmeven : Even (Nat.card P) := by
    rw [hP2]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hidx : Odd (P : Subgroup G).index := by
    have := P.not_dvd_index
    exact Nat.odd_iff.mpr (by omega)
  have hcard : Nat.card G = Nat.card P * (P : Subgroup G).index :=
    ((P : Subgroup G).card_mul_index).symm
  have hPpos : 0 < Nat.card P := Nat.card_pos
  obtain ⟨-, -, hsign⟩ := CFSG.LinearGroups.regular_permutation_sign (g : G)
  rw [← Nat.card_eq_fintype_card, hord, hcard, Nat.mul_div_cancel_left _ hPpos] at hsign
  have hodd : Odd (Nat.card P * (P : Subgroup G).index - (P : Subgroup G).index) := by
    have h1 : Nat.card P * (P : Subgroup G).index - (P : Subgroup G).index =
        (P : Subgroup G).index * (Nat.card P - 1) := by
      rw [Nat.mul_sub, mul_one, mul_comm]
    rw [h1]
    exact hidx.mul (Nat.Even.sub_odd hPpos hmeven odd_one)
  refine ⟨Equiv.Perm.sign.comp (MulAction.toPermHom G G), g, ?_⟩
  have h : (Equiv.Perm.sign.comp (MulAction.toPermHom G G)) (g : G) = -1 := by
    change Equiv.Perm.sign (MulAction.toPerm (g : G)) = -1
    have : (MulAction.toPerm (g : G) : Equiv.Perm G) = Equiv.mulLeft (g : G) :=
      Equiv.ext fun x => rfl
    rw [this, hsign]
    exact hodd.neg_one_pow
  rw [h]
  decide

theorem eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] [Group.IsPerfect G]
    (ψ : G →* A) (x : G) : ψ x = 1 := by
  have hle : commutator G ≤ ψ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    simp
  have : x ∈ ψ.ker := hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top x)
  exact this

theorem eq_one_of_oddCore_of_perfect {K H : Type*} [Group K] [Group H] [Group.IsPerfect H]
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O)) (e : K ⧸ O ≃* H) (φ : K →* ℤˣ)
    (x : K) : φ x = 1 := by
  have hker : O ≤ φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (φ y) ∣ orderOf y := orderOf_map_dvd φ y
    have h2 : orderOf y ∣ Nat.card O := by
      have := Subgroup.orderOf_dvd_natCard O hy
      simpa using this
    have h3 : orderOf (φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_sq (φ y))
    have h4 : orderOf (φ y) ∣ Nat.card O := h1.trans h2
    have h5 : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr hO
    have h6 : orderOf (φ y) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 h5) h4
    exact orderOf_eq_one_iff.mp h6
  have := eq_one_of_perfect ((QuotientGroup.lift O φ hker).comp e.symm.toMonoidHom)
    (e (x : K ⧸ O))
  simpa using this

theorem noCommutingDistinctInvolutions_of_sl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {K : Type} [Group K] [Finite K]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (T : Subgroup K) :
    NoCommutingDistinctInvolutions T := by
  intro a b hab
  have ha : orderOf (a.1 : K) = 2 := (Subgroup.orderOf_coe a.1).trans a.2
  have hb : orderOf (b.1 : K) = 2 := (Subgroup.orderOf_coe b.1).trans b.2
  have hab' : (a.1 : K) * b.1 = b.1 * a.1 := by
    have := congrArg Subtype.val hab
    simpa using this
  by_contra hne
  refine CFSG.ClassicalInvolution.ModelFacts.false_of_two_commuting_involutions_sl2 hodd e ha hb
    hab' fun h => hne (Subtype.ext (Subtype.ext h))

theorem even_card_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    2 ∣ Nat.card SL(2, F) := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hsq : (-1 : SL(2, F)) ^ 2 = 1 := by
    apply Subtype.ext
    simp
  have hord : orderOf (-1 : SL(2, F)) = 2 :=
    orderOf_eq_prime hsq (CFSG.ABGLocalTools.sl2_neg_one_ne_one h2)
  have := orderOf_dvd_natCard (-1 : SL(2, F))
  rwa [hord] at this

theorem exists_quaternion_of_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {K : Type} [Group K] [Finite K]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (T : Sylow 2 K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hNC := noCommutingDistinctInvolutions_of_sl2 hodd e (T : Subgroup K)
  rcases rank_one_two_cyclic_or_quaternion T.isPGroup' hNC with hcyc | ⟨ex, hex, ⟨φ⟩⟩
  · exfalso
    have := Fintype.ofFinite F
    have h4 : ∃ s : Finset F, s.card = 4 := by
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact ⟨s, hs⟩
    have : Group.IsPerfect SL(2, F) :=
      CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
    have h2 : 2 ∣ Nat.card K := by
      have h1 : Nat.card (K ⧸ classicalInvolutionOddCore K) = Nat.card SL(2, F) :=
        Nat.card_congr e.toEquiv
      have h3 := (classicalInvolutionOddCore K).card_eq_card_quotient_mul_card_subgroup
      rw [h3, h1]
      exact Dvd.dvd.mul_right (even_card_sl2 hodd) _
    obtain ⟨ψ, g, hg⟩ := exists_signHom_of_cyclic_sylow_two h2 T hcyc
    exact hg (eq_one_of_oddCore_of_perfect (classicalInvolutionOddCore K)
      (CFSG.ComponentClassification.OddCore.odd_card K) e ψ g)
  · refine ⟨ex + 2, by omega, ⟨?_⟩⟩
    have hex2 : ex + 2 - 2 = ex := by omega
    rw [hex2]
    exact φ.symm

theorem quaternion_sylow_of_isClassicalMember {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    [Finite G] {K : Subgroup G} {z : G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (T : Sylow 2 K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two (Fact.out) hp2).pow
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    exact hq
  exact exists_quaternion_of_sl2 hodd h5 e T

end CFSG.ClassicalInvolution.Disconnected
