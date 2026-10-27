module

public import CFSG.ClassicalInvolution.Balance.BootstrapFunctor
import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Balance.PassTwo

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_oddCoreIn_le_of_member [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {K : Subgroup G} {z : G} (hKΩ : K ∈ Ω)
    (hz : IsClassicalMember p f K z) (hzA : z ∈ A) (hKA : K ≤ Subgroup.centralizer (A : Set G))
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    ⁅oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}), K⁆ ≤
      involutionOddCore b := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hW : WeakMember (GaloisField p f) K z :=
    ⟨hz.orderOf_eq_two, hz.mem, hz.perfect, hz.subnormal, hz.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf (fun k hk => Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) (hKA hk)) hKA
  have hsub : IsSubnormal K (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer
      (A : Set G)) :=
    isSubnormal_inf_centralizer_of_isSubnormal hzA hKa hz.subnormal
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hA.2 a ha
  have htL : ∀ l ∈ K, a * l = l * a := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hKA hl) a ha
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    hKA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  exact commutator_oddCoreIn_le_of_l2PrimeBalance l2PrimeBalance hA hb hAa hKa hsub
    hmem.perfect hmem.quasisimple fun M hM =>
      hB_of_localLieSystems_of_centralizes hp2 h0 hA1 hΩ hIH hKΩ ha2 ha1 htL
        (not_subset_center_of_ne_one hnab hb1) hKb hab M hM

theorem weakBalanced_of_members [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {A : Subgroup G} {S : Set G}
    (hA : IsElemAbelian 2 A) (hAS : A = Subgroup.closure S)
    (hS : ∀ z ∈ S, ∃ K ∈ Ω, IsClassicalMember p f K z ∧
      K ≤ Subgroup.centralizer (A : Set G)) :
    WeakBalanced A := by
  intro a ha ha1 b hb hb1
  rw [Subgroup.commutator_le]
  intro r hr g hg
  have hbC : ∀ x ∈ A, x ∈ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨b, hb⟩))
  have hR : involutionOddCore a ⊓ Subgroup.centralizer {b} ≤
      oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := by
    refine le_oddCoreIn_of_normalizes (inf_le_inf (involutionOddCore_le_centralizer a) le_rfl)
      (fun x hx => mem_normalizer_inf (normalizer_oddCoreIn _ hx.1)
        (Subgroup.le_normalizer hx.2)) ?_
    exact (odd_card_oddCoreIn (Subgroup.centralizer {a})).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hrR : r ∈ oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := hR hr
  have key : ∀ x ∈ Subgroup.closure S, ⁅r, x⁆ ∈ involutionOddCore b := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ⁅r, x⁆ ∈ involutionOddCore b) ?_ ?_ ?_ ?_ hx
    · intro z hz
      obtain ⟨K, hKΩ, hzK, hKA⟩ := hS z hz
      have hzA : z ∈ A := hAS ▸ Subgroup.subset_closure hz
      exact commutator_oddCoreIn_le_of_member hnab hp2 hq h0 hA1 hΩ hIH hA hKΩ hzK hzA hKA ha ha1
        hb hb1 (Subgroup.commutator_mem_commutator hrR hzK.mem)
    · simp
    · intro x y hx hy hxM hyM
      have hxA : x ∈ A := hAS ▸ hx
      have : ⁅r, x * y⁆ = ⁅r, x⁆ * (x * ⁅r, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (involutionOddCore b).mul_mem hxM (conj_mem_oddCoreIn (hbC x hxA) hyM)
    · intro x hx hxM
      have hxA : x ∈ A := hAS ▸ hx
      have : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact conj_mem_oddCoreIn (inv_mem (hbC x hxA)) ((involutionOddCore b).inv_mem hxM)
  exact key g (hAS ▸ hg)

end CFSG.ClassicalInvolution.Balance.Bootstrap
