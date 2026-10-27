module

public import CFSG.ClassicalInvolution.Asc77.AscC25J1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Member

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


theorem crossIn_fix9 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f = 9) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        SL(2, GaloisField 3 1)) := by
  obtain ⟨e₀, hfe, he₀, ⟨φ'⟩⟩ := fs_fix_equiv' hp hq e hbN hb2 hσ1
  obtain ⟨hp3, hf2⟩ := eq_three_two_of_pow_eq_nine (Fact.out : p.Prime) h9
  have he₁ : e₀ = 1 := by omega
  subst he₁
  subst hp3
  have hO : classicalInvolutionOddCore ↥(slFix e ⟨b, hbN⟩) = ⊥ := by
    have h3 : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 (by norm_num)]
      norm_num
    obtain ⟨e'⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
    exact CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv (φ'.trans e')
      CFSG.ClassicalInvolution.Q3.componentOddCore_sl2Three
  have hsurj := fixHom_surjective e hbN hb2
  have hker : Odd (Nat.card (fixHom e hbN).ker) := by
    have hle : (fixHom e hbN).ker.map (K ⊓ Subgroup.centralizer ({b} : Set G)).subtype ≤
        oddCoreOf K := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_oddCoreOf_of_fixHom_eq_one e hbN hx
    have hcard : Nat.card ((fixHom e hbN).ker.map
        (K ⊓ Subgroup.centralizer ({b} : Set G)).subtype) = Nat.card (fixHom e hbN).ker :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨ψ⟩ := nonempty_quotEquiv_of_surjective_of_odd _ hsurj hker hO
  exact ⟨ψ.trans φ'⟩

theorem crossIn_isClassicalMember {K : Subgroup G} {z : G} (hI : IsUniqueInvolution K z)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K = K → conjSub (y * x * y⁻¹) K = K)
    {b : G} (hzA : z ∈ Subgroup.centralizer ({b} : Set G))
    (hiso : Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        SL(2, GaloisField 3 1))) :
    IsClassicalMemberU (.sl2 3 1) (crossIn K b) ⟨z, hzA⟩ := by
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Ka := K ⊓ C with hKa
  have hKaA : Ka ≤ C := inf_le_right
  have hKaK : Ka ≤ K := inf_le_left
  have hzKa : z ∈ Ka := ⟨hI.mem, hzA⟩
  have e₁ : Ka.subgroupOf C ≃* Ka := Subgroup.subgroupOfEquivOfLe hKaA
  refine ⟨⟨Nat.prime_three, by norm_num, by norm_num⟩, ?_, Subgroup.mem_subgroupOf.mpr hzKa, ?_,
    ?_, fun h => absurd (by norm_num : (3 : ℕ) ^ 1 = 3) h⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one
  · set M := Subgroup.centralizer ({(⟨z, hzA⟩ : ↥C)} : Set ↥C) with hM
    set M₁ : Subgroup ↥C := M ⊓ (Subgroup.normalizer (K : Set G)).comap C.subtype with hM₁
    have hmemM : ∀ y : ↥C, y ∈ M ↔ (y : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      intro y
      rw [hM, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hle₁ : Ka.subgroupOf C ≤ M₁ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      refine ⟨(hmemM x).mpr (hKz (hKaK hx)), ?_⟩
      exact Subgroup.le_normalizer (hKaK hx)
    have hle₂ : M₁ ≤ M := inf_le_left
    refine IsSubnormal.step hle₁ ?_ (IsSubnormal.step hle₂ ?_ (IsSubnormal.refl M))
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle₁).mpr fun y hy => ?_
      have hyK : (y : G) ∈ Subgroup.normalizer (K : Set G) := hy.2
      have hyN := t9_le_normalizer (a := b) hyK y.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hyN x)
    · have hstep : ∀ y ∈ M, ∀ x ∈ M₁, y * x * y⁻¹ ∈ M₁ := by
        intro y hy x hx
        refine ⟨(M.mul_mem (M.mul_mem hy hx.1) (M.inv_mem hy)), ?_⟩
        have hxK : conjSub (x : G) K = K := mem_normalizer_iff_conjSub_eq.mp hx.2
        have := hconj (y : G) (x : G) ((hmemM y).mp hy) ((hmemM x).mp hx.1) hxK
        exact mem_normalizer_iff_conjSub_eq.mpr this
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle₂).mpr fun y hy => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hstep y hy x hx
      · intro hx
        have h1 := hstep y⁻¹ (M.inv_mem hy) _ hx
        have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
        rwa [e] at h1
  · exact ⟨inferInstance, ⟨(QuotientGroup.congr _ _ e₁
      (CFSG.ComponentClassification.OddCore.equiv_invariant e₁)).trans (Classical.choice hiso)⟩⟩

end Member

end CFSG.ClassicalInvolution.Asc77.C25J
