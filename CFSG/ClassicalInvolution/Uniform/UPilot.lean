module

public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Uniform.UOmega4
public import CFSG.ClassicalInvolution.Uniform.USaturate
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Omega4Three

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem omega4_of_classical3 (h₀ : Q3.IsClassicalMember3 K₀ z₀)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({z₀} : Set G)) ≤ K₀) {K J : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀) (hne : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) :=
  omega4_of_memberU (MemberType.cert_sl2 3 1) (IsClassicalMemberU.ofQ3 h₀) (fun _ => hO) hK hJ hne

theorem omega4_of_classical3_saturate (h₀ : Q3.IsClassicalMember3 K₀ z₀) {K J : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass
      (K₀ ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z₀} : Set G))))
    (hJ : J ∈ CoreAssembly.conjClass
      (K₀ ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z₀} : Set G))))
    (hne : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) := by
  obtain ⟨hm, hi⟩ := (IsClassicalMemberU.ofQ3 h₀).saturate (show (3 : ℕ) ^ 1 = 3 by norm_num)
  exact omega4_of_memberU (MemberType.cert_sl2 3 1) hm hi hK hJ hne

end Omega4Three

section ThmI

variable {t : MemberType} {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

theorem twinsCommuteModOdd_of_memberU (h : IsClassicalMemberU t K z) (hi : IsIntrinsicU t K z) :
    Hat2A7R.TwinsCommuteModOdd K z := by
  intro g hg hgn
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hne : K ≠ conjSub g K := fun h' => hgn (map_conj_eq_iff_mem_normalizer.mp h'.symm)
  have hKg : IsClassicalMemberU t (conjSub g K) z := by
    have := h.conj g
    rwa [hgz] at this
  exact (twins_of_memberU h hKg hi (hi.conj_centralizer hg) hne).2.2.2

theorem thmIHyp_of_memberU (hc : t.Cert) (h : IsClassicalMemberU t K z) (hi : IsIntrinsicU t K z)
    (h3 : Hat2A7R.TwoElementsNormalize K z) : Hat2A7R.ThmIHyp K z where
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := h.subnormal
  unique_involution _ hw hw2 :=
    ConnectedA2.eq_of_orderOf_eq_two_of_isUniqueInvolution (h.isUniqueInvolution hc) hw hw2
  nonabelian_sylow T := h.exists_noncomm_sylow hc T
  two_elements := h3
  twins_commute := twinsCommuteModOdd_of_memberU h hi

end ThmI

section FusionCore

@[expose] def TwoElementsNormalizeU (t : MemberType) : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (K : Subgroup F) (z : F), IsClassicalMemberU t K z → IsIntrinsicU t K z →
      Hat2A7R.TwoElementsNormalize K z

theorem twoElementsNormalizeU_twoA7_iff :
    TwoElementsNormalizeU .twoA7 ↔ Hat2A7R.A7Omega5 :=
  ⟨fun h F _ _ _ hnab K z hK => h F hnab K z (IsClassicalMemberU.of2A7 hK)
      (IsIntrinsicU.of_not_isSolvableType MemberType.not_isSolvableType_twoA7),
    fun h F _ _ _ hnab K z hK _ => h F hnab K z hK.to2A7⟩

end FusionCore

end CFSG.ClassicalInvolution.Uniform
