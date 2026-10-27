module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open scoped MatrixGroups

@[expose] noncomputable def socSL {A : Type*} [Group A] (T : Subgroup A) [T.Normal] (z : A) :
    Subgroup (MulAut ↥T) :=
  (perfectCore (T ⊓ Subgroup.centralizer ({z} : Set A))).map (MulAut.conjNormal (H := T))

@[expose] def SocF4L3 (r : ℕ) : Prop :=
  4 ≤ r → ∀ (A : Type) [Group A] [Finite A] (T : Subgroup A) [T.Normal], IsSimpleGroup ↥T →
    (∃ a b : ↥T, a * b ≠ b * a) → Subgroup.centralizer (T : Set A) = ⊥ → EdgelessFamily ↥T →
    ∀ (R : Subgroup A) (S : Sylow 2 R) (z : A), TightDatum R S z → TightClsR r A R S z →
      ¬ TightInO2 z → TightEdgeless R →
      SmallL3Ne3 ↥T →
        socSL T z ≤ autCentOf T (sylowSet S) ∧
        autCentOf T (sylowSet S) ≤ Subgroup.normalizer ((socSL T z : Subgroup (MulAut ↥T)) :
          Set (MulAut ↥T)) ∧
        Odd ((socSL T z).relIndex (autCentOf T (sylowSet S))) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧ 4 ≤ Nat.card K ∧
          Nonempty (↥(socSL T z) ≃* SL(2, K))

@[expose] def SocF4U3 (r : ℕ) : Prop :=
  4 ≤ r → ∀ (A : Type) [Group A] [Finite A] (T : Subgroup A) [T.Normal], IsSimpleGroup ↥T →
    (∃ a b : ↥T, a * b ≠ b * a) → Subgroup.centralizer (T : Set A) = ⊥ → EdgelessFamily ↥T →
    ∀ (R : Subgroup A) (S : Sylow 2 R) (z : A), TightDatum R S z → TightClsR r A R S z →
      ¬ TightInO2 z → TightEdgeless R →
      SmallU3Ne3 ↥T →
        socSL T z ≤ autCentOf T (sylowSet S) ∧
        autCentOf T (sylowSet S) ≤ Subgroup.normalizer ((socSL T z : Subgroup (MulAut ↥T)) :
          Set (MulAut ↥T)) ∧
        Odd ((socSL T z).relIndex (autCentOf T (sylowSet S))) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧ 4 ≤ Nat.card K ∧
          Nonempty (↥(socSL T z) ≃* SL(2, K))

theorem mem_of_odd_relIndex {G : Type*} [Group G] [Finite G] {Y N : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (N.relIndex Y)) {s : G} (hs : s ∈ Y)
    {k : ℕ} (hk : s ^ 2 ^ k = 1) : s ∈ N := by
  have : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  set x := (QuotientGroup.mk (⟨s, hs⟩ : Y) : Y ⧸ N.subgroupOf Y) with hx
  have h1 : orderOf x ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨s, hs⟩ : Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have h2 : orderOf x ∣ (N.subgroupOf Y).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard x
  have hcop : Nat.Coprime (2 ^ k) ((N.subgroupOf Y).index) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : x = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hx, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem eq_of_sl2_odd_index {G : Type*} [Group G] [Finite G] {Y N : Subgroup G}
    (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (N.relIndex Y))
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (e : ↥N ≃* SL(2, K)) {ψ c : G}
    (hψY : ψ ∈ Y) (hψ : ψ * ψ = 1) (hcY : c ∈ Y) (hc : c * c = 1) (hc1 : c ≠ 1) :
    ψ = 1 ∨ ψ = c := by
  have hψN : ψ ∈ N := mem_of_odd_relIndex hYN hodd hψY (k := 1) (by rw [pow_one, pow_two]; exact hψ)
  have hcN : c ∈ N := mem_of_odd_relIndex hYN hodd hcY (k := 1) (by rw [pow_one, pow_two]; exact hc)
  have hcord : orderOf (⟨c, hcN⟩ : ↥N) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hc)
    · intro h1
      exact hc1 (congrArg Subtype.val h1)
  by_cases hψ1 : ψ = 1
  · exact Or.inl hψ1
  · right
    have hψord : orderOf (⟨ψ, hψN⟩ : ↥N) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hψ)) (fun h1 => hψ1 (congrArg Subtype.val h1))
    have h1 := (orderOf_eq_two_iff_of_equiv_sl2 hK e _).mp hψord
    have h2 := (orderOf_eq_two_iff_of_equiv_sl2 hK e _).mp hcord
    exact congrArg Subtype.val (h1.trans h2.symm)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
