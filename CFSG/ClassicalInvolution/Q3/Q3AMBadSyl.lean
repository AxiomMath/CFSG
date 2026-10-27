module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm
public import CFSG.ClassicalInvolution.AschTight.Sec7L713F
import CFSG.ClassicalInvolution.AschTight.Hall196Wr2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem badEdge_exists_isSylow2In_normalized [Finite G] {M R : Subgroup G} (hR : IsPGroup 2 R)
    (hRM : R ≤ Subgroup.normalizer (M : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P M ∧ R ≤ Subgroup.normalizer (P : Set G) := by
  have hX : M ⊔ R ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hRM
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR (le_sup_right : R ≤ M ⊔ R)
  have hP : IsSylow2In (V ⊓ M) M := Sec7.isSylow2In_inf_of_normal hV le_sup_left hX
  refine ⟨V ⊓ M, hP, fun r hr => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hrV : r ∈ V := hRV hr
  have hrM : r ∈ Subgroup.normalizer (M : Set G) := hRM hr
  constructor
  · intro hh
    exact ⟨V.mul_mem (V.mul_mem hrV hh.1) (V.inv_mem hrV),
      (Subgroup.mem_normalizer_iff.mp hrM h).mp hh.2⟩
  · intro hh
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hrM h).mpr hh.2⟩
    have h1 : r⁻¹ * (r * h * r⁻¹) * r ∈ V :=
      V.mul_mem (V.mul_mem (V.inv_mem hrV) hh.1) hrV
    have h2 : r⁻¹ * (r * h * r⁻¹) * r = h := by group
    rwa [h2] at h1

theorem badEdge_eq_bot_of_le_inf [Finite G] {M N P : Subgroup G} {a t : G}
    (hUM : IsUniqueInvolution M a) (hUN : IsUniqueInvolution N t) (hat : a ≠ t)
    (hP : IsPGroup 2 P) (hPM : P ≤ M) (hPN : P ≤ N) : P = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  obtain ⟨n, hn, hcard⟩ := (hP.nontrivial_iff_card).mp inferInstance
  have h2 : 2 ∣ Nat.card ↥P := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have hyo : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyy : (y : G) * (y : G) = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hyo])
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyo
    omega
  have hya : (y : G) = a := (hUM.unique _ (hPM y.2) hyy).resolve_left hy1
  have hyt : (y : G) = t := (hUN.unique _ (hPN y.2) hyy).resolve_left hy1
  exact hat (hya.symm.trans hyt)

theorem badEdge_centSylow_three_modOdd [Finite G] {K R V : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) (hR : IsSylow2In R K)
    (hVK : ∀ y ∈ V, conjSub y K = K) (hcomm : ∀ r ∈ R, ∀ v ∈ V, ⁅v, r⁆ ∈ oddCoreOf K) :
    ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ oddCoreOf K := by
  intro k hk v hv
  have hvN : v ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hVK v hv)
  set φ : ↥K →* SL(2, ZMod 3) :=
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K →* SL(2, ZMod 3)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, ZMod 3) :=
    Sylow.mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, Q3T6.normalizerToAutSL3 e ⟨v, hvN⟩ x = x := by
    intro x hx
    have hx' : x ∈ ((AscL62.sylowOfIsSylow2In'' hR : Subgroup ↥K)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hαr : (QuotientGroup.mk (Disconnected.AschTight.normalizerConj K ⟨v, hvN⟩ r) :
        K ⧸ classicalInvolutionOddCore K) = QuotientGroup.mk r := by
      obtain ⟨o, ho, hoe⟩ := hcomm _ (R.inv_mem hrR) v hv
      have hoe' : (o : G) = ⁅v, (r : G)⁻¹⁆ := hoe
      have key : ((Disconnected.AschTight.normalizerConj K ⟨v, hvN⟩ r)⁻¹ * r : ↥K) = o := by
        apply Subtype.ext
        have e1 : ((((Disconnected.AschTight.normalizerConj K ⟨v, hvN⟩ r)⁻¹ * r : ↥K)) : G) =
            (v * (r : G) * v⁻¹)⁻¹ * (r : G) := rfl
        rw [e1, hoe']
        simp only [commutatorElement_def]
        group
      rw [QuotientGroup.eq, key]
      exact ho
    show Q3T6.normalizerToAutSL3 e ⟨v, hvN⟩ (e (QuotientGroup.mk r)) = e (QuotientGroup.mk r)
    rw [Q3T6.normalizerToAutSL3_apply, hαr]
  exact (Q3T6.normalizerToAutSL3_eq_one_iff e ⟨v, hvN⟩).mp
    (Q3T6.sl2Three_mulAut_eq_one_of_fixes_sylow P _ hfix) k hk

theorem badEdge_exists_mul_of_mem_sup {A B : Subgroup G} (h : Commutes A B) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b :=
  CFSG.ClassicalInvolution.Asc77.exists_mul_of_mem_sup_of_commutes h hx

theorem badEdge_natCard_sup_mul_natCard_inf {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card A * Nat.card C :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196.card_sup_mul_card_inf' hC

end CFSG.ClassicalInvolution.Q3.Q3AM
