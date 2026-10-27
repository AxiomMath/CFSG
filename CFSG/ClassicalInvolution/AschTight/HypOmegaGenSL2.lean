module

public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenOfNormalizer
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
import CFSG.ClassicalInvolution.AschTight.S19MFund
import CFSG.ClassicalInvolution.AschTight.S1916F1
import CFSG.ClassicalInvolution.Q3.Q3TNGen
import CFSG.GH74.GLS.IVK.L2.ExistArith

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {F : Type} [Field F] [Finite F]

omit [Finite G] [Finite F] in
theorem mul_self_eq_one_of_mulEquiv_sl2 (e : ↥K ≃* SL(2, F)) {x : G} (hx : x ∈ K)
    (hc : ∀ y ∈ K, x * y = y * x) : x * x = 1 := by
  have hcen : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  have hcen' : e ⟨x, hx⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := e.surjective s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen y]
  have hsq : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
    simpa [pow_two] using CFSG.ABGLocalTools.sq_eq_one_of_mem_center hcen'
  have h2 : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := e.injective (by rw [map_mul, hsq, map_one])
  simpa using congrArg Subtype.val h2

theorem exists_isSylow2In_not_isMulCommutative_of_mulEquiv_sl2 (hodd : Odd (Nat.card F))
    (e : ↥K ≃* SL(2, F)) : ∃ P : Subgroup G, IsSylow2In P K ∧ ¬ IsMulCommutative ↥P := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  refine ⟨(Q : Subgroup ↥K).map K.subtype, isSylow2In_map_sylow K Q, ?_⟩
  intro h
  have hQ : IsMulCommutative ↥(Q : Subgroup ↥K) := by
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective (Q : Subgroup ↥K)]
    exact Subgroup.comap_injective_isMulCommutative _ K.subtype_injective
  have hmap : IsMulCommutative ↥((Q : Subgroup ↥K).map e.toMonoidHom) :=
    Subgroup.map_isMulCommutative (Q : Subgroup ↥K) e.toMonoidHom
  have hnot := CFSG.Semidihedral.OddFieldSL2.sylow_two_not_isMulCommutative F hodd
    (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [show ↑(Q.mapSurjective (f := e.toMonoidHom) e.surjective) =
    (Q : Subgroup ↥K).map e.toMonoidHom from
      Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective Q] at hnot
  exact hnot hmap

theorem factorization_two_natCard_sl2_galoisField_three_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {e : ℕ} (he : 1 ≤ e) :
    (Nat.card SL(2, GaloisField p (3 * e))).factorization 2 =
      (Nat.card SL(2, GaloisField p e)).factorization 2 := by
  have hp : p.Prime := Fact.out
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card p (3 * e) (by omega),
    GaloisField.card p e (by omega), pow_mul', Nat.factorization_def _ Nat.prime_two,
    Nat.factorization_def _ Nat.prime_two]
  exact CFSG.GH74.GLS.IVK.padicValNat_card_odd (hp.odd_of_ne_two hp2).pow
    (Nat.one_lt_pow (by omega) hp.one_lt) ⟨1, rfl⟩

theorem omega2_of_mulEquiv_sl2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hsl2 : ∃ f : ℕ, (f = e ∨ f = 3 * e) ∧ Nonempty (↥K ≃* SL(2, GaloisField p f))) :
    Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K ∨
      Nonempty (↥K ⧸ CFSG.Open.classicalInvolutionOddCore ↥K ≃* SL(2, ZMod 3)) := by
  obtain ⟨f, hf, ⟨φ⟩⟩ := hsl2
  have hf1 : 1 ≤ f := by rcases hf with rfl | rfl <;> omega
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  by_cases h4 : 4 ≤ Nat.card (GaloisField p f)
  · left
    have hqs : CFSG.Open.IsQuasisimple ↥K :=
      CFSG.Open.IsQuasisimple.of_mulEquiv φ
        (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two h4)
    have : Group.IsPerfect ↥K := ⟨hqs.1⟩
    exact closure_twoElements_eq
  · right
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    have hge : 3 ≤ Nat.card (GaloisField p f) := by
      rw [hcard]
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf1
    have hcard3 : Nat.card (GaloisField p f) = 3 := by omega
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    have hring : GaloisField p f ≃+* ZMod 3 :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card (α := GaloisField p f), hcard3, ZMod.card])
    let e3 : ↥K ≃* SL(2, ZMod 3) := φ.trans (S1916.slEquiv hring)
    have hO : CFSG.Open.classicalInvolutionOddCore ↥K = ⊥ :=
      CFSG.ClassicalInvolution.Q3.Q3T.oddCore_eq_bot_of_mulEquiv_sl2 e3
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e3⟩

theorem hypOmegaGen_of_mulEquiv_sl2_of_commute {Ω : Set (Subgroup G)} {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hconj : ConjInvariant Ω)
    (hsl2 : ∀ K ∈ Ω, ∃ f : ℕ, (f = e ∨ f = 3 * e) ∧ Nonempty (↥K ≃* SL(2, GaloisField p f)))
    (hcomm : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → 2 ∣ Nat.card ↥(K ⊓ J) → ⁅K, J⁆ = ⊥)
    (hnorm : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
      (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (K : Set G)) :
    HypOmegaGen Ω := by
  have hf1 : ∀ f : ℕ, (f = e ∨ f = 3 * e) → 1 ≤ f := by
    intro f hf
    rcases hf with rfl | rfl <;> omega
  refine hypOmegaGen_of_commute hconj ?_ ?_ ?_ ?_ ?_ hcomm hnorm
  · intro K hK
    obtain ⟨f, hf, ⟨φ⟩⟩ := hsl2 K hK
    exact S19M.exists_isUniqueInvolution_of_equiv_sl2
      (S19M.odd_natCard_galoisField hp2 (hf1 f hf)) φ
  · intro K hK x hx hc
    obtain ⟨f, -, ⟨φ⟩⟩ := hsl2 K hK
    exact mul_self_eq_one_of_mulEquiv_sl2 φ hx hc
  · intro K hK
    obtain ⟨f, hf, ⟨φ⟩⟩ := hsl2 K hK
    exact exists_isSylow2In_not_isMulCommutative_of_mulEquiv_sl2
      (S19M.odd_natCard_galoisField hp2 (hf1 f hf)) φ
  · intro K hK
    exact omega2_of_mulEquiv_sl2 hp2 he (hsl2 K hK)
  · intro K hK J hJ P Q hP hQ
    obtain ⟨f, hf, ⟨φ⟩⟩ := hsl2 K hK
    obtain ⟨g, hg, ⟨ψ⟩⟩ := hsl2 J hJ
    rw [CFSG.ClassicalInvolution.Asc77.AscL62.natCard_eq_pow_of_isSylow2In hP,
      CFSG.ClassicalInvolution.Asc77.AscL62.natCard_eq_pow_of_isSylow2In hQ,
      Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
    · rfl
    · rw [factorization_two_natCard_sl2_galoisField_three_mul hp2 he]
    · rw [factorization_two_natCard_sl2_galoisField_three_mul hp2 he]
    · rfl

end CFSG.ClassicalInvolution.Disconnected.AschTight
