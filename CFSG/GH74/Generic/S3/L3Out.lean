module

public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)
open scoped MatrixGroups commutatorElement

@[expose] def PerfectInInn (S : Type*) [Group S] : Prop :=
  ∀ Q : Subgroup (MulAut S), ⁅Q, Q⁆ = Q → Q ≤ inner S

theorem PerfectInInn.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) (h : PerfectInInn T) :
    PerfectInInn S := by
  intro Q hQ
  let φ : MulAut S ≃* MulAut T := MulAut.congr e
  have hQ' : ⁅Q.map φ.toMonoidHom, Q.map φ.toMonoidHom⁆ = Q.map φ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hQ]
  have hle := h _ hQ'
  intro x hx
  have hx' : φ x ∈ inner T := hle ⟨x, hx, rfl⟩
  rw [← inner_map_congr e] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have : y = x := φ.injective hyx
  exact this ▸ hy


section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem perfectInInn_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    PerfectInInn (projectiveSL n K) := by
  intro Q hQ
  obtain ⟨hgen, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, -, -, h3⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at h3
  have hQ3 : ⁅⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆, ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆⁆ = Q := by simp only [hQ]
  have hmono : ⁅⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆, ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆⁆ ≤
      ⁅⁅⁅(⊤ : Subgroup (MulAut (projectiveSL n K))), ⊤⁆, ⁅⊤, ⊤⁆⁆, ⁅⁅⊤, ⊤⁆, ⁅⊤, ⊤⁆⁆⁆ :=
    Subgroup.commutator_mono
      (Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top))
      (Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top))
  rw [hQ3] at hmono
  exact hmono.trans h3

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem perfectInInn_primeFormP {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : ¬(3 = 3 ∧ p ^ f = 2)) :
    PerfectInInn (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC (le_refl 3) hq
  obtain ⟨-, hcyc, -⟩ := unitary_full_diagonal_outer_order h (le_refl 3) hq
  set T := primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT
  set D := primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
  have hring : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hRcomm : ∀ a b : K ≃+* K, Commute a b := fun a b => by
    have : IsMulCommutative (RingAut K) := hring.isMulCommutative
    exact this.is_comm.comm a b
  intro Q hQ
  have hQD : Q ≤ D := by
    intro x hx
    have hx' : x ∈ ⁅Q, Q⁆ := by rw [hQ]; exact hx
    have hle : ⁅Q, Q⁆ ≤ (primeFormFieldFactor h hC (le_refl 3) hq).ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hRcomm _ _
    rw [← hFker]
    exact hle hx'
  have hDD : ∀ a ∈ D, ∀ b ∈ D,
      ⁅a, b⁆ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
    intro a ha b hb
    have hcomm : IsMulCommutative (D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner T).subgroupOf D) :=
      hcyc.isMulCommutative
    have h1 : ((⁅(⟨a, ha⟩ : D), (⟨b, hb⟩ : D)⁆ : D) :
        D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner T).subgroupOf D) = 1 := by
      rw [commutatorElement_def]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_commute]
      exact hcomm.is_comm.comm _ _
    exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  intro x hx
  have hx' : x ∈ ⁅Q, Q⁆ := by rw [hQ]; exact hx
  have hle : ⁅Q, Q⁆ ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hDD a (hQD ha) b (hQD hb)
  exact hle hx'

end Unitary

section Models

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem perfectInInn_of_lieModel {S : Type} [Group S] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (h5 : 5 ≤ p ^ f) (hmod : LieModel S t 3 p f) : PerfectInInn S := by
  rcases ht with rfl | rfl
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hmod
    have e' : S ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 F)).symm)
    exact (perfectInInn_projectiveSL (K := F) (le_refl 3)).of_mulEquiv e'
  · obtain ⟨hp, hf, K, _, _, hK, ⟨e⟩⟩ := lieModel_psu_data hmod
    have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun h => by omega
    obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
      (isPrimeFormGram_one (n := 3)) (le_refl 3) hq
    have e' : S ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
    exact (perfectInInn_primeFormP hU hq).of_mulEquiv e'

end Models


section Action

open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem
  mem_centralizer_of_normalizerAct_eq_one)

theorem exists_mul_centralizer_of_perfect {G : Type*} [Group G] (N : Subgroup G) [Group.IsPerfect ↥N]
    (hPI : PerfectInInn (↥N ⧸ center ↥N)) {J : Subgroup G} (hJN : J ≤ normalizer (N : Set G))
    (hJ : Group.IsPerfect ↥J) : ∀ j ∈ J, ∃ m ∈ N, j * m⁻¹ ∈ centralizer (N : Set G) := by
  let ρ : ↥J →* MulAut (↥N ⧸ center ↥N) := (normalizerAct N).comp (Subgroup.inclusion hJN)
  have hJtop : ⁅(⊤ : Subgroup ↥J), ⊤⁆ = ⊤ := hJ.commutator_eq_top
  have hperf : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hJtop]
  have hinn := hPI ρ.range hperf
  intro j hj
  obtain ⟨y, hy⟩ := hinn ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  have hmN : ((m : ↥N) : G) ∈ N := m.2
  have h1 : normalizerAct N ⟨((m : ↥N) : G), Subgroup.le_normalizer hmN⟩ = ρ ⟨j, hj⟩ := by
    rw [normalizerAct_of_mem N hmN]
    exact hy
  refine ⟨((m : ↥N) : G), hmN, ?_⟩
  have h2 : normalizerAct N (⟨j, hJN hj⟩ * ⟨((m : ↥N) : G), Subgroup.le_normalizer hmN⟩⁻¹ :
      normalizer (N : Set G)) = 1 := by
    rw [map_mul, map_inv, h1]
    exact mul_inv_cancel (ρ ⟨j, hj⟩)
  exact mem_centralizer_of_normalizerAct_eq_one N h2

end Action

end CFSG.GH74.Generic.S3
