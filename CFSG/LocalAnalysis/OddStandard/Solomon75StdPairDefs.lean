module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermSign
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.GH74.GLS

structure StdPair (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L L' : Subgroup G) (n : ℕ)
    (z a : G) : Prop where
  setup : StdSetup G L n z
  setup' : StdSetup G L' n a
  ne : a ≠ z
  comm : a * z = z * a

namespace StdPair

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}

theorem of_setup (h : StdSetup G L n z) (g : G) (hne : g⁻¹ * z * g ≠ z)
    (hc : (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g)) :
    StdPair G L (CFSG.conjugate L g) n z (g⁻¹ * z * g) :=
  ⟨h, h.conj g, hne, hc⟩

variable (P : StdPair G L L' n z a)
include P

theorem symm : StdPair G L' L n a z :=
  ⟨P.setup', P.setup, P.ne.symm, P.comm.symm⟩

theorem a_mem_centralizer : a ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 P.comm

theorem z_mem_centralizer : z ∈ centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 P.comm.symm

theorem a_mem_norm : a ∈ normalizer (L : Set G) :=
  P.setup.mem_normalizer_of_mem_centralizer P.a_mem_centralizer

theorem z_mem_norm' : z ∈ normalizer (L' : Set G) :=
  P.setup'.mem_normalizer_of_mem_centralizer P.z_mem_centralizer

theorem a_not_cent : a ∉ centralizer (L : Set G) := fun h =>
  P.ne (P.setup.inv_unique a h P.setup'.hz)

theorem z_not_cent' : z ∉ centralizer (L' : Set G) := fun h =>
  P.ne (P.setup'.inv_unique z h P.setup.hz).symm

theorem a_mul_self : a * a = 1 := by
  have h := pow_orderOf_eq_one a
  rwa [P.setup'.hz, sq] at h

theorem z_mul_self : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [P.setup.hz, sq] at h

theorem centralizer'_le : centralizer (L' : Set G) ≤ centralizer ({a} : Set G) :=
  P.setup'.centralizer_le_centralizer_singleton

theorem le_centralizer : L ≤ centralizer ({z} : Set G) := P.setup.le_centralizer_singleton

end StdPair

section Involution

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_card_support_eq_of_involution {σ : Perm α} (h2 : σ * σ = 1) :
    ∃ k, σ.support.card = 2 * k := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, h2]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  exact ⟨_, by rw [← hsum, mul_comm]⟩

theorem card_support_eq_two_mul_transCount {n : ℕ} {σ : Perm (Fin n)} (h2 : σ * σ = 1) :
    σ.support.card = 2 * transCount σ := by
  obtain ⟨k, hk⟩ := exists_card_support_eq_of_involution h2
  unfold transCount
  omega

theorem card_eq_of_involution {n : ℕ} {σ : Perm (Fin n)} (h2 : σ * σ = 1) :
    n = 2 * transCount σ + fixCount σ := by
  have h1 := fixCount_add_support σ
  have h3 := card_support_eq_two_mul_transCount h2
  omega

theorem sign_eq_one_of_even_transCount {n : ℕ} {σ : Perm (Fin n)} (h2 : σ * σ = 1)
    (he : Even (transCount σ)) : sign σ = 1 := by
  rw [sign_involution h2 (card_support_eq_two_mul_transCount h2)]
  exact he.neg_one_pow

end Involution

section ModelInvolution

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

theorem AhatModel.perm_mul_self_eq_one (hn : 8 ≤ n) (M : AhatModel X n A) {c : X}
    (hc : c ∈ normalizer (A : Set X)) (h : c * c = 1) : M.perm c hc * M.perm c hc = 1 := by
  have h1 : (⟨c, hc⟩ : ↥(normalizer (A : Set X))) * ⟨c, hc⟩ = 1 := Subtype.ext h
  have h2 := congrArg (M.permHom hn) h1
  rw [map_mul, map_one] at h2
  exact h2

end ModelInvolution

end CFSG.OddStandard.Solomon75
