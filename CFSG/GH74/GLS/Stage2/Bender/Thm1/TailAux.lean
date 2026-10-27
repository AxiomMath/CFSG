module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Cyc

variable {G : Type} [Group G]

theorem commutator_mem_centralizer_of_cyclic {H : Subgroup G} (hH : IsCyclic ↥H) {m₁ m₂ : G}
    (h₁ : m₁ ∈ normalizer (H : Set G)) (h₂ : m₂ ∈ normalizer (H : Set G)) :
    ⁅m₁, m₂⁆ ∈ centralizer (H : Set G) := by
  let _ : CommGroup (MulAut ↥H) :=
    (IsCyclic.mulAutMulEquiv ↥H).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv ↥H).injective
  let a : ↥(normalizer (H : Set G)) := ⟨m₁, h₁⟩
  let b : ↥(normalizer (H : Set G)) := ⟨m₂, h₂⟩
  have h1 : ⁅a, b⁆ ∈ H.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem commutator_le_centralizer_of_cyclic {H K : Subgroup G} (hH : IsCyclic ↥H)
    (hK : K ≤ normalizer (H : Set G)) : ⁅K, K⁆ ≤ centralizer (H : Set G) := by
  rw [Subgroup.commutator_le]
  intro m₁ h₁ m₂ h₂
  exact commutator_mem_centralizer_of_cyclic hH (hK h₁) (hK h₂)

theorem zOf_le_zOf_of_eq_sup {P Q : Subgroup G} (hQP : Q ≤ P) (hPQ : P = Q ⊔ zOf P) :
    zOf Q ≤ zOf P := by
  intro c hc
  refine ⟨hQP hc.1, ?_⟩
  show c ∈ centralizer (P : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ Q ⊔ zOf P := hPQ ▸ hh
  have hle : Q ⊔ zOf P ≤ centralizer ({c} : Set G) := by
    refine sup_le (fun q hq => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc.2 q hq)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ha.2 c (hQP hc.1)).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh')

theorem eq_one_of_mul_self_eq_one_of_odd {F : Subgroup G} [Finite G] (hodd : Odd (Nat.card ↥F))
    {b : G} (hb : b ∈ F) (h : b * b = 1) : b = 1 := by
  have h1 : orderOf (⟨b, hb⟩ : ↥F) ∣ Nat.card ↥F := orderOf_dvd_natCard _
  have h2 : orderOf (⟨b, hb⟩ : ↥F) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h))
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
  · have := orderOf_eq_one_iff.mp h3
    exact congrArg Subtype.val this
  · rw [h3] at h1
    exact absurd (Nat.not_even_iff_odd.mpr hodd) (not_not.mpr (even_iff_two_dvd.mpr h1))

end Cyc

section FitPE

variable {G : Type} [Group G] [Finite G]

theorem mem_Fm_of_centralizes_Op_Ep {M : Subgroup G} (hFs : Fs M = Fm M) {p : ℕ} (hp : p.Prime) {c : G}
    (hcM : c ∈ M) (hP : ∀ u ∈ Op p M, c * u = u * c) (hE : ∀ e ∈ Ep p M, c * e = e * c) :
    c ∈ Fm M := by
  refine mem_Fm_of_centralizes_Fs hcM ?_
  rw [hFs]
  refine Fm_le_of_forall (N := centralizer ({c} : Set G)) fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp
    exact fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hP u hu).symm
  · exact fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hE e (Op_le_Ep hq hp hqp M he)).symm

end FitPE

end CFSG.GH74.GLS.Stage2.Bender.Thm1
