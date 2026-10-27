module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Lemmas

variable {G : Type} [Group G]

theorem ka6enl_omega1Z_le (p : ℕ) (P : Subgroup G) : omega1Z p P ≤ P := fun _ hx => hx.1

theorem ka6enl_op_commute_of_ne {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p)
    (M : Subgroup G) {y e : G} (hy : y ∈ Op q M) (he : e ∈ Op p M) : y * e = e * y := by
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨e', he', rfl⟩ := he
  have hcomm := (CFSG.LocalCores.distinct_prime_cores_commute (G := ↥M) hq hp hqp).2
  have hmem : ⁅y', e'⁆ ∈ ⁅pCore q ↥M, pCore p ↥M⁆ := Subgroup.commutator_mem_commutator hy' he'
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem ka6enl_Op_le_centralizer {M : Subgroup G} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Op q M ≤ centralizer ((omega1Z p (Op p M) : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases hqp : q = p
  · subst hqp
    exact hw.2.1 y hy
  · exact (ka6enl_op_commute_of_ne hq hp hqp M hy hw.1).symm

theorem ka6enl_isElementaryAbelian_omega1Z (p : ℕ) (P : Subgroup G) :
    IsElementaryAbelian p ↥(omega1Z p P) := by
  refine
    { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
      exponent_dvd_p := ?_ }
  · exact Subtype.ext (a.2.2.1 b b.2.1)
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext x.2.2.2

theorem ka6enl_pRank_mono [Finite G] {p : ℕ} (hp : p.Prime) {H K : Subgroup G} (hHK : H ≤ K) :
    pRank p ↥H ≤ pRank p ↥K := by
  have : Fact p.Prime := ⟨hp⟩
  refine csSup_le' fun r hr => ?_
  obtain ⟨A, hA, hAr⟩ := hr
  have := hA
  refine le_csSup ⟨Nat.card ↥K, ?_⟩
    ⟨A.map (Subgroup.inclusion hHK), IsElementaryAbelian.map _, ?_⟩
  · rintro s ⟨B, -, hB⟩
    calc s ≤ p ^ s := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card ↥B := hB.symm
      _ ≤ Nat.card ↥K := Subgroup.card_le_card_group B
  · rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK), hAr]

end Lemmas

section Main

variable {G : Type} [Group G] [Finite G]

theorem Fm_le_centralizer_omega1Z (M : Subgroup G) {p : ℕ} (hp : p.Prime) :
    Fm M ≤ centralizer ((omega1Z p (Op p M) : Subgroup G) : Set G) := by
  change (fittingSubgroup ↥M).map M.subtype ≤ _
  rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
  exact iSup_le fun r => ka6enl_Op_le_centralizer hp (Nat.prime_of_mem_primeFactors r.1.2)

theorem Vof_sup_omega1Z (M E : Subgroup G) {p : ℕ} (hp : p.Prime) :
    Vof M (E ⊔ omega1Z p (Op p M)) = Vof M E := by
  ext x
  constructor
  · rintro ⟨hxF, hxC⟩
    exact ⟨hxF, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hxC⟩
  · rintro ⟨hxF, hxC⟩
    refine ⟨hxF, ?_⟩
    have hxZ := Fm_le_centralizer_omega1Z M hp hxF
    have hle : E ⊔ omega1Z p (Op p M) ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun e he => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxC e he)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxZ w hw)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hw)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem Ctx18.sup_omega1Z {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}
    {p : ℕ} {E : Subgroup G} {t : G} (h : Ctx18 G z k S M p E t) :
    Ctx18 G z k S M p (E ⊔ omega1Z p (Op p M)) t where
  base := h.base
  prime := h.prime
  odd := h.odd
  rank := h.rank
  t_mem := h.t_mem
  t_ord := h.t_ord
  t_rank := h.t_rank
  t_fail := h.t_fail
  E_le := sup_le h.E_le (ka6enl_omega1Z_le p _)
  E_elem := by
    have := h.E_elem
    have := ka6enl_isElementaryAbelian_omega1Z p (Op p M)
    refine IsElementaryAbelian.sup_of_le_centralizer fun w hw => ?_
    exact Subgroup.mem_centralizer_iff.2 fun e he => (hw.2.1 e (h.E_le he)).symm
  t_E := Subgroup.mem_sup_left h.t_E
  E_rank := h.E_rank.trans (ka6enl_pRank_mono h.prime le_sup_left)

end CFSG.GH74.GLS.Stage2.Final.Thm4
