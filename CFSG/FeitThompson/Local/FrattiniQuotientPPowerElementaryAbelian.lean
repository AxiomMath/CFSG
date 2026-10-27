module

public import Mathlib.GroupTheory.Frattini
import CFSG.FeitThompson.Local.MaximalSubgroupsPGroupPrimeIndex
import CFSG.FeitThompson.Local.AutomorphismsFixingPlaneQuotientAbelian

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p n : ℕ} {P : Type*} [Group P]

def commutatorSupPowClosure (p : ℕ) (P : Type*) [Group P] : Subgroup P :=
  commutator P ⊔ Subgroup.closure (Set.range (· ^ p : P → P))

theorem commutator_le_commutatorSupPowClosure : commutator P ≤ commutatorSupPowClosure p P :=
  le_sup_left

theorem pow_mem_commutatorSupPowClosure (x : P) : x ^ p ∈ commutatorSupPowClosure p P :=
  le_sup_right (a := commutator P) (Subgroup.subset_closure ⟨x, rfl⟩)

theorem commutatorSupPowClosure_le {H : Subgroup P} :
    commutatorSupPowClosure p P ≤ H ↔ commutator P ≤ H ∧ ∀ x : P, x ^ p ∈ H := by
  rw [commutatorSupPowClosure, sup_le_iff, Subgroup.closure_le]
  refine and_congr_right fun _ => ?_
  exact ⟨fun h x => h ⟨x, rfl⟩, fun h _ hy => by obtain ⟨x, rfl⟩ := hy; exact h x⟩

private theorem closure_range_pow_characteristic :
    (Subgroup.closure (Set.range (· ^ p : P → P))).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨-, ⟨x, rfl⟩, rfl⟩
  exact Subgroup.subset_closure ⟨φ x, by simp⟩

instance commutatorSupPowClosure_characteristic :
    (commutatorSupPowClosure p P).Characteristic :=
  have := closure_range_pow_characteristic (p := p) (P := P)
  inferInstanceAs (commutator P ⊔ _).Characteristic

instance instIsMulCommutativeQuotientCommutatorSupPowClosure :
    IsMulCommutative (P ⧸ commutatorSupPowClosure p P) :=
  (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 commutator_le_commutatorSupPowClosure

theorem pow_eq_one_quotient_commutatorSupPowClosure (x : P ⧸ commutatorSupPowClosure p P) :
    x ^ p = 1 := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_commutatorSupPowClosure y

theorem isCoatom_of_index_eq_prime {H : Subgroup P} (hp : p.Prime) (h : H.index = p) :
    IsCoatom H := by
  have hfi : H.FiniteIndex := ⟨by rw [h]; exact hp.pos.ne'⟩
  refine ⟨fun htop => ?_, fun K hK => ?_⟩
  · rw [htop, Subgroup.index_top] at h; exact hp.one_lt.ne' h.symm
  · have h1 := Subgroup.index_strictAnti hK
    have h2 := Subgroup.index_dvd_of_le hK.le
    rw [h] at h1 h2
    rcases hp.eq_one_or_self_of_dvd _ h2 with h3 | h3
    · exact Subgroup.index_eq_one.1 h3
    · omega

theorem exists_index_eq_prime_notMem {Q : Type*} [Group Q] [IsMulCommutative Q] [Finite Q]
    (hp : p.Prime) (hexp : ∀ y : Q, y ^ p = 1) {x : Q} (hx : x ≠ 1) :
    ∃ K : Subgroup Q, K.index = p ∧ x ∉ K := by
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, -, ⟨e⟩⟩ := exists_mulEquiv_pi_multiplicative_zmod hp Q hexp
  have hex : e x ≠ 1 := by simpa using hx
  obtain ⟨i, hi⟩ : ∃ i, e x i ≠ 1 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hex (funext hc)
  set ψ : Q →* Multiplicative (ZMod p) :=
    (Pi.evalMonoidHom (fun _ : Fin d => Multiplicative (ZMod p)) i).comp e.toMonoidHom with hψ
  have hψapp : ∀ y : Q, ψ y = e y i := fun _ => rfl
  have hsurj : Function.Surjective ψ := fun a =>
    ⟨e.symm (Function.update 1 i a), by rw [hψapp]; simp⟩
  refine ⟨ψ.ker, ?_, ?_⟩
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj]
    simp [Nat.card_eq_fintype_card]
  · rw [MonoidHom.mem_ker, hψapp]; exact hi

theorem frattini_eq_commutatorSupPowClosure (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    frattini P = commutatorSupPowClosure p P := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  apply le_antisymm
  ·
    by_contra hc
    rw [SetLike.not_le_iff_exists] at hc
    obtain ⟨x, hxΦ, hxD⟩ := hc
    have hne : (QuotientGroup.mk' (commutatorSupPowClosure p P) x) ≠ 1 := by
      rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hxD
    obtain ⟨K, hKidx, hKx⟩ := exists_index_eq_prime_notMem hp
      (pow_eq_one_quotient_commutatorSupPowClosure (P := P) (p := p)) hne
    have hcoatom : IsCoatom (K.comap (QuotientGroup.mk' (commutatorSupPowClosure p P))) :=
      isCoatom_of_index_eq_prime hp (by
        rw [Subgroup.index_comap_of_surjective _
          (QuotientGroup.mk'_surjective (commutatorSupPowClosure p P))]
        exact hKidx)
    exact hKx (frattini_le_coatom hcoatom hxΦ)
  ·
    refine le_iInf₂ fun K hK => ?_
    have hKn : K.Normal := normal_of_isCoatom_of_natCard_eq_prime_pow hp hP hK
    have hcard : Nat.card (P ⧸ K) = p :=
      natCard_quotient_of_isCoatom_of_natCard_eq_prime_pow hp hP hK
    have : Fact p.Prime := ⟨hp⟩
    have : IsCyclic (P ⧸ K) := isCyclic_of_prime_card hcard
    rw [commutatorSupPowClosure_le]
    refine ⟨(Subgroup.Normal.quotient_commutative_iff_commutator_le).1 inferInstance, fun x => ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'

theorem frattini_eq_commutatorSupPowClosure_of_isPGroup (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) : frattini P = commutatorSupPowClosure p P := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact frattini_eq_commutatorSupPowClosure (n := n) hp hn

theorem commutator_le_frattini (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    commutator P ≤ frattini P := by
  rw [frattini_eq_commutatorSupPowClosure (n := n) hp hP]
  exact commutator_le_commutatorSupPowClosure

theorem pow_mem_frattini (hp : p.Prime) (hP : Nat.card P = p ^ n) (x : P) :
    x ^ p ∈ frattini P := by
  rw [frattini_eq_commutatorSupPowClosure (n := n) hp hP]
  exact pow_mem_commutatorSupPowClosure x

theorem isMulCommutative_quotient_frattini (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    IsMulCommutative (P ⧸ frattini P) :=
  (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 (commutator_le_frattini hp hP)

theorem pow_eq_one_quotient_frattini (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (x : P ⧸ frattini P) : x ^ p = 1 := by
  induction x using QuotientGroup.induction_on with
  | H y => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact pow_mem_frattini hp hP y

theorem exists_mulEquiv_quotient_frattini (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    ∃ d : ℕ, Nat.card (P ⧸ frattini P) = p ^ d ∧
      Nonempty ((P ⧸ frattini P) ≃* (Fin d → Multiplicative (ZMod p))) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have hcomm := isMulCommutative_quotient_frattini (n := n) hp hP
  let _ : CommGroup (P ⧸ frattini P) := @IsMulCommutative.instCommGroup _ _ hcomm
  exact exists_mulEquiv_pi_multiplicative_zmod hp _ (pow_eq_one_quotient_frattini hp hP)

theorem exists_mulEquiv_quotient_frattini_of_isPGroup (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) : ∃ d : ℕ, Nat.card (P ⧸ frattini P) = p ^ d ∧
      Nonempty ((P ⧸ frattini P) ≃* (Fin d → Multiplicative (ZMod p))) := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact exists_mulEquiv_quotient_frattini (n := n) hp hn

end

end CFSG.FeitThompson
