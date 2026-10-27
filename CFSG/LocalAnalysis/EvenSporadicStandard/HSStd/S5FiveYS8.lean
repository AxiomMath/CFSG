module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveTriple
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv

@[expose] def sym8Y : Perm (Fin 8) := swap 0 1 * swap 1 2

theorem sym8Y_cube : sym8Y ^ 3 = 1 := by
  unfold sym8Y
  decide

theorem sym8Y_ne_one : sym8Y ≠ 1 := by
  unfold sym8Y
  decide

theorem orderOf_sym8Y : orderOf sym8Y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime sym8Y_cube sym8Y_ne_one

@[expose] def sub5 : Fin 5 ≃ {x : Fin 8 // 3 ≤ x.val} where
  toFun i := ⟨⟨i.val + 3, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 3, by omega⟩
  left_inv i := by
    ext
    simp
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have := x.2
    omega

@[expose] def iota5 : Perm (Fin 5) →* Perm (Fin 8) := Equiv.Perm.extendDomainHom sub5

theorem iota5_injective : Function.Injective iota5 := Equiv.Perm.extendDomainHom_injective sub5

theorem iota5_swap : iota5 (swap 2 3) = sym8U1 := by
  unfold sym8U1
  decide

theorem iota5_comm_Y (σ : Perm (Fin 5)) : iota5 σ * sym8Y = sym8Y * iota5 σ := by
  have hd : (iota5 σ).Disjoint sym8Y := fun x => by
    by_cases hx : 3 ≤ x.val
    · right
      have key : ∀ x : Fin 8, 3 ≤ x.val → sym8Y x = x := by
        unfold sym8Y
        decide
      exact key x hx
    · left
      exact Equiv.Perm.extendDomain_apply_not_subtype σ sub5 hx
  exact hd.commute

theorem sym8C_eq_formPerm : sym8C = List.formPerm [(0 : Fin 8), 1, 2, 3, 4] := by
  unfold sym8C
  decide

theorem cycleType_sym8C : sym8C.cycleType = {5} := by
  have hl : ([(0 : Fin 8), 1, 2, 3, 4]).Nodup := by decide
  rw [sym8C_eq_formPerm, (List.isCycle_formPerm hl (by decide)).cycleType,
    List.support_formPerm_of_nodup _ hl (by decide)]
  simp

theorem exists_conj_sym8C {ρ : Perm (Fin 8)} (hρ : orderOf ρ = 5) :
    ∃ σ : Perm (Fin 8), σ * ρ * σ⁻¹ = sym8C := by
  have hl := Equiv.Perm.lcm_cycleType ρ
  rw [hρ] at hl
  have hall : ∀ m ∈ ρ.cycleType, m = 5 := by
    intro m hm
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hm
    have hdvd : m ∣ 5 := hl ▸ Multiset.dvd_lcm hm
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · omega
    · exact h
  have hrep : ρ.cycleType = Multiset.replicate (Multiset.card ρ.cycleType) 5 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hsum : ρ.cycleType.sum ≤ 8 := by
    rw [Equiv.Perm.sum_cycleType]
    have := Finset.card_le_univ ρ.support
    simpa using this
  have hne : ρ.cycleType ≠ 0 := by
    intro h0
    have := Equiv.Perm.cycleType_eq_zero.1 h0
    rw [this, orderOf_one] at hρ
    omega
  have hpos : 0 < Multiset.card ρ.cycleType := Multiset.card_pos.2 hne
  have hcard : Multiset.card ρ.cycleType = 1 := by
    rw [hrep, Multiset.sum_replicate] at hsum
    simp only [smul_eq_mul] at hsum
    omega
  have hct : ρ.cycleType = {5} := by
    rw [hrep, hcard]
    rfl
  exact isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (hct.trans cycleType_sym8C.symm))

variable {G : Type*} [Group G]

theorem fiveTriple_of_equiv {L : Subgroup G} {v : G}
    (e : ↥(centralizer ({v} : Set G) ⊓ L) ≃* Perm (Fin 8)) :
    FiveTriple L v (e.symm sym8C : G) (e.symm sym8U1 : G) (e.symm sym8U2 : G) := by
  have hmemv : ∀ a : Perm (Fin 8), ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) * v =
      v * ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) :=
    fun a => mem_centralizer_singleton_iff.1 (e.symm a).2.1
  have hmemL : ∀ a : Perm (Fin 8),
      ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) ∈ L := fun a => (e.symm a).2.2
  have hmulv : ∀ a b : Perm (Fin 8),
      ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) *
        ((e.symm b : ↥(centralizer ({v} : Set G) ⊓ L)) : G) =
      ((e.symm (a * b) : ↥(centralizer ({v} : Set G) ⊓ L)) : G) := fun a b => by
    rw [map_mul]
    rfl
  have hpow : ∀ (a : Perm (Fin 8)) (k : ℕ),
      ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) ^ k =
      ((e.symm (a ^ k) : ↥(centralizer ({v} : Set G) ⊓ L)) : G) := fun a k => by
    rw [map_pow]
    rfl
  have hone : ∀ a : Perm (Fin 8),
      ((e.symm a : ↥(centralizer ({v} : Set G) ⊓ L)) : G) = 1 → a = 1 := by
    intro a ha
    have : e.symm a = 1 := Subtype.ext ha
    exact e.symm.injective (by rw [this, map_one])
  have hone' : ((e.symm (1 : Perm (Fin 8)) : ↥(centralizer ({v} : Set G) ⊓ L)) : G) = 1 := by
    rw [map_one]
    rfl
  refine ⟨hmemL _, hmemL _, hmemL _, hmemv _, hmemv _, hmemv _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_sym8C
  · rw [hmulv, sym8U1_mul_self, hone']
  · rw [hmulv, sym8U2_mul_self, hone']
  · rw [hmulv, hpow, sym8_cube, hone']
  · intro h
    rw [hmulv] at h
    exact sym8_U1U2_ne_one (hone _ h)
  · rw [hmulv, hmulv, sym8U1_comm_C]
  · rw [hmulv, hmulv, sym8U2_comm_C]

structure S8Data (L : Subgroup G) (v r : G) where
  u₁ : G
  u₂ : G
  y : G
  J : Subgroup G
  ψ : Perm (Fin 5) ≃* ↥J
  tr : FiveTriple L v r u₁ u₂
  y_mem : y ∈ L
  y_comm_v : y * v = v * y
  y_ord : orderOf y = 3
  J_le : J ≤ L
  J_comm_v : ∀ j ∈ J, j * v = v * j
  J_comm_y : ∀ j ∈ J, j * y = y * j
  u₁_eq : u₁ = ((ψ (swap 2 3) : ↥J) : G)

theorem exists_s8Data {L : Subgroup G} {v r : G}
    (e : ↥(centralizer ({v} : Set G) ⊓ L) ≃* Perm (Fin 8))
    (hrT : r ∈ centralizer ({v} : Set G) ⊓ L) (hr5 : orderOf r = 5) : Nonempty (S8Data L v r) := by
  set T : Subgroup G := centralizer ({v} : Set G) ⊓ L with hT
  obtain ⟨σ, hσ⟩ := exists_conj_sym8C (ρ := e ⟨r, hrT⟩)
    (by rw [MulEquiv.orderOf_eq]; exact (Subgroup.orderOf_mk r hrT).trans hr5)
  let e' : ↥T ≃* Perm (Fin 8) := e.trans (MulAut.conj σ)
  have he'r : e' ⟨r, hrT⟩ = sym8C := by
    simp only [e', MulEquiv.trans_apply, MulAut.conj_apply]
    exact hσ
  have hr : ((e'.symm sym8C : ↥T) : G) = r := by
    rw [← he'r, MulEquiv.symm_apply_apply]
  have tr := fiveTriple_of_equiv e'
  rw [hr] at tr
  let φ : Perm (Fin 5) →* G := T.subtype.comp (e'.symm.toMonoidHom.comp iota5)
  have hφ : Function.Injective φ := fun a b hab =>
    iota5_injective (e'.symm.injective (Subtype.ext hab))
  have hφmem : ∀ a : Perm (Fin 5), φ a = ((e'.symm (iota5 a) : ↥T) : G) := fun a => rfl
  refine ⟨⟨((e'.symm sym8U1 : ↥T) : G), ((e'.symm sym8U2 : ↥T) : G),
    ((e'.symm sym8Y : ↥T) : G), φ.range, MonoidHom.ofInjective hφ, tr,
    (e'.symm sym8Y).2.2, mem_centralizer_singleton_iff.1 (e'.symm sym8Y).2.1, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_sym8Y
  · rintro _ ⟨a, rfl⟩
    rw [hφmem]
    exact (e'.symm (iota5 a)).2.2
  · rintro _ ⟨a, rfl⟩
    rw [hφmem]
    exact mem_centralizer_singleton_iff.1 (e'.symm (iota5 a)).2.1
  · rintro _ ⟨a, rfl⟩
    rw [hφmem]
    have h := iota5_comm_Y a
    have h2 : e'.symm (iota5 a) * e'.symm sym8Y = e'.symm sym8Y * e'.symm (iota5 a) := by
      rw [← map_mul, ← map_mul, h]
    exact congrArg Subtype.val h2
  · show ((e'.symm sym8U1 : ↥T) : G) = φ (swap 2 3)
    rw [hφmem, iota5_swap]

end CFSG.EvenSporadicStandard.HSStd.FiveY
