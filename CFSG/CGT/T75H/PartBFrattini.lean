module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.T75H

open scoped commutatorElement

variable {M : Type*} [Group M]

theorem mem_of_sq_mem {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hM : IsPGroup p M)
    {K : Subgroup M} {c : M} (hc : c ^ 2 ∈ K) : c ∈ K := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hM) c
  have hodd : Odd (orderOf c) := by
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := hodd
  have hc1 : c ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one c
  have : c = (c ^ 2) ^ (r + 1) := by
    rw [← pow_mul, show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, hc1, one_mul]
  rw [this]
  exact K.pow_mem hc _

theorem commutator_mem_of_index_prime {K : Subgroup M} [K.Normal] [Finite M]
    (hK : K.index.Prime) (a b : M) : ⁅a, b⁆ ∈ K := by
  have hcard : (Nat.card (M ⧸ K)).Prime := by rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.card (M ⧸ K)).Prime := ⟨hcard⟩
  have hcyc : IsCyclic (M ⧸ K) := isCyclic_of_prime_card rfl
  have hcomm : Commute (QuotientGroup.mk a : M ⧸ K) (QuotientGroup.mk b) := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk a))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk b))
    rw [← hi, ← hj]
    exact (Commute.refl g).zpow_zpow i j
  have h1 : (QuotientGroup.mk' K) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem eq_top_of_closure_fixed {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite M]
    (hM : IsPGroup p M) (φ : M ≃* M)
    (hgen : Subgroup.closure {m : M | φ m = m⁻¹} = ⊤) (X : Subgroup M)
    (hX : ∀ x ∈ X, φ x ∈ X)
    (hsup : Subgroup.closure ((X : Set M) ∪ {m : M | φ m = m}) = ⊤) : X = ⊤ := by
  classical
  by_contra hXtop
  have hnil : Group.IsNilpotent M := hM.isNilpotent
  obtain ⟨K, hK, hXK⟩ := (eq_top_or_exists_le_coatom X).resolve_left hXtop
  have hnc : NormalizerCondition M := Group.normalizerCondition_of_isNilpotent
  have hKn : K.Normal := Subgroup.NormalizerCondition.normal_of_coatom K hnc hK
  have hKp : K.index.Prime := (Subgroup.isCoatom_iff_index_prime K).1 hK
  set K' : Subgroup M := K ⊓ K.comap φ.toMonoidHom with hK'
  have hK'n : K'.Normal := by
    have : (K.comap φ.toMonoidHom).Normal := hKn.comap _
    infer_instance
  have hXK' : X ≤ K' := fun x hx => ⟨hXK hx, hXK (hX x hx)⟩
  have hK'top : K' ≠ ⊤ := by
    intro h
    apply hK.1
    rw [eq_top_iff, ← h]
    exact inf_le_left
  have hcomm : ∀ a b : M, ⁅a, b⁆ ∈ K' := by
    intro a b
    refine ⟨commutator_mem_of_index_prime hKp a b, ?_⟩
    show φ ⁅a, b⁆ ∈ K
    rw [map_commutatorElement]
    exact commutator_mem_of_index_prime hKp _ _
  have hqc : ∀ x y : M ⧸ K', x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | _ a =>
    induction y using QuotientGroup.induction_on with | _ b =>
    have h1 : (QuotientGroup.mk' K') ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm a b)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.1 h1
  let _ : CommGroup (M ⧸ K') := { (inferInstance : Group (M ⧸ K')) with mul_comm := hqc }
  let π : M →* M ⧸ K' := QuotientGroup.mk' K'
  let ψ : M →* M ⧸ K' := (π.comp φ.toMonoidHom) * π
  have hψgen : ∀ j ∈ {m : M | φ m = m⁻¹}, ψ j = 1 := by
    intro j hj
    simp only [Set.mem_ofPred_eq] at hj
    show π (φ j) * π j = 1
    rw [hj, map_inv, inv_mul_cancel]
  have hψtop : ∀ m : M, ψ m = 1 := by
    intro m
    have : m ∈ ψ.ker := by
      have hle : Subgroup.closure {m : M | φ m = m⁻¹} ≤ ψ.ker :=
        (Subgroup.closure_le _).2 fun j hj => hψgen j hj
      exact hle (hgen ▸ Subgroup.mem_top m)
    exact this
  have hfix : ∀ c : M, φ c = c → c ∈ K' := by
    intro c hc
    have h1 : ψ c = 1 := hψtop c
    have h2 : π c * π c = 1 := by
      have : π (φ c) * π c = 1 := h1
      rwa [hc] at this
    have h3 : c ^ 2 ∈ K' := by
      rw [sq]
      exact (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_mul]; exact h2)
    exact mem_of_sq_mem hp2 hM h3
  have hle : Subgroup.closure ((X : Set M) ∪ {m : M | φ m = m}) ≤ K' := by
    rw [Subgroup.closure_le]
    rintro m (hm | hm)
    · exact hXK' hm
    · exact hfix m hm
  rw [hsup] at hle
  exact hK'top (top_le_iff.1 hle)

theorem odd_orderOf_of_pGroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {A : Type*} [Group A]
    {N : Subgroup A} (hN : IsPGroup p N) {c : A} (hc : c ∈ N) : Odd (orderOf c) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN) ⟨c, hc⟩
  rw [(Subgroup.orderOf_coe ⟨c, hc⟩).trans hk]
  exact (hp.out.odd_of_ne_two hp2).pow

theorem eq_one_of_mul_self_of_odd_card {A : Type*} [Group A] {K : Subgroup A}
    (hK : Odd (Nat.card K)) {r : A} (hr : r ∈ K) (hrr : r * r = 1) : r = 1 := by
  have h2 : orderOf (⟨r, hr⟩ : K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hrr))
  have hodd' : Odd (orderOf (⟨r, hr⟩ : K)) := Odd.of_dvd_nat hK (orderOf_dvd_natCard _)
  have h1 : orderOf (⟨r, hr⟩ : K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

end CFSG.CGT.T75H
