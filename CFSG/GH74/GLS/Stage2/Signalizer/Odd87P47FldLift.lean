module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld

open Subgroup

section Fixed

theorem exists_fixed_of_involutive {S : Type} [Finite S] (T : S → S) (hT : Function.Involutive T)
    (hodd : Odd (Nat.card S)) : ∃ s, T s = s := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.not_even_iff_odd.mpr hodd) ∘ even_iff_two_dvd.mpr
  have hσ : (hT.toPerm T) ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, hT x]
  exact Equiv.Perm.exists_fixed_point_of_prime hnd hσ

theorem exists_lift_fixed {K P : Type} [Group K] [Finite K] [Group P] (φ : K →* P)
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) (T : K → K)
    (hT : Function.Involutive T) (α : P → P) (hαT : ∀ k, φ (T k) = α (φ k)) {x : P}
    (hx : α x = x) : ∃ k, T k = k ∧ φ k = x := by
  let f : ↥(φ ⁻¹' {x}) → ↥(φ ⁻¹' {x}) := fun k => ⟨T k.1, by
    show φ (T k.1) = x
    rw [hαT]
    have hk : φ k.1 = x := k.2
    rw [hk, hx]⟩
  have hf : Function.Involutive f := fun k => Subtype.ext (hT k.1)
  have hcard : Nat.card ↥(φ ⁻¹' {x}) = Nat.card φ.ker :=
    Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hφ x)
  obtain ⟨k, hk⟩ := exists_fixed_of_involutive f hf (by rw [hcard]; exact hodd)
  exact ⟨k.1, congrArg Subtype.val hk, k.2⟩

end Fixed

section PerfCore

variable {K : Type} [Group K]

theorem commutator_self_le (J : Subgroup K) : ⁅J, J⁆ ≤ J := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

@[expose] def perfCore (M : Subgroup K) : Subgroup K :=
  sSup {H : Subgroup K | H ≤ M ∧ ⁅H, H⁆ = H}

theorem le_perfCore {M H : Subgroup K} (hH : H ≤ M) (hp : ⁅H, H⁆ = H) : H ≤ perfCore M :=
  le_sSup ⟨hH, hp⟩

theorem perfCore_le (M : Subgroup K) : perfCore M ≤ M :=
  sSup_le fun _ hH => hH.1

theorem perfCore_perfect (M : Subgroup K) : ⁅perfCore M, perfCore M⁆ = perfCore M := by
  refine le_antisymm (commutator_self_le _) (sSup_le fun H hH => ?_)
  calc H = ⁅H, H⁆ := hH.2.symm
    _ ≤ ⁅perfCore M, perfCore M⁆ :=
        Subgroup.commutator_mono (le_perfCore hH.1 hH.2) (le_perfCore hH.1 hH.2)

theorem map_perfCore_le {K' : Type} [Group K'] (f : K →* K') {M : Subgroup K} {M' : Subgroup K'}
    (h : M.map f ≤ M') : (perfCore M).map f ≤ perfCore M' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun H hH => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_perfCore ((Subgroup.map_mono hH.1).trans h) ?_
  rw [← Subgroup.map_commutator, hH.2]

theorem mem_normalizer_perfCore {M : Subgroup K} {g : K} (hg : ∀ x ∈ M, g * x * g⁻¹ ∈ M)
    (hg' : ∀ x ∈ M, g⁻¹ * x * g ∈ M) : g ∈ normalizer (perfCore M : Set K) := by
  have key : ∀ c : K, (∀ x ∈ M, c * x * c⁻¹ ∈ M) → ∀ y ∈ perfCore M, c * y * c⁻¹ ∈ perfCore M := by
    intro c hc y hy
    have h := map_perfCore_le (MulAut.conj c).toMonoidHom (M := M) (M' := M) (by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hc x hx)
    exact h ⟨y, hy, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (fun x hx => by simpa using hg' x hx) _ hy
  simpa [mul_assoc] using this

theorem exists_perfect_cover {K P : Type} [Group K] [Finite K] [Group P] (φ : K →* P)
    {M : Subgroup K} {Q : Subgroup P} (hQ : ⁅Q, Q⁆ = Q) (hM : M.map φ = Q) :
    ∃ H : Subgroup K, H ≤ M ∧ ⁅H, H⁆ = H ∧ H.map φ = Q := by
  obtain ⟨H, ⟨hHM, hHQ⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup K))
    {H : Subgroup K | H ≤ M ∧ H.map φ = Q} ⟨M, le_rfl, hM⟩
  refine ⟨H, hHM, ?_, hHQ⟩
  have hle : ⁅H, H⁆ ≤ H := commutator_self_le H
  by_contra hne
  refine hmin ⁅H, H⁆ ⟨hle.trans hHM, ?_⟩ (lt_of_le_of_ne hle hne)
  rw [Subgroup.map_commutator, hHQ, hQ]

end PerfCore

section Core

theorem exists_perfect_fixed_lift {K P : Type} [Group K] [Finite K] [Group P] (φ : K →* P)
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) (E : MulAut K)
    (hE : ∀ k, E (E k) = k) (α : MulAut P) (hα : ∀ k, α (φ k) = φ (E k)) (Q : Subgroup P)
    (hQp : ⁅Q, Q⁆ = Q) (hQα : ∀ s ∈ Q, α s = s)
    (hQn : ∀ x, α x = x → x ∈ normalizer (Q : Set P)) {b : K} (hb : E b = b) :
    ∃ J : Subgroup K, ⁅J, J⁆ = J ∧ (∀ j ∈ J, E j = j) ∧ J.map φ = Q ∧
      b ∈ normalizer (J : Set K) := by
  let M : Subgroup K :=
    { carrier := {k | E k = k ∧ φ k ∈ Q}
      mul_mem' := fun {a c} ha hc =>
        ⟨by rw [map_mul, ha.1, hc.1], by rw [map_mul]; exact Q.mul_mem ha.2 hc.2⟩
      one_mem' := ⟨map_one E, by rw [map_one]; exact Q.one_mem⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1], by rw [map_inv]; exact Q.inv_mem ha.2⟩ }
  have hMQ : M.map φ = Q := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro q hq
      obtain ⟨k, hk, hkq⟩ := exists_lift_fixed φ hφ hodd (⇑E) hE (⇑α) (fun k => (hα k).symm) (hQα q hq)
      exact ⟨k, ⟨hk, hkq ▸ hq⟩, hkq⟩
  obtain ⟨H, hHM, hHp, hHQ⟩ := exists_perfect_cover φ hQp hMQ
  have hnorm : ∀ c : K, E c = c → ∀ x ∈ M, c * x * c⁻¹ ∈ M := by
    intro c hc x hx
    refine ⟨by rw [map_mul, map_mul, map_inv, hc, hx.1], ?_⟩
    have hαc : α (φ c) = φ c := by rw [hα, hc]
    have hn := (Subgroup.mem_normalizer_iff.1 (hQn _ hαc)) (φ x)
    rw [map_mul, map_mul, map_inv]
    exact hn.1 hx.2
  refine ⟨perfCore M, perfCore_perfect M, fun j hj => (perfCore_le M hj).1, ?_, ?_⟩
  · refine le_antisymm ((Subgroup.map_mono (perfCore_le M)).trans hMQ.le) ?_
    rw [← hHQ]
    exact Subgroup.map_mono (le_perfCore hHM hHp)
  · refine mem_normalizer_perfCore (hnorm b hb) (fun x hx => ?_)
    have := hnorm b⁻¹ (by rw [map_inv, hb]) x hx
    simpa using this

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld
