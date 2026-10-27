module

public import CFSG.HardMathSupport.Lang.AnisoF4.ElementE1
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Conj
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge TauCeti
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem closure_centralizers_eq_top_of_map_conj {G : Type*} [Group G] (g : G) (E : Subgroup G)
    (h : Subgroup.closure {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x} = ⊤) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have himg : {k | ∃ x ∈ E.map φ, x ≠ 1 ∧ Commute k x} =
      φ '' {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx⟩
      refine ⟨g⁻¹ * k * g, ⟨x, hx, fun h => hx1 (by rw [h, map_one]), ?_⟩, ?_⟩
      · have h := hkx.map (MulAut.conj g⁻¹).toMonoidHom
        simpa [hφ, MulAut.conj_apply, mul_assoc] using h
      · simp [hφ, MulAut.conj_apply, mul_assoc]
    · rintro ⟨k', ⟨x, hx, hx1, hkx⟩, rfl⟩
      refine ⟨φ x, ⟨x, hx, rfl⟩, fun h => hx1 ?_, hkx.map φ⟩
      exact (MulAut.conj g).injective (h.trans (map_one φ).symm)
  rw [himg, ← MonoidHom.map_closure] at h
  rw [eq_top_iff]
  intro k _
  have hk : φ k ∈ (Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x}).map φ := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨k', hk', hkk⟩ := hk
  rwa [(MulAut.conj g).injective hkk] at hk'


theorem closure_centralizers_eq_top_F4_four_odd {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {p : ℕ} [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1)
    (E₀ : Subgroup (adjointGroup .F4 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_F4_four (K := K) (p := p) (by omega) hpq
  have heX : e ∈ ⨆ k, b4Chain K k :=
    (sup_le (sup_le (le_iSup (b4Chain K) 0) (le_iSup (b4Chain K) 1)) (le_iSup (b4Chain K) 2)) heA
  obtain ⟨g, hgX, hge⟩ := exists_conj_plane_b4 h2 hp5 hpq heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    omega
  apply closure_centralizers_eq_top_of_map_conj g E₀
  apply eq_top_of_b4Chain_le_of_delta_le
  · exact iSup_b4Chain_le_closure_centralizers h2 hpF.out hp5 hpq _ hgX hE₁p hE₁c
  · intro y hy
    exact Subgroup.subset_closure ⟨e, hge, he1, (hec y hy).symm⟩


@[expose] def F4FourEvenClosure : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) = 0 → 4 ≤ Nat.card K →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → p ∣ Nat.card K ^ 2 + 1 →
      ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem seitzExcAnisotropicF4Class_four_of_even (heven : F4FourEvenClosure) :
    SeitzExcAnisotropicF4Class 4 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, hX, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K ^ 2 + 1 := by
    rw [hKq]
    exact dvd_sq_add_one_of_orderOf_eq_four hp hord
  refine CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.planeGen_of_native_closure e
    center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  by_cases h2 : (2 : K) = 0
  · have hq2 : q.p = 2 := by
      have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
      rw [CharP.cast_eq_zero_iff K q.p] at h2'
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2'
    have he1 : q.exponent ≠ 1 := fun h => hX ⟨hq2, h⟩
    have hK4 : 4 ≤ Nat.card K := by
      rw [hKq, PrimePower.card_def, hq2]
      have he2 : 2 ≤ q.exponent := by have := q.exponent_pos; omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he2
    exact heven K h2 hK4 p hp5 hpq E₀ hE₀p hE₀c
  · exact closure_centralizers_eq_top_F4_four_odd h2 hp5 hpq E₀ hE₀p hE₀c

end CFSG.HardMathSupport.Lang.AnisoF4
