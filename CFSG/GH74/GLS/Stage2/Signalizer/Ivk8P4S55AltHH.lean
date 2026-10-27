module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltY

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Equiv Equiv.Perm Subgroup

theorem autTransport_apply {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) (φ : MulAut Y) (y : Y) :
    ((e (φ y) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      autTransport hn5 hn6 e φ * ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) *
        (autTransport hn5 hn6 e φ)⁻¹ := by
  have h : autEquivPerm n hn5 hn6 (autTransport hn5 hn6 e φ) = MulAut.congr e φ := by
    show autEquivPerm n hn5 hn6 ((autEquivPerm n hn5 hn6).symm (MulAut.congr e φ)) = _
    exact MulEquiv.apply_symm_apply _ _
  have h2 := congrArg
    (fun m : MulAut (alternatingGroup (Fin n)) => ((m (e y) : alternatingGroup (Fin n)) :
      Perm (Fin n))) h
  simp [autEquivPerm, MulAut.congr_apply] at h2
  exact h2.symm

namespace AltHH

theorem klein_abstract {G : Type*} [Group G] {u₁ u₂ c : G} (A : Subgroup G) (hu₁ : u₁ ∈ A)
    (hu₂ : u₂ ∈ A) (h11 : u₁ * u₁ = 1)
    (h22 : u₂ * u₂ = 1) (hc : u₁ * u₂ = u₂ * u₁) (hcu1 : c * u₁ * c⁻¹ = u₂)
    (hcu2 : c * u₂ * c⁻¹ = u₁ * u₂) (hne : u₂ ≠ u₁) :
    ∃ Q : Subgroup G, Q ≤ A ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
      (∀ x ∈ Q, c * x * c⁻¹ ∈ Q) ∧ ∃ x ∈ Q, c * x * c⁻¹ ≠ x := by
  let k : Set G := {u₁, u₂}
  have hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hc
    · exact hc.symm
    · rfl
  have hall : ∀ x ∈ closure k, ∀ y ∈ closure k, x * y = y * x := by
    intro x hx y hy
    have hpair : k.Pairwise Commute := fun a ha b hb _ => hcomm a ha b hb
    have := (Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hkA : closure k ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu₁
    · exact hu₂
  refine ⟨closure k, hkA, hall, ?_, ?_, ⟨u₁, subset_closure (Or.inl rfl), ?_⟩⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact h11
      · exact h22
    | one => simp
    | mul x y hx hy hxx hyy =>
      have := hall x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← this]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hxx, hyy]; simp
    | inv x hx hxx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hxx]; simp
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [hcu1]
        exact subset_closure (Or.inr rfl)
      · rw [hcu2]
        exact Subgroup.mul_mem _ (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl))
    | one => simp
    | mul x y hx hy hxx hyy =>
      have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hxx hyy
    | inv x hx hxx =>
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hxx
  · rw [hcu1]
    exact hne

theorem klein_exists {n : ℕ} (hn : n = 7 ∨ n = 11) {σ : Perm (Fin n)} (hσ : σ.IsThreeCycle) :
    ∃ Q : Subgroup (Perm (Fin n)), Q ≤ alternatingGroup (Fin n) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
      (∀ x ∈ Q, σ * x * σ⁻¹ ∈ Q) ∧ ∃ x ∈ Q, σ * x * σ⁻¹ ≠ x := by
  have hstd : ∃ c₀ u₁ u₂ : Perm (Fin n), c₀.IsThreeCycle ∧ u₁ ∈ alternatingGroup (Fin n) ∧
      u₂ ∈ alternatingGroup (Fin n) ∧ u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧
      c₀ * u₁ * c₀⁻¹ = u₂ ∧ c₀ * u₂ * c₀⁻¹ = u₁ * u₂ ∧ u₂ ≠ u₁ := by
    rcases hn with rfl | rfl
    · refine ⟨swap (0 : Fin 7) 1 * swap 0 2, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
        isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
          Perm.sign_swap (by decide)]
        rfl
      · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
          Perm.sign_swap (by decide)]
        rfl
      all_goals decide
    · refine ⟨swap (0 : Fin 11) 1 * swap 0 2, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
        isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
          Perm.sign_swap (by decide)]
        rfl
      · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
          Perm.sign_swap (by decide)]
        rfl
      all_goals decide
  obtain ⟨c₀, u₁, u₂, hc₀, hu₁A, hu₂A, h11, h22, hcomm, hcu1, hcu2, hne⟩ := hstd
  have hconj : IsConj c₀ σ := isConj_iff_cycleType_eq.2 (by rw [hc₀.cycleType, hσ.cycleType])
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  obtain ⟨v₁, hv₁⟩ : ∃ v : Perm (Fin n), v = g * u₁ * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Perm (Fin n), v = g * u₂ * g⁻¹ := ⟨_, rfl⟩
  have hv₁A : v₁ ∈ alternatingGroup (Fin n) := by
    rw [hv₁]
    exact Subgroup.Normal.conj_mem inferInstance _ hu₁A g
  have hv₂A : v₂ ∈ alternatingGroup (Fin n) := by
    rw [hv₂]
    exact Subgroup.Normal.conj_mem inferInstance _ hu₂A g
  have e1 : v₁ * v₁ = 1 := by
    have : v₁ * v₁ = g * (u₁ * u₁) * g⁻¹ := by rw [hv₁]; group
    rw [this, h11]
    group
  have e2 : v₂ * v₂ = 1 := by
    have : v₂ * v₂ = g * (u₂ * u₂) * g⁻¹ := by rw [hv₂]; group
    rw [this, h22]
    group
  have e3 : v₁ * v₂ = v₂ * v₁ := by
    have a1 : v₁ * v₂ = g * (u₁ * u₂) * g⁻¹ := by rw [hv₁, hv₂]; group
    have a2 : v₂ * v₁ = g * (u₂ * u₁) * g⁻¹ := by rw [hv₁, hv₂]; group
    rw [a1, a2, hcomm]
  have hσ' : σ = g * c₀ * g⁻¹ := hg.symm
  have e4 : σ * v₁ * σ⁻¹ = v₂ := by
    have : σ * v₁ * σ⁻¹ = g * (c₀ * u₁ * c₀⁻¹) * g⁻¹ := by rw [hσ', hv₁]; group
    rw [this, hcu1, hv₂]
  have e5 : σ * v₂ * σ⁻¹ = v₁ * v₂ := by
    have : σ * v₂ * σ⁻¹ = g * (c₀ * u₂ * c₀⁻¹) * g⁻¹ := by rw [hσ', hv₂]; group
    rw [this, hcu2, hv₁, hv₂]
    group
  have e6 : v₂ ≠ v₁ := by
    intro h
    apply hne
    rw [hv₁, hv₂] at h
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨Q, hQA, hQc, hQe, hQn, x, hxQ, hxn⟩ := klein_abstract (alternatingGroup (Fin n)) hv₁A
    hv₂A e1 e2 e3 e4 e5 e6
  exact ⟨Q, hQA, hQc, hQe, hQn, x, hxQ, hxn⟩

end AltHH

theorem hhobs_of_threeCycle {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hn : n = 7 ∨ n = 11) (e : Y ≃* alternatingGroup (Fin n)) (b : MulAut Y)
    (hb : (autTransport hn5 hn6 e b).IsThreeCycle) :
    ∃ E : Subgroup Y, IsPGroup 2 ↥E ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, b x ∈ E) ∧ ∃ x ∈ E, b x ≠ x := by
  obtain ⟨Q, hQA, hQc, hQe, hQn, q, hqQ, hqn⟩ := AltHH.klein_exists hn hb
  let E : Subgroup Y := Q.comap (((alternatingGroup (Fin n)).subtype).comp e.toMonoidHom)
  have hmemE : ∀ y, y ∈ E ↔ ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ Q :=
    fun y => Iff.rfl
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · refine IsPGroup.iff_orderOf.2 fun g => ?_
    have hg2 : g * g = 1 := by
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      have := hQe _ g.2
      simpa using this
    have hord : orderOf g ∣ 2 ^ 1 := by
      have := orderOf_dvd_of_pow_eq_one (x := g) (n := 2) (by rw [pow_two]; exact hg2)
      simpa using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact ⟨k, hk⟩
  · intro x hx y hy
    have := hQc _ hx _ hy
    apply e.injective
    apply Subtype.ext
    simpa using this
  · intro x hx
    rw [hmemE, autTransport_apply hn5 hn6 e b x]
    exact hQn _ hx
  · have hqA : q ∈ alternatingGroup (Fin n) := hQA hqQ
    obtain ⟨x, hx⟩ := e.surjective ⟨q, hqA⟩
    refine ⟨x, ?_, ?_⟩
    · rw [hmemE, hx]
      exact hqQ
    · intro h
      apply hqn
      have h1 := autTransport_apply hn5 hn6 e b x
      rw [h, hx] at h1
      simpa using h1.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
