module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

theorem exists_hyperplane {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x ^ 2 = 1) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : ∃ B : Subgroup G, B ≤ A ∧ a ∉ B ∧ ∀ g ∈ A, g ∈ B ∨ a * g ∈ B := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun Y : Subgroup G => (Y : Set G)) SetLike.coe_injective
  obtain ⟨B, ⟨hBA, haB⟩, hmax⟩ := Set.exists_max_image {B : Subgroup G | B ≤ A ∧ a ∉ B}
    (fun B : Subgroup G => Nat.card B) (Set.toFinite _) ⟨⊥, bot_le, by
      rw [Subgroup.mem_bot]
      exact ha1⟩
  refine ⟨B, hBA, haB, fun g hg => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hgB, hagB⟩ := h
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq g hg)
  have hA_of : ∀ x, x * g ∈ B → x ∈ A := fun x hx => by
    have := A.mul_mem (hBA hx) (A.inv_mem hg)
    rwa [mul_inv_cancel_right] at this
  let B₁ : Subgroup G :=
    { carrier := {x | x ∈ B ∨ x * g ∈ B}
      one_mem' := Or.inl B.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (B.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact B.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y (hBA hy) g hg, ← mul_assoc]
          exact B.mul_mem hx hy
        · refine Or.inl ?_
          have h1 := B.mul_mem hx hy
          have h2 : x * g * (y * g) = x * y := by
            rw [mul_assoc, ← mul_assoc g, hcomm g hg y (hA_of y hy), mul_assoc y, ← sq,
              hsq g hg, mul_one]
          rwa [h2] at h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (B.inv_mem hx)
        · refine Or.inr ?_
          have h1 := B.inv_mem hx
          rw [mul_inv_rev, hginv, ← hcomm x⁻¹ (A.inv_mem (hA_of x hx)) g hg] at h1
          exact h1 }
  have hB₁A : B₁ ≤ A := by
    rintro x (hx | hx)
    · exact hBA hx
    · exact hA_of x hx
  have haB₁ : a ∉ B₁ := by
    rintro (h | h)
    · exact haB h
    · rw [hcomm a ha g hg] at h
      have h2 : a * g = g * a := hcomm a ha g hg
      apply hagB
      rw [h2]
      exact h
  have hle : B ≤ B₁ := fun x hx => Or.inl hx
  have hgB₁ : g ∈ B₁ := Or.inr (by rw [← sq, hsq g hg]; exact B.one_mem)
  have hlt : Nat.card B < Nat.card B₁ := by
    have h1 : B < B₁ := lt_of_le_of_ne hle fun h => hgB (h ▸ hgB₁)
    exact Subgroup.card_lt_of_lt h1
  exact absurd (hmax B₁ ⟨hB₁A, haB₁⟩) (not_le.2 hlt)

variable {m n : ℕ}

theorem exists_embedding_range_eq (T : Finset (Fin n)) (hT : T.card = m) :
    ∃ ι : Fin m ↪ Fin n, ∀ x, x ∈ Set.range ι ↔ x ∈ T := by
  classical
  obtain ⟨ι, hι⟩ := exists_embedding_range_compl Tᶜ (m := m) (by
    rw [Finset.card_compl, Fintype.card_fin, ← hT]
    have := Finset.card_le_univ T
    rw [Fintype.card_fin] at this
    omega)
  exact ⟨ι, fun x => (hι x).trans (by rw [Finset.mem_compl, not_not])⟩

section DoubleLift

variable (ι : Fin m ↪ Fin n) (t : Perm (Fin n))

@[expose] noncomputable def doubleLift (σ : Perm (Fin m)) : Perm (Fin n) :=
  viaEmbedding σ ι * viaEmbedding σ (ι.trans t.toEmbedding)

variable {ι t} (ht : ∀ x, t x ∈ Set.range ι ↔ x ∉ Set.range ι)

include ht in
theorem doubleLift_apply_left (σ : Perm (Fin m)) (i : Fin m) :
    doubleLift ι t σ (ι i) = ι (σ i) := by
  have h1 : ι i ∉ Set.range (ι.trans t.toEmbedding) := by
    rintro ⟨j, hj⟩
    have h2 : t (ι j) ∈ Set.range ι := ⟨i, hj.symm⟩
    exact (ht (ι j)).1 h2 ⟨j, rfl⟩
  rw [doubleLift, Perm.mul_apply, viaEmbedding_apply_of_notMem _ _ _ h1, viaEmbedding_apply]

include ht in
theorem doubleLift_apply_right (σ : Perm (Fin m)) (i : Fin m) :
    doubleLift ι t σ (t (ι i)) = t (ι (σ i)) := by
  have h1 : t (ι (σ i)) ∉ Set.range ι := fun h => (ht _).1 h ⟨σ i, rfl⟩
  have h2 : viaEmbedding σ (ι.trans t.toEmbedding) (t (ι i)) = t (ι (σ i)) :=
    viaEmbedding_apply σ (ι.trans t.toEmbedding) i
  rw [doubleLift, Perm.mul_apply, h2, viaEmbedding_apply_of_notMem _ _ _ h1]

include ht in
theorem eq_or_eq_apply_of_swap (ht2 : ∀ x, t (t x) = x) (x : Fin n) :
    (∃ i, x = ι i) ∨ ∃ i, x = t (ι i) := by
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    exact Or.inl ⟨i, rfl⟩
  · obtain ⟨i, hi⟩ := (ht x).2 hx
    exact Or.inr ⟨i, by rw [hi, ht2]⟩

theorem doubleLift_mem_alternatingGroup (σ : Perm (Fin m)) :
    doubleLift ι t σ ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, doubleLift, map_mul, sign_viaEmbedding, sign_viaEmbedding,
    Int.units_mul_self]

include ht in
theorem doubleLift_commute (ht2 : ∀ x, t (t x) = x) (σ : Perm (Fin m)) :
    doubleLift ι t σ * t = t * doubleLift ι t σ := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  rcases eq_or_eq_apply_of_swap ht ht2 x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [doubleLift_apply_right ht, doubleLift_apply_left ht]
  · rw [ht2, doubleLift_apply_left ht, doubleLift_apply_right ht, ht2]

include ht in
theorem doubleLift_mem_permSetStab (ht2 : ∀ x, t (t x) = x) (σ : Perm (Fin m)) :
    doubleLift ι t σ ∈ permSetStab (Set.range ι) := by
  intro x
  rcases eq_or_eq_apply_of_swap ht ht2 x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [doubleLift_apply_left ht]
    exact ⟨fun _ => ⟨i, rfl⟩, fun _ => ⟨σ i, rfl⟩⟩
  · rw [doubleLift_apply_right ht]
    constructor
    · intro h
      exact absurd ⟨σ i, rfl⟩ ((ht _).1 h)
    · intro h
      exact absurd ⟨i, rfl⟩ ((ht _).1 h)

end DoubleLift

section TransM

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin n)}

@[expose] def transM (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n) (t : Perm (Fin n)) :
    Subgroup (MulAut V) :=
  preSub ψ (Subgroup.centralizer {t} ⊓ permSetStab (Set.range ι))

theorem transM_le (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n) (t : Perm (Fin n)) :
    transM ψ ι t ≤ preSub ψ (permSetStab (Set.range ι)) :=
  preSub_mono inf_le_right

variable {ι : Fin m ↪ Fin n} {t : Perm (Fin n)}

theorem apply_mem_centralizer_transM (k : ↥(transM ψ ι t)) :
    ψ (Subgroup.inclusion ((transM_le ψ ι t).trans preSub_le) k) * t =
      t * ψ (Subgroup.inclusion ((transM_le ψ ι t).trans preSub_le) k) :=
  Subgroup.mem_centralizer_singleton_iff.1
    ((coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion ((transM_le ψ ι t).trans preSub_le) k)).1
      k.2).1

theorem restrictHom_transM_surjective (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (ht : ∀ x, t x ∈ Set.range ι ↔ x ∉ Set.range ι) (ht2 : ∀ x, t (t x) = x)
    (σ : Perm (Fin m)) :
    ∃ k : ↥(transM ψ ι t), restrictHom ψ ι _ (transM_le ψ ι t) k = σ ∧
      ψ (Subgroup.inclusion ((transM_le ψ ι t).trans preSub_le) k) = doubleLift ι t σ := by
  obtain ⟨h, hh⟩ := hAlt (doubleLift_mem_alternatingGroup σ)
  have hM : (h : MulAut V) ∈ transM ψ ι t := coe_mem_preSub.2 (by
    rw [hh]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (doubleLift_commute ht ht2 σ),
      doubleLift_mem_permSetStab ht ht2 σ⟩)
  refine ⟨⟨h, hM⟩, (restrictHom_eq_iff _ σ).2 fun i => ?_, hh⟩
  change ψ h (ι i) = ι (σ i)
  rw [hh, doubleLift_apply_left ht]

theorem restrictHom_transM_injective (hψ : Function.Injective ψ)
    (ht : ∀ x, t x ∈ Set.range ι ↔ x ∉ Set.range ι) (ht2 : ∀ x, t (t x) = x) :
    Function.Injective (restrictHom ψ ι (transM ψ ι t) (transM_le ψ ι t)) :=
  restrictHom_injective hψ fun k hk => by
    have hc := apply_mem_centralizer_transM k
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    rcases eq_or_eq_apply_of_swap ht ht2 x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hk i
    · have h1 := congrArg (fun g : Perm (Fin n) => g (ι i)) hc
      simp only [Perm.mul_apply] at h1
      rw [h1, hk i]

end TransM

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
