module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZM

open Module CFSG.RankThree.OrthogonalInvolutions QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem commSpace_mul_le (f g : V ≃ₗ[ZMod 2] V) :
    commSpace (f * g) ≤ commSpace f ⊔ commSpace g := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.1 hx
  have e : (f * g) v - v = (f (g v) - g v) + (g v - v) := by
    rw [LinearEquiv.mul_apply]
    abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem_commSpace f _) (sub_mem_commSpace g _)

theorem commute_of_triv {W C : Submodule (ZMod 2) V} (hWC : W ⊔ C = ⊤)
    {f₁ f₂ : V ≃ₗ[ZMod 2] V} (h₁W : ∀ w ∈ W, f₁ w = w) (h₁C : ∀ c ∈ C, f₁ c ∈ C)
    (h₂C : ∀ c ∈ C, f₂ c = c) (h₂W : ∀ w ∈ W, f₂ w ∈ W) (v : V) : f₁ (f₂ v) = f₂ (f₁ v) := by
  have hv : v ∈ W ⊔ C := hWC ▸ Submodule.mem_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
  simp only [map_add, h₂C c hc, h₁W w hw, h₁W _ (h₂W w hw), h₂C _ (h₁C c hc)]

variable (q : QuadraticForm (ZMod 2) V)

theorem mem_orth_iff {A : Submodule (ZMod 2) V} {x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin A ↔ ∀ a ∈ A, polar q a x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

theorem le_orth_comm {A B : Submodule (ZMod 2) V}
    (h : B ≤ LinearMap.BilinForm.orthogonal q.polarBilin A) :
    A ≤ LinearMap.BilinForm.orthogonal q.polarBilin B := by
  intro a ha
  rw [mem_orth_iff]
  intro b hb
  rw [polar_comm]
  exact (mem_orth_iff q).1 (h hb) a ha

theorem le_orth_sup {A₁ A₂ B : Submodule (ZMod 2) V}
    (h₁ : B ≤ LinearMap.BilinForm.orthogonal q.polarBilin A₁)
    (h₂ : B ≤ LinearMap.BilinForm.orthogonal q.polarBilin A₂) :
    B ≤ LinearMap.BilinForm.orthogonal q.polarBilin (A₁ ⊔ A₂) := by
  intro x hx
  rw [mem_orth_iff]
  intro y hy
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  rw [polar_add_left, (mem_orth_iff q).1 (h₁ hx) y₁ hy₁, (mem_orth_iff q).1 (h₂ hx) y₂ hy₂,
    add_zero]

theorem nondeg_sup {A B : Submodule (ZMod 2) V}
    (hA : A ⊓ LinearMap.BilinForm.orthogonal q.polarBilin A = ⊥)
    (hB : B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin B = ⊥)
    (hAB : B ≤ LinearMap.BilinForm.orthogonal q.polarBilin A) [FiniteDimensional (ZMod 2) V] :
    (A ⊔ B) ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (A ⊔ B) = ⊥ ∧
      finrank (ZMod 2) (A ⊔ B : Submodule (ZMod 2) V) =
        finrank (ZMod 2) A + finrank (ZMod 2) B := by
  have hBA := le_orth_comm q hAB
  constructor
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv1
    have hv2' := (mem_orth_iff q).1 hv2
    have ha0 : a = 0 := by
      have : a ∈ A ⊓ LinearMap.BilinForm.orthogonal q.polarBilin A := by
        refine Submodule.mem_inf.2 ⟨ha, (mem_orth_iff q).2 fun a' ha' => ?_⟩
        have h1 := hv2' a' (Submodule.mem_sup_left ha')
        rw [polar_add_right, (mem_orth_iff q).1 (hAB hb) a' ha', add_zero] at h1
        exact h1
      rw [hA] at this
      exact (Submodule.mem_bot _).1 this
    have hb0 : b = 0 := by
      have : b ∈ B ⊓ LinearMap.BilinForm.orthogonal q.polarBilin B := by
        refine Submodule.mem_inf.2 ⟨hb, (mem_orth_iff q).2 fun b' hb' => ?_⟩
        have h1 := hv2' b' (Submodule.mem_sup_right hb')
        rw [polar_add_right, (mem_orth_iff q).1 (hBA ha) b' hb', zero_add] at h1
        exact h1
      rw [hB] at this
      exact (Submodule.mem_bot _).1 this
    rw [ha0, hb0, add_zero, Submodule.mem_bot]
  · have hinf : A ⊓ B = ⊥ := by
      rw [eq_bot_iff, ← hA]
      exact inf_le_inf_left _ hAB
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hinf, finrank_bot, add_zero] at h
    exact h

@[expose] def orthSum (W : Submodule (ZMod 2) V) (Vs : ℕ → Submodule (ZMod 2) V) :
    ℕ → Submodule (ZMod 2) V
  | 0 => W
  | m + 1 => orthSum W Vs m ⊔ Vs m

omit q in
theorem orthSum_zero (W : Submodule (ZMod 2) V) (Vs : ℕ → Submodule (ZMod 2) V) :
    orthSum W Vs 0 = W := rfl

omit q in
theorem orthSum_succ (W : Submodule (ZMod 2) V) (Vs : ℕ → Submodule (ZMod 2) V) (m : ℕ) :
    orthSum W Vs (m + 1) = orthSum W Vs m ⊔ Vs m := rfl

omit q in
theorem orthSum_le {W X : Submodule (ZMod 2) V} {Vs : ℕ → Submodule (ZMod 2) V} {m : ℕ}
    (hW : W ≤ X) (hV : ∀ i < m, Vs i ≤ X) : orthSum W Vs m ≤ X := by
  induction m with
  | zero => exact hW
  | succ m ih =>
    exact sup_le (ih fun i hi => hV i (by omega)) (hV m (by omega))

theorem orthSum_nondeg [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V}
    {Vs : ℕ → Submodule (ZMod 2) V} {M d : ℕ}
    (hW : W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W = ⊥)
    (hV : ∀ i < M, Vs i ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (Vs i) = ⊥)
    (hVd : ∀ i < M, finrank (ZMod 2) (Vs i) = d)
    (hVW : ∀ i < M, Vs i ≤ LinearMap.BilinForm.orthogonal q.polarBilin W)
    (hVV : ∀ i < M, ∀ j < M, i ≠ j → Vs i ≤ LinearMap.BilinForm.orthogonal q.polarBilin (Vs j)) :
    ∀ m ≤ M, orthSum W Vs m ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (orthSum W Vs m) = ⊥ ∧
      finrank (ZMod 2) (orthSum W Vs m) = finrank (ZMod 2) W + d * m ∧
      ∀ j, m ≤ j → j < M →
        Vs j ≤ LinearMap.BilinForm.orthogonal q.polarBilin (orthSum W Vs m) := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨hW, by rw [orthSum_zero, mul_zero, add_zero], fun j _ hj => hVW j hj⟩
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    obtain ⟨h4, h5⟩ := nondeg_sup q h1 (hV m (by omega)) (h3 m le_rfl (by omega))
    refine ⟨h4, ?_, fun j hj hjM => ?_⟩
    · rw [orthSum_succ, h5, h2, hVd m (by omega)]
      ring
    · rw [orthSum_succ]
      exact le_orth_sup q (h3 j (by omega) hjM) (hVV j hjM m (by omega) (by omega))

theorem orth_mem_of_isometry {f : V ≃ₗ[ZMod 2] V} (hf : ∀ v, q (f v) = q v)
    {Y : Submodule (ZMod 2) V} (hpre : ∀ y ∈ Y, ∃ y' ∈ Y, f y' = y) {v : V}
    (hv : v ∈ LinearMap.BilinForm.orthogonal q.polarBilin Y) :
    f v ∈ LinearMap.BilinForm.orthogonal q.polarBilin Y := by
  rw [mem_orth_iff] at hv ⊢
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hpre y hy
  rw [polar, ← map_add, hf, hf, hf]
  exact hv y' hy'

theorem sup_orth_eq_top [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {Y : Submodule (ZMod 2) V} (hY : Y ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y = ⊥) :
    Y ⊔ LinearMap.BilinForm.orthogonal q.polarBilin Y = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq Y
    (LinearMap.BilinForm.orthogonal q.polarBilin Y)
  rw [hY, finrank_bot, add_zero, LinearMap.BilinForm.finrank_orthogonal hq] at h
  have hle := Submodule.finrank_le Y
  exact Submodule.eq_top_of_finrank_eq (by omega)

omit q in
theorem le_orthSum_W (W : Submodule (ZMod 2) V) (Vs : ℕ → Submodule (ZMod 2) V) (m : ℕ) :
    W ≤ orthSum W Vs m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans le_sup_left

omit q in
theorem le_orthSum_V (W : Submodule (ZMod 2) V) (Vs : ℕ → Submodule (ZMod 2) V) {i m : ℕ}
    (hi : i < m) : Vs i ≤ orthSum W Vs m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact (ih h).trans le_sup_left
    · rw [h, orthSum_succ]
      exact le_sup_right

end CFSG.LargeExtraspecial.AS35ZM
