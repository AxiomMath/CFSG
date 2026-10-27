module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

section Span


variable {K : Type} [Field K]

abbrev triple (σ : K ≃+* K) (s : K) : Fin 3 → K := ![s, σ s, σ (σ s)]

theorem span_triple_eq_top {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ : ∃ x : K, σ x ≠ x) :
    Submodule.span K (Set.range fun s : K => triple σ s) = ⊤ := by
  classical
  let m : Fin 3 → (Kˣ →* K) := ![(RingHom.id K).toMonoidHom.comp (Units.coeHom K),
    σ.toRingHom.toMonoidHom.comp (Units.coeHom K),
    (σ.toRingHom.comp σ.toRingHom).toMonoidHom.comp (Units.coeHom K)]
  have e0 : ∀ u : Kˣ, m 0 u = (u : K) := fun u => rfl
  have e1 : ∀ u : Kˣ, m 1 u = σ (u : K) := fun u => rfl
  have e2 : ∀ u : Kˣ, m 2 u = σ (σ (u : K)) := fun u => rfl
  have hm : ∀ (j : Fin 3) (u : Kˣ), m j u = triple σ (u : K) j := by
    intro j u
    fin_cases j <;> rfl
  obtain ⟨x, hx⟩ := hσ
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  set u1 : Kˣ := Units.mk0 x hx0 with hu1
  have hσ2 : ∃ y : K, σ (σ y) ≠ y := by
    by_contra h
    push Not at h
    apply hx
    have h1 := hσ3 x
    rw [h (σ x)] at h1
    exact h1
  obtain ⟨y, hy⟩ := hσ2
  have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero, map_zero])
  set u2 : Kˣ := Units.mk0 y hy0 with hu2
  have d01 : m 0 ≠ m 1 := fun h => by
    have := congrArg (fun g : Kˣ →* K => g u1) h
    simp only [e0, e1] at this
    exact hx this.symm
  have d02 : m 0 ≠ m 2 := fun h => by
    have := congrArg (fun g : Kˣ →* K => g u2) h
    simp only [e0, e2] at this
    exact hy this.symm
  have d12 : m 1 ≠ m 2 := fun h => by
    have := congrArg (fun g : Kˣ →* K => g u1) h
    simp only [e1, e2] at this
    exact hx (σ.injective this).symm
  have hinj : Function.Injective m := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij d01
      | exact absurd hij d02
      | exact absurd hij d12
      | exact absurd hij.symm d01
      | exact absurd hij.symm d02
      | exact absurd hij.symm d12
  have hli : LinearIndependent K (fun j => (m j : Kˣ → K)) :=
    (linearIndependent_monoidHom Kˣ K).comp m hinj
  by_contra hne
  obtain ⟨f, hf0, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.2 hne) inferInstance
  set a : Fin 3 → K := fun j => f (Pi.single j 1) with ha
  have hfv : ∀ v : Fin 3 → K, f v = ∑ j, v j * a j := by
    intro v
    have hv : v = ∑ j, v j • (Pi.single j (1 : K) : Fin 3 → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hzero : ∀ s : K, ∑ j, triple σ s j * a j = 0 := by
    intro s
    have hmem : f (triple σ s) = 0 := by
      have h1 : f (triple σ s) ∈ (Submodule.span K (Set.range fun s : K => triple σ s)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨s, rfl⟩)
      rw [hfp] at h1
      exact (Submodule.mem_bot K).1 h1
    have h2 := hfv (triple σ s)
    rw [hmem] at h2
    exact h2.symm
  have ha0 : a = 0 := by
    have hsum : ∑ j, a j • (m j : Kˣ → K) = 0 := by
      funext u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have h := hzero (u : K)
      simp only [Fin.sum_univ_three] at h ⊢
      have hm' : ∀ j, (m j : Kˣ → K) u = triple σ (u : K) j := fun j => hm j u
      rw [hm' 0, hm' 1, hm' 2]
      simp only [triple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h ⊢
      linear_combination h
    have := (Fintype.linearIndependent_iff.1 hli) a hsum
    funext j
    exact this j
  apply hf0
  refine LinearMap.ext fun v => ?_
  rw [hfv v, ha0]
  simp

theorem forall_of_triples {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ : ∃ x : K, σ x ≠ x) (P : (Fin 3 → K) → Prop) (h0 : P 0)
    (hadd : ∀ p q, P p → P q → P (p + q)) (hT : ∀ (μ s : K), P (μ • triple σ s)) :
    ∀ p, P p := by
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {p | ∀ μ : K, P (μ • p)}
      add_mem' := fun {p q} hp hq μ => by
        rw [smul_add]
        exact hadd _ _ (hp μ) (hq μ)
      zero_mem' := fun μ => by
        rw [smul_zero]
        exact h0
      smul_mem' := fun c p hp μ => by
        rw [smul_smul]
        exact hp (μ * c) }
  have hT' : Set.range (fun s : K => triple σ s) ⊆ (W : Set (Fin 3 → K)) := by
    rintro _ ⟨s, rfl⟩ μ
    exact hT μ s
  have hle : Submodule.span K (Set.range fun s : K => triple σ s) ≤ W :=
    Submodule.span_le.2 hT'
  rw [span_triple_eq_top hσ3 hσ] at hle
  intro p
  have hp := hle (Submodule.mem_top (x := p))
  have hp' : ∀ μ : K, P (μ • p) := hp
  simpa using hp' 1

end Span

section Outer


variable {K : Type} [Field K]

theorem outer_pos_mul (a b c a' b' c' : K) :
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c *
      (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a' *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b' *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') =
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) (a + a') *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (b + b') *
        xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (c + c') := by
  have hBCA' := (commute_outer_xPar (K := K) (a := nd 1) (b := nd 0) (nd_ne 1 2 (by decide)
    (by decide) (by decide)) (nd_ne 0 2 (by decide) (by decide) (by decide))
    (nd_ne 1 0 (by decide) (by decide) (by decide)) b a').mul_left
    (commute_outer_xPar (K := K) (a := nd 3) (b := nd 0) (nd_ne 3 2 (by decide) (by decide)
      (by decide)) (nd_ne 0 2 (by decide) (by decide) (by decide))
      (nd_ne 3 0 (by decide) (by decide) (by decide)) c a')
  have hCB' := commute_outer_xPar (K := K) (a := nd 3) (b := nd 1) (nd_ne 3 2 (by decide)
    (by decide) (by decide)) (nd_ne 1 2 (by decide) (by decide) (by decide))
    (nd_ne 3 1 (by decide) (by decide) (by decide)) c b'
  calc _ = xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b' *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a' *
          (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
            xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c)) *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b' *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') := by
        erw [hBCA'.eq]
        try rfl
    _ = (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
          (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c *
            xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b') *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
          (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b' *
            xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c) *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') := by
        erw [hCB'.eq]
        try rfl
    _ = (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b') *
        (xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c *
          xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = _ := by
        erw [← xPar_add, ← xPar_add, ← xPar_add]

theorem outer_neg_mul (a b c a' b' c' : K) :
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c *
      (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a' *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b' *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') =
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) (a + a') *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (b + b') *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (c + c') := by
  have hBCA' := (commute_outer_neg_xPar (K := K) (a := nd 1) (b := nd 0) (nd_ne 1 2 (by decide)
    (by decide) (by decide)) (nd_ne 0 2 (by decide) (by decide) (by decide))
    (nd_ne 1 0 (by decide) (by decide) (by decide)) b a').mul_left
    (commute_outer_neg_xPar (K := K) (a := nd 3) (b := nd 0) (nd_ne 3 2 (by decide) (by decide)
      (by decide)) (nd_ne 0 2 (by decide) (by decide) (by decide))
      (nd_ne 3 0 (by decide) (by decide) (by decide)) c a')
  have hCB' := commute_outer_neg_xPar (K := K) (a := nd 3) (b := nd 1) (nd_ne 3 2 (by decide)
    (by decide) (by decide)) (nd_ne 1 2 (by decide) (by decide) (by decide))
    (nd_ne 3 1 (by decide) (by decide) (by decide)) c b'
  calc _ = xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b' *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a' *
          (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
            xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c)) *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b' *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') := by
        erw [hBCA'.eq]
        try rfl
    _ = (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
          (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c *
            xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b') *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
          (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b' *
            xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c) *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') := by
        erw [hCB'.eq]
        try rfl
    _ = (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a') *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b') *
        (xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c *
          xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c') := by
        simp only [mul_assoc]
    _ = _ := by
        erw [← xPar_add, ← xPar_add, ← xPar_add]

theorem xPar_zero_D4 (γ : Fin Tag.D4.rank → ℤ) :
    xPar (rootOperatorFamily Tag.D4) γ (0 : K) = 1 :=
  xPar_zero γ

theorem outer_zero_mem (S : Subgroup (adjointGroup Tag.D4 K)) :
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) (0 : K) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (0 : K) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (0 : K) ∈ S := by
  erw [xPar_zero_D4, xPar_zero_D4, xPar_zero_D4, mul_one, one_mul]
  exact S.one_mem

theorem outer_zero_mem_neg (S : Subgroup (adjointGroup Tag.D4 K)) :
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) (0 : K) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (0 : K) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (0 : K) ∈ S := by
  erw [xPar_zero_D4, xPar_zero_D4, xPar_zero_D4, mul_one, one_mul]
  exact S.one_mem

theorem outer_pos_all {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ : ∃ x : K, σ x ≠ x) {S : Subgroup (adjointGroup Tag.D4 K)}
    (hE : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ S)
    (hT : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (σ (σ s)) ∈ S) :
    ∀ p : Fin 3 → K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) (p 0) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (p 1) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (p 2) ∈ S := by
  refine forall_of_triples (K := K) hσ3 hσ
    (fun p : Fin 3 → K => xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) (p 0) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (p 1) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (p 2) ∈ S) ?_ ?_ ?_
  · exact outer_zero_mem S
  · intro p q hp hq
    have h := S.mul_mem hp hq
    rw [outer_pos_mul] at h
    exact h
  · intro μ s
    by_cases hμ : μ = 0
    · subst hμ
      rw [zero_smul]
      exact outer_zero_mem S
    · set t : Kˣ := Units.mk0 μ⁻¹ (inv_ne_zero hμ) with ht
      have hT0 := torusElement_e2_mem hE t
      have hT' := S.mul_mem (S.mul_mem hT0 (hT s)) (S.inv_mem hT0)
      have e0 := torus_conj_outer_pos t (j := nd 0) (Or.inl rfl) s
      have e1 := torus_conj_outer_pos t (j := nd 1) (Or.inr (Or.inl rfl)) (σ s)
      have e3 := torus_conj_outer_pos t (j := nd 3) (Or.inr (Or.inr rfl)) (σ (σ s))
      have hconj : ∀ (T a b c : adjointGroup Tag.D4 K), T * (a * b * c) * T⁻¹ =
          (T * a * T⁻¹) * (T * b * T⁻¹) * (T * c * T⁻¹) := fun T a b c => by
        simp only [mul_assoc, inv_mul_cancel_left]
      erw [hconj, e0, e1, e3] at hT'
      have hmu : (t : K)⁻¹ = μ := by
        rw [ht, Units.val_mk0, inv_inv]
      rw [hmu] at hT'
      exact hT'

theorem outer_neg_all {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ : ∃ x : K, σ x ≠ x) {S : Subgroup (adjointGroup Tag.D4 K)}
    (hE : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ S)
    (hTm : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (σ (σ s)) ∈ S) :
    ∀ p : Fin 3 → K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) (p 0) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (p 1) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (p 2) ∈ S := by
  refine forall_of_triples (K := K) hσ3 hσ
    (fun p : Fin 3 → K => xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) (p 0) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (p 1) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (p 2) ∈ S) ?_ ?_ ?_
  · exact outer_zero_mem_neg S
  · intro p q hp hq
    have h := S.mul_mem hp hq
    rw [outer_neg_mul] at h
    exact h
  · intro μ s
    by_cases hμ : μ = 0
    · subst hμ
      rw [zero_smul]
      exact outer_zero_mem_neg S
    · set t : Kˣ := Units.mk0 μ hμ with ht
      have hT0 := torusElement_e2_mem hE t
      have hT' := S.mul_mem (S.mul_mem hT0 (hTm s)) (S.inv_mem hT0)
      have e0 := torus_conj_outer_neg t (j := nd 0) (Or.inl rfl) s
      have e1 := torus_conj_outer_neg t (j := nd 1) (Or.inr (Or.inl rfl)) (σ s)
      have e3 := torus_conj_outer_neg t (j := nd 3) (Or.inr (Or.inr rfl)) (σ (σ s))
      have hconj : ∀ (T a b c : adjointGroup Tag.D4 K), T * (a * b * c) * T⁻¹ =
          (T * a * T⁻¹) * (T * b * T⁻¹) * (T * c * T⁻¹) := fun T a b c => by
        simp only [mul_assoc, inv_mul_cancel_left]
      erw [hconj, e0, e1, e3] at hT'
      have hmu : (t : K) = μ := by
        rw [ht, Units.val_mk0]
      rw [hmu] at hT'
      exact hT'

theorem outer_root_mem_of_triples {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ : ∃ x : K, σ x ≠ x) {S : Subgroup (adjointGroup Tag.D4 K)}
    (hE : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ S)
    (hT : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (σ (σ s)) ∈ S)
    (hTm : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (σ (σ s)) ∈ S) :
    (∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) c ∈ S) ∧
    (∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) c ∈ S) ∧
    (∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c ∈ S) := by
  have hPos := outer_pos_all hσ3 hσ hE hT
  have hNeg := outer_neg_all hσ3 hσ hE hTm
  have hPos' : ∀ a b c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) a *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) b *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) c ∈ S :=
    fun a b c => hPos ![a, b, c]
  have hNeg' : ∀ a b c : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) a *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) b *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) c ∈ S :=
    fun a b c => hNeg ![a, b, c]
  have z0 : xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) (0 : K) = 1 := xPar_zero_D4 _
  have z1 : xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (0 : K) = 1 := xPar_zero_D4 _
  have z3 : xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (0 : K) = 1 := xPar_zero_D4 _
  have n0 : xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) (0 : K) = 1 := xPar_zero_D4 _
  have n1 : xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (0 : K) = 1 := xPar_zero_D4 _
  have n3 : xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (0 : K) = 1 := xPar_zero_D4 _
  refine ⟨fun c => ⟨?_, ?_⟩, fun c => ⟨?_, ?_⟩, fun c => ⟨?_, ?_⟩⟩
  · have h := hPos' c 0 0
    rw [z1, z3, mul_one, mul_one] at h
    exact h
  · have h := hNeg' c 0 0
    rw [n1, n3, mul_one, mul_one] at h
    exact h
  · have h := hPos' 0 c 0
    rw [z0, z3, one_mul, mul_one] at h
    exact h
  · have h := hNeg' 0 c 0
    rw [n0, n3, one_mul, mul_one] at h
    exact h
  · have h := hPos' 0 0 c
    rw [z0, z1, one_mul, one_mul] at h
    exact h
  · have h := hNeg' 0 0 c
    rw [n0, n1, one_mul, one_mul] at h
    exact h

end Outer

end CFSG.LieType.SeitzGeneration.ExcWideThree
