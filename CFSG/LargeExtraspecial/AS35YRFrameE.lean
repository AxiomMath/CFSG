module

public import CFSG.LargeExtraspecial.AS35YRFrameB
public import CFSG.LargeExtraspecial.OrthoF2PairsCases
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem exists_polar_eq_one (hq : q.polarBilin.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ v, polar q v x = 1 := by
  by_contra hcon
  push Not at hcon
  apply hx
  refine hq.1 x fun v => ?_
  rw [polarBilin_apply_apply, polar_comm]
  rcases Frame.zmod2_cases_YR (polar q v x) with h | h
  · exact h
  · exact absurd h (hcon v)

theorem exists_dual_pair (hq : q.polarBilin.Nondegenerate) {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    ∃ x y : V, polar q x a = 1 ∧ polar q x b = 0 ∧ polar q y a = 0 ∧ polar q y b = 1 := by
  obtain ⟨v₁, h₁⟩ := exists_polar_eq_one hq ha
  obtain ⟨v₂, h₂⟩ := exists_polar_eq_one hq hb
  have hab' : a + b ≠ 0 := by
    intro h
    apply hab
    have := congrArg (· + b) h
    simpa [add_assoc, add_self_YR] using this
  obtain ⟨v₃, h₃⟩ := exists_polar_eq_one hq hab'
  rw [polar_add_right] at h₃
  have hsum : ∀ x y : V, polar q (x + y) a = polar q x a + polar q y a ∧
      polar q (x + y) b = polar q x b + polar q y b := fun x y =>
    ⟨polar_add_left _ _ _ _, polar_add_left _ _ _ _⟩
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases Frame.zmod2_cases_YR (polar q v₁ b) with h1b | h1b <;>
    rcases Frame.zmod2_cases_YR (polar q v₂ a) with h2a | h2a
  · exact ⟨v₁, v₂, h₁, h1b, h2a, h₂⟩
  · refine ⟨v₁, v₂ + v₁, h₁, h1b, ?_, ?_⟩
    · rw [(hsum _ _).1, h2a, h₁, h11]
    · rw [(hsum _ _).2, h₂, h1b, add_zero]
  · refine ⟨v₁ + v₂, v₂, ?_, ?_, h2a, h₂⟩
    · rw [(hsum _ _).1, h₁, h2a, add_zero]
    · rw [(hsum _ _).2, h1b, h₂, h11]
  · rcases Frame.zmod2_cases_YR (polar q v₃ a) with h3a | h3a
    · have h3b : polar q v₃ b = 1 := by rw [h3a, zero_add] at h₃; exact h₃
      refine ⟨v₃ + v₁, v₃, ?_, ?_, h3a, h3b⟩
      · rw [(hsum _ _).1, h3a, h₁, zero_add]
      · rw [(hsum _ _).2, h3b, h1b, h11]
    · have h3b : polar q v₃ b = 0 := by
        rw [h3a] at h₃
        rcases Frame.zmod2_cases_YR (polar q v₃ b) with h | h
        · exact h
        · rw [h] at h₃; exact absurd h₃ (by decide)
      refine ⟨v₃, v₃ + v₁, h3a, h3b, ?_, ?_⟩
      · rw [(hsum _ _).1, h3a, h₁, h11]
      · rw [(hsum _ _).2, h3b, h1b, zero_add]

theorem exists_frame (hq : q.polarBilin.Nondegenerate) {a b : V} (qa : q a = 0) (qb : q b = 0)
    (ab : polar q a b = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ F : Frame q, F.a = a ∧ F.b = b := by
  obtain ⟨x, y, hxa, hxb, hya, hyb⟩ := exists_dual_pair hq ha hb hab
  have hba : polar q b a = 0 := by rw [polar_comm]; exact ab
  set c := y + q y • b with hc
  set c₀ := x + q x • a with hc₀
  have hca : polar q c a = 0 := by
    rw [hc, polar_add_left, polar_smul_left, hya, hba]
    simp
  have hcb : polar q c b = 1 := by
    rw [hc, polar_add_left, polar_smul_left, hyb, polar_self_eq_zero qb]
    simp
  have hqc : q c = 0 := by
    rw [hc, QuadraticMap.map_add q, QuadraticMap.map_smul, qb, polar_smul_right, hyb]
    simp only [mul_zero, add_zero, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero _
  have hc₀a : polar q c₀ a = 1 := by
    rw [hc₀, polar_add_left, polar_smul_left, hxa, polar_self_eq_zero qa]
    simp
  have hc₀b : polar q c₀ b = 0 := by
    rw [hc₀, polar_add_left, polar_smul_left, hxb, ab]
    simp
  have hqc₀ : q c₀ = 0 := by
    rw [hc₀, QuadraticMap.map_add q, QuadraticMap.map_smul, qa, polar_smul_right, hxa]
    simp only [mul_zero, add_zero, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero _
  set c' := c₀ + polar q c₀ c • b with hc'
  have hc'a : polar q c' a = 1 := by
    rw [hc', polar_add_left, polar_smul_left, hc₀a, hba]
    simp
  have hc'b : polar q c' b = 0 := by
    rw [hc', polar_add_left, polar_smul_left, hc₀b, polar_self_eq_zero qb]
    simp
  have hc'c : polar q c c' = 0 := by
    rw [polar_comm, hc', polar_add_left, polar_smul_left, polar_comm q b c, hcb, smul_eq_mul,
      mul_one]
    exact CharTwo.add_self_eq_zero _
  have hqc' : q c' = 0 := by
    rw [hc', QuadraticMap.map_add q, QuadraticMap.map_smul, qb, polar_smul_right, hc₀b, hqc₀]
    simp
  exact ⟨⟨a, b, c, c', qa, qb, hqc, hqc', ab, by rw [polar_comm]; exact hca,
    by rw [polar_comm]; exact hcb, by rw [polar_comm]; exact hc'a,
    by rw [polar_comm]; exact hc'b, hc'c⟩, rfl, rfl⟩

theorem commSpace_siegel_le {u w : V} (hu : q u = 0) (hw : q w = 0) (huw : polar q u w = 0) :
    commSpace (eichler q u w) ≤ Submodule.span (ZMod 2) {u, w} := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  rw [siegel_apply hu hw huw, add_assoc, add_sub_cancel_left]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem q_eq_zero_of_mem_span_pair {u w : V} (hu : q u = 0) (hw : q w = 0)
    (huw : polar q u w = 0) {z : V} (hz : z ∈ Submodule.span (ZMod 2) {u, w}) : q z = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.map_smul, hu, hw,
    polar_smul_left, polar_smul_right, huw]
  simp

theorem even_finrank_commSpace_siegel [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {u w : V} (hu : q u = 0) (hw : q w = 0)
    (huw : polar q u w = 0) : Even (finrank (ZMod 2) (commSpace (eichler q u w))) :=
  even_finrank_commSpace_of_forall_eq_zero hq (eichler_mem_orthogonalGroup q u w)
    (siegel_mul_self huw) fun _ hx =>
      q_eq_zero_of_mem_span_pair hu hw huw (commSpace_siegel_le hu hw huw hx)

namespace Frame

variable (F : Frame q)

theorem a_ne_zero : F.a ≠ 0 := by
  intro h
  have := F.ac'
  rw [h, polar_zero_left] at this
  exact absurd this (by decide)

theorem b_ne_zero : F.b ≠ 0 := by
  intro h
  have := F.bc
  rw [h, polar_zero_left] at this
  exact absurd this (by decide)

theorem a_ne_b : F.a ≠ F.b := by
  intro h
  have h1 := F.ac'
  rw [h, F.bc'] at h1
  exact absurd h1 (by decide)

theorem t_c : F.t F.c = F.c + F.a := by
  rw [F.t_apply, polar_comm q F.c F.a, F.ac, polar_comm q F.c F.b, F.bc]
  simp

theorem t_c' : F.t F.c' = F.c' + F.b := by
  rw [F.t_apply, polar_comm q F.c' F.a, F.ac', polar_comm q F.c' F.b, F.bc']
  simp

theorem commSpace_t : commSpace F.t = F.ell := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [F.t_apply, add_assoc, add_sub_cancel_left]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ F.b_mem_ell)
      (Submodule.smul_mem _ _ F.a_mem_ell)
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact mem_commSpace.mpr ⟨F.c, by rw [F.t_c, add_sub_cancel_left]⟩
    · exact mem_commSpace.mpr ⟨F.c', by rw [F.t_c', add_sub_cancel_left]⟩

theorem finrank_ell [FiniteDimensional (ZMod 2) V] : finrank (ZMod 2) F.ell = 2 := by
  have hli : LinearIndependent (ZMod 2) ![F.a, F.b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x => polar q x F.c') hst
    have h2 := congrArg (fun x => polar q x F.c) hst
    simp only [polar_add_left, polar_smul_left, F.ac', F.bc', F.bc, F.ac, polar_zero_left,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  have hr : Set.range ![F.a, F.b] = {F.a, F.b} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have := finrank_span_eq_card hli
  rw [hr] at this
  simpa using this

theorem isTypeA_t [FiniteDimensional (ZMod 2) V] : IsTypeA q F.t 2 := by
  refine ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup F.t_mem v, ?_,
    F.t_mul_self, by rw [F.commSpace_t, F.finrank_ell], fun x hx => ?_⟩
  · intro h
    have := F.t_c
    rw [h, LinearEquiv.coe_one, id] at this
    apply F.a_ne_zero
    have h' := congrArg (· - F.c) this
    simpa using h'.symm
  · rw [F.commSpace_t] at hx
    exact q_eq_zero_of_mem_ell hx

theorem eq_t_of_isTypeA [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {τ : V ≃ₗ[ZMod 2] V} (hτ : IsTypeA q τ 2) (h : commSpace τ = F.ell) : τ = F.t :=
  OrthoF2.eq_of_commSpace_eq hq hτ F.isTypeA_t (h.trans F.commSpace_t.symm)

theorem conj_t_eq [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hgℓ : ∀ z ∈ F.ell, g z ∈ F.ell) : g * F.t * g⁻¹ = F.t := by
  have hA := F.isTypeA_t
  have hcomm : commSpace (g * F.t * g⁻¹) = F.ell := by
    rw [commSpace_conj, F.commSpace_t]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hgℓ z hz
    · exact LinearEquiv.finrank_map_eq g F.ell
  refine F.eq_t_of_isTypeA hq ⟨fun v => ?_, ?_, ?_, ?_, fun x hx => ?_⟩ hcomm
  · exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (mul_mem (mul_mem hg F.t_mem) (inv_mem hg)) v
  · intro h1
    apply hA.2.1
    have : F.t = g⁻¹ * (g * F.t * g⁻¹) * g := by group
    rw [this, h1, mul_one, inv_mul_cancel]
  · have : g * F.t * g⁻¹ * (g * F.t * g⁻¹) = g * (F.t * F.t) * g⁻¹ := by group
    rw [this, F.t_mul_self, mul_one, mul_inv_cancel]
  · rw [hcomm, F.finrank_ell]
  · rw [hcomm] at hx
    exact q_eq_zero_of_mem_ell hx

theorem s₁_mem_ell {z : V} (hz : z ∈ F.ell) : F.s₁ z ∈ F.ell := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [map_add, map_smul, map_smul, s₁_apply, s₁_apply, polar_self_eq_zero F.qa, F.ac,
    polar_comm q F.b F.a, F.ab, F.bc]
  simp only [zero_smul, add_zero, one_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ F.a_mem_ell)
    (Submodule.smul_mem _ _ (Submodule.add_mem _ F.b_mem_ell F.a_mem_ell))

theorem s₂_mem_ell {z : V} (hz : z ∈ F.ell) : F.s₂ z ∈ F.ell := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [map_add, map_smul, map_smul, s₂_apply, s₂_apply, F.ab, F.ac', polar_self_eq_zero F.qb,
    F.bc']
  simp only [zero_smul, add_zero, one_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ F.a_mem_ell F.b_mem_ell))
    (Submodule.smul_mem _ _ F.b_mem_ell)

theorem s₁_comm [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate) :
    F.s₁ * F.t = F.t * F.s₁ := by
  have h := F.conj_t_eq hq F.s₁_mem fun z hz => F.s₁_mem_ell hz
  calc F.s₁ * F.t = F.s₁ * F.t * F.s₁⁻¹ * F.s₁ := by group
    _ = F.t * F.s₁ := by rw [h]

theorem s₂_comm [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate) :
    F.s₂ * F.t = F.t * F.s₂ := by
  have h := F.conj_t_eq hq F.s₂_mem fun z hz => F.s₂_mem_ell hz
  calc F.s₂ * F.t = F.s₂ * F.t * F.s₂⁻¹ * F.s₂ := by group
    _ = F.t * F.s₂ := by rw [h]

theorem even_finrank_commSpace_s₁ [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) : Even (finrank (ZMod 2) (commSpace F.s₁)) :=
  even_finrank_commSpace_siegel hq F.qa F.qc F.ac

theorem even_finrank_commSpace_s₂ [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) : Even (finrank (ZMod 2) (commSpace F.s₂)) :=
  even_finrank_commSpace_siegel hq F.qb F.qc' F.bc'

end Frame

end AS35YR

end CFSG.LargeExtraspecial
