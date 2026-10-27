module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricTwoFlag

open Module Matrix

@[expose] def symMat (a : Fin 3 → ZMod 2) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![a 0, a 1; a 1, a 2]

theorem symMat_add (a b : Fin 3 → ZMod 2) : symMat (a + b) = symMat a + symMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symMat_smul (c : ZMod 2) (a : Fin 3 → ZMod 2) : symMat (c • a) = c • symMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

abbrev FlagU := (Fin 3 → ZMod 2) × (Fin 2 → ZMod 2)

abbrev FlagY := (Fin 2 → ZMod 2) × ZMod 2

abbrev FlagW := FlagU × FlagY

@[expose] def flagQuad (v : FlagW) : Fin 2 → ZMod 2 :=
  symMat v.1.1 *ᵥ v.2.1 + v.2.2 • v.1.2

@[expose] def flagUSub : Submodule (ZMod 2) FlagW :=
  LinearMap.ker (LinearMap.snd (ZMod 2) FlagU FlagY)

theorem mem_flagUSub {v : FlagW} : v ∈ flagUSub ↔ v.2 = 0 :=
  LinearMap.mem_ker

theorem finrank_flagU : finrank (ZMod 2) FlagU = 5 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]

theorem finrank_flagY : finrank (ZMod 2) FlagY = 3 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]

theorem finrank_flagUSub : finrank (ZMod 2) flagUSub = 5 := by
  rw [flagUSub, LinearMap.ker_snd, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    finrank_flagU]

theorem flagQuad_eq_zero_of_mem_flagUSub {v : FlagW} (hv : v ∈ flagUSub) : flagQuad v = 0 := by
  rw [mem_flagUSub] at hv
  simp [flagQuad, hv]

@[expose] def pairWith (v : FlagY) : FlagU →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun u := symMat u.1 *ᵥ v.1 + v.2 • u.2
  map_add' u u' := by
    simp only [Prod.fst_add, Prod.snd_add, symMat_add, Matrix.add_mulVec, smul_add]
    abel
  map_smul' c u := by
    simp only [Prod.smul_fst, Prod.smul_snd, symMat_smul, Matrix.smul_mulVec, RingHom.id_apply,
      smul_add, smul_comm c v.2]

theorem pairWith_apply_zero (v : FlagY) (u : FlagU) :
    pairWith v u 0 = u.1 0 * v.1 0 + u.1 1 * v.1 1 + v.2 * u.2 0 := by
  simp [pairWith, symMat, dotProduct, Fin.sum_univ_two, Matrix.vecHead]

theorem pairWith_apply_one (v : FlagY) (u : FlagU) :
    pairWith v u 1 = u.1 1 * v.1 0 + u.1 2 * v.1 1 + v.2 * u.2 1 := by
  simp [pairWith, symMat, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

theorem flagQuad_add_inl (v : FlagW) (u : FlagU) :
    flagQuad (v + (u, 0)) = flagQuad v + pairWith v.2 u := by
  simp only [flagQuad, pairWith, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
    symMat_add, Matrix.add_mulVec, add_zero, smul_add]
  abel

theorem flagY_ne_zero_iff {v : FlagY} : v ≠ 0 ↔ ¬(v.1 0 = 0 ∧ v.1 1 = 0 ∧ v.2 = 0) := by
  constructor
  · rintro hv ⟨h0, h1, h2⟩
    apply hv
    ext i
    · fin_cases i
      · exact h0
      · exact h1
    · exact h2
  · rintro h rfl
    exact h ⟨rfl, rfl, rfl⟩

theorem flagU_ext {u u' : FlagU} (h0 : u.1 0 = u'.1 0) (h1 : u.1 1 = u'.1 1) (h2 : u.1 2 = u'.1 2)
    (h3 : u.2 0 = u'.2 0) (h4 : u.2 1 = u'.2 1) : u = u' := by
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · ext i
    fin_cases i
    · exact h3
    · exact h4

theorem pairWith_eq_zero_iff (v : FlagY) (u : FlagU) :
    pairWith v u = 0 ↔ (u.1 0 * v.1 0 + u.1 1 * v.1 1 + v.2 * u.2 0 = 0 ∧
      u.1 1 * v.1 0 + u.1 2 * v.1 1 + v.2 * u.2 1 = 0) := by
  rw [← pairWith_apply_zero, ← pairWith_apply_one]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

theorem pairing_surjective_coords : ∀ y₀ y₁ t w₀ w₁ : ZMod 2, ¬(y₀ = 0 ∧ y₁ = 0 ∧ t = 0) →
    ∃ a b c k₀ k₁ : ZMod 2, a * y₀ + b * y₁ + t * k₀ = w₀ ∧ b * y₀ + c * y₁ + t * k₁ = w₁ := by
  decide

theorem pairing_separates_coords : ∀ y₀ y₁ s z₀ z₁ t : ZMod 2, ¬(y₀ = 0 ∧ y₁ = 0 ∧ s = 0) →
    ¬(z₀ = 0 ∧ z₁ = 0 ∧ t = 0) → ¬(y₀ = z₀ ∧ y₁ = z₁ ∧ s = t) →
    ∃ a b c k₀ k₁ : ZMod 2, (a * y₀ + b * y₁ + s * k₀ = 0 ∧ b * y₀ + c * y₁ + s * k₁ = 0) ∧
      ¬(a * z₀ + b * z₁ + t * k₀ = 0 ∧ b * z₀ + c * z₁ + t * k₁ = 0) := by
  decide

theorem pairing_nondegenerate_coords : ∀ a b c k₀ k₁ : ZMod 2,
    (∀ y₀ y₁ t : ZMod 2, a * y₀ + b * y₁ + t * k₀ = 0 ∧ b * y₀ + c * y₁ + t * k₁ = 0) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ k₀ = 0 ∧ k₁ = 0 := by
  decide

theorem pairWith_surjective {v : FlagY} (hv : v ≠ 0) : Function.Surjective (pairWith v) := by
  intro w
  obtain ⟨a, b, c, k₀, k₁, h0, h1⟩ :=
    pairing_surjective_coords (v.1 0) (v.1 1) v.2 (w 0) (w 1) (flagY_ne_zero_iff.mp hv)
  refine ⟨(![a, b, c], ![k₀, k₁]), ?_⟩
  ext i
  fin_cases i
  · rw [Fin.zero_eta, pairWith_apply_zero]
    simpa [mul_comm v.2] using h0
  · rw [Fin.mk_one, pairWith_apply_one]
    simpa [mul_comm v.2] using h1

theorem finrank_ker_pairWith {v : FlagY} (hv : v ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker (pairWith v)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (pairWith v)
  rw [LinearMap.range_eq_top.mpr (pairWith_surjective hv), finrank_top, Module.finrank_fin_fun,
    finrank_flagU] at h
  omega

theorem exists_pairWith_eq_zero_ne_zero {v₁ v₂ : FlagY} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₁₂ : v₁ ≠ v₂) : ∃ u, pairWith v₁ u = 0 ∧ pairWith v₂ u ≠ 0 := by
  have hne : ¬(v₁.1 0 = v₂.1 0 ∧ v₁.1 1 = v₂.1 1 ∧ v₁.2 = v₂.2) := by
    rintro ⟨e0, e1, e2⟩
    apply h₁₂
    ext i
    · fin_cases i
      · exact e0
      · exact e1
    · exact e2
  obtain ⟨a, b, c, k₀, k₁, ⟨h0, h1⟩, hn⟩ := pairing_separates_coords _ _ _ _ _ _
    (flagY_ne_zero_iff.mp h₁) (flagY_ne_zero_iff.mp h₂) hne
  refine ⟨(![a, b, c], ![k₀, k₁]), ?_, ?_⟩
  · rw [pairWith_eq_zero_iff]
    simpa [mul_comm v₁.2] using And.intro h0 h1
  · rw [Ne, pairWith_eq_zero_iff]
    simpa [mul_comm v₂.2] using hn

theorem eq_zero_of_forall_pairWith {u : FlagU} (h : ∀ v, pairWith v u = 0) : u = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pairing_nondegenerate_coords (u.1 0) (u.1 1) (u.1 2) (u.2 0)
    (u.2 1) fun y₀ y₁ t => by
      have hv := (pairWith_eq_zero_iff (![y₀, y₁], t) u).mp (h (![y₀, y₁], t))
      simpa [mul_comm t] using hv
  exact flagU_ext h0 h1 h2 h3 h4

theorem binary_symmetric_two_flag_quadratic_unique_maximal_singular_subspace :
    (∀ v ∈ flagUSub, flagQuad v = 0) ∧ finrank (ZMod 2) flagUSub = 5 ∧
      ∀ L : Submodule (ZMod 2) FlagW, (∀ v ∈ L, flagQuad v = 0) →
        finrank (ZMod 2) L ≤ 5 ∧ (finrank (ZMod 2) L = 5 → L = flagUSub) := by
  refine ⟨fun v hv => flagQuad_eq_zero_of_mem_flagUSub hv, finrank_flagUSub, fun L hL => ?_⟩
  set f := (LinearMap.snd (ZMod 2) FlagU FlagY).comp L.subtype with hf
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hker2 : ∀ x : LinearMap.ker f, ((x : L) : FlagW).2 = 0 := fun x =>
    LinearMap.mem_ker.mp x.2
  set g := (LinearMap.fst (ZMod 2) FlagU FlagY).comp (L.subtype.comp (LinearMap.ker f).subtype)
    with hg
  have hginj : Function.Injective g := fun x y hxy =>
    Subtype.ext (Subtype.ext (Prod.ext hxy ((hker2 x).trans (hker2 y).symm)))
  have hkerg : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) (LinearMap.range g) :=
    (LinearMap.finrank_range_of_inj hginj).symm
  have hpair : ∀ v ∈ LinearMap.range f, LinearMap.range g ≤ LinearMap.ker (pairWith v) := by
    rintro v ⟨l, rfl⟩ _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hxL : (((x : L) : FlagW).1, (0 : FlagY)) ∈ L := by
      have hx : ((x : L) : FlagW) = (((x : L) : FlagW).1, 0) := Prod.ext rfl (hker2 x)
      rw [← hx]
      exact (x : L).2
    have h1 := hL _ (L.add_mem l.2 hxL)
    rw [flagQuad_add_inl, hL _ l.2, zero_add] at h1
    exact h1
  by_cases h0 : LinearMap.range f = ⊥
  · have hle : L ≤ flagUSub := fun v hv => by
      have h := LinearMap.mem_range_self f ⟨v, hv⟩
      rw [h0, Submodule.mem_bot] at h
      exact mem_flagUSub.mpr h
    refine ⟨(Submodule.finrank_mono hle).trans_eq finrank_flagUSub, fun h5 => ?_⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (h5.trans finrank_flagUSub.symm)
  · obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hY : finrank (ZMod 2) (LinearMap.range f) ≤ 3 := by
      have h := Submodule.finrank_le (LinearMap.range f)
      rwa [finrank_flagY] at h
    have hk3 : finrank (ZMod 2) (LinearMap.ker f) ≤ 3 := by
      rw [hkerg]
      exact (Submodule.finrank_mono (hpair v₁ hv₁)).trans_eq (finrank_ker_pairWith hv₁0)
    have h4 : finrank (ZMod 2) L ≤ 4 := by
      rcases Nat.lt_or_ge (finrank (ZMod 2) (LinearMap.range f)) 2 with hr | hr
      · omega
      have hspan : Submodule.span (ZMod 2) {v₁} < LinearMap.range f := by
        refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₁) fun heq => ?_
        have h1 := finrank_span_singleton (K := ZMod 2) hv₁0
        rw [heq] at h1
        omega
      obtain ⟨v₂, hv₂, hv₂n⟩ := IsConcreteLE.exists_of_lt hspan
      have hv₂0 : v₂ ≠ 0 := fun h => hv₂n (h ▸ Submodule.zero_mem _)
      have hv₁₂ : v₁ ≠ v₂ := fun h => hv₂n (h ▸ Submodule.mem_span_singleton_self v₁)
      have hk2 : finrank (ZMod 2) (LinearMap.ker f) ≤ 2 := by
        obtain ⟨u, hu1, hu2⟩ := exists_pairWith_eq_zero_ne_zero hv₁0 hv₂0 hv₁₂
        have hlt : LinearMap.ker (pairWith v₁) ⊓ LinearMap.ker (pairWith v₂) <
            LinearMap.ker (pairWith v₁) := by
          refine lt_of_le_of_ne inf_le_left fun heq => hu2 ?_
          have hu : u ∈ LinearMap.ker (pairWith v₁) ⊓ LinearMap.ker (pairWith v₂) := by
            rw [heq]
            exact hu1
          exact (Submodule.mem_inf.mp hu).2
        have h3 := Submodule.finrank_lt_finrank_of_lt hlt
        rw [finrank_ker_pairWith hv₁0] at h3
        rw [hkerg]
        exact (Submodule.finrank_mono (le_inf (hpair v₁ hv₁) (hpair v₂ hv₂))).trans (by omega)
      rcases Nat.lt_or_ge (finrank (ZMod 2) (LinearMap.range f)) 3 with hr3 | hr3
      · omega
      have htop : LinearMap.range f = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [finrank_flagY]; omega)
      have hk0 : finrank (ZMod 2) (LinearMap.ker f) = 0 := by
        rw [hkerg, Submodule.finrank_eq_zero, eq_bot_iff]
        intro u hu
        rw [Submodule.mem_bot]
        exact eq_zero_of_forall_pairWith fun v => hpair v (htop ▸ Submodule.mem_top) hu
      omega
    exact ⟨by omega, fun h5 => by omega⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricTwoFlag
