module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GL
public import CFSG.LieType.SeitzGeneration.OutdiagScope
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups
open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration

section Glue

open Matrix

variable {F : Type} [Field F] [Finite F]

theorem preimage_plane_facts (B : Subgroup (MulAut (projectiveSL 3 F))) (hBa : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 3 ^ 2) (hlin : B ≤ linearAutGroup 3 F) :
    sc F ≤ B.comap (conjAut 3 F) ∧ (∀ x ∈ B.comap (conjAut 3 F), x ^ 3 ∈ sc F) ∧
      (∀ x ∈ B.comap (conjAut 3 F), ∀ y ∈ B.comap (conjAut 3 F), x * y * x⁻¹ * y⁻¹ ∈ sc F) ∧
      ((sc F).subgroupOf (B.comap (conjAut 3 F))).index = 9 := by
  have hsc : ∀ g : GL (Fin 3) F, conjAut 3 F g = 1 ↔ g ∈ sc F := fun g => by
    rw [ProjectivePlane.conjAut_eq_one_iff (le_refl 3), mem_sc_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_comap, (hsc g).2 hg]
    exact B.one_mem
  · intro x hx
    rw [← hsc, map_pow]
    exact hBa.2 _ hx
  · intro x hx y hy
    rw [← hsc]
    simp only [map_mul, map_inv]
    have := hBa.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [h2]
    group
  · set A := B.comap (conjAut 3 F) with hA
    let f : A →* MulAut (projectiveSL 3 F) := (conjAut 3 F).comp A.subtype
    have hker : f.ker = (sc F).subgroupOf A := by
      ext x
      simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf]
      exact hsc x
    have hrange : f.range = B := by
      ext b
      simp only [MonoidHom.mem_range, f, MonoidHom.comp_apply, Subgroup.coe_subtype]
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hb
        obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.1 (hlin hb)
        exact ⟨⟨x, by rw [hA, Subgroup.mem_comap, hx]; exact hb⟩, hx⟩
    have := Subgroup.index_ker f
    rw [hker, hrange, hB9] at this
    rw [this]
    norm_num

omit [Finite F] in
theorem conjAut_toGL (k : SpecialLinearGroup (Fin 3) F) :
    conjAut 3 F (SpecialLinearGroup.toGL k) = MulAut.conj (proj 3 F k) := by
  ext g'
  obtain ⟨g, rfl⟩ := proj_surjective 3 F g'
  have h : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F
      (SpecialLinearGroup.toGL k) g = k * g * k⁻¹ := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← map_inv SpecialLinearGroup.toGL k]
    rfl
  rw [conjAut_proj, h, map_mul, map_mul, map_inv, MulAut.conj_apply]

omit [Finite F] in
theorem exists_det_noncube_of_not_inner {b : MulAut (projectiveSL 3 F)}
    (hb : b ∈ linearAutGroup 3 F)
    (hnot : b ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F)) :
    ∃ x : GL (Fin 3) F, conjAut 3 F x = b ∧
      ∀ c : Fˣ, (x : Matrix (Fin 3) (Fin 3) F).det ≠ (c : F) ^ 3 := by
  obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.1 hb
  refine ⟨x, hx, fun c hc => hnot ?_⟩
  have hdet : ((x * Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hc, Matrix.GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar_apply, Matrix.det_diagonal]
  set x' : GL (Fin 3) F := x * Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ with hx'
  have hb' : conjAut 3 F x' = b := by
    rw [hx', map_mul, conjAut_scalar, mul_one, hx]
  let k : SpecialLinearGroup (Fin 3) F := ⟨(x' : Matrix (Fin 3) (Fin 3) F), hdet⟩
  have hk : SpecialLinearGroup.toGL k = x' := Units.ext rfl
  refine ⟨proj 3 F k, ?_⟩
  rw [← conjAut_toGL, hk, hb']

theorem planeGen_of_conj {M : Type*} [Group M] (c : MulAut M) {B : Subgroup (MulAut M)}
    (h : PlaneGen (B.map (MulAut.conj c).toMonoidHom)) : PlaneGen B := by
  unfold PlaneGen planeClosure at h ⊢
  set S : Set M := {k | ∃ e ∈ B, e ≠ 1 ∧ e k = k} with hS
  have hS' : {k | ∃ e ∈ B.map (MulAut.conj c).toMonoidHom, e ≠ 1 ∧ e k = k} =
      c.toMonoidHom '' S := by
    ext k
    constructor
    · rintro ⟨e', ⟨e, he, rfl⟩, he1, hek⟩
      refine ⟨c.symm k, ⟨e, he, ?_, ?_⟩, by simp⟩
      · rintro rfl
        apply he1
        simp
      · have h1 : c (e (c.symm k)) = k := hek
        have h2 := congrArg c.symm h1
        simpa using h2
    · rintro ⟨k₀, ⟨e, he, he1, hek⟩, rfl⟩
      refine ⟨MulAut.conj c e, ⟨e, he, rfl⟩, ?_, ?_⟩
      · intro h1
        apply he1
        have h2 : c⁻¹ * (c * e * c⁻¹) * c = 1 := by
          have h3 : c * e * c⁻¹ = 1 := h1
          rw [h3]; group
        calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
          _ = 1 := h2
      · simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
        show c (e (c.symm (c k₀))) = c k₀
        rw [MulEquiv.symm_apply_apply, hek]
  rw [hS', ← MonoidHom.map_closure] at h
  rw [eq_top_iff]
  intro x _
  have hx : c x ∈ (Subgroup.closure S).map c.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := c.injective hyx
  rwa [this] at hy

@[expose] def OuterHeisCoreAt (F : Type) [Field F] : Prop :=
  ∀ ω α : F, ω ^ 2 + ω + 1 = 0 → ω ≠ 1 → α ≠ 0 → (¬ ∃ μ : F, μ ^ 3 = α) →
    Subgroup.closure (outerHeisSet ω α) = ⊤

omit [Finite F] in
theorem nonScalarGL_of_entry {g : GL (Fin 3) F} {i j : Fin 3} (hij : i ≠ j)
    (h : (g : Matrix (Fin 3) (Fin 3) F) i j ≠ 0) : NonScalarGL g := by
  intro c hc
  apply h
  rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem planeGen_of_linearAut_core (hcore : OuterHeisCoreAt F) (h3F : 3 ∣ Nat.card F - 1)
    {B : Subgroup (MulAut (projectiveSL 3 F))} (hBa : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 3 ^ 2) (hlin : B ≤ linearAutGroup 3 F)
    (hout : ¬ B ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F)) :
    PlaneGen B := by
  obtain ⟨hS, hcube, hcomm, hidx⟩ := preimage_plane_facts B hBa hB9 hlin
  set A := B.comap (conjAut 3 F) with hA
  obtain ⟨b, hbB, hbn⟩ := Set.not_subset.mp hout
  obtain ⟨x₁, hx₁, hdet⟩ := exists_det_noncube_of_not_inner (hlin hbB) hbn
  have hx₁A : x₁ ∈ A := by rw [hA, Subgroup.mem_comap, hx₁]; exact hbB
  have hout' : ∃ x ∈ A, ∀ c : Fˣ, (x : Matrix (Fin 3) (Fin 3) F).det ≠ (c : F) ^ 3 :=
    ⟨x₁, hx₁A, hdet⟩
  by_cases habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  · have hp : Nat.Prime 3 := Nat.prime_three
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    have hζ := exists_primitiveRoot_of_dvd_card_sub_one hp h3F
    obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp B hBa.2 hB9
    obtain ⟨x, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₁)
    obtain ⟨y, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₂)
    have hxA : x ∈ A := by rw [hA, Subgroup.mem_comap]; exact he₁
    have hyA : y ∈ A := by rw [hA, Subgroup.mem_comap]; exact he₂
    have hxy : x * y = y * x := habel x hxA y hyA
    have hsc := fun c : Fˣ => (ProjectivePlane.conjAut_eq_one_iff (n := 3) (F := F) (le_refl 3)
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c)).2 ⟨c, rfl⟩
    obtain ⟨α, hα⟩ : ∃ α : Fˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α :=
      (ProjectivePlane.conjAut_eq_one_iff (le_refl 3) _).1 (by rw [map_pow]; exact hBa.2 _ he₁)
    obtain ⟨β, hβ⟩ : ∃ β : Fˣ, y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) β :=
      (ProjectivePlane.conjAut_eq_one_iff (le_refl 3) _).1 (by rw [map_pow]; exact hBa.2 _ he₂)
    have hind : ∀ a b : ℕ,
        (∃ c : Fˣ, x ^ a * y ^ b = Matrix.GeneralLinearGroup.scalar (Fin 3) c) → 3 ∣ a ∧ 3 ∣ b := by
      rintro a b ⟨c, hcab⟩
      have h1 : conjAut 3 F x ^ a * conjAut 3 F y ^ b = 1 := by
        rw [← map_pow, ← map_pow, ← map_mul, hcab, hsc c]
      have h3x : conjAut 3 F x ^ 3 = 1 := hBa.2 _ he₁
      have ha : 3 ∣ a := by
        by_contra ha
        apply he₁₂
        have h2 : conjAut 3 F x ^ a ∈ Subgroup.zpowers (conjAut 3 F y) := by
          have : conjAut 3 F x ^ a = (conjAut 3 F y ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) b)
        rcases (by omega : a % 3 = 1 ∨ a % 3 = 2) with h | h
        · rwa [pow_eq_pow_mod a h3x, h, pow_one] at h2
        · have h5 : conjAut 3 F x = (conjAut 3 F x ^ a) ^ 2 := by
            rw [← pow_mul, pow_eq_pow_mod (a * 2) h3x, show a * 2 % 3 = 1 by omega, pow_one]
          rw [h5]
          exact Subgroup.pow_mem _ h2 2
      refine ⟨ha, ?_⟩
      obtain ⟨k, rfl⟩ := ha
      have h6 : conjAut 3 F y ^ b = 1 := by
        rw [pow_mul, h3x, one_pow, one_mul] at h1; exact h1
      rw [← orderOf_eq_prime (hBa.2 _ he₂) he₂1]
      exact orderOf_dvd_of_pow_eq_one h6
    have hx3M : ((x ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (α : F) • 1 := by
      rw [hα, coe_scalarGL]
    have hy3M : ((y ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (β : F) • 1 := by
      rw [hβ, coe_scalarGL]
    have hind' : ∀ a b : ℕ,
        (∃ c : F, ((x ^ a * y ^ b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1) →
          3 ∣ a ∧ 3 ∣ b := fun a b ⟨c, hc⟩ => hind a b (exists_scalarGL_of_coe_eq (by norm_num) hc)
    refine planeGen_of_planeFix he₁ he₂ ?_ ?_ ?_ ?_
      (closure_planeFix_abelian h3F hζ hxy α.ne_zero β.ne_zero hx3M hy3M hind')
    · intro c hc; have := hind 1 0 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 0 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 2 ⟨c, by simpa using hc⟩; omega
  · push Not at habel
    obtain ⟨x₀, hx₀, z₀, hz₀, hne⟩ := habel
    obtain ⟨g, lam, ω, hω, hlam, hgA⟩ :=
      nonabelian_heisenberg h3F A hS hcube hcomm hidx hout' hx₀ hz₀ hne
    set c : MulAut (projectiveSL 3 F) := conjAut 3 F g with hc
    refine planeGen_of_conj c ?_
    have hmem : ∀ z ∈ heisenbergThree F lam ω, conjAut 3 F z ∈ B.map (MulAut.conj c).toMonoidHom := by
      intro z hz
      rw [← hgA] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      refine ⟨conjAut 3 F a, ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_inv, hc]
    have hxmem : monomGL F lam ∈ heisenbergThree F lam ω :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hymem : diagGL F 1 ω (ω ^ 2) ∈ heisenbergThree F lam ω :=
      Subgroup.subset_closure (Or.inr (Or.inr rfl))
    have hω' : (ω : F) ^ 2 + ω + 1 = 0 := by
      have := hω.geom_sum_eq_zero (by norm_num)
      simp [Finset.sum_range_succ] at this
      linear_combination this
    have hω1 : (ω : F) ≠ 1 := hω.ne_one (by norm_num)
    have hlam' : ¬ ∃ μ : F, μ ^ 3 = (lam : F) := by
      rintro ⟨μ, hμ⟩
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        simp at hμ
        exact lam.ne_zero hμ.symm
      exact hlam (Units.mk0 μ hμ0) (Units.ext (by simp [hμ]))
    have hgen : Subgroup.closure (planeFix (monomGL F lam) (diagGL F 1 ω (ω ^ 2))) = ⊤ := by
      have hcl := hcore (ω : F) lam hω' hω1 lam.ne_zero hlam'
      have h1 : ((monomGL F lam : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = heisC (lam : F) := rfl
      have h2 : ((diagGL F 1 ω (ω ^ 2) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          heisD (ω : F) := by simp [diagGL, heisD]
      have hset : planeFix (monomGL F lam) (diagGL F 1 ω (ω ^ 2)) = outerHeisSet (ω : F) lam := by
        unfold planeFix outerHeisSet
        rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, h1, h2]
      rw [hset]
      exact hcl
    refine planeGen_of_planeFix (hmem _ hxmem) (hmem _ hymem) ?_ ?_ ?_ ?_ hgen
    · exact nonScalarGL_of_entry (i := 1) (j := 0) (by decide) (by simp [monomGL])
    · intro c hc
      have h00 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) hc
      have h11 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 1) hc
      simp [diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
      exact hω1 (h11.trans h00.symm)
    · exact nonScalarGL_of_entry (i := 1) (j := 0) (by decide)
        (by simp [monomGL, diagGL, Matrix.mul_apply, Fin.sum_univ_three])
    · exact nonScalarGL_of_entry (i := 1) (j := 0) (by decide)
        (by simp [monomGL, diagGL, pow_two, Matrix.mul_apply, Fin.sum_univ_three])

end Glue

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
