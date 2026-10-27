module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem perfect_smul_eq_of_card_le_four {E S : Type*} [Group E] [Group.IsPerfect E]
    [MulAction E S] [Finite S] (hS : Nat.card S ≤ 4) (e : E) (s : S) : e • s = s := by
  have hsolv : Group.IsSolvable (Equiv.Perm S) := Equiv.Perm.isSolvable hS
  let f : E →* Equiv.Perm S := MulAction.toPermHom E S
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Group.IsSolvable f.range := inferInstance
  have : Subsingleton f.range := by
    by_contra h
    have : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have h1 : f e = 1 := by
    have : (⟨f e, e, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 : (f e) s = e • s := rfl
  rw [← h2, h1]
  rfl

theorem perfect_commute_of_weight_spaces
    {K V Z E : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group E] [Group.IsPerfect E] [MulAction E Z]
    (hdim : Module.finrank K V ≤ 4)
    (f : Z → Module.End K V) (hcomm : ∀ x y, Commute (f x) (f y))
    (hss : ∀ z, (f z).IsSemisimple)
    (g : E →* (Module.End K V)ˣ)
    (hg : ∀ (e : E) (z : Z), (g e : Module.End K V) * f z = f (e • z) * g e) :
    ∀ (e : E) (z : Z), (g e : Module.End K V) * f z = f z * g e := by
  classical
  let W : (Z → K) → Submodule K V := fun χ => ⨅ z, (f z).maxGenEigenspace (χ z)
  have hW : ∀ χ v, v ∈ W χ ↔ ∀ z, f z v = χ z • v := by
    intro χ v
    simp only [W, Submodule.mem_iInf]
    refine forall_congr' fun z => ?_
    rw [(hss z).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff]
  have hmaps : ∀ i j φ, Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hcomm i j) (fun z => Module.End.iSup_maxGenEigenspace_eq_top (f z))
  let _ : Fintype {χ // W χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  have hcard : Fintype.card {χ // W χ ≠ ⊥} ≤ 4 :=
    le_trans hind.subtype_ne_bot_le_finrank hdim
  let _ : MulAction E (Z → K) := arrowAction
  have key : ∀ (e : E) (χ : Z → K) (v : V), v ∈ W χ → (g e : Module.End K V) v ∈ W (e • χ) := by
    intro e χ v hv
    rw [hW] at hv ⊢
    intro z
    have h1 := hg e (e⁻¹ • z)
    rw [smul_inv_smul] at h1
    have h3 : (e • χ) z = χ (e⁻¹ • z) := rfl
    rw [h3]
    have h4 := congrArg (fun T : Module.End K V => T v) h1
    simp only [Module.End.mul_apply] at h4
    rw [← h4, hv (e⁻¹ • z), map_smul]
  let S : SubMulAction E (Z → K) :=
    { carrier := {χ | W χ ≠ ⊥}
      smul_mem' := by
        intro e χ hχ
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
        refine (Submodule.ne_bot_iff _).mpr ⟨(g e : Module.End K V) v, key e χ v hv, ?_⟩
        intro h0
        apply hv0
        have := congrArg (fun T : V => ((g e⁻¹ : (Module.End K V)ˣ) : Module.End K V) T) h0
        simpa [← Module.End.mul_apply, ← Units.val_mul, ← map_mul] using this }
  have hScard : Nat.card S ≤ 4 := by
    have h : Nat.card S = Nat.card {χ // W χ ≠ ⊥} := rfl
    rw [h, Nat.card_eq_fintype_card]
    exact hcard
  have : Finite S := (inferInstance : Finite {χ // W χ ≠ ⊥})
  intro e z
  have hle : ⨆ χ, W χ ≤ LinearMap.eqLocus ((g e : Module.End K V) * f z) (f z * g e) := by
    refine iSup_le fun χ v hv => ?_
    rw [LinearMap.mem_eqLocus]
    by_cases hχ : W χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hv
      subst hv
      simp
    · have hfix : e • χ = χ := by
        have := perfect_smul_eq_of_card_le_four (E := E) hScard e (⟨χ, hχ⟩ : S)
        exact congrArg Subtype.val this
      have h5 := (hW (e • χ) _).mp (key e χ v hv) z
      rw [hfix] at h5
      rw [Module.End.mul_apply, Module.End.mul_apply, h5, (hW χ v).mp hv z, map_smul]
  rw [htop] at hle
  exact LinearMap.eqLocus_eq_top.mp (top_le_iff.mp hle)

theorem perfect_centralizes_coprime_abelian
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
    (hι : Fintype.card ι ≤ 4)
    (Z E : Subgroup (GL ι F))
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hcop : Nat.Coprime (Nat.card Z) (ringChar F))
    (hE : Group.IsPerfect ↥E)
    (hEN : ∀ e ∈ E, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z) :
    ∀ e ∈ E, ∀ z ∈ Z, e * z = z * e := by
  classical
  let K := AlgebraicClosure F
  let φ : Matrix ι ι F →+* Module.End K (ι → K) :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toAlgHom.toRingHom.comp
      (algebraMap F K).mapMatrix
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 := Matrix.toLinAlgEquiv'.injective hab
    exact Matrix.map_injective (algebraMap F K).injective h1
  let f : ↥Z → Module.End K (ι → K) := fun z => φ ((z : GL ι F) : Matrix ι ι F)
  let g : ↥E →* (Module.End K (ι → K))ˣ :=
    (Units.map (φ : Matrix ι ι F →* Module.End K (ι → K))).comp E.subtype
  have hgval : ∀ e : ↥E, ((g e : (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) =
      φ ((e : GL ι F) : Matrix ι ι F) := fun e => rfl
  let act : MulAction ↥E ↥Z :=
    { smul := fun e z => ⟨(e : GL ι F) * (z : GL ι F) * (e : GL ι F)⁻¹, hEN e e.2 z z.2⟩
      one_smul := fun z => Subtype.ext (by
        show ((1 : ↥E) : GL ι F) * (z : GL ι F) * ((1 : ↥E) : GL ι F)⁻¹ = z
        simp)
      mul_smul := fun a b z => Subtype.ext (by
        show ((a * b : ↥E) : GL ι F) * (z : GL ι F) * ((a * b : ↥E) : GL ι F)⁻¹ =
          (a : GL ι F) * ((b : GL ι F) * (z : GL ι F) * (b : GL ι F)⁻¹) * (a : GL ι F)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hact : ∀ (e : ↥E) (z : ↥Z),
      ((e • z : ↥Z) : GL ι F) = (e : GL ι F) * (z : GL ι F) * (e : GL ι F)⁻¹ :=
    fun e z => rfl
  have hcomm : ∀ x y, Commute (f x) (f y) := by
    intro x y
    have h := congrArg Units.val (hZ x x.2 y y.2)
    simp only [Units.val_mul] at h
    show φ _ * φ _ = φ _ * φ _
    rw [← map_mul, ← map_mul, h]
  have hm : ((Nat.card Z : ℕ) : K) ≠ 0 := by
    intro h0
    have h1 : ((Nat.card Z : ℕ) : F) = 0 := by
      apply (algebraMap F K).injective
      rw [map_natCast, map_zero]
      exact h0
    have h2 : ringChar F ∣ Nat.card Z := (ringChar.spec F _).mp h1
    have h3 := Nat.Coprime.eq_one_of_dvd hcop.symm h2
    exact CharP.ringChar_ne_one h3
  have hsq : Squarefree (Polynomial.X ^ (Nat.card Z) - 1 : Polynomial K) := by
    have := (Polynomial.separable_X_pow_sub_C (1 : K) hm one_ne_zero).squarefree
    simpa using this
  have hss : ∀ z, (f z).IsSemisimple := by
    intro z
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    have h1 : z ^ (Nat.card Z) = 1 := pow_card_eq_one'
    have h2 : (f z) ^ (Nat.card Z) = 1 := by
      show φ _ ^ _ = 1
      rw [← map_pow]
      have h3 : ((z : GL ι F) : Matrix ι ι F) ^ (Nat.card Z) = 1 := by
        rw [← Units.val_pow_eq_pow_val]
        have := congrArg (fun w : ↥Z => ((w : GL ι F))) h1
        simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [this]
        rfl
      rw [h3, map_one]
    simp [h2]
  have hg : ∀ (e : ↥E) (z : ↥Z),
      ((g e : (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) * f z = f (e • z) * g e := by
    intro e z
    rw [hgval]
    show φ _ * φ _ = φ _ * φ _
    rw [← map_mul, ← map_mul, hact, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have hfin : Module.finrank K (ι → K) ≤ 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hι
  have key := perfect_commute_of_weight_spaces (K := K) (V := ι → K) (Z := ↥Z) (E := ↥E)
    hfin f hcomm hss g hg
  intro e he z hz
  have h := key ⟨e, he⟩ ⟨z, hz⟩
  rw [hgval] at h
  change φ _ * φ _ = φ _ * φ _ at h
  rw [← map_mul, ← map_mul] at h
  have h2 := hφinj h
  apply Units.ext
  simpa using h2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
