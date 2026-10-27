module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusRoots

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Torus

variable {K : Type*} [Group K] {k : Type*} [Field k] {D : UniversalRootDatum K}
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

@[expose] def hElt {r : ℕ} (x : (Fin r → ℤ) → k → K) (i : Fin r) (s : kˣ) : K :=
  weylElement x i s * (weylElement x i 1)⁻¹

@[expose] def torusOf {r : ℕ} (x : (Fin r → ℤ) → k → K) : Subgroup K :=
  Subgroup.closure {t | ∃ (i : Fin r) (s : kˣ), t = hElt x i s}

theorem hElt_conj_x (hX : ChevalleyExtras D k x C O) (i : Fin D.rank) (s : kˣ)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (u : k) :
    hElt x i s * x β u * (hElt x i s)⁻¹ =
      x β (((s ^ (∑ l, D.cartan i l * β l) : kˣ) : k) * u) := by
  have hβ' : CFSG.LieType.RootSystem.reflection D.cartan i β ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i β hβ
  have hrr : CFSG.LieType.RootSystem.reflection D.cartan i
      (CFSG.LieType.RootSystem.reflection D.cartan i β) = β :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).refl_refl i β
  have hcor : (∑ l, D.cartan i l * (CFSG.LieType.RootSystem.reflection D.cartan i β) l) =
      -(∑ l, D.cartan i l * β l) := by
    have := CFSG.LieType.RootSystem.coroot_reflection (D.isFiniteType.apply_self i) β
    simpa [CFSG.LieType.RootSystem.coroot_apply] using this
  obtain ⟨ε, hε, hrel⟩ := hX.weyl i _ hβ'
  have hε2 : (ε : k) * (ε : k) = 1 := by rcases hε with rfl | rfl <;> simp
  have h1 : weylElement x i 1 * x (CFSG.LieType.RootSystem.reflection D.cartan i β) ((ε : k) * u) *
      (weylElement x i 1)⁻¹ = x β u := by
    rw [hrel 1 ((ε : k) * u), hrr]
    congr 1
    simp only [one_zpow, Units.val_one, mul_one]
    rw [← mul_assoc, hε2, one_mul]
  have h2 : (weylElement x i 1)⁻¹ * x β u * weylElement x i 1 =
      x (CFSG.LieType.RootSystem.reflection D.cartan i β) ((ε : k) * u) := by
    rw [← h1]
    group
  have h3 : weylElement x i s * x (CFSG.LieType.RootSystem.reflection D.cartan i β)
      ((ε : k) * u) * (weylElement x i s)⁻¹ =
      x β (((s ^ (∑ l, D.cartan i l * β l) : kˣ) : k) * u) := by
    rw [hrel s ((ε : k) * u), hrr, hcor, neg_neg]
    congr 1
    linear_combination ((((s ^ (∑ l, D.cartan i l * β l) : kˣ)) : k) * u) * hε2
  unfold hElt
  calc weylElement x i s * (weylElement x i 1)⁻¹ * x β u *
        (weylElement x i s * (weylElement x i 1)⁻¹)⁻¹
      = weylElement x i s * ((weylElement x i 1)⁻¹ * x β u * weylElement x i 1) *
          (weylElement x i s)⁻¹ := by group
    _ = _ := by rw [h2, h3]

variable {X : Type*} [Group X]

theorem ActsByScalar.inv' {u l : k → X} {e : X} {a : kˣ} (he : ActsByScalar u l e a) :
    ActsByScalar u l e⁻¹ a⁻¹ := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · have h := he.1 ((a⁻¹ : kˣ) * c)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group
  · have h := he.2 ((a : k) * c)
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h
    rw [inv_inv, ← h]
    group

theorem actsByScalar_one (u l : k → X) : ActsByScalar u l 1 1 := by
  refine ⟨fun c => ?_, fun c => ?_⟩ <;> simp

theorem exists_actsDiagonallyOnSimple_of_mem_torusOf (hX : ChevalleyExtras D k x C O) {t : K}
    (ht : t ∈ torusOf x) (j : Fin D.rank) :
    ∃ a : kˣ, ActsDiagonallyOnSimple x (MonoidHom.id K) 1 j t a := by
  have hgen : ∀ i s, ∃ a : kˣ, ActsDiagonallyOnSimple x (MonoidHom.id K) 1 j (hElt x i s) a := by
    intro i s
    refine ⟨s ^ D.cartan i j, fun c => ?_, fun c => ?_⟩
    · simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one]
      rw [hElt_conj_x hX i s (single_mem_roots D j) c]
      simp [Pi.single_apply]
    · simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one]
      rw [hElt_conj_x hX i s ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        (single_mem_roots D j)) c]
      simp [Pi.single_apply, zpow_neg]
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨i, s, rfl⟩ := ht
    exact hgen i s
  | one => exact ⟨1, actsByScalar_one _ _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₁, ha₁⟩ := ha
    obtain ⟨b₁, hb₁⟩ := hb
    exact ⟨a₁ * b₁, ActsByScalar.mul ha₁ hb₁⟩
  | inv a _ ha =>
    obtain ⟨a₁, ha₁⟩ := ha
    exact ⟨a₁⁻¹, ha₁.inv'⟩

theorem indexTwoCentralizes_rankOneImage_of_le_torusOf (hX : ChevalleyExtras D k x C O)
    {Ē : Subgroup K} (hĒ : Ē ≤ torusOf x) (hĒ2 : ∀ y ∈ Ē, y * y = 1) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hind : ∀ δ ∈ D.roots, γ ≠ 2 • δ) :
    IndexTwoCentralizes Ē (rankOneImage D (MonoidHom.id K) 1 γ) := by
  refine indexTwoCentralizes_rankOneImage_of_diagonal hX (ψ := MonoidHom.id K) ?_ 1 hĒ2 ?_ hγ hind
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hy
    rw [hy]
    exact Subgroup.one_mem _
  · intro e he
    choose a ha using fun j => exists_actsDiagonallyOnSimple_of_mem_torusOf hX (hĒ he) j
    exact ⟨a, ha⟩

theorem exists_actsDiagonallyOnSimple_of_actsAsTorus (hX : ChevalleyExtras D k x C O)
    (ψ : K →* X) (g : K) (e : X) {t : K} (ht : t ∈ torusOf x)
    (hconj : ∀ y : K, e * ψ y * e⁻¹ = ψ (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) (j : Fin D.rank) :
    ∃ a : kˣ, ActsDiagonallyOnSimple x ψ g j e a := by
  obtain ⟨a, ha⟩ := exists_actsDiagonallyOnSimple_of_mem_torusOf hX ht j
  refine ⟨a, fun c => ?_, fun c => ?_⟩
  · rw [hconj]
    have h := ha.1 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]
  · rw [hconj]
    have h := ha.2 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (-Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (-Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]

end Torus

end CFSG.ClassicalInvolution.Balance
