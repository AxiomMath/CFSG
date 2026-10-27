module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Scalar

variable {k : Type*} [Field k] {X : Type*} [Group X]

private theorem coe_sl2Upper' (c : k) :
    ((sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, c; 0, 1] := rfl

private theorem coe_sl2Lower' (c : k) :
    ((sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; c, 1] := rfl

@[expose] def ActsByScalar (u l : k → X) (e : X) (a : kˣ) : Prop :=
  (∀ c : k, e * u c * e⁻¹ = u ((a : k) * c)) ∧ ∀ c : k, e * l c * e⁻¹ = l (((a⁻¹ : kˣ) : k) * c)

@[expose] def pairGroup (u l : k → X) : Subgroup X := Subgroup.closure (Set.range u ∪ Set.range l)

variable {u l : k → X} {e b : X} {a a' : kˣ}

theorem ActsByScalar.mul (he : ActsByScalar u l e a) (hb : ActsByScalar u l b a') :
    ActsByScalar u l (e * b) (a * a') := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · have h : e * b * u c * (e * b)⁻¹ = e * (b * u c * b⁻¹) * e⁻¹ := by group
    rw [h, hb.1, he.1, Units.val_mul, mul_assoc]
  · have h : e * b * l c * (e * b)⁻¹ = e * (b * l c * b⁻¹) * e⁻¹ := by group
    rw [h, hb.2, he.2, mul_inv_rev, Units.val_mul]
    congr 1
    ring

theorem ActsByScalar.mem_pairGroup (he : ActsByScalar u l e a) {r : X} (hr : r ∈ pairGroup u l) :
    e * r * e⁻¹ ∈ pairGroup u l := by
  have hle : pairGroup u l ≤ (pairGroup u l).comap (MulAut.conj e).toMonoidHom := by
    rw [pairGroup, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [he.1 c]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [he.2 c]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  exact hle hr

theorem ActsByScalar.centralizes_of_eq_one (he : ActsByScalar u l e 1) {r : X}
    (hr : r ∈ pairGroup u l) : e * r = r * e := by
  have hle : pairGroup u l ≤ Subgroup.centralizer ({e} : Set X) := by
    rw [pairGroup, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have := he.1 c
      simp only [Units.val_one, one_mul] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
    · have := he.2 c
      simp only [inv_one, Units.val_one, one_mul] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hr)).symm

theorem eq_one_or_neg_one_of_actsByScalar (hadd : ∀ c d : k, u (c + d) = u c * u d)
    (hinj : ∀ c : k, u c = 1 → c = 0) (he : ActsByScalar u l e a) (he2 : e * e = 1) :
    a = 1 ∨ a = -1 := by
  have h1 : e * (e * u 1 * e⁻¹) * e⁻¹ = u 1 := by
    have : e * (e * u 1 * e⁻¹) * e⁻¹ = (e * e) * u 1 * (e * e)⁻¹ := by group
    rw [this, he2]
    simp
  rw [he.1, mul_one, he.1] at h1
  have h2 : u ((a : k) * (a : k) - 1) = 1 := by
    have h3 : u ((a : k) * (a : k)) = u ((a : k) * (a : k) - 1) * u 1 := by
      rw [← hadd]
      congr 1
      ring
    rw [h1] at h3
    exact mul_eq_right.mp h3.symm
  have h4 : (a : k) * (a : k) = 1 := by linear_combination hinj _ h2
  rcases mul_self_eq_one_iff.mp h4 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

theorem indexTwoCentralizes_pairGroup_of_scalar {Ē : Subgroup X} (hĒ2 : ∀ x ∈ Ē, x * x = 1)
    (hadd : ∀ c d : k, u (c + d) = u c * u d) (hinj : ∀ c : k, u c = 1 → c = 0)
    (hdiag : ∀ e ∈ Ē, ∃ a : kˣ, ActsByScalar u l e a) : IndexTwoCentralizes Ē (pairGroup u l) := by
  have hnorm : Ē ≤ Subgroup.normalizer (pairGroup u l : Set X) := by
    intro e he
    obtain ⟨a, ha⟩ := hdiag e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => ha.mem_pairGroup hr, fun hr => ?_⟩
    obtain ⟨a', ha'⟩ := hdiag e⁻¹ (Ē.inv_mem he)
    have h := ha'.mem_pairGroup hr
    have e1 : e⁻¹ * (e * r * e⁻¹) * e⁻¹⁻¹ = r := by group
    rwa [e1] at h
  by_cases hall : ∀ e ∈ Ē, ∀ r ∈ pairGroup u l, e * r = r * e
  · exact ⟨hnorm, 1, Ē.one_mem, fun x hx => Or.inl (hall x hx)⟩
  · push Not at hall
    obtain ⟨b, hb, r₀, hr₀, hbr₀⟩ := hall
    obtain ⟨ab, hab⟩ := hdiag b hb
    have hab1 : ab = -1 := by
      rcases eq_one_or_neg_one_of_actsByScalar hadd hinj hab (hĒ2 b hb) with h | h
      · exact absurd (by subst h; exact hab.centralizes_of_eq_one hr₀) hbr₀
      · exact h
    refine ⟨hnorm, b, hb, fun x hx => ?_⟩
    obtain ⟨ax, hax⟩ := hdiag x hx
    rcases eq_one_or_neg_one_of_actsByScalar hadd hinj hax (hĒ2 x hx) with h | h
    · left
      subst h
      exact fun r hr => hax.centralizes_of_eq_one hr
    · right
      subst h
      subst hab1
      have hxb : ActsByScalar u l (x * b) ((-1) * (-1)) := hax.mul hab
      have h11 : ((-1 : kˣ) * (-1)) = 1 := by simp
      rw [h11] at hxb
      exact fun r hr => hxb.centralizes_of_eq_one hr

end Scalar

section Chevalley

variable {K : Type*} [Group K] {X : Type*} [Group X] {k : Type*} [Field k]
  {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

@[expose] def ActsDiagonallyOnSimple (x : (Fin D.rank → ℤ) → k → K) (ψ : K →* X) (g : K)
    (i : Fin D.rank) (e : X) (a : kˣ) : Prop :=
  ActsByScalar (fun c => ψ (g * x (Pi.single i 1) c * g⁻¹))
    (fun c => ψ (g * x (-Pi.single i 1) c * g⁻¹)) e a

theorem rankOneImage_eq_pairGroup (hX : ChevalleyExtras D k x C O) (ψ : K →* X) (g : K)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    rankOneImage D ψ g γ =
      pairGroup (fun c => ψ (g * x γ c * g⁻¹)) (fun c => ψ (g * x (-γ) c * g⁻¹)) := by
  have hγ' : -γ ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ
  have h1 : (D.rootGroup γ : Set K) = Set.range (x γ) := by
    ext y
    exact (hX.param γ hγ).1 y
  have h2 : (D.rootGroup (-γ) : Set K) = Set.range (x (-γ)) := by
    ext y
    exact (hX.param (-γ) hγ').1 y
  have h3 : D.rootGroup γ ⊔ D.rootGroup (-γ) =
      Subgroup.closure (Set.range (x γ) ∪ Set.range (x (-γ))) := by
    rw [Subgroup.closure_union, ← h1, ← h2, Subgroup.closure_eq, Subgroup.closure_eq]
  unfold rankOneImage rankOneRoot pairGroup
  rw [h3, Subgroup.map_map, MonoidHom.map_closure, Set.image_union, ← Set.range_comp,
    ← Set.range_comp]
  rfl

theorem eq_zero_of_ker_le_center_simple (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) (c : k)
    (h : ψ (g * x (Pi.single i 1) c * g⁻¹) = 1) : c = 0 := by
  obtain ⟨φ, hφinj, hφU, hφL⟩ := hX.rankOne i
  have hz : g * x (Pi.single i 1) c * g⁻¹ ∈ Subgroup.center K := hker h
  have hz' : x (Pi.single i 1) c ∈ Subgroup.center K := by
    have e : x (Pi.single i 1) c = g⁻¹ * (g * x (Pi.single i 1) c * g⁻¹) * g := by group
    rw [e]
    have := Subgroup.mem_center_iff.mp hz g⁻¹
    rw [this]
    simpa using hz
  rw [← hφU] at hz'
  have hcomm := Subgroup.mem_center_iff.mp hz' (φ (sl2Lower 1))
  rw [← map_mul, ← map_mul] at hcomm
  have := hφinj hcomm
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
    (A : Matrix (Fin 2) (Fin 2) k) 0 0) this
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper', coe_sl2Lower', Matrix.mul_apply,
    Fin.sum_univ_two] at h00
  exact h00

theorem map_conj_x_add (hX : ChevalleyExtras D k x C O) (ψ : K →* X) (g : K) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (c d : k) :
    ψ (g * x γ (c + d) * g⁻¹) = ψ (g * x γ c * g⁻¹) * ψ (g * x γ d * g⁻¹) := by
  rw [(hX.param γ hγ).2.1, ← map_mul]
  congr 1
  group

theorem indexTwoCentralizes_rankOneImage_simple (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {Ē : Subgroup X}
    (hĒ2 : ∀ y ∈ Ē, y * y = 1)
    (hdiag : ∀ e ∈ Ē, ∃ a : kˣ, ActsDiagonallyOnSimple x ψ g i e a) :
    IndexTwoCentralizes Ē (rankOneImage D ψ g (Pi.single i 1)) := by
  rw [rankOneImage_eq_pairGroup hX ψ g (single_mem_roots D i)]
  exact indexTwoCentralizes_pairGroup_of_scalar hĒ2
    (fun c d => map_conj_x_add hX ψ g (single_mem_roots D i) c d)
    (fun c h => eq_zero_of_ker_le_center_simple hX hker g i c h) hdiag

end Chevalley

end CFSG.ClassicalInvolution.Balance
