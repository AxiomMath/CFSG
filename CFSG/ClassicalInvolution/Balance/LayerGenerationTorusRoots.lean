module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorus

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Character

variable {k : Type*} [Field k] {r : ℕ}

@[expose] def simpleRootChar (a : Fin r → kˣ) (γ : Fin r → ℤ) : kˣ := ∏ i, a i ^ γ i

theorem simpleRootChar_single (a : Fin r → kˣ) (i : Fin r) :
    simpleRootChar a (Pi.single i 1) = a i := by
  unfold simpleRootChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

theorem simpleRootChar_neg (a : Fin r → kˣ) (γ : Fin r → ℤ) :
    simpleRootChar a (-γ) = (simpleRootChar a γ)⁻¹ := by
  unfold simpleRootChar
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem simpleRootChar_reflection (A : Matrix (Fin r) (Fin r) ℤ) (a : Fin r → kˣ) (j : Fin r)
    (β : Fin r → ℤ) :
    simpleRootChar a (CFSG.LieType.RootSystem.reflection A j β) =
      simpleRootChar a β * a j ^ (-(∑ m, A j m * β m)) := by
  have hcoord : ∀ l, CFSG.LieType.RootSystem.reflection A j β l =
      β l + (-(∑ m, A j m * β m)) * (Pi.single j (1 : ℤ) : Fin r → ℤ) l := by
    intro l
    rw [CFSG.LieType.RootSystem.reflection_apply]
    simp [sub_eq_add_neg]
  unfold simpleRootChar
  simp_rw [hcoord, zpow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

end Character

section Propagation

variable {K : Type*} [Group K] {X : Type*} [Group X] {k : Type*} [Field k]
  {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem actsOn_reflection (hX : ChevalleyExtras D k x C O) (ρ : K →* X) (e : X)
    (a : Fin D.rank → kˣ) (j : Fin D.rank)
    (hj : ActsByScalar (fun c => ρ (x (Pi.single j 1) c)) (fun c => ρ (x (-Pi.single j 1) c)) e
      (a j)) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (hP : ∀ c, e * ρ (x β c) * e⁻¹ = ρ (x β ((simpleRootChar a β : kˣ) * c))) (c : k) :
    e * ρ (x (CFSG.LieType.RootSystem.reflection D.cartan j β) c) * e⁻¹ =
      ρ (x (CFSG.LieType.RootSystem.reflection D.cartan j β)
        ((simpleRootChar a (CFSG.LieType.RootSystem.reflection D.cartan j β) : kˣ) * c)) := by
  obtain ⟨ε, hε, hrel⟩ := hX.weyl j β hβ
  have hε2 : (ε : k) * (ε : k) = 1 := by rcases hε with rfl | rfl <;> simp
  have hW : e * ρ (weylElement x j 1) * e⁻¹ = ρ (weylElement x j (a j)) := by
    unfold weylElement
    have h1 : e * ρ (x (Pi.single j 1) ((1 : kˣ) : k) *
        x (-Pi.single j 1) (-(((1 : kˣ)⁻¹ : kˣ) : k)) *
        x (Pi.single j 1) ((1 : kˣ) : k)) * e⁻¹ =
        (e * ρ (x (Pi.single j 1) ((1 : kˣ) : k)) * e⁻¹) *
          (e * ρ (x (-Pi.single j 1) (-(((1 : kˣ)⁻¹ : kˣ) : k))) * e⁻¹) *
          (e * ρ (x (Pi.single j 1) ((1 : kˣ) : k)) * e⁻¹) := by
      rw [map_mul, map_mul]
      group
    rw [h1, hj.1, hj.2, map_mul, map_mul]
    simp
  have hx : ∀ v : k, x (CFSG.LieType.RootSystem.reflection D.cartan j β) v =
      weylElement x j 1 * x β (ε * v) * (weylElement x j 1)⁻¹ := by
    intro v
    rw [hrel 1 (ε * v)]
    congr 1
    simp only [one_zpow, Units.val_one, mul_one]
    rw [← mul_assoc, hε2, one_mul]
  have hx2 : ∀ v : k,
      ρ (weylElement x j (a j)) * ρ (x β v) * (ρ (weylElement x j (a j)))⁻¹ =
      ρ (x (CFSG.LieType.RootSystem.reflection D.cartan j β)
        ((ε : k) * ((a j ^ (-(∑ l, D.cartan j l * β l)) : kˣ) : k) * v)) := by
    intro v
    rw [← map_inv, ← map_mul, ← map_mul, hrel]
  rw [hx c, map_mul, map_mul, map_inv]
  have e1 : e * (ρ (weylElement x j 1) * ρ (x β (ε * c)) * (ρ (weylElement x j 1))⁻¹) * e⁻¹ =
      (e * ρ (weylElement x j 1) * e⁻¹) * (e * ρ (x β (ε * c)) * e⁻¹) *
        (e * ρ (weylElement x j 1) * e⁻¹)⁻¹ := by group
  rw [e1, hW, hP, hx2, simpleRootChar_reflection]
  have hAB : (ε : k) * ((a j ^ (-(∑ l, D.cartan j l * β l)) : kˣ) : k) *
      ((simpleRootChar a β : kˣ) * ((ε : k) * c)) =
      (((simpleRootChar a β * a j ^ (-(∑ l, D.cartan j l * β l)) : kˣ)) : k) * c := by
    rw [Units.val_mul]
    linear_combination
      (((a j ^ (-(∑ l, D.cartan j l * β l)) : kˣ) : k) * (simpleRootChar a β : kˣ) * c) * hε2
  rw [hAB]

theorem exists_x_reflection (hX : ChevalleyExtras D k x C O) (j : Fin D.rank)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ ε : k, ε * ε = 1 ∧ ∀ v : k, x (CFSG.LieType.RootSystem.reflection D.cartan j β) v =
      weylElement x j 1 * x β (ε * v) * (weylElement x j 1)⁻¹ := by
  obtain ⟨ε, hε, hrel⟩ := hX.weyl j β hβ
  have hε2 : (ε : k) * (ε : k) = 1 := by rcases hε with rfl | rfl <;> simp
  refine ⟨ε, hε2, fun v => ?_⟩
  rw [hrel 1 (ε * v)]
  congr 1
  simp only [one_zpow, Units.val_one, mul_one]
  rw [← mul_assoc, hε2, one_mul]

theorem actsOn_wordAct (hX : ChevalleyExtras D k x C O) (ρ : K →* X) (e : X)
    (a : Fin D.rank → kˣ)
    (hsimple : ∀ i, ActsByScalar (fun c => ρ (x (Pi.single i 1) c))
      (fun c => ρ (x (-Pi.single i 1) c)) e (a i)) (w : List (Fin D.rank)) (i : Fin D.rank)
    (c : k) :
    e * ρ (x (wordAct (RootSystem.ofCartan D.isFiniteType D.divisible).refl w (Pi.single i 1)) c) *
        e⁻¹ =
      ρ (x (wordAct (RootSystem.ofCartan D.isFiniteType D.divisible).refl w (Pi.single i 1))
        ((simpleRootChar a (wordAct (RootSystem.ofCartan D.isFiniteType D.divisible).refl w
          (Pi.single i 1)) : kˣ) * c)) := by
  induction w generalizing c with
  | nil =>
    simp only [wordAct_nil]
    rw [simpleRootChar_single]
    exact (hsimple i).1 c
  | cons j w ih =>
    simp only [wordAct_cons]
    exact actsOn_reflection hX ρ e a j (hsimple j)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).wordAct_mem w
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)) ih c

theorem actsOn_root (hX : ChevalleyExtras D k x C O) (ρ : K →* X) (e : X)
    (a : Fin D.rank → kˣ)
    (hsimple : ∀ i, ActsByScalar (fun c => ρ (x (Pi.single i 1) c))
      (fun c => ρ (x (-Pi.single i 1) c)) e (a i)) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hind : ∀ δ ∈ D.roots, γ ≠ 2 • δ) (c : k) :
    e * ρ (x γ c) * e⁻¹ = ρ (x γ ((simpleRootChar a γ : kˣ) * c)) := by
  obtain ⟨w, i, rfl⟩ := (RootSystem.ofCartan D.isFiniteType D.divisible).exists_word γ hγ hind
  exact actsOn_wordAct hX ρ e a hsimple w i c

theorem eq_zero_of_wordAct (hX : ChevalleyExtras D k x C O) (ρ : K →* X)
    (hρ : ∀ i (c : k), ρ (x (Pi.single i 1) c) = 1 → c = 0)
    (w : List (Fin D.rank)) (i : Fin D.rank) (c : k)
    (h : ρ (x (wordAct (RootSystem.ofCartan D.isFiniteType D.divisible).refl w
      (Pi.single i 1)) c) = 1) : c = 0 := by
  induction w generalizing c with
  | nil => exact hρ i c h
  | cons j w ih =>
    simp only [wordAct_cons] at h
    obtain ⟨ε, hε2, hx⟩ := exists_x_reflection hX j
      ((RootSystem.ofCartan D.isFiniteType D.divisible).wordAct_mem w
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i))
    have hε0 : ε ≠ 0 := fun h0 => by rw [h0] at hε2; simp at hε2
    have h' : ρ (x (CFSG.LieType.RootSystem.reflection D.cartan j
        (wordAct (RootSystem.ofCartan D.isFiniteType D.divisible).refl w (Pi.single i 1))) c)
        = 1 := h
    rw [hx c, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h'
    exact (mul_eq_zero.mp (ih _ h')).resolve_left hε0

theorem neg_indivisible {γ : Fin D.rank → ℤ} (hind : ∀ δ ∈ D.roots, γ ≠ 2 • δ) :
    ∀ δ ∈ D.roots, -γ ≠ 2 • δ := by
  intro δ hδ h
  refine hind (-δ) ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hδ) ?_
  rw [smul_neg, ← h, neg_neg]

theorem indexTwoCentralizes_rankOneImage_of_diagonal (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) {Ē : Subgroup X} (hĒ2 : ∀ y ∈ Ē, y * y = 1)
    (hdiag : ∀ e ∈ Ē, ∃ a : Fin D.rank → kˣ, ∀ i, ActsDiagonallyOnSimple x ψ g i e (a i))
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hind : ∀ δ ∈ D.roots, γ ≠ 2 • δ) :
    IndexTwoCentralizes Ē (rankOneImage D ψ g γ) := by
  rw [rankOneImage_eq_pairGroup hX ψ g hγ]
  refine indexTwoCentralizes_pairGroup_of_scalar hĒ2 (map_conj_x_add hX ψ g hγ) ?_ ?_
  · obtain ⟨w, i, rfl⟩ := (RootSystem.ofCartan D.isFiniteType D.divisible).exists_word γ hγ hind
    intro c hc
    exact eq_zero_of_wordAct hX (ψ.comp (MulAut.conj g).toMonoidHom)
      (fun i c h => eq_zero_of_ker_le_center_simple hX hker g i c h) w i c hc
  · intro e he
    obtain ⟨a, ha⟩ := hdiag e he
    refine ⟨simpleRootChar a γ, ?_, ?_⟩
    · exact actsOn_root hX (ψ.comp (MulAut.conj g).toMonoidHom) e a ha hγ hind
    · intro c
      have := actsOn_root hX (ψ.comp (MulAut.conj g).toMonoidHom) e a ha
        ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ) (neg_indivisible hind) c
      rw [simpleRootChar_neg] at this
      exact this

end Propagation

end CFSG.ClassicalInvolution.Balance
