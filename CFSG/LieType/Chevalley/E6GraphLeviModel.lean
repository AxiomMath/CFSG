module

public import CFSG.LieType.Chevalley.E6GraphHighestRootData
public import CFSG.LieType.Chevalley.C2E6ExteriorCube

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.ExteriorCube Matrix

abbrev pathIdx (t : Fin 5) : Fin TwistTag.E6.tag.rank := a5Path t

@[expose] def matRoot (a b : Fin 6) : Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ t : Fin 5, ((if a.val ≤ t.val ∧ t.val < b.val then 1 else 0) -
    (if b.val ≤ t.val ∧ t.val < a.val then 1 else 0) : ℤ) • Pi.single (pathIdx t) 1

@[expose] def cubeRoot (S : Finset (Fin 6)) : Fin TwistTag.E6.tag.rank → ℤ :=
  Pi.single (e6Idx 1) 1 + ∑ t : Fin 5,
    (((S.filter fun s => s.val ≤ t.val).card : ℤ) - ((t.val - 2 : ℕ) : ℤ)) •
      Pi.single (pathIdx t) 1

theorem matRoot_mem : ∀ a b : Fin 6, a ≠ b → matRoot a b ∈ a5Roots := by decide +kernel

theorem mem_a5Roots_iff_matRoot : ∀ β ∈ a5Roots, ∃ a b : Fin 6, a ≠ b ∧ matRoot a b = β := by
  decide +kernel

theorem matRoot_injective : ∀ a b a' b' : Fin 6, a ≠ b → a' ≠ b' → matRoot a b = matRoot a' b' →
    a = a' ∧ b = b' := by
  decide +kernel

theorem cubeRoot_mem : ∀ S : Finset (Fin 6), S.card = 3 → cubeRoot S ∈ degOneRoots := by
  decide +kernel

theorem cubeRoot_surj : ∀ β ∈ degOneRoots, ∃ S : Finset (Fin 6), S.card = 3 ∧ cubeRoot S = β := by
  decide +kernel

theorem cubeRoot_injective : ∀ S S' : Finset (Fin 6), S.card = 3 → S'.card = 3 →
    cubeRoot S = cubeRoot S' → S = S' := by
  decide +kernel

theorem matRoot_add : ∀ (a b : Fin 6) (t : Fin 5), a ≠ b → ¬(a = t.castSucc ∧ b = t.succ) →
    ¬(a = t.succ ∧ b = t.castSucc) → ∀ x y : Fin 6,
      (x ≠ y ∧ matRoot x y = matRoot a b + Pi.single (pathIdx t) 1) ↔
        ((a = t.succ ∧ x = t.castSucc ∧ y = b) ∨ (b = t.castSucc ∧ x = a ∧ y = t.succ)) := by
  decide +kernel

theorem matRoot_sub : ∀ (a b : Fin 6) (t : Fin 5), a ≠ b → ¬(a = t.castSucc ∧ b = t.succ) →
    ¬(a = t.succ ∧ b = t.castSucc) → ∀ x y : Fin 6,
      (x ≠ y ∧ matRoot x y = matRoot a b - Pi.single (pathIdx t) 1) ↔
        ((a = t.castSucc ∧ x = t.succ ∧ y = b) ∨ (b = t.succ ∧ x = a ∧ y = t.castSucc)) := by
  decide +kernel

theorem cubeRoot_add : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → ∀ S' : Finset (Fin 6),
    S'.card = 3 → (cubeRoot S' = cubeRoot S + Pi.single (pathIdx t) 1 ↔
      (t.succ ∈ S ∧ t.castSucc ∉ S ∧ S' = insert t.castSucc (S.erase t.succ))) := by
  decide +kernel


theorem matRoot_one : ∀ a b : Fin 6, matRoot a b (e6Idx 1) = 0 := by decide

theorem cubeRoot_one : ∀ S : Finset (Fin 6), cubeRoot S (e6Idx 1) = 1 := by decide

theorem e6HighestRoot_one : e6HighestRoot (e6Idx 1) = 2 := by decide

theorem isRoot_matRoot
    {a b : Fin 6} (h : a ≠ b) : IsRoot TwistTag.E6.tag (matRoot a b) := by
  have h1 := matRoot_mem a b h
  rw [← filter_coord_zero, Finset.mem_filter] at h1
  exact mem_rootFinset.1 h1.1

theorem isRoot_cubeRoot {S : Finset (Fin 6)} (h : S.card = 3) :
    IsRoot TwistTag.E6.tag (cubeRoot S) := by
  have h1 := cubeRoot_mem S h
  rw [degOneRoots, Finset.mem_filter] at h1
  exact mem_rootFinset.1 h1.1

theorem card_compl_three {S : Finset (Fin 6)} (h : S.card = 3) : Sᶜ.card = 3 := by
  rw [Finset.card_compl, h]
  rfl

theorem root_cases : ∀ β ∈ rootFinset TwistTag.E6.tag, (∃ a b : Fin 6, a ≠ b ∧ matRoot a b = β) ∨
    β = e6HighestRoot ∨ β = -e6HighestRoot ∨ (∃ S : Finset (Fin 6), S.card = 3 ∧ cubeRoot S = β) ∨
    ∃ S : Finset (Fin 6), S.card = 3 ∧ -cubeRoot Sᶜ = β := by
  decide +kernel


theorem matRoot_adjacent : ∀ t : Fin 5,
    matRoot t.castSucc t.succ = Pi.single (pathIdx t) 1 := by decide

theorem matRoot_adjacent_neg : ∀ t : Fin 5,
    matRoot t.succ t.castSucc = -Pi.single (pathIdx t) 1 := by decide

theorem not_isRoot_e6HighestRoot_add : ∀ t : Fin 5,
    e6HighestRoot + Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag ∧
    e6HighestRoot - Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag ∧
    -e6HighestRoot + Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag ∧
    -e6HighestRoot - Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem negCube_add : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → ∀ S' : Finset (Fin 6),
    S'.card = 3 → (-cubeRoot S'ᶜ = -cubeRoot Sᶜ + Pi.single (pathIdx t) 1 ↔
      (t.succ ∈ S ∧ t.castSucc ∉ S ∧ S' = insert t.castSucc (S.erase t.succ))) := by
  decide +kernel

theorem cubeRoot_sub : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → ∀ S' : Finset (Fin 6),
    S'.card = 3 → (cubeRoot S' = cubeRoot S - Pi.single (pathIdx t) 1 ↔
      (t.castSucc ∈ S ∧ t.succ ∉ S ∧ S' = insert t.succ (S.erase t.castSucc))) := by
  decide +kernel

theorem negCube_sub : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → ∀ S' : Finset (Fin 6),
    S'.card = 3 → (-cubeRoot S'ᶜ = -cubeRoot Sᶜ - Pi.single (pathIdx t) 1 ↔
      (t.castSucc ∈ S ∧ t.succ ∉ S ∧ S' = insert t.succ (S.erase t.castSucc))) := by
  decide +kernel


theorem matRoot_add_left : ∀ (t : Fin 5) (b : Fin 6), b ≠ t.castSucc → b ≠ t.succ →
    matRoot t.succ b + Pi.single (pathIdx t) 1 = matRoot t.castSucc b := by decide

theorem matRoot_add_right : ∀ (t : Fin 5) (a : Fin 6), a ≠ t.castSucc → a ≠ t.succ →
    matRoot a t.castSucc + Pi.single (pathIdx t) 1 = matRoot a t.succ := by decide

theorem matRoot_add_not : ∀ (t : Fin 5) (a b : Fin 6), a ≠ b → a ≠ t.succ → b ≠ t.castSucc →
    ¬(a = t.castSucc ∧ b = t.succ) →
      matRoot a b + Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem matRoot_sub_left : ∀ (t : Fin 5) (b : Fin 6), b ≠ t.castSucc → b ≠ t.succ →
    matRoot t.castSucc b - Pi.single (pathIdx t) 1 = matRoot t.succ b := by decide

theorem matRoot_sub_right : ∀ (t : Fin 5) (a : Fin 6), a ≠ t.castSucc → a ≠ t.succ →
    matRoot a t.succ - Pi.single (pathIdx t) 1 = matRoot a t.castSucc := by decide

theorem matRoot_sub_not : ∀ (t : Fin 5) (a b : Fin 6), a ≠ b → a ≠ t.castSucc → b ≠ t.succ →
    ¬(a = t.succ ∧ b = t.castSucc) →
      matRoot a b - Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem cubeRoot_add_eq : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → t.succ ∈ S →
    t.castSucc ∉ S →
      cubeRoot S + Pi.single (pathIdx t) 1 = cubeRoot (insert t.castSucc (S.erase t.succ)) := by
  decide +kernel

theorem cubeRoot_add_not : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 →
    ¬(t.succ ∈ S ∧ t.castSucc ∉ S) →
      cubeRoot S + Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem negCube_add_eq : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → t.succ ∈ S →
    t.castSucc ∉ S → -cubeRoot Sᶜ + Pi.single (pathIdx t) 1 =
      -cubeRoot (insert t.castSucc (S.erase t.succ))ᶜ := by
  decide +kernel

theorem negCube_add_not : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 →
    ¬(t.succ ∈ S ∧ t.castSucc ∉ S) →
      -cubeRoot Sᶜ + Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem cubeRoot_sub_eq : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → t.castSucc ∈ S →
    t.succ ∉ S →
      cubeRoot S - Pi.single (pathIdx t) 1 = cubeRoot (insert t.succ (S.erase t.castSucc)) := by
  decide +kernel

theorem cubeRoot_sub_not : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 →
    ¬(t.castSucc ∈ S ∧ t.succ ∉ S) →
      cubeRoot S - Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel

theorem negCube_sub_eq : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 → t.castSucc ∈ S →
    t.succ ∉ S → -cubeRoot Sᶜ - Pi.single (pathIdx t) 1 =
      -cubeRoot (insert t.succ (S.erase t.castSucc))ᶜ := by
  decide +kernel

theorem negCube_sub_not : ∀ (S : Finset (Fin 6)) (t : Fin 5), S.card = 3 →
    ¬(t.castSucc ∈ S ∧ t.succ ∉ S) →
      -cubeRoot Sᶜ - Pi.single (pathIdx t) 1 ∉ rootFinset TwistTag.E6.tag := by decide +kernel



variable (E : Type) [Field E]

abbrev Model : Type :=
  Matrix (Fin 6) (Fin 6) E × E × E × ⋀[E]^3 (Fin 6 → E) × ⋀[E]^3 (Fin 6 → E)

variable {E}

@[expose] def modelLin (B B' : Matrix (Fin 6) (Fin 6) E) : Model E →ₗ[E] Model E :=
  LinearMap.prodMap ((LinearMap.mulLeft E B).comp (LinearMap.mulRight E B'))
    (LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id
      (LinearMap.prodMap (exteriorPower.map 3 (Matrix.toLin' B))
        (exteriorPower.map 3 (Matrix.toLin' B)))))

theorem modelLin_apply (B B' : Matrix (Fin 6) (Fin 6) E) (x : Model E) :
    modelLin B B' x = (B * x.1 * B', x.2.1, x.2.2.1,
      exteriorPower.map 3 (Matrix.toLin' B) x.2.2.2.1,
      exteriorPower.map 3 (Matrix.toLin' B) x.2.2.2.2) := by
  simp [modelLin, mul_assoc]

@[expose] def modelHom : SpecialLinearGroup (Fin 6) E →* Module.End E (Model E) where
  toFun B := modelLin (B : Matrix (Fin 6) (Fin 6) E) ((B⁻¹ : SpecialLinearGroup (Fin 6) E) :
    Matrix (Fin 6) (Fin 6) E)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    rw [modelLin_apply]
    simp [Matrix.toLin'_one, exteriorPower.map_id]
  map_mul' B C := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, modelLin_apply, modelLin_apply, modelLin_apply]
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul,
      exteriorPower.map_comp, LinearMap.comp_apply, Matrix.mul_assoc]


abbrev cubeBasis : Module.Basis (Set.powersetCard (Fin 6) 3) E (⋀[E]^3 (Fin 6 → E)) :=
  (Pi.basisFun E (Fin 6)).exteriorPower 3

@[expose] def rootImage (β : Fin TwistTag.E6.tag.rank → ℤ) : Model E :=
  (Matrix.of fun x y => if x ≠ y ∧ matRoot x y = β then 1 else 0,
    if β = e6HighestRoot then 1 else 0, if β = -e6HighestRoot then 1 else 0,
    ∑ S : Set.powersetCard (Fin 6) 3, (if cubeRoot S.1 = β then 1 else 0 : E) • cubeBasis S,
    ∑ S : Set.powersetCard (Fin 6) 3, (if -cubeRoot S.1ᶜ = β then 1 else 0 : E) • cubeBasis S)

@[expose] def diagCoeff : Fin 6 → Fin 6 → ℕ :=
  ![![1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 1]]

@[expose] def invCoeff : Fin 6 → Fin 6 → ℕ :=
  ![![1, 1, 1, 1, 0, 1], ![0, 1, 1, 1, 0, 1], ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 0, 0, 1],
    ![0, 1, 0, 0, 1, 1], ![0, 1, 0, 0, 1, 0]]

theorem diag_inv_mod : ∀ j j' : Fin 6,
    (∑ i, diagCoeff j i * invCoeff i j') % 2 = if j = j' then 1 else 0 := by decide

theorem inv_diag_mod : ∀ i i' : Fin 6,
    (∑ j, invCoeff i j * diagCoeff j i') % 2 = if i = i' then 1 else 0 := by decide

theorem diagCoeff_path : ∀ (t : Fin 5) (i : Fin 6),
    diagCoeff (pathIdx t) i = if i = t.castSucc ∨ i = t.succ then 1 else 0 := by decide

theorem cartan_diagCoeff : ∀ (j : Fin 6) (t : Fin 5),
    ((TwistTag.E6.tag.cartan j (pathIdx t)).natAbs + diagCoeff j t.castSucc +
      diagCoeff j t.succ) % 2 = 0 := by decide


@[expose] def hImage (j : Fin TwistTag.E6.tag.rank) : Model E :=
  (Matrix.diagonal fun i => (diagCoeff j i : E), 0, 0, 0, 0)

@[expose] def labelImage : Label TwistTag.E6.tag → Model E
  | .inl j => hImage j
  | .inr β => rootImage β.1

@[expose] def toModel : RootModule TwistTag.E6.tag E →ₗ[E] Model E :=
  Finsupp.linearCombination E labelImage

theorem toModel_hVec (j : Fin TwistTag.E6.tag.rank) :
    toModel (hVec TwistTag.E6.tag E j) = hImage j := by
  rw [hVec, toModel, Finsupp.linearCombination_single, one_smul]
  rfl

theorem rootImage_of_not_isRoot
    {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : ¬IsRoot TwistTag.E6.tag β) : rootImage (E := E) β = 0 := by
  have h1 : ∀ x y : Fin 6, ¬(x ≠ y ∧ matRoot x y = β) := fun x y h =>
    hβ (h.2 ▸ isRoot_matRoot h.1)
  have h2 : β ≠ e6HighestRoot := fun h => hβ (h ▸ isRoot_e6HighestRoot)
  have h3 : β ≠ -e6HighestRoot := fun h => hβ (h ▸ IsRoot.neg isRoot_e6HighestRoot)
  have h4 : ∀ S : Set.powersetCard (Fin 6) 3, cubeRoot S.1 ≠ β := fun S h =>
    hβ (h ▸ isRoot_cubeRoot S.2)
  have h5 : ∀ S : Set.powersetCard (Fin 6) 3, -cubeRoot S.1ᶜ ≠ β := fun S h =>
    hβ (h ▸ IsRoot.neg (isRoot_cubeRoot (card_compl_three S.2)))
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp [rootImage, h1 x y]
  · simp [rootImage, h2]
  · simp [rootImage, h3]
  · simp [rootImage, h4]
  · simp [rootImage, h5]

theorem rootImage_matRoot {a b : Fin 6} (hab : a ≠ b) :
    rootImage (E := E) (matRoot a b) = (Matrix.single a b 1, 0, 0, 0, 0) := by
  have h1 : ∀ x y : Fin 6, (x ≠ y ∧ matRoot x y = matRoot a b) ↔ (x = a ∧ y = b) :=
    fun x y => ⟨fun h => matRoot_injective x y a b h.1 hab h.2,
      by rintro ⟨rfl, rfl⟩; exact ⟨hab, rfl⟩⟩
  have h2 : matRoot a b ≠ e6HighestRoot := fun h => by
    have := congrFun h (e6Idx 1)
    rw [matRoot_one, e6HighestRoot_one] at this
    exact absurd this (by norm_num)
  have h3 : matRoot a b ≠ -e6HighestRoot := fun h => by
    have := congrFun h (e6Idx 1)
    rw [matRoot_one, Pi.neg_apply, e6HighestRoot_one] at this
    exact absurd this (by norm_num)
  have h4 : ∀ S : Set.powersetCard (Fin 6) 3, cubeRoot S.1 ≠ matRoot a b := fun S h => by
    have := congrFun h (e6Idx 1)
    rw [matRoot_one, cubeRoot_one] at this
    exact absurd this (by norm_num)
  have h5 : ∀ S : Set.powersetCard (Fin 6) 3, -cubeRoot S.1ᶜ ≠ matRoot a b := fun S h => by
    have := congrFun h (e6Idx 1)
    rw [matRoot_one, Pi.neg_apply, cubeRoot_one] at this
    exact absurd this (by norm_num)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp only [rootImage, Matrix.of_apply, h1, Matrix.single_apply]
    by_cases h : x = a ∧ y = b
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.symm, h.2.symm⟩]
    · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩]
  · simp [rootImage, h2]
  · simp [rootImage, h3]
  · simp [rootImage, h4]
  · simp [rootImage, h5]

theorem cubeRoot_ne_neg : ∀ S S' : Finset (Fin 6), cubeRoot S ≠ -cubeRoot S' := fun S S' h => by
  have := congrFun h (e6Idx 1)
  rw [Pi.neg_apply, cubeRoot_one, cubeRoot_one] at this
  exact absurd this (by norm_num)

theorem cubeRoot_ne_e6HighestRoot (S : Finset (Fin 6)) : cubeRoot S ≠ e6HighestRoot := fun h => by
  have := congrFun h (e6Idx 1)
  rw [cubeRoot_one, e6HighestRoot_one] at this
  exact absurd this (by norm_num)

theorem cubeRoot_ne_neg_e6HighestRoot (S : Finset (Fin 6)) : cubeRoot S ≠ -e6HighestRoot :=
  fun h => by
  have := congrFun h (e6Idx 1)
  rw [cubeRoot_one, Pi.neg_apply, e6HighestRoot_one] at this
  exact absurd this (by norm_num)

theorem e6HighestRoot_ne_neg : e6HighestRoot ≠ -e6HighestRoot := fun h => by
  have := congrFun h (e6Idx 1)
  rw [Pi.neg_apply, e6HighestRoot_one] at this
  exact absurd this (by norm_num)

theorem rootImage_e6HighestRoot :
    rootImage (E := E) e6HighestRoot = (0, 1, 0, 0, 0) := by
  have h1 : ∀ x y : Fin 6, ¬(x ≠ y ∧ matRoot x y = e6HighestRoot) := fun x y h => by
    have := congrFun h.2 (e6Idx 1)
    rw [matRoot_one, e6HighestRoot_one] at this
    exact absurd this (by norm_num)
  have h4 : ∀ S : Set.powersetCard (Fin 6) 3, cubeRoot S.1 ≠ e6HighestRoot := fun S =>
    cubeRoot_ne_e6HighestRoot S.1
  have h5 : ∀ S : Set.powersetCard (Fin 6) 3, -cubeRoot S.1ᶜ ≠ e6HighestRoot := fun S h =>
    cubeRoot_ne_neg_e6HighestRoot S.1ᶜ (by rw [← h, neg_neg])
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp [rootImage, h1 x y]
  · simp [rootImage]
  · simp [rootImage, e6HighestRoot_ne_neg]
  · simp [rootImage, h4]
  · simp [rootImage, h5]

theorem rootImage_neg_e6HighestRoot :
    rootImage (E := E) (-e6HighestRoot) = (0, 0, 1, 0, 0) := by
  have h1 : ∀ x y : Fin 6, ¬(x ≠ y ∧ matRoot x y = -e6HighestRoot) := fun x y h => by
    have := congrFun h.2 (e6Idx 1)
    rw [matRoot_one, Pi.neg_apply, e6HighestRoot_one] at this
    exact absurd this (by norm_num)
  have h4 : ∀ S : Set.powersetCard (Fin 6) 3, cubeRoot S.1 ≠ -e6HighestRoot := fun S =>
    cubeRoot_ne_neg_e6HighestRoot S.1
  have h5 : ∀ S : Set.powersetCard (Fin 6) 3, -cubeRoot S.1ᶜ ≠ -e6HighestRoot := fun S h =>
    cubeRoot_ne_e6HighestRoot S.1ᶜ (neg_injective h)
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp [rootImage, h1 x y]
  · simp [rootImage, Ne.symm e6HighestRoot_ne_neg]
  · simp [rootImage]
  · simp [rootImage, h4]
  · simp [rootImage, h5]

theorem rootImage_cubeRoot (S : Set.powersetCard (Fin 6) 3) :
    rootImage (E := E) (cubeRoot S.1) = (0, 0, 0, cubeBasis S, 0) := by
  have h1 : ∀ x y : Fin 6, ¬(x ≠ y ∧ matRoot x y = cubeRoot S.1) := fun x y h => by
    have := congrFun h.2 (e6Idx 1)
    rw [matRoot_one, cubeRoot_one] at this
    exact absurd this (by norm_num)
  have h5 : ∀ S' : Set.powersetCard (Fin 6) 3, -cubeRoot S'.1ᶜ ≠ cubeRoot S.1 := fun S' h =>
    cubeRoot_ne_neg S.1 S'.1ᶜ h.symm
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp [rootImage, h1 x y]
  · simp [rootImage, cubeRoot_ne_e6HighestRoot]
  · simp [rootImage, cubeRoot_ne_neg_e6HighestRoot]
  · simp only [rootImage]
    rw [Finset.sum_eq_single S]
    · simp
    · intro S' _ hS'
      rw [ite_eq_right fun h => hS' (Subtype.ext (cubeRoot_injective _ _ S'.2 S.2 h)), zero_smul]
    · simp
  · simp [rootImage, h5]

theorem rootImage_neg_cubeRoot (S : Set.powersetCard (Fin 6) 3) :
    rootImage (E := E) (-cubeRoot S.1ᶜ) = (0, 0, 0, 0, cubeBasis S) := by
  have h1 : ∀ x y : Fin 6, ¬(x ≠ y ∧ matRoot x y = -cubeRoot S.1ᶜ) := fun x y h => by
    have := congrFun h.2 (e6Idx 1)
    rw [matRoot_one, Pi.neg_apply, cubeRoot_one] at this
    exact absurd this (by norm_num)
  have h4 : ∀ S' : Set.powersetCard (Fin 6) 3, cubeRoot S'.1 ≠ -cubeRoot S.1ᶜ := fun S' =>
    cubeRoot_ne_neg S'.1 S.1ᶜ
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · ext x y
    simp [rootImage, h1 x y]
  · simp only [rootImage]
    rw [ite_eq_right fun h =>
      cubeRoot_ne_neg_e6HighestRoot S.1ᶜ (by rw [← neg_neg (cubeRoot _), h])]
  · simp only [rootImage]
    rw [ite_eq_right fun h => cubeRoot_ne_e6HighestRoot S.1ᶜ (neg_injective h)]
  · simp [rootImage, h4]
  · simp only [rootImage]
    rw [Finset.sum_eq_single S]
    · simp
    · intro S' _ hS'
      have hne : -cubeRoot S'.1ᶜ ≠ -cubeRoot S.1ᶜ := fun h => hS' (Subtype.ext (compl_injective
        (cubeRoot_injective _ _ (card_compl_three S'.2) (card_compl_three S.2) (neg_injective h))))
      rw [ite_eq_right hne, zero_smul]
    · simp


theorem toModel_rootVec
    (β : Fin TwistTag.E6.tag.rank → ℤ) :
    toModel (rootVec TwistTag.E6.tag E β) = rootImage β := by
  by_cases hβ : IsRoot TwistTag.E6.tag β
  · rw [rootVec, dite_eq_left hβ, toModel, Finsupp.linearCombination_single, one_smul]
    rfl
  · rw [rootVec, dite_eq_right hβ, map_zero, rootImage_of_not_isRoot hβ]


@[expose] def hComb (i : Fin 6) : RootModule TwistTag.E6.tag E :=
  ∑ j : Fin 6, (invCoeff i j : E) • hVec TwistTag.E6.tag E (e6Idx j)

@[expose] def matImage (x y : Fin 6) : RootModule TwistTag.E6.tag E :=
  if x = y then hComb x else rootVec TwistTag.E6.tag E (matRoot x y)

@[expose] def matLin : Matrix (Fin 6) (Fin 6) E →ₗ[E] RootModule TwistTag.E6.tag E where
  toFun A := ∑ x, ∑ y, A x y • matImage x y
  map_add' A B := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c A := by simp [smul_smul, Finset.smul_sum]

@[expose] def fromModel : Model E →ₗ[E] RootModule TwistTag.E6.tag E :=
  matLin.coprod ((LinearMap.toSpanSingleton E _ (rootVec TwistTag.E6.tag E e6HighestRoot)).coprod
    ((LinearMap.toSpanSingleton E _ (rootVec TwistTag.E6.tag E (-e6HighestRoot))).coprod
      ((cubeBasis.constr E fun S => rootVec TwistTag.E6.tag E (cubeRoot S.1)).coprod
        (cubeBasis.constr E fun S => rootVec TwistTag.E6.tag E (-cubeRoot S.1ᶜ)))))

theorem fromModel_apply (x : Model E) : fromModel x = matLin x.1 +
    (x.2.1 • rootVec TwistTag.E6.tag E e6HighestRoot +
      (x.2.2.1 • rootVec TwistTag.E6.tag E (-e6HighestRoot) +
        (cubeBasis.constr E (fun S => rootVec TwistTag.E6.tag E (cubeRoot S.1)) x.2.2.2.1 +
          cubeBasis.constr E (fun S => rootVec TwistTag.E6.tag E (-cubeRoot S.1ᶜ))
            x.2.2.2.2))) := by
  simp [fromModel]

theorem matLin_single (x y : Fin 6) : matLin (Matrix.single x y (1 : E)) = matImage x y := by
  simp only [matLin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.single_apply]
  rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem matLin_diagonal (d : Fin 6 → E) : matLin (Matrix.diagonal d) = ∑ x, d x • hComb x := by
  simp only [matLin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp [matImage]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

variable (E) in
theorem natCast_eq_mod_two (h2 : (2 : E) = 0) (n : ℕ) : (n : E) = ((n % 2 : ℕ) : E) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, h2, zero_mul, add_zero]

theorem fromModel_hImage (h2 : (2 : E) = 0) (j : Fin 6) :
    fromModel (hImage (e6Idx j)) = hVec TwistTag.E6.tag E (e6Idx j) := by
  rw [fromModel_apply]
  simp only [hImage, zero_smul, map_zero, add_zero]
  rw [matLin_diagonal]
  simp only [hComb, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hc : ∀ j' : Fin 6, ∑ i : Fin 6, ((diagCoeff j i : E) * (invCoeff i j' : E)) =
      if j = j' then 1 else 0 := fun j' => by
    rw [show (∑ i : Fin 6, ((diagCoeff j i : E) * (invCoeff i j' : E))) =
      ((∑ i : Fin 6, diagCoeff j i * invCoeff i j' : ℕ) : E) by push_cast; rfl,
      natCast_eq_mod_two E h2, diag_inv_mod]
    split_ifs <;> simp
  simp only [← Finset.sum_smul, hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]


theorem rootVec_eq_single' {β : Fin TwistTag.E6.tag.rank → ℤ} (h : IsRoot TwistTag.E6.tag β) :
    rootVec TwistTag.E6.tag E β = Finsupp.single (Sum.inr ⟨β, h⟩) 1 := by
  rw [rootVec, dite_eq_left h]

theorem fromModel_mat (A : Matrix (Fin 6) (Fin 6) E) :
    fromModel ((A, 0, 0, 0, 0) : Model E) = matLin A := by
  simp [fromModel_apply]

theorem fromModel_lineP : fromModel ((0, 1, 0, 0, 0) : Model E) =
    rootVec TwistTag.E6.tag E e6HighestRoot := by
  simp [fromModel_apply]

theorem fromModel_lineN : fromModel ((0, 0, 1, 0, 0) : Model E) =
    rootVec TwistTag.E6.tag E (-e6HighestRoot) := by
  simp [fromModel_apply]

theorem fromModel_cubeP (S : Set.powersetCard (Fin 6) 3) :
    fromModel ((0, 0, 0, cubeBasis S, 0) : Model E) = rootVec TwistTag.E6.tag E (cubeRoot S.1) := by
  rw [fromModel_apply]
  simp only [map_zero, zero_smul, zero_add, add_zero]
  exact Module.Basis.constr_basis _ _ _ S

theorem fromModel_cubeN (S : Set.powersetCard (Fin 6) 3) :
    fromModel ((0, 0, 0, 0, cubeBasis S) : Model E) =
      rootVec TwistTag.E6.tag E (-cubeRoot S.1ᶜ) := by
  rw [fromModel_apply]
  simp only [map_zero, zero_smul, zero_add]
  exact Module.Basis.constr_basis _ _ _ S

theorem fromModel_rootImage
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    fromModel (rootImage (E := E) β) = rootVec TwistTag.E6.tag E β := by
  rcases root_cases β (mem_rootFinset.2 hβ) with ⟨a, b, hab, rfl⟩ | rfl | rfl |
    ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · rw [rootImage_matRoot hab, fromModel_mat, matLin_single, matImage, ite_eq_right hab]
  · rw [rootImage_e6HighestRoot, fromModel_lineP]
  · rw [rootImage_neg_e6HighestRoot, fromModel_lineN]
  · have := rootImage_cubeRoot (E := E) ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    rw [this, fromModel_cubeP]
  · have := rootImage_neg_cubeRoot (E := E) ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    rw [this, fromModel_cubeN]

theorem fromModel_toModel
    (h2 : (2 : E) = 0) (x : RootModule TwistTag.E6.tag E) :
    fromModel (toModel x) = x := by
  have h : fromModel ∘ₗ toModel = (LinearMap.id : RootModule TwistTag.E6.tag E →ₗ[E] _) := by
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
    rcases b with j | ⟨β, hβ⟩
    · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule TwistTag.E6.tag E) =
        hVec TwistTag.E6.tag E j from rfl, toModel_hVec]
      exact fromModel_hImage h2 j
    · rw [← rootVec_eq_single' hβ, toModel_rootVec, fromModel_rootImage hβ]
  exact LinearMap.congr_fun h x


theorem toModel_hComb (h2 : (2 : E) = 0) (x : Fin 6) :
    toModel (hComb x) = ((Matrix.single x x (1 : E), 0, 0, 0, 0) : Model E) := by
  simp only [hComb, map_sum, map_smul]
  simp only [toModel_hVec, hImage]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · rw [Prod.fst_sum]
    simp only [Prod.smul_fst]
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, Matrix.single_apply]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      have hc : ∑ j : Fin 6, ((invCoeff x j : E) * (diagCoeff j a : E)) =
          if x = a then 1 else 0 := by
        rw [show (∑ j : Fin 6, ((invCoeff x j : E) * (diagCoeff j a : E))) =
          ((∑ j : Fin 6, invCoeff x j * diagCoeff j a : ℕ) : E) by push_cast; rfl,
          natCast_eq_mod_two E h2, inv_diag_mod]
        split_ifs <;> simp
      rw [hc]
      by_cases hxa : x = a <;> simp [hxa]
    · simp only [hab, ite_false, mul_zero, Finset.sum_const_zero]
      rw [ite_eq_right fun h => hab (h.1.symm.trans h.2)]
  · simp [Prod.snd_sum]
  · simp [Prod.snd_sum]
  · simp [Prod.snd_sum]
  · simp [Prod.snd_sum]

theorem toModel_matImage
    (h2 : (2 : E) = 0) (x y : Fin 6) :
    toModel (matImage x y) = ((Matrix.single x y (1 : E), 0, 0, 0, 0) : Model E) := by
  by_cases hxy : x = y
  · subst hxy
    rw [matImage, ite_eq_left rfl, toModel_hComb h2]
  · rw [matImage, ite_eq_right hxy, toModel_rootVec, rootImage_matRoot hxy]

theorem toModel_fromModel
    (h2 : (2 : E) = 0) (x : Model E) : toModel (fromModel x) = x := by
  have h : toModel ∘ₗ fromModel = (LinearMap.id : Model E →ₗ[E] Model E) := by
    refine LinearMap.prod_ext ?_ (LinearMap.prod_ext ?_ (LinearMap.prod_ext ?_
      (LinearMap.prod_ext ?_ ?_)))
    · refine (Matrix.stdBasis E (Fin 6) (Fin 6)).ext fun p => ?_
      rw [Matrix.stdBasis_eq_single]
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.id_apply]
      rw [show ((Matrix.single p.1 p.2 (1 : E), (0 : E × E × _ × _)) : Model E) =
        (Matrix.single p.1 p.2 1, 0, 0, 0, 0) from rfl, fromModel_mat, matLin_single,
        toModel_matImage h2]
    · refine LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [show ((0 : Matrix (Fin 6) (Fin 6) E), ((1 : E), (0 : E × _ × _))) =
        ((0, 1, 0, 0, 0) : Model E) from rfl, fromModel_lineP, toModel_rootVec,
        rootImage_e6HighestRoot]
    · refine LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [show ((0 : Matrix (Fin 6) (Fin 6) E), ((0 : E), ((1 : E), (0 : _ × _)))) =
        ((0, 0, 1, 0, 0) : Model E) from rfl, fromModel_lineN, toModel_rootVec,
        rootImage_neg_e6HighestRoot]
    · refine cubeBasis.ext fun S => ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [show ((0 : Matrix (Fin 6) (Fin 6) E), ((0 : E), ((0 : E), (cubeBasis S, 0)))) =
        ((0, 0, 0, cubeBasis S, 0) : Model E) from rfl, fromModel_cubeP, toModel_rootVec,
        rootImage_cubeRoot]
    · refine cubeBasis.ext fun S => ?_
      simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.id_apply]
      rw [show ((0 : Matrix (Fin 6) (Fin 6) E), ((0 : E), ((0 : E), (0, cubeBasis S)))) =
        ((0, 0, 0, 0, cubeBasis S) : Model E) from rfl, fromModel_cubeN, toModel_rootVec,
        rootImage_neg_cubeRoot]
  exact LinearMap.congr_fun h x

@[expose] def modelEquiv
    (h2 : (2 : E) = 0) : RootModule TwistTag.E6.tag E ≃ₗ[E] Model E :=
  LinearEquiv.ofLinearMap toModel fromModel
    (LinearMap.ext (toModel_fromModel h2)) (LinearMap.ext (fromModel_toModel h2))



abbrev xMat (t : Fin 5) (c : E) : Matrix (Fin 6) (Fin 6) E :=
  Matrix.transvection t.castSucc t.succ c

abbrev yMat (t : Fin 5) (c : E) : Matrix (Fin 6) (Fin 6) E :=
  Matrix.transvection t.succ t.castSucc c

theorem transvection_conj (i j : Fin 6) (c : E) (A : Matrix (Fin 6) (Fin 6) E) :
    Matrix.transvection i j c * A * Matrix.transvection i j (-c) =
      A + Matrix.single i j c * A - A * Matrix.single i j c -
        Matrix.single i j c * A * Matrix.single i j c := by
  rw [Matrix.transvection, Matrix.transvection, ← Matrix.single_neg]
  noncomm_ring

theorem single_mul_single' (i j a b : Fin 6) (c d : E) :
    Matrix.single i j c * Matrix.single a b d = if j = a then Matrix.single i b (c * d) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same c i j b d
  · exact Matrix.single_mul_single_of_ne c i j a h d

theorem castSucc_ne_succ (t : Fin 5) : t.castSucc ≠ t.succ := Fin.castSucc_lt_succ.ne

theorem neg_eq_self_of_two (h2 : (2 : E) = 0) (x : E) : -x = x := by
  linear_combination (-x) * h2

theorem sub_eq_add_of_two (h2 : (2 : E) = 0) (x y : E) : x - y = x + y := by
  linear_combination (-y) * h2

end CFSG.LieType.Chevalley.E6GraphLevi
