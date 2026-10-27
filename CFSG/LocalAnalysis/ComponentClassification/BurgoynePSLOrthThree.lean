module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem inv_of_fixedPointFree {G : Type*} [Group G] {O : Subgroup G} [Finite O] {s : G}
    (hs : s * s = 1) (hn : ∀ x ∈ O, s * x * s⁻¹ ∈ O)
    (hC : ∀ x ∈ O, s * x = x * s → x = 1) : ∀ x ∈ O, s * x * s⁻¹ = x⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  set f : O → O := fun x => ⟨(x : G)⁻¹ * (s * x * s⁻¹), mul_mem (inv_mem x.2) (hn x x.2)⟩ with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (s * x * s⁻¹) = (y : G)⁻¹ * (s * y * s⁻¹) := congrArg Subtype.val hxy
    have hmem : (y : G) * (x : G)⁻¹ ∈ O := mul_mem y.2 (inv_mem x.2)
    have hfix : s * ((y : G) * (x : G)⁻¹) = (y : G) * (x : G)⁻¹ * s := by
      calc s * ((y : G) * (x : G)⁻¹) = (y : G) * ((y : G)⁻¹ * (s * y * s⁻¹)) * s * (x : G)⁻¹ := by
            group
        _ = (y : G) * ((x : G)⁻¹ * (s * x * s⁻¹)) * s * (x : G)⁻¹ := by rw [← h1]
        _ = (y : G) * (x : G)⁻¹ * s := by group
    have := hC _ hmem hfix
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro z hz
  obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
  have hz' : z = (x : G)⁻¹ * (s * x * s⁻¹) := (congrArg Subtype.val hx).symm
  rw [hz', hsi]
  calc s * ((x : G)⁻¹ * (s * x * s)) * s = s * (x : G)⁻¹ * s * x * (s * s) := by group
    _ = s * (x : G)⁻¹ * s * x := by rw [hs, mul_one]
    _ = s⁻¹ * (x : G)⁻¹ * s⁻¹ * x := by rw [hsi]
    _ = ((x : G)⁻¹ * (s * x * s))⁻¹ := by group

theorem eq_bot_of_four_group {G : Type*} [Group G] {O : Subgroup G} [Finite O] {s₁ s₂ : G}
    (h1 : s₁ * s₁ = 1) (h2 : s₂ * s₂ = 1)
    (hn₁ : ∀ x ∈ O, s₁ * x * s₁⁻¹ ∈ O) (hn₂ : ∀ x ∈ O, s₂ * x * s₂⁻¹ ∈ O)
    (hC₁ : ∀ x ∈ O, s₁ * x = x * s₁ → x = 1) (hC₂ : ∀ x ∈ O, s₂ * x = x * s₂ → x = 1)
    (hC₁₂ : ∀ x ∈ O, s₁ * s₂ * x = x * (s₁ * s₂) → x = 1) : O = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have i₁ := inv_of_fixedPointFree h1 hn₁ hC₁
  have i₂ := inv_of_fixedPointFree h2 hn₂ hC₂
  refine hC₁₂ x hx ?_
  have e₂ := i₂ x hx
  have e₁ := i₁ x⁻¹ (inv_mem hx)
  calc s₁ * s₂ * x = s₁ * (s₂ * x * s₂⁻¹) * s₁⁻¹ * (s₁ * s₂) := by group
    _ = s₁ * x⁻¹ * s₁⁻¹ * (s₁ * s₂) := by rw [e₂]
    _ = x * (s₁ * s₂) := by rw [e₁, inv_inv]

theorem zmod_three_pow_eight_one : ∀ x l u : ZMod 3, l ≠ 0 → u ≠ 0 →
    !![x] * !![u] * (!![x])ᵀ = !![l * u] → (!![x]) ^ 8 = 1 := by
  decide

theorem zmod_three_pow_eight_two : ∀ a b c d l u v : ZMod 3, l ≠ 0 → u ≠ 0 → v ≠ 0 →
    !![a, b; c, d] * !![u, 0; 0, v] * (!![a, b; c, d])ᵀ = !![l * u, 0; 0, l * v] →
    (!![a, b; c, d]) ^ 8 = 1 := by
  decide

theorem pow_eight_of_similitude_three [Finite K] (h3 : Nat.card K = 3) {m : ℕ}
    (hm : m = 1 ∨ m = 2) {X : Matrix (Fin m) (Fin m) K} {u : Fin m → K} (hu : ∀ i, u i ≠ 0)
    {l : K} (hl : l ≠ 0) (hX : X * diagonal u * Xᵀ = diagonal fun i => l * u i) : X ^ 8 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set f : K →+* ZMod 3 := (FiniteField.ringEquivOfCardEq hc).toRingHom
  have hfinj : Function.Injective f := (FiniteField.ringEquivOfCardEq hc).injective
  have hX' := congrArg (fun M : Matrix (Fin m) (Fin m) K => M.map f) hX
  simp only [Matrix.map_mul, transpose_map, diagonal_map (map_zero f), map_mul] at hX'
  have hinj : ∀ M N : Matrix (Fin m) (Fin m) K, M.map f = N.map f → M = N := fun M N h => by
    ext i j
    exact hfinj (congrFun (congrFun h i) j)
  have hl' : f l ≠ 0 := (map_ne_zero f).2 hl
  have hu' : ∀ i, f (u i) ≠ 0 := fun i => (map_ne_zero f).2 (hu i)
  apply hinj
  rw [Matrix.map_pow, Matrix.map_one f (map_zero f) (map_one f)]
  rcases hm with rfl | rfl
  · have hXe : X.map f = !![(X.map f) 0 0] := by
      ext i j
      fin_cases i
      fin_cases j
      rfl
    rw [hXe, diagonal_fin_one, diagonal_fin_one] at hX'
    rw [hXe]
    exact zmod_three_pow_eight_one _ _ _ hl' (hu' 0) hX'
  · have hXe := eta_fin_two (X.map f)
    have hd : ∀ v : Fin 2 → ZMod 3, diagonal v = !![v 0, 0; 0, v 1] := fun v => by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hXe, hd, hd] at hX'
    rw [hXe]
    exact zmod_three_pow_eight_two _ _ _ _ _ _ _ hl' (hu' 0) (hu' 1) hX'

section Blocks

variable {m : ℕ} {ι : Fin m → Fin n}

@[expose] def embedVec (ι : Fin m → Fin n) (c : Fin m → K) : Fin n → K :=
  fun x => ∑ u, if ι u = x then c u else 0

theorem embedVec_apply (hι : Function.Injective ι) (c : Fin m → K) (u : Fin m) :
    embedVec ι c (ι u) = c u := by
  rw [embedVec, Finset.sum_eq_single u (fun v _ hv => by simp [hι.ne hv]) (by simp)]
  simp

theorem embedVec_apply_of_not_mem (c : Fin m → K) {x : Fin n} (hx : x ∉ Set.range ι) :
    embedVec ι c x = 0 :=
  Finset.sum_eq_zero fun u _ => by simp [show ι u ≠ x from fun h => hx ⟨u, h⟩]

theorem embedVec_single (hι : Function.Injective ι) (u : Fin m) :
    embedVec ι (Pi.single u (1 : K)) = Pi.single (ι u) 1 := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨v, rfl⟩ := hx
    simp only [embedVec_apply hι, Pi.single_apply, hι.eq_iff]
  · rw [embedVec_apply_of_not_mem _ hx]
    simp [show x ≠ ι u from fun h => hx ⟨u, h.symm⟩]

theorem sum_range_eq {f : Fin n → K} (hι : Function.Injective ι)
    (hf : ∀ z, z ∉ Set.range ι → f z = 0) : ∑ z, f z = ∑ u, f (ι u) :=
  (Fintype.sum_of_injective ι hι (fun u => f (ι u)) f hf fun _ => rfl).symm

theorem mulVec_embedVec (hι : Function.Injective ι) {D : Matrix (Fin n) (Fin n) K}
    (hD : ∀ x u, x ∉ Set.range ι → D x (ι u) = 0) (c : Fin m → K) :
    D *ᵥ embedVec ι c = embedVec ι (D.submatrix ι ι *ᵥ c) := by
  ext x
  rw [mulVec, dotProduct, sum_range_eq hι fun z hz => by
    rw [embedVec_apply_of_not_mem _ hz, mul_zero]]
  simp only [embedVec_apply hι]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨v, rfl⟩ := hx
    rw [embedVec_apply hι]
    rfl
  · rw [embedVec_apply_of_not_mem _ hx]
    exact Finset.sum_eq_zero fun u _ => by rw [hD x u hx, zero_mul]

theorem pow_mulVec_embedVec (hι : Function.Injective ι) {D : Matrix (Fin n) (Fin n) K}
    (hD : ∀ x u, x ∉ Set.range ι → D x (ι u) = 0) (c : Fin m → K) (k : ℕ) :
    D ^ k *ᵥ embedVec ι c = embedVec ι ((D.submatrix ι ι) ^ k *ᵥ c) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, mulVec_embedVec hι hD, ih, pow_succ, ← mulVec_mulVec]

theorem similitude_submatrix (hι : Function.Injective ι) {D : Matrix (Fin n) (Fin n) K}
    {a : Fin n → K} {l : K} (hsim : D * diagonal a * Dᵀ = diagonal fun x => l * a x)
    (hD' : ∀ u z, z ∉ Set.range ι → D (ι u) z = 0) :
    D.submatrix ι ι * diagonal (fun u => a (ι u)) * (D.submatrix ι ι)ᵀ =
      diagonal fun u => l * a (ι u) := by
  ext u v
  have e := congrFun (congrFun hsim (ι u)) (ι v)
  rw [Matrix.mul_apply] at e ⊢
  simp only [mul_diagonal, transpose_apply, submatrix_apply] at e ⊢
  rw [sum_range_eq hι fun z hz => by rw [hD' u z hz, zero_mul, zero_mul]] at e
  rw [e]
  simp only [diagonal_apply, hι.eq_iff]

end Blocks

theorem pow_eight_eq_one_of_commute_sign [Finite K] (h3 : Nat.card K = 3) (hn3 : 3 ≤ n)
    (hn4 : n ≤ 4) {D : Matrix (Fin n) (Fin n) K} {a : Fin n → K} (ha : ∀ x, a x ≠ 0) {l : K}
    (hl : l ≠ 0) (hsim : D * diagonal a * Dᵀ = diagonal fun x => l * a x) {i j : Fin n}
    (hij : i ≠ j) (hcomm : D * signMat K {i, j} = signMat K {i, j} * D) : D ^ 8 = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  set J : Finset (Fin n) := {i, j} with hJ
  have hblock : ∀ x y, (x ∈ J ↔ y ∉ J) → D x y = 0 := by
    intro x y hxy
    have e := congrFun (congrFun hcomm x) y
    simp only [signMat, mul_diagonal, diagonal_mul] at e
    by_cases hy : y ∈ J
    · have hx : x ∉ J := fun hx => (hxy.1 hx) hy
      simp only [hy, hx, ↓reduceIte] at e
      have : (2 : K) * D x y = 0 := by linear_combination -e
      exact (mul_eq_zero.1 this).resolve_left h2
    · have hx : x ∈ J := hxy.2 hy
      simp only [hy, hx, ↓reduceIte] at e
      have : (2 : K) * D x y = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left h2
  have hJcard : J.card = 2 := Finset.card_pair hij
  have hT : ∀ T : Finset (Fin n), (T = J ∨ T = Jᶜ) → ∀ x ∈ T,
      D ^ 8 *ᵥ Pi.single x 1 = Pi.single x 1 := by
    intro T hTJ x hx
    have hcard : T.card = 1 ∨ T.card = 2 := by
      rcases hTJ with rfl | rfl
      · exact Or.inr hJcard
      · rw [Finset.card_compl, hJcard, Fintype.card_fin]
        omega
    set ι : Fin T.card → Fin n := fun u => (T.equivFin.symm u : Fin n) with hι
    have hιinj : Function.Injective ι := fun u v h => T.equivFin.symm.injective (Subtype.ext h)
    have hrange : ∀ z, z ∈ Set.range ι ↔ z ∈ T := by
      intro z
      constructor
      · rintro ⟨u, rfl⟩
        exact (T.equivFin.symm u).2
      · intro hz
        exact ⟨T.equivFin ⟨z, hz⟩, by simp [hι]⟩
    have hsep : ∀ x y, x ∈ T → y ∉ T → (x ∈ J ↔ y ∉ J) := by
      intro x y hx hy
      rcases hTJ with rfl | rfl
      · exact ⟨fun _ => hy, fun _ => hx⟩
      · rw [Finset.mem_compl] at hx hy
        exact ⟨fun h => absurd h hx, fun h => absurd h hy⟩
    have hD : ∀ x u, x ∉ Set.range ι → D x (ι u) = 0 := by
      intro x u hx
      rw [hrange] at hx
      have h1 := hsep _ _ ((hrange _).1 ⟨u, rfl⟩) hx
      exact hblock _ _ (by tauto)
    have hD' : ∀ u z, z ∉ Set.range ι → D (ι u) z = 0 := by
      intro u z hz
      rw [hrange] at hz
      exact hblock _ _ (hsep _ _ ((hrange _).1 ⟨u, rfl⟩) hz)
    have hX := pow_eight_of_similitude_three h3 hcard (fun u => ha (ι u)) hl
      (similitude_submatrix hιinj hsim hD')
    obtain ⟨u, rfl⟩ := (hrange x).2 hx
    rw [← embedVec_single hιinj, pow_mulVec_embedVec hιinj hD, hX, one_mulVec]
  ext y x
  have hx := hT (if x ∈ J then J else Jᶜ) (by split_ifs <;> simp) x (by
    split_ifs with h
    · exact h
    · exact Finset.mem_compl.2 h)
  have e := congrFun hx y
  rw [mulVec_single_one, Matrix.col_apply] at e
  rw [e, Pi.single_apply, one_apply, eq_comm]

theorem conj_mem_oddCoreIn {G : Type} [Group G] {B : Subgroup G} {t y c : G}
    (hy : y ∈ oddCoreIn B t) (hc : c ∈ B ⊓ centralizer ({t} : Set G)) :
    c * y * c⁻¹ ∈ oddCoreIn B t := by
  obtain ⟨y', hy', rfl⟩ := hy
  set c' : ↥(B ⊓ centralizer ({t} : Set G)) := ⟨c, hc⟩
  exact ⟨c' * y' * c'⁻¹, (pPrimeCore_normal (p := 2)).conj_mem _ hy' c', by simp [c']⟩

theorem similitude_of_commute_conjAut_dualAut [Finite K] (hn : 3 ≤ n) {D A : GL (Fin n) K}
    (hc : conjAut n K D * (conjAut n K A * dualAut n K) =
      (conjAut n K A * dualAut n K) * conjAut n K D) :
    ∃ c : Kˣ, (D : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) *
      (D : Matrix (Fin n) (Fin n) K)ᵀ = (c : K) • (A : Matrix (Fin n) (Fin n) K) := by
  have h1 : conjAut n K D * conjAut n K A * dualAut n K =
      conjAut n K A * conjAut n K (GeneralLinearGroup.inverseTranspose D) * dualAut n K := by
    calc conjAut n K D * conjAut n K A * dualAut n K
        = conjAut n K D * (conjAut n K A * dualAut n K) := mul_assoc _ _ _
      _ = (conjAut n K A * dualAut n K) * conjAut n K D := hc
      _ = conjAut n K A * (dualAut n K * conjAut n K D) := mul_assoc _ _ _
      _ = conjAut n K A * (conjAut n K (GeneralLinearGroup.inverseTranspose D) *
          dualAut n K) := by
          rw [LocalAnalysis.ComponentInitial.LinearFlag.dualAut_mul_conjAut]
      _ = _ := (mul_assoc _ _ _).symm
  have h2' : conjAut n K (D * A) = conjAut n K (A * GeneralLinearGroup.inverseTranspose D) := by
    rw [map_mul, map_mul]
    exact mul_right_cancel h1
  have h1' : conjAut n K ((A * GeneralLinearGroup.inverseTranspose D)⁻¹ * (D * A)) *
      fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h2', inv_mul_cancel]
  obtain ⟨-, c, hcs⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h1'
  refine ⟨c, ?_⟩
  have hDA : D * A = A * GeneralLinearGroup.inverseTranspose D *
      GeneralLinearGroup.scalar (Fin n) c := by
    rw [hcs, mul_inv_cancel_left]
  have hm := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K) *
    (D : Matrix (Fin n) (Fin n) K)ᵀ) hDA
  simp only [Units.val_mul] at hm
  rw [hm, GeneralLinearGroup.coe_inverseTranspose]
  have hsc : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (c : K) • 1 := by
    ext a b
    simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
  rw [hsc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc,
    ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one,
    Matrix.mul_one]

theorem orth_oddCoreIn_eq_bot_three [Finite K] (h3 : Nat.card K = 3) (hn3 : 3 ≤ n)
    (hn4 : n ≤ 4) {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {w : Fin n → K} (hw : ∀ i, w i ≠ 0) :
    oddCoreIn B (conjAut n K (diagGL hw)⁻¹ * dualAut n K) = ⊥ := by
  have : Finite (projectiveSL n K) := inferInstance
  set A := (diagGL hw)⁻¹ with hA
  set t := conjAut n K A * dualAut n K with ht
  set O := oddCoreIn B t with hO
  have : Finite O := inferInstance
  have hAinv : A⁻¹ = diagGL hw := inv_inv _
  have hsignmem : ∀ (J : Finset (Fin n)) (hJ : Even J.card),
      conjProj n K (signSL K J hJ) ∈ B ⊓ centralizer ({t} : Set _) := by
    intro J hJ
    have hfix : graphLift A (signSL K J hJ) = signSL K J hJ := by
      rw [graphLift_eq_iff, hAinv]
      change SpecialLinearGroup.toGL (signSL K J hJ) ∈ CatalogueBGraphForm.isometryGroup n K _
      rw [CatalogueBGraphForm.mem_isometryGroup]
      change (signMat K J)ᵀ * diagonal w * signMat K J = diagonal w
      rw [signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext k
      split_ifs <;> ring
    refine ⟨hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : t * conjProj n K (signSL K J hJ) * t⁻¹ = conjProj n K (signSL K J hJ) := by
      rw [MonoidHom.comp_apply, mul_conj_mul_inv, ht, conjAut_mul_dualAut_proj, hfix]
    calc conjProj n K (signSL K J hJ) * t = t * conjProj n K (signSL K J hJ) * t⁻¹ * t := by
          rw [h1]
      _ = t * conjProj n K (signSL K J hJ) := by group
  have hsq : ∀ (J : Finset (Fin n)) (hJ : Even J.card),
      conjProj n K (signSL K J hJ) * conjProj n K (signSL K J hJ) = 1 := by
    intro J hJ
    rw [← map_mul, signSL_mul_self, map_one]
  have hC : ∀ {i j : Fin n} (hij : i ≠ j), ∀ y ∈ O,
      conjProj n K (signSL K {i, j} (by rw [Finset.card_pair hij]; exact even_two)) * y =
        y * conjProj n K (signSL K {i, j} (by rw [Finset.card_pair hij]; exact even_two)) →
      y = 1 := by
    intro i j hij y hy hcomm
    have hodd := odd_orderOf_of_mem_oddCoreIn hy
    obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn3 hodd
    have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card (by rw [h3]; exact Nat.prime_three) τ
    subst hτ
    rw [map_one, mul_one] at hodd hcomm ⊢
    have hyt := commute_of_mem_oddCoreIn hy
    rw [map_one, mul_one] at hyt
    set S := signSL K {i, j} (by rw [Finset.card_pair hij]; exact even_two) with hS
    have hcS : conjProj n K S = conjAut n K (SpecialLinearGroup.toGL S) := (conjAut_toGL S).symm
    rw [hcS] at hcomm
    have hSS : ∃ ν : Kˣ, SpecialLinearGroup.toGL S * SpecialLinearGroup.toGL S =
        GeneralLinearGroup.scalar (Fin n) ν := ⟨1, by
      rw [← map_mul, hS, signSL_mul_self, map_one, map_one]⟩
    have hDS := commute_of_odd_conjAut hn3 hSS hodd hcomm.symm
    have hDSm : (D : Matrix (Fin n) (Fin n) K) * signMat K {i, j} = signMat K {i, j} * D := by
      have := congrArg Units.val hDS
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    obtain ⟨c, hc⟩ := similitude_of_commute_conjAut_dualAut hn3 hyt
    have hsim : (D : Matrix (Fin n) (Fin n) K) * diagonal (fun x => (w x)⁻¹) *
        (D : Matrix (Fin n) (Fin n) K)ᵀ = diagonal fun x => (c : K) * (w x)⁻¹ := by
      have hAm : (A : Matrix (Fin n) (Fin n) K) = diagonal fun x => (w x)⁻¹ := rfl
      rw [hAm, ← diagonal_smul] at hc
      exact hc
    have hD8 := pow_eight_eq_one_of_commute_sign h3 hn3 hn4 (fun x => inv_ne_zero (hw x))
      c.ne_zero hsim hij hDSm
    have hpow : conjAut n K D ^ 8 = 1 := by
      rw [← map_pow]
      have : D ^ 8 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hD8, Units.val_one])
      rw [this, map_one]
    have hdvd : orderOf (conjAut n K D) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hprod : signSL K {i0, i1} (by rw [Finset.card_pair h01]; exact even_two) *
      signSL K {i0, i2} (by rw [Finset.card_pair h02]; exact even_two) =
      signSL K {i1, i2} (by rw [Finset.card_pair h12]; exact even_two) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_signSL, coe_signSL, coe_signSL, signMat,
      signMat, signMat, diagonal_mul_diagonal]
    congr 1
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hk0 : k = i0
    · subst hk0
      simp [h01, h02]
    · by_cases hk1 : k = i1
      · subst hk1
        simp [hk0, h12]
      · by_cases hk2 : k = i2
        · subst hk2
          simp [hk0, hk1]
        · simp [hk0, hk1, hk2]
  refine eq_bot_of_four_group (hsq _ _) (hsq _ _)
    (fun x hx => conj_mem_oddCoreIn hx (hsignmem _ _))
    (fun x hx => conj_mem_oddCoreIn hx (hsignmem _ _)) (hC h01) (hC h02) ?_
  rw [← map_mul, hprod]
  exact hC h12

end CFSG.ComponentClassification.Burgoyne.PSL
