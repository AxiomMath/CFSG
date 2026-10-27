module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CatalogueBProjectiveInvolution
  CatalogueBProjectiveCoordinates ProjectiveEigenspace
open scoped MatrixGroups

namespace OddProjectivePair

variable {K : Type*} [Field K] {n : ℕ}

theorem fin_two_eq_one_or_eq_neg_one (htwo : (2 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  have hs : M 0 0 + M 1 1 ≠ 0 := by
    intro hs
    apply htwo
    linear_combination M 0 0 * hs - h00 - hdet
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right hs
  have had : M 1 1 = M 0 0 := by
    have : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by linear_combination h00 - h11
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs)).symm
  have ha : M 0 0 * M 0 0 = 1 := by linear_combination h00 - M 1 0 * hb
  rcases mul_self_eq_one_iff.1 ha with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had, h]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had, h]

theorem restrict_eq_one_or_neg_one (htwo : (2 : K) ≠ 0) {A W : Submodule K (Fin n → K)}
    (hA2 : Module.finrank K A = 2) {x : GL (Fin n) K} (hx : x ∈ summandSpecialLinear A W)
    (hx2 : x * x = 1) :
    (∀ a ∈ A, (x : Matrix (Fin n) (Fin n) K) *ᵥ a = a) ∨
      ∀ a ∈ A, (x : Matrix (Fin n) (Fin n) K) *ᵥ a = -a := by
  obtain ⟨-, hA, hdet⟩ := hx
  set f := (mulVecLin (x : Matrix (Fin n) (Fin n) K)).restrict hA
  have hff : f * f = 1 := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    change (x : Matrix (Fin n) (Fin n) K) *ᵥ ((x : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K)) =
      a
    rw [mulVec_mulVec, ← Units.val_mul, hx2, Units.val_one, one_mulVec]
  set b := Module.finBasisOfFinrankEq K A hA2
  have hM : LinearMap.toMatrix b b f * LinearMap.toMatrix b b f = 1 := by
    rw [← LinearMap.toMatrix_mul, hff, LinearMap.toMatrix_one]
  have hMdet : (LinearMap.toMatrix b b f).det = 1 := by rw [LinearMap.det_toMatrix, hdet]
  rcases fin_two_eq_one_or_eq_neg_one htwo hM hMdet with h | h
  · left
    have hf1 : f = 1 := (LinearMap.toMatrix b b).injective (by rw [h, LinearMap.toMatrix_one])
    intro a ha
    exact congrArg Subtype.val (LinearMap.congr_fun hf1 ⟨a, ha⟩)
  · right
    intro a ha
    have h1 : f = Matrix.toLin b b (-1) := by rw [← h, Matrix.toLin_toMatrix]
    have h2 := LinearMap.congr_fun h1 ⟨a, ha⟩
    rw [map_neg, Matrix.toLin_one, LinearMap.neg_apply, LinearMap.id_apply] at h2
    exact congrArg Subtype.val h2

theorem eq_of_isCompl {A W : Submodule K (Fin n → K)} (hAW : IsCompl A W) {x y : GL (Fin n) K}
    (hA : ∀ a ∈ A, (x : Matrix (Fin n) (Fin n) K) *ᵥ a = (y : Matrix (Fin n) (Fin n) K) *ᵥ a)
    (hW : ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = (y : Matrix (Fin n) (Fin n) K) *ᵥ w) :
    x = y := by
  refine Units.ext (matrix_eq_of_mulVec_eq fun v => ?_)
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (hAW.sup_eq_top ▸ Submodule.mem_top : v ∈ A ⊔ W)
  rw [mulVec_add, mulVec_add, hA a ha, hW w hw]

theorem eq_of_mem_summandSpecialLinear_of_finrank_eq_two (htwo : (2 : K) ≠ 0)
    {A W : Submodule K (Fin n → K)} (hAW : IsCompl A W) (hA2 : Module.finrank K A = 2)
    {x y : GL (Fin n) K} (hx : x ∈ summandSpecialLinear A W) (hy : y ∈ summandSpecialLinear A W)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hneg : ∀ z : GL (Fin n) K, z ∈ summandSpecialLinear A W → z * z = 1 → z ≠ 1 →
      ∀ a ∈ A, (z : Matrix (Fin n) (Fin n) K) *ᵥ a = -a := by
    intro z hz hz2 hz1
    refine (restrict_eq_one_or_neg_one htwo hA2 hz hz2).resolve_left fun h => hz1 ?_
    exact eq_of_isCompl hAW (fun a ha => by rw [h a ha, Units.val_one, one_mulVec])
      (fun w hw => by rw [hz.1 w hw, Units.val_one, one_mulVec])
  exact eq_of_isCompl hAW (fun a ha => by rw [hneg x hx hx2 hx1 a ha, hneg y hy hy2 hy1 a ha])
    (fun w hw => by rw [hx.1 w hw, hy.1 w hw])

section Diagonal

variable {A W : Submodule K (Fin n → K)} (hAW : IsCompl A W) {r : ℕ} (b : Module.Basis (Fin r) K A)

@[expose] def summandDiagonalMap (d : Fin r → K) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  (Submodule.prodEquivOfIsCompl A W hAW).toLinearMap ∘ₗ
    ((Matrix.toLin b b (Matrix.diagonal d)).prodMap LinearMap.id) ∘ₗ
    (Submodule.prodEquivOfIsCompl A W hAW).symm.toLinearMap

theorem summandDiagonalMap_left (d : Fin r → K) (a : A) :
    summandDiagonalMap hAW b d a = (Matrix.toLin b b (Matrix.diagonal d) a : Fin n → K) := by
  simp [summandDiagonalMap]

theorem summandDiagonalMap_right (d : Fin r → K) (w : W) : summandDiagonalMap hAW b d w = w := by
  simp [summandDiagonalMap]

omit hAW in
theorem toLin_diagonal_apply_self (d : Fin r → K) (i : Fin r) :
    Matrix.toLin b b (Matrix.diagonal d) (b i) = d i • b i := by
  rw [Matrix.toLin_self]
  simp [Matrix.diagonal_apply]

theorem summandDiagonalMap_involutive (d : Fin r → K) (hd : ∀ i, d i * d i = 1) :
    Function.Involutive (summandDiagonalMap hAW b d) := by
  have hDD : ∀ x : A, Matrix.toLin b b (Matrix.diagonal d)
      (Matrix.toLin b b (Matrix.diagonal d) x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal,
      show (fun i => d i * d i) = fun _ => (1 : K) from funext hd, Matrix.diagonal_one,
      Matrix.toLin_one, LinearMap.id_apply]
  intro v
  simp only [summandDiagonalMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_apply, hDD]
  exact (Submodule.prodEquivOfIsCompl A W hAW).apply_symm_apply v

@[expose] def summandDiagonal (d : Fin r → K) (hd : ∀ i, d i * d i = 1) : GL (Fin n) K :=
  matrixActionEquiv.symm (LinearEquiv.ofInvolutive (summandDiagonalMap hAW b d)
    (summandDiagonalMap_involutive hAW b d hd))

theorem summandDiagonal_mulVec (d : Fin r → K) (hd : ∀ i, d i * d i = 1) (v : Fin n → K) :
    (summandDiagonal hAW b d hd : Matrix (Fin n) (Fin n) K) *ᵥ v = summandDiagonalMap hAW b d v :=
  matrixActionEquiv_symm_mulVec _ v

theorem summandDiagonal_mulVec_basis (d : Fin r → K) (hd : ∀ i, d i * d i = 1) (i : Fin r) :
    (summandDiagonal hAW b d hd : Matrix (Fin n) (Fin n) K) *ᵥ (b i : Fin n → K) =
      d i • (b i : Fin n → K) := by
  rw [summandDiagonal_mulVec, summandDiagonalMap_left, toLin_diagonal_apply_self,
    Submodule.coe_smul]

theorem summandDiagonal_mul_self (d : Fin r → K) (hd : ∀ i, d i * d i = 1) :
    summandDiagonal hAW b d hd * summandDiagonal hAW b d hd = 1 := by
  refine Units.ext (matrix_eq_of_mulVec_eq fun v => ?_)
  rw [Units.val_mul, ← mulVec_mulVec, summandDiagonal_mulVec, summandDiagonal_mulVec,
    summandDiagonalMap_involutive hAW b d hd v, Units.val_one, one_mulVec]

theorem summandDiagonal_mem (d : Fin r → K) (hd : ∀ i, d i * d i = 1) (hprod : ∏ i, d i = 1) :
    summandDiagonal hAW b d hd ∈ summandSpecialLinear A W := by
  have hA : ∀ a ∈ A, (summandDiagonal hAW b d hd : Matrix (Fin n) (Fin n) K) *ᵥ a ∈ A := by
    intro a ha
    rw [summandDiagonal_mulVec, summandDiagonalMap_left hAW b d ⟨a, ha⟩]
    exact Submodule.coe_mem _
  refine ⟨fun w hw => ?_, hA, ?_⟩
  · rw [summandDiagonal_mulVec]
    exact summandDiagonalMap_right hAW b d ⟨w, hw⟩
  · have hres : (mulVecLin (summandDiagonal hAW b d hd : Matrix (Fin n) (Fin n) K)).restrict hA =
        Matrix.toLin b b (Matrix.diagonal d) := by
      refine LinearMap.ext fun a => Subtype.ext ?_
      change (summandDiagonal hAW b d hd : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = _
      rw [summandDiagonal_mulVec, summandDiagonalMap_left]
    rw [hres, LinearMap.det_toLin, Matrix.det_diagonal, hprod]

end Diagonal

@[expose] def signs {r : ℕ} (p q : Fin r) : Fin r → K :=
  fun i => (if i = p then -1 else 1) * (if i = q then -1 else 1)

theorem signs_mul_self {r : ℕ} (p q : Fin r) (i : Fin r) :
    (signs p q i : K) * signs p q i = 1 := by
  simp only [signs]
  split_ifs <;> ring

theorem prod_signs {r : ℕ} (p q : Fin r) : ∏ i, (signs p q i : K) = 1 := by
  simp only [signs, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem signs_left {r : ℕ} {p q : Fin r} (hpq : p ≠ q) : (signs p q p : K) = -1 := by
  simp [signs, hpq]

theorem signs_right {r : ℕ} {p q : Fin r} (hpq : p ≠ q) : (signs p q q : K) = -1 := by
  simp [signs, hpq.symm]

theorem signs_of_ne {r : ℕ} {p q i : Fin r} (hp : i ≠ p) (hq : i ≠ q) : (signs p q i : K) = 1 := by
  simp [signs, hp, hq]

theorem commutator_eq_self_of_isQuasisimple {G : Type*} [Group G] {B : Subgroup G}
    (hB : CFSG.Assembly.IsQuasisimple B) : ⁅B, B⁆ = B := by
  have h := congrArg (Subgroup.map B.subtype) hB.1
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

theorem exists_ne_one_ne_one_ne {G : Type*} [Group G] {V : Subgroup G} (hV : Nat.card V = 4) :
    ∃ v ∈ V, ∃ v' ∈ V, v ≠ 1 ∧ v' ≠ 1 ∧ v ≠ v' := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite V
  have h3 : 2 < Fintype.card V := by rw [← Nat.card_eq_fintype_card, hV]; norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  have hne : ∀ x y : V, x ≠ y → (x : G) ≠ y := fun x y h h' => h (Subtype.ext h')
  by_cases ha : a = 1
  · subst ha
    exact ⟨b, b.2, c, c.2, (hne _ _ hab).symm, (hne _ _ hac).symm, hne _ _ hbc⟩
  by_cases hb : b = 1
  · subst hb
    exact ⟨a, a.2, c, c.2, hne _ _ ha, (hne _ _ hbc).symm, hne _ _ hac⟩
  exact ⟨a, a.2, b, b.2, hne _ _ ha, hne _ _ hb, hne _ _ hab⟩

theorem ne_bot_of_card_eq_four {G : Type*} [Group G] {V B : Subgroup G} (hVB : V ≤ B)
    (hV : Nat.card V = 4) : B ≠ ⊥ := by
  rintro rfl
  rw [le_bot_iff.1 hVB, Subgroup.card_bot] at hV
  omega

end OddProjectivePair

open OddProjectivePair

theorem odd_projective_linear_commuting_universal_pair_exclusion
    {K : Type*} [Field K] [Finite K] (htwo : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ B₁ B₂ : Subgroup (ProjGenLinGroup (Fin n) K),
      CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧ ⁅B₁, B₂⁆ = ⊥ ∧
      (∃ V : Subgroup (ProjGenLinGroup (Fin n) K), V ≤ B₁ ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4) ∧
      (∃ V : Subgroup (ProjGenLinGroup (Fin n) K), V ≤ B₂ ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4) ∧
      (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁
        (centralizer ({t} : Set (ProjGenLinGroup (Fin n) K)))) ∧
      (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂
        (centralizer ({s} : Set (ProjGenLinGroup (Fin n) K)))) := by
  rintro ⟨B₁, B₂, hq₁, hq₂, hcomm, ⟨V₁, hV₁, hV₁e, hV₁c⟩, ⟨V₂, hV₂, hV₂e, hV₂c⟩, h₁, h₂⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB₁p := commutator_eq_self_of_isQuasisimple hq₁
  have hB₂p := commutator_eq_self_of_isQuasisimple hq₂
  have hB₁ne := ne_bot_of_card_eq_four hV₁ hV₁c
  have hB₂ne := ne_bot_of_card_eq_four hV₂ hV₂c
  have hB₁B₂ : B₁ ≤ centralizer (B₂ : Set (ProjGenLinGroup (Fin n) K)) :=
    commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hB₂B₁ : B₂ ≤ centralizer (B₁ : Set (ProjGenLinGroup (Fin n) K)) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hcomm)
  set B₁hat := ⁅B₁.comap (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K),
    B₁.comap (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K)⁆
  have hmk₁ : ∀ g ∈ B₁hat, ProjGenLinGroup.mk g ∈ B₁ := fun g hg =>
    commutator_le_self (B₁.comap ProjGenLinGroup.mk) hg
  obtain ⟨t, htV, -, -, ht1, -, -⟩ := exists_ne_one_ne_one_ne hV₂c
  have ht2 : t ^ 2 = 1 := by
    have := hV₂e
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₂) t htV
  have htB₂ : t ∈ B₂ := hV₂ htV
  obtain ⟨T, hT⟩ := ProjGenLinGroup.mk_surjective t
  have hC₁ := h₁ t htB₂ (orderOf_eq_prime ht2 ht1)
  have hBcomp₁ := (isComponentOf_iff_isComponent_subgroupOf hC₁.1).1 hC₁
  have hmap₁ : ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype :
      Subgroup (ProjGenLinGroup (Fin n) K)) = B₁ := map_subgroupOf_eq_of_le hC₁.1
  obtain ⟨lam, -, hcompl, hAne, hWne, A, W, hAW, hdimA, hBhat, ⟨e, he⟩, -⟩ :=
    odd_projective_linear_local_component_supported_on_eigenspace htwo hn ht1 ht2 hT hBcomp₁
      (Q := B₂) (by rw [hmap₁]; exact hB₂B₁) hB₂ne hB₂p (Bhat := B₁hat) (by rw [hmap₁]) rfl
  have hAWc : IsCompl A W := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcompl
    · exact hcompl.symm
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hWne
    · exact hAne
  have hmemB : ∀ g : GL (Fin n) K, g ∈ summandSpecialLinear A W → g ∈ B₁hat := fun g hg => by
    rw [← SetLike.mem_coe, hBhat]
    exact hg
  have hr2 : Module.finrank K A ≠ 2 := by
    intro hr
    obtain ⟨v, hv, v', hv', hv1, hv'1, hvv'⟩ := exists_ne_one_ne_one_ne hV₁c
    have hsq : ∀ w ∈ V₁, w * w = 1 := fun w hw => by
      have := hV₁e
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₁) w hw
    have hlift : ∀ w ∈ V₁, ∃ x : B₁hat, ProjGenLinGroup.mk (x : GL (Fin n) K) = w ∧
        (x : GL (Fin n) K) * x = 1 := by
      intro w hw
      set y : B₁.subgroupOf (centralizer {t}) :=
        ⟨⟨w, hC₁.1 (hV₁ hw)⟩, by rw [mem_subgroupOf]; exact hV₁ hw⟩
      refine ⟨e.symm y, ?_, ?_⟩
      · rw [← he, MulEquiv.apply_symm_apply]
      · have hy : y * y = 1 := Subtype.ext (Subtype.ext (hsq w hw))
        rw [← Subgroup.coe_mul, ← map_mul, hy, map_one, Subgroup.coe_one]
    obtain ⟨x, hxv, hx2⟩ := hlift v hv
    obtain ⟨x', hx'v, hx'2⟩ := hlift v' hv'
    have hxS : (x : GL (Fin n) K) ∈ summandSpecialLinear A W := by
      rw [← hBhat]
      exact x.2
    have hx'S : (x' : GL (Fin n) K) ∈ summandSpecialLinear A W := by
      rw [← hBhat]
      exact x'.2
    have hx1 : (x : GL (Fin n) K) ≠ 1 := fun h => hv1 (by rw [← hxv, h, map_one])
    have hx'1 : (x' : GL (Fin n) K) ≠ 1 := fun h => hv'1 (by rw [← hx'v, h, map_one])
    apply hvv'
    rw [← hxv, ← hx'v,
      eq_of_mem_summandSpecialLinear_of_finrank_eq_two htwo hAWc hr hxS hx'S hx2 hx'2 hx1 hx'1]
  have hr3 : 3 ≤ Module.finrank K A := by omega
  set r := Module.finrank K A
  let b : Module.Basis (Fin r) K A := Module.finBasis K A
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  set i₂ : Fin r := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h21 : i₂ ≠ i₁ := by simp [i₂, i₁, Fin.ext_iff]
  have hSS := summandDiagonal_mem hAWc b _ (signs_mul_self i₀ i₁) (prod_signs i₀ i₁)
  have hgS := summandDiagonal_mem hAWc b _ (signs_mul_self i₀ i₂) (prod_signs i₀ i₂)
  set S := summandDiagonal hAWc b (signs i₀ i₁) (signs_mul_self i₀ i₁)
  set g := summandDiagonal hAWc b (signs i₀ i₂) (signs_mul_self i₀ i₂)
  have hSmem : S ∈ B₁hat := hmemB S hSS
  have hgmem : g ∈ B₁hat := hmemB g hgS
  have hS0 : (S : Matrix (Fin n) (Fin n) K) *ᵥ (b i₀ : Fin n → K) = -(b i₀ : Fin n → K) := by
    rw [summandDiagonal_mulVec_basis, signs_left h01, neg_one_smul]
  have hS2 : (S : Matrix (Fin n) (Fin n) K) *ᵥ (b i₂ : Fin n → K) = (b i₂ : Fin n → K) := by
    rw [summandDiagonal_mulVec_basis, signs_of_ne h02.symm h21, one_smul]
  have hg2 : (g : Matrix (Fin n) (Fin n) K) *ᵥ (b i₂ : Fin n → K) = -(b i₂ : Fin n → K) := by
    rw [summandDiagonal_mulVec_basis, signs_right h02, neg_one_smul]
  have hneg : ∀ v : Fin n → K, -v = v → v = 0 := by
    intro v hv
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hv]
      exact neg_add_cancel v
    exact (smul_eq_zero.1 h2v).resolve_left htwo
  have hb0 : ∀ i, (b i : Fin n → K) ≠ 0 := fun i h => b.ne_zero i (Subtype.ext h)
  set s := ProjGenLinGroup.mk S with hsdef
  have hsB₁ : s ∈ B₁ := hmk₁ S hSmem
  have hs2 : s ^ 2 = 1 := by
    rw [hsdef, ← map_pow, sq, summandDiagonal_mul_self, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    have hS1 := eq_one_of_mk_eq_one_of_fix hW0 h hSS.1
    apply hb0 i₀
    apply hneg
    rw [← hS0, hS1, Units.val_one, one_mulVec]
  have hC₂ := h₂ s hsB₁ (orderOf_eq_prime hs2 hs1)
  have hBcomp₂ := (isComponentOf_iff_isComponent_subgroupOf hC₂.1).1 hC₂
  have hmap₂ : ((B₂.subgroupOf (centralizer {s})).map (centralizer {s}).subtype :
      Subgroup (ProjGenLinGroup (Fin n) K)) = B₂ := map_subgroupOf_eq_of_le hC₂.1
  obtain ⟨lam', -, -, -, -, A', W', hA'W', hdimA', -, -, hfix'⟩ :=
    odd_projective_linear_local_component_supported_on_eigenspace htwo hn hs1 hs2 hsdef.symm
      hBcomp₂ (Q := B₁) (by rw [hmap₂]; exact hB₁B₂) hB₁ne hB₁p
      (Bhat := ⁅B₂.comap ProjGenLinGroup.mk, B₂.comap ProjGenLinGroup.mk⁆) (by rw [hmap₂]) rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : K, A' = (splitMatrixOperator S).eigenspace μ := by
    rcases hA'W' with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hA'ne : A' ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimA'
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA'ne
  have hμ1 : μ = 1 := by
    have h1 := hfix' S hSmem a ha
    rw [hμ] at ha
    have h2 := Module.End.mem_eigenspace_iff.1 ha
    change (S : Matrix (Fin n) (Fin n) K) *ᵥ a = μ • a at h2
    rw [h1] at h2
    have h3 : (μ - 1) • a = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right ha0)
  have hb2A' : (b i₂ : Fin n → K) ∈ A' := by
    rw [hμ, hμ1]
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [one_smul]
    exact hS2
  apply hb0 i₂
  apply hneg
  rw [← hg2, hfix' g hgmem _ hb2A']

end CFSG.LocalAnalysis.ComponentInitial
