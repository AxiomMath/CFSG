module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryTransvections
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Permutation

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace FourUnitary

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

section Field

variable {F : Type*} [Field F] (hF : UnitaryFieldData 2 1 F)

include hF in
theorem sq_add_self_add_one {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have h3 := pow_three_eq_one hF hω0
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)

include hF in
theorem eq_zero_or_one_or_of_ne {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (s : F) :
    s = 0 ∨ s = 1 ∨ s = ω ∨ s = ω ^ 2 := by
  by_cases hs0 : s = 0
  · exact Or.inl hs0
  by_cases hs1 : s = 1
  · exact Or.inr (Or.inl hs1)
  have hs := sq_add_self_add_one hF hs0 hs1
  have hω := sq_add_self_add_one hF hω0 hω1
  have h : (s - ω) * (s + ω + 1) = 0 := by linear_combination hs - hω
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h - hω)))

include hF in
theorem exists_ne_zero_ne_one : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  obtain ⟨ω, hω⟩ := hF.exists_bar_ne
  rw [bar_eq_sq] at hω
  refine ⟨ω, fun h => hω ?_, fun h => hω ?_⟩ <;> simp [h]

include hF in
theorem natCard_units : Nat.card Fˣ = 3 := by
  have := hF.finite
  rw [Nat.card_units, hF.card]
  norm_num

end Field

section Basis

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] {ι : Type*}
  [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem eq_smul_basis_of_repr (e : Basis ι F W) {z : W} {i : ι}
    (hz : ∀ l, l ≠ i → e.repr z l = 0) : z = e.repr z i • e i := by
  refine e.ext_elem fun l => ?_
  rw [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases hl : i = l
  · subst hl
    rw [ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hl, mul_zero, hz l (Ne.symm hl)]

omit [Fintype ι] in
theorem repr_basis_of_ne (e : Basis ι F W) {i l : ι} (hl : l ≠ i) : e.repr (e i) l = 0 := by
  rw [Basis.repr_self, Finsupp.single_apply, ite_eq_right (Ne.symm hl)]

theorem diag_apply_basis (e : Basis ι F W) (c : ι → F) (l : ι) :
    Matrix.toLin e e (Matrix.diagonal c) (e l) = c l • e l := by
  rw [Matrix.toLin_self, Finset.sum_eq_single l]
  · rw [Matrix.diagonal_apply_eq]
  · intro m _ hm
    rw [Matrix.diagonal_apply_ne _ hm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem repr_diag (e : Basis ι F W) (c : ι → F) (y : W) (l : ι) :
    e.repr (Matrix.toLin e e (Matrix.diagonal c) y) l = c l * e.repr y l := by
  rw [Matrix.toLin_apply, Basis.repr_sum_self, Matrix.mulVec_diagonal]

theorem perm_apply_basis (e : Basis ι F W) (σ : Equiv.Perm ι) (l : ι) :
    Matrix.toLin e e (σ.permMatrix F) (e l) = e (σ.symm l) := by
  rw [Matrix.toLin_self, Finset.sum_eq_single (σ.symm l)]
  · simp [PEquiv.toMatrix_apply]
  · intro m _ hm
    have hm' : σ m ≠ l := fun h => hm (by rw [← h, Equiv.symm_apply_apply])
    simp [PEquiv.toMatrix_apply, hm']
  · intro h
    exact absurd (Finset.mem_univ _) h

end Basis

section SpecialUnitary

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

theorem isometry_of_basis {ι : Type*} (e : Basis ι F W) {f : W →ₗ[F] W}
    (h : ∀ i j, B (f (e i)) (f (e j)) = B (e i) (e j)) (x y : W) : B (f x) (f y) = B x y := by
  have key : (B.comp f).compl₂ f = B := LinearMap.ext_basis e e fun i j => h i j
  exact LinearMap.congr_fun₂ key x y

theorem exists_mem_specialUnitary [Module.Finite F W] {f : W →ₗ[F] W}
    (hiso : ∀ x y, B (f x) (f y) = B x y) (hdet : LinearMap.det f = 1) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (g : W →ₗ[F] W) = f := by
  have hu : IsUnit f := (LinearMap.isUnit_iff_isUnit_det f).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, hu.unit_spec]
  exact ⟨hiso, hdet⟩

theorem smul_isometry {s : F} (hs : s ≠ 0) (x y : W) : B (s • x) (s • y) = B x y := by
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    bar_mul_self hF hs, one_mul]

theorem exists_scalar_mem [Module.Finite F W] {s : F} (hs : s ≠ 0) (hsd : s ^ finrank F W = 1) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (g : W →ₗ[F] W) = s • LinearMap.id := by
  refine exists_mem_specialUnitary (fun x y => ?_) ?_
  · exact smul_isometry hs x y
  · rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hsd]

end SpecialUnitary

section Commuting

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

theorem exists_smul_of_commute [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : 3 ≤ finrank F W) (φ : W →+ W)
    (hφ : ∀ g ∈ sesqSpecialUnitaryGroup B, ∀ x,
      φ ((g : W →ₗ[F] W) x) = (g : W →ₗ[F] W) (φ x)) :
    ∃ s : F, ∀ x, φ x = s • x := by
  classical
  obtain ⟨e, he⟩ := hF.exists_orthonormal_basis hB hBl
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hF
  have hω3 := pow_three_eq_one hF hω0
  have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  obtain ⟨c, hc⟩ : ∃ c : Fin (finrank F W) → Fin (finrank F W) → Fin (finrank F W) → F,
      ∀ i j, c i j = Function.update (Function.update (1 : Fin (finrank F W) → F) i ω) j (ω ^ 2) :=
    ⟨_, fun _ _ => rfl⟩
  have hci : ∀ i j, j ≠ i → c i j i = ω := by
    intro i j hji
    rw [hc, Function.update_of_ne (Ne.symm hji), Function.update_self]
  have hcj : ∀ i j, c i j j = ω ^ 2 := by
    intro i j
    rw [hc, Function.update_self]
  have hcl : ∀ i j l, l ≠ i → l ≠ j → c i j l = 1 := by
    intro i j l hli hlj
    rw [hc, Function.update_of_ne hlj, Function.update_of_ne hli, Pi.one_apply]
  have hc0 : ∀ i j l, c i j l ≠ 0 := by
    intro i j l
    by_cases hlj : l = j
    · rw [hlj, hcj]
      exact hω20
    · by_cases hli : l = i
      · rw [hli, hci i j (Ne.symm (hli ▸ hlj))]
        exact hω0
      · rw [hcl i j l hli hlj]
        exact one_ne_zero
  have hD : ∀ i j, j ≠ i → ∃ g ∈ sesqSpecialUnitaryGroup B,
      (g : W →ₗ[F] W) = Matrix.toLin e e (Matrix.diagonal (c i j)) := by
    intro i j hji
    refine exists_mem_specialUnitary (isometry_of_basis e fun a b => ?_) ?_
    · rw [diag_apply_basis, diag_apply_basis, LinearMap.map_smulₛₗ₂, map_smul, he]
      split_ifs with hab
      · subst hab
        rw [smul_eq_mul, smul_eq_mul, mul_one, bar_mul_self hF (hc0 i j a)]
      · rw [smul_zero, smul_zero]
    · rw [LinearMap.det_toLin, Matrix.det_diagonal, hc,
        Finset.prod_update_of_mem (Finset.mem_univ j),
        Finset.prod_update_of_mem (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, by simpa using hji.symm⟩)]
      simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
      linear_combination hω3
  have hsupp : ∀ i x, (∀ l, l ≠ i → e.repr x l = 0) → ∀ l, l ≠ i → e.repr (φ x) l = 0 := by
    intro i x hx
    have h2 : 1 < (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 h2
    rw [Finset.mem_erase] at hj hk
    have hmoved : ∀ j, j ≠ i → ∀ l, l ≠ i → l ≠ j → e.repr (φ x) l = 0 := by
      intro j hji l hli hlj
      obtain ⟨g, hg, hgD⟩ := hD i j hji
      have hxy : x = (g : W →ₗ[F] W) ((ω - 1)⁻¹ • x) - (ω - 1)⁻¹ • x := by
        refine e.ext_elem fun m => ?_
        rw [map_sub, Finsupp.sub_apply, hgD, repr_diag, map_smul, Finsupp.smul_apply,
          smul_eq_mul]
        by_cases hmi : m = i
        · subst hmi
          rw [hci m j hji, show ω * ((ω - 1)⁻¹ * e.repr x m) - (ω - 1)⁻¹ * e.repr x m =
            (ω - 1) * (ω - 1)⁻¹ * e.repr x m by ring, mul_inv_cancel₀ (sub_ne_zero.2 hω1),
            one_mul]
        · rw [hx m hmi]
          ring
      rw [hxy, map_sub, hφ g hg, map_sub, Finsupp.sub_apply, hgD, repr_diag,
        hcl i j l hli hlj, one_mul, sub_self]
    intro l hli
    by_cases hlj : l = j
    · exact hmoved k hk.1 l hli (by rw [hlj]; exact hjk)
    · exact hmoved j hj.1 l hli hlj
  have hω : ∀ i x, (∀ l, l ≠ i → e.repr x l = 0) → φ (ω • x) = ω • φ x := by
    intro i x hx
    obtain ⟨j, hji⟩ : ∃ j : Fin (finrank F W), j ≠ i := by
      by_cases hi : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [hi]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm hi⟩
    obtain ⟨g, hg, hgD⟩ := hD i j hji
    have hDz : ∀ z, (∀ l, l ≠ i → e.repr z l = 0) → (g : W →ₗ[F] W) z = ω • z := by
      intro z hz
      refine e.ext_elem fun m => ?_
      rw [hgD, repr_diag, map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hmi : m = i
      · subst hmi
        rw [hci m j hji]
      · rw [hz m hmi, mul_zero, mul_zero]
    rw [← hDz x hx, hφ g hg, hDz _ (hsupp i x hx)]
  have hlin : ∀ i x, (∀ l, l ≠ i → e.repr x l = 0) → ∀ a : F, φ (a • x) = a • φ x := by
    intro i x hx a
    rcases eq_zero_or_one_or_of_ne hF hω0 hω1 a with rfl | rfl | rfl | rfl
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
    · exact hω i x hx
    · have hωx : ∀ l, l ≠ i → e.repr (ω • x) l = 0 := fun l hl => by
        rw [map_smul, Finsupp.smul_apply, hx l hl, smul_zero]
      rw [sq, mul_smul, hω i _ hωx, hω i x hx, mul_smul]
  obtain ⟨s, hs⟩ : ∃ s : Fin (finrank F W) → F, ∀ i, s i = e.repr (φ (e i)) i :=
    ⟨_, fun _ => rfl⟩
  have hφe : ∀ i, φ (e i) = s i • e i := fun i => by
    rw [hs]
    exact eq_smul_basis_of_repr e (hsupp i (e i) fun l hl => repr_basis_of_ne e hl)
  have hseq : ∀ i j, s i = s j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨g, hg, hgP⟩ := exists_mem_specialUnitary (B := B)
      (f := Matrix.toLin e e ((Equiv.swap i j).permMatrix F))
      (isometry_of_basis e fun a b => by
        rw [perm_apply_basis, perm_apply_basis, he, he]
        simp only [Equiv.apply_eq_iff_eq])
      (by
        rw [LinearMap.det_toLin, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
        exact neg_eq_self hF 1)
    have h1 : φ (e j) = s i • e j := by
      have hPi : (g : W →ₗ[F] W) (e i) = e j := by
        rw [hgP, perm_apply_basis, Equiv.symm_swap, Equiv.swap_apply_left]
      rw [← hPi, hφ g hg, hφe i, map_smul, hPi]
    have h2 : (s i - s j) • e j = 0 := by
      rw [sub_smul, ← h1, ← hφe j, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (e.ne_zero j))
  refine ⟨s ⟨0, by omega⟩, fun x => ?_⟩
  have hx := e.sum_repr x
  calc φ x = φ (∑ l, e.repr x l • e l) := by rw [hx]
    _ = ∑ l, s ⟨0, by omega⟩ • (e.repr x l • e l) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hlin l (e l) (fun m hm => repr_basis_of_ne e hm), hφe l, hseq l ⟨0, by omega⟩,
        smul_comm]
    _ = s ⟨0, by omega⟩ • x := by rw [← Finset.smul_sum, hx]

end Commuting

end FourUnitary

open FourUnitary Module CFSG.LocalAnalysis.ComponentInitial in
theorem four_element_special_unitary_binary_scalar_centralizer {F : Type*} [Field F]
    (hF : UnitaryFieldData 2 1 F) {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hd : 3 ≤ finrank F W) :
    (∀ φ : W →+ W, (∀ g ∈ sesqSpecialUnitaryGroup B, ∀ x,
        φ ((g : W →ₗ[F] W) x) = (g : W →ₗ[F] W) (φ x)) ↔ ∃ s : F, ∀ x, φ x = s • x) ∧
    (∀ φ : W ≃+ W, (∀ g ∈ sesqSpecialUnitaryGroup B, ∀ x,
        φ ((g : W →ₗ[F] W) x) = (g : W →ₗ[F] W) (φ x)) ↔ ∃ s : F, s ≠ 0 ∧ ∀ x, φ x = s • x) ∧
    (∀ g : LinearMap.GeneralLinearGroup F W,
      (g ∈ sesqSpecialUnitaryGroup B ∧ ∀ g' ∈ sesqSpecialUnitaryGroup B, g * g' = g' * g) ↔
        ∃ s : F, s ≠ 0 ∧ s ^ finrank F W = 1 ∧ (g : W →ₗ[F] W) = s • LinearMap.id) ∧
    Nat.card (Subgroup.center (sesqSpecialUnitaryGroup B)) = Nat.gcd (finrank F W) 3 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x : W, x ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F)).1 (by omega)
  have hEnd : ∀ φ : W →+ W, (∀ g ∈ sesqSpecialUnitaryGroup B, ∀ x,
      φ ((g : W →ₗ[F] W) x) = (g : W →ₗ[F] W) (φ x)) ↔ ∃ s : F, ∀ x, φ x = s • x := by
    intro φ
    refine ⟨exists_smul_of_commute hB hBl hd φ, ?_⟩
    rintro ⟨s, hs⟩ g _ x
    rw [hs, hs, map_smul]
  have hZ : ∀ g : LinearMap.GeneralLinearGroup F W,
      (g ∈ sesqSpecialUnitaryGroup B ∧ ∀ g' ∈ sesqSpecialUnitaryGroup B, g * g' = g' * g) ↔
        ∃ s : F, s ≠ 0 ∧ s ^ finrank F W = 1 ∧ (g : W →ₗ[F] W) = s • LinearMap.id := by
    intro g
    constructor
    · rintro ⟨hg, hcomm⟩
      obtain ⟨s, hs⟩ := (hEnd (g : W →ₗ[F] W).toAddMonoidHom).1 fun g' hg' x => by
        have h := congrArg (fun k : LinearMap.GeneralLinearGroup F W => (k : W →ₗ[F] W) x)
          (hcomm g' hg')
        exact h
      have hgs : (g : W →ₗ[F] W) = s • LinearMap.id := LinearMap.ext fun x => hs x
      have hdet := ((mem_sesqSpecialUnitaryGroup.1 hg).2)
      rw [hgs, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_pow (by omega)] at hdet
        exact zero_ne_one hdet
      exact ⟨s, hs0, hdet, hgs⟩
    · rintro ⟨s, hs0, hsd, hgs⟩
      refine ⟨?_, fun g' _ => Units.ext (LinearMap.ext fun x => ?_)⟩
      · rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, hgs, LinearMap.det_smul,
          LinearMap.det_id, mul_one]
        exact ⟨fun x y => smul_isometry hs0 x y, hsd⟩
      · simp only [Units.val_mul, Module.End.mul_apply, hgs, LinearMap.smul_apply,
          LinearMap.id_apply, map_smul]
  refine ⟨hEnd, fun φ => ⟨fun hφ => ?_, ?_⟩, hZ, ?_⟩
  · obtain ⟨s, hs⟩ := (hEnd φ.toAddMonoidHom).1 hφ
    refine ⟨s, fun hs0 => hx₀ (φ.injective ?_), hs⟩
    rw [map_zero]
    exact (hs x₀).trans (by rw [hs0, zero_smul])
  · rintro ⟨s, -, hs⟩ g _ x
    rw [hs, hs, map_smul]
  classical
  have := hF.finite
  set d := finrank F W
  let K := (powMonoidHom d : Fˣ →* Fˣ).ker
  have hscal : ∀ u : K, ∃ g ∈ sesqSpecialUnitaryGroup B,
      (g : W →ₗ[F] W) = ((u : Fˣ) : F) • LinearMap.id := by
    intro u
    have hu : ((u : Fˣ) : F) ^ d = 1 := by
      have := u.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    exact exists_scalar_mem (B := B) (u : Fˣ).ne_zero hu
  choose gs hgs hgsv using hscal
  have hcen : ∀ u : K, (⟨gs u, hgs u⟩ : sesqSpecialUnitaryGroup B) ∈
      Subgroup.center (sesqSpecialUnitaryGroup B) := by
    intro u
    rw [Subgroup.mem_center_iff]
    intro g'
    have h := ((hZ (gs u)).2 ⟨_, (u : Fˣ).ne_zero, by
      have := u.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one], hgsv u⟩).2 g' g'.2
    exact Subtype.ext h.symm
  let f : K → Subgroup.center (sesqSpecialUnitaryGroup B) := fun u => ⟨⟨gs u, hgs u⟩, hcen u⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u u' huu => ?_, fun z => ?_⟩
    · have h := congrArg (fun z : Subgroup.center (sesqSpecialUnitaryGroup B) =>
        (((z : sesqSpecialUnitaryGroup B) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) x₀) huu
      simp only [f, hgsv, LinearMap.smul_apply, LinearMap.id_apply] at h
      exact Subtype.ext (Units.ext (smul_left_injective F hx₀ h))
    · obtain ⟨⟨g, hg⟩, hz⟩ := z
      have hcomm : ∀ g' ∈ sesqSpecialUnitaryGroup B, g * g' = g' * g := by
        intro g' hg'
        have := (Subgroup.mem_center_iff.1 hz) ⟨g', hg'⟩
        exact (congrArg Subtype.val this).symm
      obtain ⟨s, hs0, hsd, hgs'⟩ := (hZ g).1 ⟨hg, hcomm⟩
      refine ⟨⟨Units.mk0 s hs0, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, powMonoidHom_apply]
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hsd, Units.val_one])
      · refine Subtype.ext (Subtype.ext (Units.ext ?_))
        simp only [f]
        rw [hgsv, hgs', Units.val_mk0]
  rw [← Nat.card_eq_of_bijective f hf, IsCyclic.card_powMonoidHom_ker, natCard_units hF,
    Nat.gcd_comm]

end CFSG.LocalAnalysis.GorensteinLyons
