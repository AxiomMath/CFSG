module

public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport
public import Mathlib.LinearAlgebra.Basis.Bilinear

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

universe u

variable {p f : ℕ} {K : Type*} [Field K]

section Chains

variable {V : Type u} [AddCommGroup V] [Module K V]

@[expose] def IsIsotropicChain {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K) (k : ℕ)
    (W : ℕ → Submodule K V) : Prop :=
  (∀ i ≤ k, Module.finrank K (W i) = i) ∧ (∀ i < k, W i ≤ W (i + 1)) ∧
    ∀ i ≤ k, ∀ x ∈ W i, ∀ y ∈ W i, B x y = 0

@[expose] def aSpan {r ε : ℕ} (w : HypIndex r ε → V) (i : ℕ) : Submodule K V :=
  Submodule.span K ((fun j : Fin r => w (.inl j)) '' {j | (j : ℕ) < i})

theorem aSpan_zero {r ε : ℕ} (w : HypIndex r ε → V) : aSpan w 0 = (⊥ : Submodule K V) := by
  simp [aSpan]

theorem IsIsotropicChain.le {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {k : ℕ}
    {W : ℕ → Submodule K V} (hW : IsIsotropicChain B k W) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ k) : W i ≤ W j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hW.2.1 j (by omega))

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem eq_span_sup_inf_orthogonal {a b : V} (hba : B b a = 1) {W : Submodule K V}
    (ha : a ∈ W) (hW : ∀ x ∈ W, B a x = 0) :
    W = K ∙ a ⊔ (W ⊓ (Submodule.span K {a, b}).orthogonalBilin B) := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr ha) inf_le_left)
  have hmem : x - B b x • a ∈ (Submodule.span K {a, b}).orthogonalBilin B := by
    rw [Submodule.mem_orthogonalBilin]
    intro z hz
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp [hW x hx, hW a ha, hba]
  rw [show x = B b x • a + (x - B b x • a) by abel]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
    ⟨W.sub_mem hx (W.smul_mem _ ha), hmem⟩

theorem span_inf_orthogonal_eq_bot {a b : V} (hba : B b a = 1) :
    K ∙ a ⊓ (Submodule.span K {a, b}).orthogonalBilin B = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
  have hb := (Submodule.mem_orthogonalBilin.mp hx2) b (Submodule.subset_span (by simp))
  rw [map_smul, hba, smul_eq_mul, mul_one] at hb
  rw [hb, zero_smul]
  exact Submodule.zero_mem _

theorem finrank_inf_orthogonal_add_one [FiniteDimensional K V] {a b : V} (ha0 : a ≠ 0)
    (hba : B b a = 1) {W : Submodule K V} (ha : a ∈ W) (hW : ∀ x ∈ W, B a x = 0) :
    Module.finrank K ↥(W ⊓ (Submodule.span K {a, b}).orthogonalBilin B) + 1 =
      Module.finrank K W := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a)
    (W ⊓ (Submodule.span K {a, b}).orthogonalBilin B)
  have h0 : K ∙ a ⊓ (W ⊓ (Submodule.span K {a, b}).orthogonalBilin B) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (span_inf_orthogonal_eq_bot hba).le)
  rw [← eq_span_sup_inf_orthogonal hba ha hW, h0, finrank_bot, finrank_span_singleton ha0] at h1
  omega

omit [Module K V] in
theorem finrank_comap_subtype [Module K V] (U X : Submodule K V) :
    Module.finrank K ↥(X.comap U.subtype) = Module.finrank K ↥(X ⊓ U) := by
  rw [(Submodule.equivMapOfInjective U.subtype U.injective_subtype _).finrank_eq,
    Submodule.map_comap_subtype, inf_comm]

end Chains

theorem exists_hypBasis_of_isotropicChain (h : UnitaryFieldData p f K) (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft → ∀ {r ε : ℕ}, ε ≤ 1 →
      Module.finrank K V = 2 * r + ε → ∀ W : ℕ → Submodule K V, IsIsotropicChain B k W →
      k ≤ r ∧ ∃ w : Module.Basis (HypIndex r ε) K V,
        (∀ x y, B (w x) (w y) = hypGram r ε K x y) ∧ ∀ i ≤ k, W i = aSpan w i := by
  induction k with
  | zero =>
    intro V _ _ _ B hB hBl r ε _ hn W hW
    obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn
    refine ⟨Nat.zero_le r, w, hw, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [aSpan_zero, ← Submodule.finrank_eq_zero]
    exact hW.1 0 le_rfl
  | succ k ih =>
    intro V _ _ _ B hB hBl r ε hε hn W hW
    obtain ⟨hdim, hle, hiso⟩ := hW
    obtain ⟨a, ha1, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W 1) (by
      intro h0
      have := hdim 1 (by omega)
      rw [h0, finrank_bot] at this
      exact zero_ne_one this)
    have haW : ∀ i, 1 ≤ i → i ≤ k + 1 → a ∈ W i := fun i hi hik =>
      IsIsotropicChain.le ⟨hdim, hle, hiso⟩ hi hik ha1
    have haa : B a a = 0 := hiso 1 (by omega) a ha1 a ha1
    obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 haa
    obtain ⟨hH2, -, -, hUsep, hUdim⟩ := hsplit b hab hbb
    have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
    set U := (Submodule.span K {a, b}).orthogonalBilin B with hU
    have h2 : 2 ≤ Module.finrank K V := hH2 ▸ Submodule.finrank_le _
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hW' : IsIsotropicChain (B.domRestrict₁₂ U U) k
        (fun i => (W (i + 1)).comap U.subtype) := by
      refine ⟨fun i hi => ?_, fun i hi => Submodule.comap_mono (hle (i + 1) (by omega)),
        fun i hi x hx y hy => hiso (i + 1) (by omega) x hx y hy⟩
      have := finrank_inf_orthogonal_add_one ha0 hba (haW (i + 1) (by omega) (by omega))
        (fun x hx => hiso (i + 1) (by omega) a (haW (i + 1) (by omega) (by omega)) x hx)
      rw [hdim (i + 1) (by omega), ← hU] at this
      change Module.finrank K ↥((W (i + 1)).comap U.subtype) = i
      rw [finrank_comap_subtype]
      omega
    obtain ⟨hkr, w', hw', hspan'⟩ := ih (hB.domRestrict U) hUsep (r := r) hε
      (by rw [hUdim, hn]; omega) _ hW'
    have haU : ∀ x : U, B a x = 0 := fun x =>
      (Submodule.mem_orthogonalBilin.mp x.2) a (Submodule.subset_span (by simp))
    have hbU : ∀ x : U, B b x = 0 := fun x =>
      (Submodule.mem_orthogonalBilin.mp x.2) b (Submodule.subset_span (by simp))
    have hUa : ∀ x : U, B x a = 0 := fun x => by rw [← hB.eq a x, haU, map_zero]
    have hUb : ∀ x : U, B x b = 0 := fun x => by rw [← hB.eq b x, hbU, map_zero]
    have hw'' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y := fun x y => by
      rw [← hw' x y, LinearMap.domRestrict₁₂_apply]
    let v : HypIndex (r + 1) ε → V
      | .inl i => Fin.cases a (fun j => (w' (.inl j) : V)) i
      | .inr (.inl l) => (w' (.inr (.inl l)) : V)
      | .inr (.inr i) => Fin.cases b (fun j => (w' (.inr (.inr j)) : V)) i
    have hv : ∀ x y, B (v x) (v y) = hypGram (r + 1) ε K x y := by
      intro x y
      rcases x with i | l | i <;> rcases y with j | m | j <;>
        [cases i using Fin.cases <;> cases j using Fin.cases;
         cases i using Fin.cases;
         cases i using Fin.cases <;> cases j using Fin.cases;
         cases j using Fin.cases;
         skip;
         cases j using Fin.cases;
         cases i using Fin.cases <;> cases j using Fin.cases;
         cases i using Fin.cases;
         cases i using Fin.cases <;> cases j using Fin.cases] <;>
        simp [v, haa, hbb, hab, hba, haU, hbU, hUa, hUb, hw'', Fin.succ_ne_zero,
          (Fin.succ_ne_zero _).symm]
    refine ⟨by omega, basisOfHypGram v hv hn, fun x y => by rw [coe_basisOfHypGram, hv],
      fun i hi => ?_⟩
    rw [coe_basisOfHypGram]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [aSpan_zero, ← Submodule.finrank_eq_zero]
      exact hdim 0 (Nat.zero_le _)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have himage : (fun l : Fin (r + 1) => v (.inl l)) '' {l | (l : ℕ) < j + 1} =
        insert a (U.subtype '' ((fun m : Fin r => w' (.inl m)) '' {m | (m : ℕ) < j})) := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨m, rfl⟩
        · exact Set.mem_insert _ _
        · refine Set.mem_insert_of_mem _ ⟨w' (.inl m), ⟨m, ?_, rfl⟩, rfl⟩
          have hl' : ((Fin.succ m : Fin (r + 1)) : ℕ) < j + 1 := hl
          rw [Fin.val_succ] at hl'
          change (m : ℕ) < j
          omega
      · rintro (rfl | ⟨_, ⟨m, hm, rfl⟩, rfl⟩)
        · exact ⟨0, Nat.succ_pos j, rfl⟩
        · refine ⟨m.succ, ?_, rfl⟩
          have hm' : (m : ℕ) < j := hm
          change ((Fin.succ m : Fin (r + 1)) : ℕ) < j + 1
          rw [Fin.val_succ]
          omega
    rw [aSpan, himage, Submodule.span_insert, Submodule.span_image,
      show Submodule.span K ((fun m : Fin r => w' (.inl m)) '' {m | (m : ℕ) < j}) =
        (W (j + 1)).comap U.subtype from (hspan' j (by omega)).symm,
      Submodule.map_comap_subtype, inf_comm]
    exact eq_span_sup_inf_orthogonal hba (haW (j + 1) (by omega) hi)
      (fun x hx => hiso (j + 1) hi a (haW (j + 1) (by omega) hi) x hx)

section Transitivity

variable {V : Type u} [AddCommGroup V] [Module K V]

theorem isometry_basis_equiv {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {ι : Type*}
    (w w' : Module.Basis ι K V) (hww' : ∀ x y, B (w' x) (w' y) = B (w x) (w y)) (x y : V) :
    B (w.equiv w' (Equiv.refl ι) x) (w.equiv w' (Equiv.refl ι) y) = B x y := by
  have := LinearMap.ext_basis w w (B := (B.comp (w.equiv w' (Equiv.refl ι)).toLinearMap).compl₂
    (w.equiv w' (Equiv.refl ι)).toLinearMap) (B' := B) fun i j => by
      simp [Module.Basis.equiv_apply, hww']
  exact LinearMap.congr_fun₂ this x y

theorem exists_diagonal_isometry (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    {r ε : ℕ} (w : Module.Basis (HypIndex r ε) K V)
    (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y) (c : HypIndex r ε → K)
    (hc : ∀ x, h.bar (c x) * c (hypPartner x) = 1) :
    ∃ φ : V →ₗ[K] V, (∀ x y, B (φ x) (φ y) = B x y) ∧ LinearMap.det φ = ∏ x, c x ∧
      ∀ x, φ (w x) = c x • w x := by
  classical
  have hφw : ∀ x, Matrix.toLin w w (Matrix.diagonal c) (w x) = c x • w x := fun x => by
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  refine ⟨Matrix.toLin w w (Matrix.diagonal c), fun x y => ?_, by
    rw [LinearMap.det_toLin, Matrix.det_diagonal], hφw⟩
  have := LinearMap.ext_basis w w (B := (B.comp (Matrix.toLin w w (Matrix.diagonal c))).compl₂
    (Matrix.toLin w w (Matrix.diagonal c))) (B' := B) fun x y => by
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hφw, map_smulₛₗ,
        LinearMap.smul_apply, smul_eq_mul, hw, hypGram_apply]
      split_ifs with hxy
      · subst hxy
        simp only [RingHom.id_apply, mul_one]
        linear_combination hc x
      · rw [mul_zero, mul_zero]
  exact LinearMap.congr_fun₂ this x y

theorem map_aSpan_of_diagonal {r ε : ℕ} (w : HypIndex r ε → V) {φ : V →ₗ[K] V}
    {c : HypIndex r ε → K} (hc : ∀ x, c x ≠ 0) (hφ : ∀ x, φ (w x) = c x • w x) (i : ℕ) :
    (aSpan w i).map φ = aSpan w i := by
  rw [aSpan, Submodule.map_span, Set.image_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    change φ (w (.inl j)) ∈ _
    rw [hφ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    change w (.inl j) ∈ _
    have : w (.inl j) = (c (.inl j))⁻¹ • φ (w (.inl j)) := by
      rw [hφ, smul_smul, inv_mul_cancel₀ (hc _), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

theorem exists_sesqSpecialUnitary_map_aSpan (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r ε : ℕ}
    (hε : ε ≤ 1) (w w' : Module.Basis (HypIndex r ε) K V)
    (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y)
    (hw' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, ∀ i, (aSpan w i).map (g : V →ₗ[K] V) = aSpan w' i := by
  classical
  set g₀ : V →ₗ[K] V := (w.equiv w' (Equiv.refl _)).toLinearMap with hg₀def
  have hg₀ : ∀ x y, B (g₀ x) (g₀ y) = B x y :=
    isometry_basis_equiv w w' (fun x y => by rw [hw, hw'])
  have hg₀w : ∀ x, g₀ (w x) = w' x := fun x => by
    rw [hg₀def, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB hBl
  have hd : h.norm (LinearMap.det g₀) = 1 :=
    norm_det_of_isometry h e (mem_orthonormalFrames.mpr he) hg₀
  set d := LinearMap.det g₀ with hddef
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, UnitaryFieldData.norm, map_zero, mul_zero] at hd
    exact zero_ne_one hd
  have hdinv : h.norm d⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, ← UnitaryFieldData.norm, hd, inv_one]
  obtain ⟨c, hc0, hcp, hcprod⟩ : ∃ c : HypIndex r ε → K, (∀ x, c x ≠ 0) ∧
      (∀ x, h.bar (c x) * c (hypPartner x) = 1) ∧ ∏ x, c x = d⁻¹ := by
    rcases Nat.eq_zero_or_pos ε with rfl | hε0
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · have hV : Module.finrank K V = 0 := by
          rw [Module.finrank_eq_card_basis w]
          simp
        refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ => by rw [map_one, one_mul], ?_⟩
        rw [Finset.prod_const_one, hddef, LinearMap.det_eq_one_of_finrank_eq_zero hV g₀,
          inv_one]
      · obtain ⟨μ, hμ0, hμ⟩ := h.exists_div_bar_eq hdinv
        have hbμ : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
        let i₀ : Fin r := ⟨0, hr0⟩
        refine ⟨fun x => match x with
          | .inl i => if i = i₀ then μ else 1
          | .inr (.inl _) => 1
          | .inr (.inr i) => if i = i₀ then (h.bar μ)⁻¹ else 1, fun x => ?_, fun x => ?_, ?_⟩
        · rcases x with i | l | i
          · change (if i = i₀ then μ else 1) ≠ 0
            split_ifs <;> simp [hμ0]
          · exact one_ne_zero
          · change (if i = i₀ then (h.bar μ)⁻¹ else 1) ≠ 0
            split_ifs <;> simp [hbμ]
        · rcases x with i | l | i
          · change h.bar (if i = i₀ then μ else 1) * (if i = i₀ then (h.bar μ)⁻¹ else 1) = 1
            split_ifs <;> simp [hbμ]
          · change h.bar 1 * 1 = 1
            simp
          · change h.bar (if i = i₀ then (h.bar μ)⁻¹ else 1) * (if i = i₀ then μ else 1) = 1
            split_ifs <;> simp [h.bar_bar, hμ0]
        · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
          simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.prod_const_one,
            one_mul]
          rw [← hμ, div_eq_mul_inv]
    · obtain rfl : ε = 1 := by omega
      refine ⟨fun x => match x with
        | .inl _ => 1
        | .inr (.inl _) => d⁻¹
        | .inr (.inr _) => 1, fun x => ?_, fun x => ?_, ?_⟩
      · rcases x with i | l | i <;> simp [hd0]
      · rcases x with i | l | i <;> simp only [hypPartner, map_one, one_mul]
        rw [mul_comm]
        exact hdinv
      · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp
  obtain ⟨φ, hφ, hφdet, hφw⟩ := exists_diagonal_isometry h w' hw' c hcp
  have hcomp : ∀ x y, B ((φ ∘ₗ g₀) x) ((φ ∘ₗ g₀) y) = B x y := fun x y => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, hg₀]
  refine ⟨isometryUnit hBl hcomp, mem_sesqSpecialUnitaryGroup.mpr ⟨(isometryUnit hBl hcomp).2,
    ?_⟩, fun i => ?_⟩
  · rw [coe_isometryUnit, LinearMap.det_comp, hφdet, hcprod, ← hddef, inv_mul_cancel₀ hd0]
  · rw [coe_isometryUnit, Submodule.map_comp]
    have hg₀span : (aSpan w i).map g₀ = aSpan w' i := by
      rw [aSpan, aSpan, Submodule.map_span, Set.image_image]
      simp only [hg₀w]
    rw [hg₀span]
    exact map_aSpan_of_diagonal w' hc0 hφw i

theorem exists_isotropicChain_eq {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} [FiniteDimensional K V]
    (U : Submodule K V) (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0) :
    ∃ W : ℕ → Submodule K V, IsIsotropicChain B (Module.finrank K U) W ∧
      W (Module.finrank K U) = U := by
  set k := Module.finrank K U with hk
  let e : Module.Basis (Fin k) K U := Module.finBasisOfFinrankEq K U hk.symm
  let W : ℕ → Submodule K V := fun i =>
    if hi : i ≤ k then Submodule.span K (Set.range fun j : Fin i => (e (Fin.castLE hi j) : V))
    else U
  have hWi : ∀ i (hi : i ≤ k),
      W i = Submodule.span K (Set.range fun j : Fin i => (e (Fin.castLE hi j) : V)) :=
    fun i hi => by simp only [W, hi, ↓reduceDIte]
  have hWU : ∀ i ≤ k, W i ≤ U := fun i hi => by
    rw [hWi i hi, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (e _).2
  refine ⟨W, ⟨fun i hi => ?_, fun i hi => ?_, fun i hi x hx y hy =>
    hU x (hWU i hi hx) y (hWU i hi hy)⟩, ?_⟩
  · have hli : LinearIndependent K fun j : Fin i => (e (Fin.castLE hi j) : V) :=
      (e.linearIndependent.map' U.subtype (Submodule.ker_subtype U)).comp (Fin.castLE hi)
        (Fin.castLE_injective hi)
    rw [hWi i hi, finrank_span_eq_card hli, Fintype.card_fin]
  · rw [hWi i hi.le, hWi (i + 1) hi]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, rfl⟩
  · rw [hWi k le_rfl]
    have : (Set.range fun j : Fin k => (e (Fin.castLE le_rfl j) : V)) =
        U.subtype '' Set.range e := by
      rw [← Set.range_comp]
      congr 1
    rw [this, Submodule.span_image, e.span_eq, Submodule.map_subtype_top]

end Transitivity

theorem isotropic_flag_extension (h : UnitaryFieldData p f K) {V : Type u} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : Module.finrank K V = n) :
    (∀ (k : ℕ) (W : ℕ → Submodule K V), IsIsotropicChain B k W → k ≤ n / 2 ∧
      ∃ w : Module.Basis (HypIndex (n / 2) (n - 2 * (n / 2))) K V,
        (∀ x y, B (w x) (w y) = hypGram (n / 2) (n - 2 * (n / 2)) K x y) ∧
        ∀ i ≤ k, W i = aSpan w i) ∧
    (∀ (k : ℕ) (W W' : ℕ → Submodule K V), IsIsotropicChain B k W →
      IsIsotropicChain B k W' →
      ∃ g ∈ sesqSpecialUnitaryGroup B, ∀ i ≤ k, (W i).map (g : V →ₗ[K] V) = W' i) ∧
    ∀ U U' : Submodule K V, (∀ x ∈ U, ∀ y ∈ U, B x y = 0) → (∀ x ∈ U', ∀ y ∈ U', B x y = 0) →
      Module.finrank K U = Module.finrank K U' →
      ∃ g ∈ sesqSpecialUnitaryGroup B, U.map (g : V →ₗ[K] V) = U' := by
  have hε : n - 2 * (n / 2) ≤ 1 := by omega
  have hn' : Module.finrank K V = 2 * (n / 2) + (n - 2 * (n / 2)) := by omega
  have hchain := fun k W hW => exists_hypBasis_of_isotropicChain h k hB hBl hε hn' W hW
  have htrans : ∀ (k : ℕ) (W W' : ℕ → Submodule K V), IsIsotropicChain B k W →
      IsIsotropicChain B k W' →
      ∃ g ∈ sesqSpecialUnitaryGroup B, ∀ i ≤ k, (W i).map (g : V →ₗ[K] V) = W' i := by
    intro k W W' hW hW'
    obtain ⟨-, w, hw, hWw⟩ := hchain k W hW
    obtain ⟨-, w', hw', hWw'⟩ := hchain k W' hW'
    obtain ⟨g, hg, hgw⟩ := exists_sesqSpecialUnitary_map_aSpan h hB hBl hε w w' hw hw'
    exact ⟨g, hg, fun i hi => by rw [hWw i hi, hWw' i hi, hgw]⟩
  refine ⟨hchain, htrans, fun U U' hU hU' hUU' => ?_⟩
  obtain ⟨W, hW, hWU⟩ := exists_isotropicChain_eq U hU
  obtain ⟨W', hW', hWU'⟩ := exists_isotropicChain_eq U' hU'
  rw [← hUU'] at hW' hWU'
  obtain ⟨g, hg, hgW⟩ := htrans _ W W' hW hW'
  exact ⟨g, hg, by rw [← hWU, ← hWU', hgW _ le_rfl]⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
