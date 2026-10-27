module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open Module Matrix Submodule CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  exists_symplectic_basis_prescribed_pair isometry_iff_matrix)
open LinearMap (BilinForm)

section Pair

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
  (hB : B.IsAlt) {e f : V} (hfe : B f e = 1)

@[expose] def pairProj : V →ₗ[K] B.orthogonal (span K {e, f}) :=
  LinearMap.codRestrict _ (LinearMap.id - (B f).smulRight e + (B e).smulRight f)
    fun u => by simpa using hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe u

include hB hfe

theorem coe_pairProj (u : V) : (pairProj hB hfe u : V) = u - B f u • e + B e u • f := by
  simp [pairProj]

omit hB hfe in
theorem apply_eq_zero_of_mem_orthogonal {z : V} (hz : z ∈ B.orthogonal (span K {e, f})) :
    B e z = 0 ∧ B f z = 0 :=
  ⟨BilinForm.mem_orthogonal_iff.mp hz e (subset_span (by simp)),
    BilinForm.mem_orthogonal_iff.mp hz f (subset_span (by simp))⟩

theorem pairProj_coe (z : B.orthogonal (span K {e, f})) : pairProj hB hfe (z : V) = z := by
  obtain ⟨he, hf⟩ := apply_eq_zero_of_mem_orthogonal z.2
  apply Subtype.ext
  rw [coe_pairProj, he, hf, zero_smul, zero_smul, sub_zero, add_zero]

theorem sub_pairProj (u : V) : u - (pairProj hB hfe u : V) = B f u • e - B e u • f := by
  rw [coe_pairProj]
  abel

theorem pairProj_left : pairProj hB hfe e = 0 := by
  apply Subtype.ext
  rw [coe_pairProj, hfe, hB.self_eq_zero, one_smul, zero_smul, sub_self, add_zero]
  rfl

theorem pairProj_right : pairProj hB hfe f = 0 := by
  have hef : B e f = -1 := by rw [← hB.neg_eq, hfe]
  apply Subtype.ext
  rw [coe_pairProj, hef, hB.self_eq_zero, zero_smul, sub_zero, neg_one_smul, add_neg_cancel]
  rfl

omit hfe in
theorem apply_eq_zero_of_mem_span_pair {u z : V} (hu : u ∈ span K {e, f})
    (hz : z ∈ B.orthogonal (span K {e, f})) : B u z = 0 ∧ B z u = 0 := by
  have h₁ : B u z = 0 := BilinForm.mem_orthogonal_iff.mp hz u hu
  exact ⟨h₁, by rw [← hB.neg_eq, h₁, neg_zero]⟩

theorem sub_pairProj_mem (u : V) : u - (pairProj hB hfe u : V) ∈ span K {e, f} := by
  rw [sub_pairProj hB hfe]
  exact sub_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))

@[expose] def pairExt (h : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f})) :
    V →ₗ[K] V :=
  LinearMap.id - (B.orthogonal (span K {e, f})).subtype ∘ₗ pairProj hB hfe +
    (B.orthogonal (span K {e, f})).subtype ∘ₗ h ∘ₗ pairProj hB hfe

theorem pairExt_apply (h : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f}))
    (x : V) : pairExt hB hfe h x = x - (pairProj hB hfe x : V) + (h (pairProj hB hfe x) : V) :=
  rfl

theorem pairProj_pairExt (h : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f}))
    (x : V) : pairProj hB hfe (pairExt hB hfe h x) = h (pairProj hB hfe x) := by
  rw [pairExt_apply, map_add, map_sub, pairProj_coe, pairProj_coe, sub_self, zero_add]

theorem pairExt_comp (h h' : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f})) :
    pairExt hB hfe h ∘ₗ pairExt hB hfe h' = pairExt hB hfe (h ∘ₗ h') := by
  ext x
  rw [LinearMap.comp_apply, pairExt_apply hB hfe h, pairProj_pairExt, pairExt_apply hB hfe h',
    pairExt_apply, LinearMap.comp_apply]
  abel

theorem pairExt_id : pairExt hB hfe LinearMap.id = LinearMap.id := by
  ext x
  rw [pairExt_apply, LinearMap.id_apply, LinearMap.id_apply]
  abel

theorem pairExt_coe (h : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f}))
    (z : B.orthogonal (span K {e, f})) : pairExt hB hfe h z = h z := by
  rw [pairExt_apply, pairProj_coe, sub_self, zero_add]

theorem pairExt_isometry {h : B.orthogonal (span K {e, f}) →ₗ[K] B.orthogonal (span K {e, f})}
    (hh : ∀ x y, B (h x) (h y) = B x y) (x y : V) :
    B (pairExt hB hfe h x) (pairExt hB hfe h y) = B x y := by
  have hx := sub_pairProj_mem hB hfe x
  have hy := sub_pairProj_mem hB hfe y
  have hsplit : ∀ (u u' : V), u ∈ span K {e, f} → u' ∈ span K {e, f} →
      ∀ z z' : B.orthogonal (span K {e, f}), B (u + z) (u' + z') = B u u' + B z z' := by
    intro u u' hu hu' z z'
    simp only [map_add, LinearMap.add_apply]
    rw [(apply_eq_zero_of_mem_span_pair hB hu z'.2).1,
      (apply_eq_zero_of_mem_span_pair hB hu' z.2).2]
    ring
  have hxs : x = (x - (pairProj hB hfe x : V)) + (pairProj hB hfe x : V) := by abel
  have hys : y = (y - (pairProj hB hfe y : V)) + (pairProj hB hfe y : V) := by abel
  conv_rhs => rw [hxs, hys, hsplit _ _ hx hy]
  rw [pairExt_apply, pairExt_apply, hsplit _ _ hx hy, hh]

end Pair

section Isometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_stabilizer_pair {B : BilinForm K V} (hB : B.IsAlt) {e f : V} (hfe : B f e = 1) :
    Nat.card (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f)) =
      Nat.card (TauCeti.BilinForm.isometryGroup (B.restrict (B.orthogonal (span K {e, f})))) := by
  set Z := B.orthogonal (span K {e, f})
  have hmapZ : ∀ g : MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f),
      Z.map ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V).toLinearMap = Z := by
    have key : ∀ g : MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f),
        ∀ z ∈ Z, ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) z ∈ Z := by
      intro g z hz
      have hg := g.2
      rw [MulAction.mem_stabilizer_iff, Prod.ext_iff] at hg
      obtain ⟨hge, hgf⟩ := hg
      change ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) e = e at hge
      change ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) f = f at hgf
      have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp
        (g : TauCeti.BilinForm.isometryGroup B).2
      obtain ⟨he, hf⟩ := apply_eq_zero_of_mem_orthogonal hz
      set g' := ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V)
      have h₁ : B e (g' z) = 0 := by
        calc B e (g' z) = B (g' e) (g' z) := by rw [hge]
          _ = 0 := by rw [hiso, he]
      have h₂ : B f (g' z) = 0 := by
        calc B f (g' z) = B (g' f) (g' z) := by rw [hgf]
          _ = 0 := by rw [hiso, hf]
      rw [BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, h₁, h₂, smul_zero, smul_zero, add_zero]
    intro g
    refine le_antisymm ?_ fun z hz => ⟨_, key g⁻¹ z hz, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact key g z hz
    · exact LinearEquiv.apply_symm_apply ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) z
  set ρ : MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f) →
      TauCeti.BilinForm.isometryGroup (B.restrict Z) := fun g =>
    ⟨LinearEquiv.ofSubmodules _ Z Z (hmapZ g), TauCeti.BilinForm.mem_isometryGroup_iff.mpr
      fun x y => by
        rw [BilinForm.restrict_apply, LinearMap.domRestrict_apply, BilinForm.restrict_apply,
          LinearMap.domRestrict_apply, LinearEquiv.ofSubmodules_apply,
          LinearEquiv.ofSubmodules_apply]
        exact TauCeti.BilinForm.mem_isometryGroup_iff.mp
          (g : TauCeti.BilinForm.isometryGroup B).2 x y⟩ with hρ
  have hρapply : ∀ g z, ((ρ g : Z ≃ₗ[K] Z) z : V) =
      ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) z := fun _ _ => rfl
  refine (Nat.card_congr (Equiv.ofBijective ρ ⟨fun g g' hgg' => ?_, fun h => ?_⟩)).symm.symm
  ·
    have hfix : ∀ g : MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f),
        ∀ x, ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) x =
          (x - (pairProj hB hfe x : V)) + ((ρ g : Z ≃ₗ[K] Z) (pairProj hB hfe x) : V) := by
      intro g x
      have hg := g.2
      rw [MulAction.mem_stabilizer_iff, Prod.ext_iff] at hg
      obtain ⟨hge, hgf⟩ := hg
      change ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) e = e at hge
      change ((g : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) f = f at hgf
      rw [hρapply]
      conv_lhs => rw [show x = (x - (pairProj hB hfe x : V)) + (pairProj hB hfe x : V) by abel]
      rw [map_add, sub_pairProj hB hfe, map_sub, map_smul, map_smul, hge, hgf]
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [hfix g x, hfix g' x, hgg']
  ·
    set φ : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (pairExt hB hfe (h : Z ≃ₗ[K] Z).toLinearMap)
      (pairExt hB hfe ((h : Z ≃ₗ[K] Z).symm).toLinearMap)
      (by rw [pairExt_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, pairExt_id])
      (by rw [pairExt_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, pairExt_id]) with hφ
    have hφapply : ∀ x, φ x = pairExt hB hfe (h : Z ≃ₗ[K] Z).toLinearMap x := fun _ => rfl
    have hφiso : φ ∈ TauCeti.BilinForm.isometryGroup B :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => by
        rw [hφapply, hφapply]
        refine pairExt_isometry hB hfe (fun x y => ?_) x y
        have := TauCeti.BilinForm.mem_isometryGroup_iff.mp h.2 x y
        rwa [BilinForm.restrict_apply, LinearMap.domRestrict_apply, BilinForm.restrict_apply,
          LinearMap.domRestrict_apply] at this
    have hφstab : (⟨φ, hφiso⟩ : TauCeti.BilinForm.isometryGroup B) ∈
        MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f) := by
      rw [MulAction.mem_stabilizer_iff]
      refine Prod.ext ?_ ?_
      · change φ e = e
        rw [hφapply, pairExt_apply, pairProj_left hB hfe, map_zero]
        simp
      · change φ f = f
        rw [hφapply, pairExt_apply, pairProj_right hB hfe, map_zero]
        simp
    refine ⟨⟨⟨φ, hφiso⟩, hφstab⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    apply Subtype.ext
    rw [hρapply]
    exact pairExt_coe hB hfe _ z

theorem exists_isometry_apply_pair [FiniteDimensional K V] {B : BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {e f e' f' : V} (hfe : B f e = 1) (hfe' : B f' e' = 1) :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup B, g e = e' ∧ g f = f' := by
  obtain ⟨m, c, hm, hc₁, hc₂, hc₃, hcf, hce⟩ :=
    exists_symplectic_basis_prescribed_pair B hB hnd f e hfe
  obtain ⟨m', c', hm', hc₁', hc₂', hc₃', hcf', hce'⟩ :=
    exists_symplectic_basis_prescribed_pair B hB hnd f' e' hfe'
  have hmm : m' = m := by omega
  subst hmm
  have hmat : BilinForm.toMatrix c B = BilinForm.toMatrix c' B := by
    ext (i | i) (j | j)
    · simp only [BilinForm.toMatrix_apply, hc₁, hc₁']
    · simp only [BilinForm.toMatrix_apply, hc₃, hc₃']
    · simp only [BilinForm.toMatrix_apply]
      rw [← hB.neg_eq, hc₃, ← hB.neg_eq (c' (Sum.inl j)), hc₃']
    · simp only [BilinForm.toMatrix_apply, hc₂, hc₂']
  set g := c.isometryEquivOfToMatrixEq c' hmat
  refine ⟨g.toLinearEquiv, TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => g.map_app y x,
    ?_, ?_⟩
  · have := c.isometryEquivOfToMatrixEq_apply_basis c' hmat (Sum.inr 0)
    rw [hce, hce'] at this
    exact this
  · have := c.isometryEquivOfToMatrixEq_apply_basis c' hmat (Sum.inl 0)
    rw [hcf, hcf'] at this
    exact this

theorem card_fiber_eq_one [Finite K] [FiniteDimensional K V] {φ : V →ₗ[K] K} (hφ : φ ≠ 0) :
    Nat.card {y : V // φ y = 1} = Nat.card K ^ (finrank K V - 1) := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.ext h)
  set y₀ := (φ v)⁻¹ • v
  have hy₀ : φ y₀ = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  have hrange : finrank K (LinearMap.range φ) = 1 := by
    have : LinearMap.range φ = ⊤ := by
      refine eq_top_iff.mpr fun c _ => ⟨c • y₀, ?_⟩
      rw [map_smul, hy₀, smul_eq_mul, mul_one]
    rw [this, finrank_top, finrank_self]
  have hker := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at hker
  have e : {y : V // φ y = 1} ≃ LinearMap.ker φ :=
    { toFun := fun y => ⟨y - y₀, by rw [LinearMap.mem_ker, map_sub, y.2, hy₀, sub_self]⟩
      invFun := fun k => ⟨k + y₀, by rw [map_add, LinearMap.mem_ker.mp k.2, hy₀, zero_add]⟩
      left_inv := fun y => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun k => Subtype.ext (add_sub_cancel_right _ _) }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  omega

theorem card_hyperbolicPairs [Finite K] [FiniteDimensional K V] {B : BilinForm K V}
    (hnd : B.Nondegenerate) :
    Nat.card {p : V × V // B p.2 p.1 = 1} =
      (Nat.card V - 1) * Nat.card K ^ (finrank K V - 1) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have := Fintype.ofFinite V
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun x y => B y x = 1), Nat.card_sigma]
  have hterm : ∀ x : V, Nat.card {y : V // B y x = 1} =
      if x = 0 then 0 else Nat.card K ^ (finrank K V - 1) := by
    intro x
    split_ifs with hx
    · subst hx
      have : IsEmpty {y : V // B y 0 = 1} := ⟨fun y => by
        have := y.2
        rw [map_zero] at this
        exact zero_ne_one this⟩
      exact Nat.card_of_isEmpty
    · have hφ : B.flip x ≠ 0 := by
        intro h
        exact hx (hnd.2 x fun y => by
          have := LinearMap.congr_fun h y
          rwa [BilinForm.flip_apply] at this)
      have := card_fiber_eq_one hφ
      simpa [BilinForm.flip_apply] using this
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, smul_eq_mul, Finset.filter_ne', Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card]

theorem card_isometryGroup [Finite K] : ∀ (m : ℕ) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : BilinForm K V), B.IsAlt → B.Nondegenerate →
    finrank K V = 2 * m →
    Nat.card (TauCeti.BilinForm.isometryGroup B) =
      Nat.card K ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ B _ _ hV
    have : Subsingleton V := finrank_zero_iff.mp (by rw [hV])
    have : Subsingleton (V ≃ₗ[K] V) := ⟨fun a b => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩]
    simp
  | succ m ih =>
    intro V _ _ _ B hB hnd hV
    have : Nontrivial V := by
      rw [← finrank_pos_iff (R := K)]
      omega
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    obtain ⟨y, hy⟩ : ∃ y, B y e ≠ 0 := by
      by_contra! h
      exact he (hnd.2 e h)
    set f := (B y e)⁻¹ • y
    have hfe : B f e = 1 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy]
    have horbit : MulAction.orbit (TauCeti.BilinForm.isometryGroup B) (e, f) =
        {p : V × V | B p.2 p.1 = 1} := by
      ext p
      constructor
      · rintro ⟨g, rfl⟩
        change B ((g : V ≃ₗ[K] V) f) ((g : V ≃ₗ[K] V) e) = 1
        rw [TauCeti.BilinForm.mem_isometryGroup_iff.mp g.2, hfe]
      · intro h
        obtain ⟨g, hg, hge, hgf⟩ := exists_isometry_apply_pair hB hnd hfe h
        exact ⟨⟨g, hg⟩, Prod.ext hge hgf⟩
    have hcard := (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup B) (e, f)).card_mul_index
    rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq, card_stabilizer_pair hB hfe]
      at hcard
    have hZ : finrank K (B.orthogonal (span K {e, f})) = 2 * m := by
      have := hB.finrank_orthogonal_span_pair_add_two hnd hfe
      omega
    rw [← hcard, ih (B.restrict _) (fun z => hB.self_eq_zero z)
      (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd) hZ]
    have hpairs : Nat.card ↥{p : V × V | B p.2 p.1 = 1} =
        (Nat.card V - 1) * Nat.card K ^ (finrank K V - 1) := card_hyperbolicPairs hnd
    rw [hpairs, Module.natCard_eq_pow_finrank (K := K) (V := V), hV,
      Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hexp : (m + 1) ^ 2 = m ^ 2 + (2 * (m + 1) - 1) := by
      have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [this]
      ring
    rw [hexp, pow_add]
    ring

end Isometry

section Standard

variable {r : ℕ} {K : Type} [Field K]

theorem map_isometryGroup_eq_statedSp :
    (TauCeti.BilinForm.isometryGroup (pairedSympForm K r)).map
      (basisMatrixEquiv (Pi.basisFun K (Fin r ⊕ Fin r))).toMonoidHom = StatedSp r K := by
  ext M
  rw [Subgroup.mem_map_equiv, isometry_iff_matrix (Pi.basisFun K (Fin r ⊕ Fin r)),
    MulEquiv.apply_symm_apply, toMatrix_pairedSympForm, SymplecticTorusWeyl.mem_statedSp_iff]

theorem card_statedSp [Finite K] (r : ℕ) :
    Nat.card (StatedSp r K) =
      Nat.card K ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1) := by
  rw [← map_isometryGroup_eq_statedSp, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact card_isometryGroup r _ pairedSympForm_isAlt pairedSympForm_nondegenerate finrank_standard

theorem card_statedSp_two (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp 2 K) = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  rw [card_statedSp, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_statedSp_two_zmod_three : Nat.card (StatedSp 2 (ZMod 3)) = 51840 := by
  rw [card_statedSp_two, Nat.card_zmod]
  rfl

@[expose] def symmetricEquiv (r : ℕ) (K : Type) :
    {C : Matrix (Fin r) (Fin r) K // Cᵀ = C} ≃ (Sym2 (Fin r) → K) :=
  (Equiv.subtypeEquiv Matrix.of.symm fun C => by
    rw [← Matrix.ext_iff]
    exact ⟨fun h a b => h b a, fun h i j => h j i⟩).trans
    (Sym2.lift (α := Fin r) (β := K))

omit [Field K] in
theorem card_symmetric [Finite K] (r : ℕ) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // Cᵀ = C} = Nat.card K ^ (r * (r + 1) / 2) := by
  rw [Nat.card_congr (symmetricEquiv r K), Nat.card_fun, Nat.card_eq_fintype_card (α := Sym2 _),
    Sym2.card, Fintype.card_fin, Nat.choose_two_right, mul_comm]
  rfl

theorem card_unipotent [Finite K] (r : ℕ) :
    Nat.card (unipotent r K) = Nat.card K ^ (r ^ 2) := by
  set Ψ : LinearFlag.unitriangular r K × {C : Matrix (Fin r) (Fin r) K // Cᵀ = C} →
      unipotent r K := fun x =>
    ⟨blockElt (show IsUnit ((x.1 : SpecialLinearGroup (Fin r) K) :
        Matrix (Fin r) (Fin r) K).det by rw [(x.1 : SpecialLinearGroup (Fin r) K).2]; exact
        isUnit_one) x.2.2,
      ⟨_, _, ⟨fun _ _ hij => x.1.2.1 _ _ hij, x.1.2.2⟩, x.2.2, coe_blockElt _ _⟩⟩ with hΨ
  have hbij : Function.Bijective Ψ := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have h := congrArg (fun g : unipotent r K => (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hxy
      simp only [hΨ, coe_blockElt] at h
      obtain ⟨h₁, h₂⟩ := blockMat_inj (by
        rw [(x.1 : SpecialLinearGroup (Fin r) K).2]
        exact isUnit_one) h
      exact Prod.ext (Subtype.ext (Subtype.ext h₁)) (Subtype.ext h₂)
    · obtain ⟨A, C, hA, hC, hg⟩ := g.2
      refine ⟨(⟨⟨A, hA.det_eq_one⟩, fun i j hij => hA.1 hij, hA.2⟩, ⟨C, hC⟩), ?_⟩
      apply Subtype.ext
      apply SymplecticTorusWeyl.statedSp_ext
      simp only [hΨ, coe_blockElt]
      exact hg.symm
  rw [← Nat.card_congr (Equiv.ofBijective Ψ hbij), Nat.card_prod, LinearFlag.card_unitriangular,
    card_symmetric, ← pow_add]
  congr 1
  rcases r with _ | s
  · rfl
  · have h1 : (s + 1) * (s + 1 + 1) = (s + 1) * (s + 1 - 1) + 2 * (s + 1) := by
      rw [Nat.add_sub_cancel]
      ring
    have h2 : 2 ∣ (s + 1) * (s + 1 - 1) := by
      rw [Nat.add_sub_cancel]
      exact (Nat.even_mul_succ_self s).two_dvd.trans (by rw [mul_comm])
    rw [h1, Nat.add_mul_div_left _ _ two_pos]
    obtain ⟨t, ht⟩ := h2
    rw [ht, Nat.mul_div_cancel_left _ two_pos]
    have : (s + 1) ^ 2 = 2 * t + (s + 1) := by
      rw [← ht, Nat.add_sub_cancel]
      ring
    omega

theorem card_borelSubgroup [Finite K] (r : ℕ) :
    Nat.card (borelSubgroup r K) = Nat.card K ^ (r ^ 2) * (Nat.card K - 1) ^ r := by
  have h := (diagHom r K).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ diagHom_surjective).toEquiv,
    ker_diagHom, Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotent_le_borelSubgroup).toEquiv,
    card_unipotent, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.card_units] at h
  rw [h, mul_comm]

theorem card_scalars_dvd [Finite K] (hr : 1 ≤ r) :
    Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) ∣ Nat.card K - 1 := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (R := K)) := by
    intro c d h
    apply Units.ext
    have h' := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K)) h
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] using h'
  have hZ : Nat.card (StatedScalars (Fin r ⊕ Fin r) K) = Nat.card K - 1 := by
    rw [StatedScalars, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]
  rw [← hZ]
  exact Subgroup.card_dvd_of_injective
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } fun x y h => Subtype.ext (Subtype.ext (congrArg
        (fun z : StatedScalars (Fin r ⊕ Fin r) K => (z : GL (Fin r ⊕ Fin r) K)) h))

theorem unipotent_inf_scalars (hr : 1 ≤ r) :
    unipotent r K ⊓ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg'
  obtain ⟨⟨A, C, hA, -, hg⟩, hgZ⟩ := Subgroup.mem_inf.mp hg'
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hgZ
  obtain ⟨c, hc⟩ := hgZ
  have hmat : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.scalar (Fin r ⊕ Fin r) (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hc1 : (c : K) = 1 := by
    have h := congrFun₂ (hg.symm.trans hmat) (Sum.inl ⟨0, hr⟩) (Sum.inl ⟨0, hr⟩)
    rw [blockMat, fromBlocks_apply₁₁, hA.2, Matrix.scalar_apply, diagonal_apply_eq] at h
    exact h.symm
  rw [Subgroup.mem_bot]
  apply SymplecticTorusWeyl.statedSp_ext
  rw [hmat, hc1, map_one]
  rfl

theorem proj_injOn_unipotent (hr : 1 ≤ r) {g h : StatedSp r K} (hg : g ∈ unipotent r K)
    (hh : h ∈ unipotent r K) (hgh : proj r K g = proj r K h) : g = h := by
  have hm : g⁻¹ * h ∈ unipotent r K ⊓ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K) :=
    ⟨(unipotent r K).mul_mem ((unipotent r K).inv_mem hg) hh, QuotientGroup.eq.mp hgh⟩
  rw [unipotent_inf_scalars hr, Subgroup.mem_bot, inv_mul_eq_one] at hm
  exact hm

theorem card_projUnipotent [Finite K] (hr : 1 ≤ r) :
    Nat.card (projUnipotent r K) = Nat.card K ^ (r ^ 2) := by
  rw [projUnipotent, ← card_unipotent r]
  refine Nat.card_congr (Equiv.ofBijective ((proj r K).subgroupMap (unipotent r K))
    ⟨fun x y h => Subtype.ext (proj_injOn_unipotent hr x.2 y.2 (congrArg Subtype.val h)),
      (proj r K).subgroupMap_surjective _⟩).symm

theorem not_dvd_prod_pow_two_mul_sub_one {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q)
    (r : ℕ) : ¬ p ∣ ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) := by
  rw [Prime.dvd_finsetProd_iff hp.prime]
  rintro ⟨j, hj, hdvd⟩
  rw [Finset.mem_Icc] at hj
  have hqj : p ∣ q ^ (2 * j) := hpq.trans (dvd_pow_self q (by omega))
  have h1 : 1 ≤ q ^ (2 * j) := Nat.one_le_pow _ _ hq
  have : p ∣ q ^ (2 * j) - (q ^ (2 * j) - 1) := Nat.dvd_sub hqj hdvd
  rw [Nat.sub_sub_self h1] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem exists_sylow_unipotent [Finite K] (p : ℕ) [CharP K p] (r : ℕ) :
    ∃ P : Sylow p (StatedSp r K), (P : Subgroup _) = unipotent r K := by
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card] at hk
  have hpq : p ∣ Nat.card K := by
    rw [hk]
    exact dvd_pow_self p k.ne_zero
  have hU : IsPGroup p (unipotent r K) := by
    refine IsPGroup.of_card (n := k * r ^ 2) ?_
    rw [card_unipotent, hk, pow_mul]
  have hindex : (unipotent r K).index = ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1) := by
    have h := (unipotent r K).card_mul_index
    rw [card_unipotent, card_statedSp] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Finite.card_pos _) h
  refine ⟨hU.toSylow ?_, rfl⟩
  rw [hindex]
  exact not_dvd_prod_pow_two_mul_sub_one hp hpq Finite.card_pos r

theorem exists_sylow_projUnipotent [Finite K] (p : ℕ) [CharP K p] (hr : 1 ≤ r) :
    ∃ P : Sylow p (StatedProj (StatedSp r K)), (P : Subgroup _) = projUnipotent r K := by
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card] at hk
  have hpq : p ∣ Nat.card K := by
    rw [hk]
    exact dvd_pow_self p k.ne_zero
  have hU : IsPGroup p (projUnipotent r K) := by
    refine IsPGroup.of_card (n := k * r ^ 2) ?_
    rw [card_projUnipotent hr, hk, pow_mul]
  have hZ := ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
    (StatedSp r K)).card_eq_card_quotient_mul_card_subgroup
  have hP := (projUnipotent r K).card_mul_index
  rw [card_statedSp] at hZ
  rw [card_projUnipotent hr] at hP
  have hprod : (projUnipotent r K).index * Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) = ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1) := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos (Finite.card_pos (α := K)) (r ^ 2)) ?_
    rw [hZ, ← mul_assoc, hP]
  refine ⟨hU.toSylow fun h => ?_, rfl⟩
  exact not_dvd_prod_pow_two_mul_sub_one hp hpq Finite.card_pos r (hprod ▸ h.mul_right _)

end Standard


theorem symplectic_higher_order_and_Sylow {K : Type} [Field K] [Finite K] (p : ℕ) [CharP K p]
    (q : ℕ) (hq : Nat.card K = q) {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (StatedSp r K) = q ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) ∧
      Nat.card (unipotent r K) = q ^ (r ^ 2) ∧
      Nat.card (borelSubgroup r K) = q ^ (r ^ 2) * (q - 1) ^ r ∧
      Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) ∣ q - 1 ∧
      (∃ P : Sylow p (StatedSp r K), (P : Subgroup _) = unipotent r K) ∧
      unipotent r K ⊓ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) = ⊥ ∧
      (∃ P : Sylow p (StatedProj (StatedSp r K)), (P : Subgroup _) = projUnipotent r K) ∧
      Nat.card (projUnipotent r K) = q ^ (r ^ 2) := by
  subst hq
  exact ⟨card_statedSp r, card_unipotent r, card_borelSubgroup r, card_scalars_dvd hr,
    exists_sylow_unipotent p r, unipotent_inf_scalars hr, exists_sylow_projUnipotent p hr,
    card_projUnipotent hr⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
