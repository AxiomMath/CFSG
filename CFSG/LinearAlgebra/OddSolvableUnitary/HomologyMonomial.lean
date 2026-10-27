module

public import CFSG.LinearAlgebra.OddSolvableUnitary.PlaneOdd

public section

namespace CFSG.OddSolvableUnitary

open Module Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover

variable {f : ℕ} {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable abbrev glMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V) :
    LinearMap.GeneralLinearGroup K V ≃* GL ι K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toMulEquiv

theorem coe_glMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V)
    (g : LinearMap.GeneralLinearGroup K V) :
    ((glMatrix e g : GL ι K) : Matrix ι ι K) = LinearMap.toMatrix e e (g : V →ₗ[K] V) :=
  rfl

theorem eq_span_singleton_of_finrank_eq_one {L : Submodule K V} (hL : finrank K L = 1) {v : V}
    (hv : v ∈ L) (hv0 : v ≠ 0) : L = K ∙ v := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hL
  refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v L).2 hv) ?_).symm
  rw [finrank_span_singleton hv0, hL]

section Matrix

variable (hK : UnitaryFieldData 2 f K) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
include hK

theorem apply_smul_smul (c : K) (v : V) : B (c • v) (c • v) = hK.norm c * B v v := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [UnitaryFieldData.norm]
  ring

theorem norm_eq_one_of_apply_eq_smul {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqUnitaryGroup B) {v w : V} (hv : B v v = 1) (hw : B w w = 1) {c : K}
    (hc : (g : V →ₗ[K] V) v = c • w) : hK.norm c = 1 := by
  have h := (mem_sesqUnitaryGroup.1 hg) v v
  rw [hc, apply_smul_smul hK, hw, mul_one, hv] at h
  exact h

variable (e : Basis (Fin 3) K V) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
include he

theorem glMatrix_mem_torus3 {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqSpecialUnitaryGroup B) (c : Fin 3 → K)
    (hc : ∀ i, (g : V →ₗ[K] V) (e i) = c i • e i) :
    glMatrix e g ∈ torus3 (normOne K (2 ^ f)) := by
  obtain ⟨hgU, hdet⟩ := mem_sesqSpecialUnitaryGroup.1 hg
  have hN : ∀ i, hK.norm (c i) = 1 := fun i =>
    norm_eq_one_of_apply_eq_smul hK hgU (by simp [he]) (by simp [he]) (hc i)
  have hc0 : ∀ i, c i ≠ 0 := fun i h => by
    have := hN i
    rw [h, UnitaryFieldData.norm, zero_mul] at this
    exact zero_ne_one this
  have hmat : LinearMap.toMatrix e e (g : V →ₗ[K] V) = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, e.repr_self, Matrix.diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h1 h2 h2
    · rw [h2]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  refine (mem_torus3 _).2 ⟨fun i => Units.mk0 (c i) (hc0 i), fun i => ?_, ?_, ?_⟩
  · exact (mem_normOne_iff_norm hK).2 (hN i)
  · apply Units.ext
    have h := LinearMap.det_toMatrix e (g : V →ₗ[K] V)
    rw [hmat, Matrix.det_diagonal, Fin.prod_univ_three, hdet] at h
    simpa using h
  · apply Units.ext
    rw [coe_glMatrix, hmat, coe_diagHom]
    rfl

theorem exists_glMatrix_eq_mul_cycGL {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqSpecialUnitaryGroup B) (c : Fin 3 → K)
    (hc : ∀ i, (g : V →ₗ[K] V) (e i) = c i • e (finRotate 3 i)) :
    ∃ d ∈ torus3 (normOne K (2 ^ f)), glMatrix e g = d * cycGL := by
  obtain ⟨hgU, hdet⟩ := mem_sesqSpecialUnitaryGroup.1 hg
  have hN : ∀ i, hK.norm (c i) = 1 := fun i =>
    norm_eq_one_of_apply_eq_smul hK hgU (by simp [he]) (by simp [he]) (hc i)
  have hc0 : ∀ i, c i ≠ 0 := fun i h => by
    have := hN i
    rw [h, UnitaryFieldData.norm, zero_mul] at this
    exact zero_ne_one this
  set u : Fin 3 → Kˣ := fun i => Units.mk0 (c i) (hc0 i)
  have hmat : LinearMap.toMatrix e e (g : V →ₗ[K] V) =
      ((cycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, e.repr_self, Matrix.mul_diagonal, coe_cycGL]
    fin_cases i <;> fin_cases j <;> simp [cycMat]
  have hg' : glMatrix e g = cycGL * diagHom 3 u := by
    apply Units.ext
    rw [coe_glMatrix, hmat, Units.val_mul, coe_diagHom]
    rfl
  have hprod : u 0 * u 1 * u 2 = 1 := by
    apply Units.ext
    have h := LinearMap.det_toMatrix e (g : V →ₗ[K] V)
    rw [hmat, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, hdet, coe_cycGL,
      det_cycMat, one_mul] at h
    simpa [u] using h
  refine ⟨diagHom 3 ![u 2, u 0, u 1], (mem_torus3 _).2 ⟨_, fun i => ?_, ?_, rfl⟩, ?_⟩
  · fin_cases i <;> exact (mem_normOne_iff_norm hK).2 (hN _)
  · change u 2 * u 0 * u 1 = 1
    rw [← hprod]
    ac_rfl
  · rw [hg', ← cycGL_conj_diagHom, inv_mul_cancel_right]

end Matrix

section Eigen

theorem eigenspace_conj (g w : LinearMap.GeneralLinearGroup K V) (c : K) :
    Module.End.eigenspace ((g * w * g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) c =
      (Module.End.eigenspace (w : Module.End K V) c).map (g : V →ₗ[K] V) := by
  have hgg : ∀ x : V, (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hgg' : ∀ x : V, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      ((g : V →ₗ[K] V) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_map, Units.val_mul,
    Module.End.mul_apply]
  constructor
  · intro hx
    refine ⟨((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x, ?_, hgg x⟩
    have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) hx
    rwa [hgg', map_smul] at this
  · rintro ⟨y, hy, rfl⟩
    rw [hgg', hy, map_smul]

theorem eigenspace_inf_eigenspace (g : Module.End K V) {μ ν : K} (hμν : μ ≠ ν) :
    g.eigenspace μ ⊓ g.eigenspace ν = ⊥ :=
  disjoint_iff.1 ((Module.End.eigenspaces_iSupIndep g).pairwiseDisjoint hμν)

variable (hK : UnitaryFieldData 2 f K) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}

include hK in
theorem apply_eq_zero_of_mem_eigenspace {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqUnitaryGroup B) {μ ν : K} (hμ : hK.norm μ = 1) (hμν : μ ≠ ν) {v x : V}
    (hv : v ∈ Module.End.eigenspace (g : Module.End K V) μ)
    (hx : x ∈ Module.End.eigenspace (g : Module.End K V) ν) :
    B v x = 0 := by
  rw [Module.End.mem_eigenspace_iff] at hv hx
  have h := (mem_sesqUnitaryGroup.1 hg) v x
  rw [hv, hx] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h
  have hbar : hK.bar μ * μ = 1 := by rw [mul_comm]; exact hμ
  have hne : hK.bar μ * ν - 1 ≠ 0 := by
    intro h'
    apply hμν
    have h0 : hK.bar μ ≠ 0 := left_ne_zero_of_mul_eq_one hbar
    exact mul_left_cancel₀ h0 (by rw [hbar]; linear_combination -h')
  have : (hK.bar μ * ν - 1) * B v x = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left hne

include hK in
theorem apply_eq_zero_swap (hB : B.IsSymm) {v x : V} (h : B v x = 0) : B x v = 0 := by
  rw [← hB.eq v x, h, map_zero]

end Eigen

section Action

variable (g h : LinearMap.GeneralLinearGroup K V)

theorem apply_inv_apply (x : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem inv_apply_apply (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem map_mul_eq (L : Submodule K V) :
    L.map ((g * h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      (L.map (h : V →ₗ[K] V)).map (g : V →ₗ[K] V) := by
  rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]

theorem map_one_eq (L : Submodule K V) :
    L.map ((1 : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = L := by
  rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id]

theorem map_inv_map (L : Submodule K V) :
    (L.map (g : V →ₗ[K] V)).map ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = L := by
  rw [← map_mul_eq, inv_mul_cancel, map_one_eq]

theorem map_injective {L L' : Submodule K V}
    (h : L.map (g : V →ₗ[K] V) = L'.map (g : V →ₗ[K] V)) : L = L' := by
  rw [← map_inv_map g L, h, map_inv_map]

theorem finrank_map_eq (L : Submodule K V) :
    finrank K (L.map (g : V →ₗ[K] V)) = finrank K L := by
  rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap g,
    LinearEquiv.finrank_map_eq]

theorem map_top_eq : (⊤ : Submodule K V).map (g : V →ₗ[K] V) = ⊤ := by
  rw [Submodule.map_top, LinearMap.range_eq_top]
  exact fun x => ⟨_, apply_inv_apply g x⟩

theorem map_eq_of_map_sq_eq (hg : Odd (orderOf g)) {L : Submodule K V}
    (h2 : L.map ((g ^ 2 : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = L) :
    L.map (g : V →ₗ[K] V) = L := by
  obtain ⟨k, hk⟩ := hg
  have hpow : ∀ n : ℕ,
      L.map ((g ^ (2 * n) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = L := by
    intro n
    induction n with
    | zero => rw [mul_zero, pow_zero, map_one_eq]
    | succ n ih => rw [mul_add, mul_one, pow_add, map_mul_eq, h2, ih]
  have h : (L.map ((g ^ (2 * k) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)).map
      (g : V →ₗ[K] V) = L.map (g : V →ₗ[K] V) := by rw [hpow k]
  rw [← map_mul_eq, ← pow_succ', ← hk, pow_orderOf_eq_one, map_one_eq] at h
  exact h.symm

end Action

section Homology

variable [FiniteDimensional K V] {w : LinearMap.GeneralLinearGroup K V} {ν μ : K}

theorem eigenspace_sup_eq_top (hV : finrank K V = 3) (hνμ : ν ≠ μ)
    (hwν : finrank K (Module.End.eigenspace (w : Module.End K V) ν) = 2)
    (hwμ : finrank K (Module.End.eigenspace (w : Module.End K V) μ) = 1) :
    Module.End.eigenspace (w : Module.End K V) μ ⊔ Module.End.eigenspace (w : Module.End K V) ν =
      ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace (w : Module.End K V) μ)
    (Module.End.eigenspace (w : Module.End K V) ν)
  rw [eigenspace_inf_eigenspace _ hνμ.symm, finrank_bot, hwμ, hwν] at h
  omega

omit [FiniteDimensional K V] in
theorem apply_mem_of_eigenspace_le
    (htop : Module.End.eigenspace (w : Module.End K V) μ ⊔
      Module.End.eigenspace (w : Module.End K V) ν = ⊤)
    {U : Submodule K V} (hU : Module.End.eigenspace (w : Module.End K V) μ ≤ U) {u : V}
    (hu : u ∈ U) : (w : V →ₗ[K] V) u ∈ U := by
  have hu' : u ∈ Module.End.eigenspace (w : Module.End K V) μ ⊔
      Module.End.eigenspace (w : Module.End K V) ν := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu'
  have haU := hU ha
  rw [Module.End.mem_eigenspace_iff] at ha hb
  have e : (w : V →ₗ[K] V) (a + b) = ν • (a + b) + (μ - ν) • a := by
    rw [map_add, ha, hb]
    module
  rw [e]
  exact U.add_mem (U.smul_mem _ hu) (U.smul_mem _ haU)

variable (hK : UnitaryFieldData 2 f K) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}

omit [FiniteDimensional K V] in
include hK in
theorem eq_zero_of_apply_self_eq_zero (hBl : B.SeparatingLeft) (hwS : w ∈ sesqUnitaryGroup B)
    (hμ : hK.norm μ = 1) (hμν : μ ≠ ν)
    (htop : Module.End.eigenspace (w : Module.End K V) μ ⊔
      Module.End.eigenspace (w : Module.End K V) ν = ⊤)
    (hwμ : finrank K (Module.End.eigenspace (w : Module.End K V) μ) = 1) {v : V}
    (hv : v ∈ Module.End.eigenspace (w : Module.End K V) μ) (h0 : B v v = 0) : v = 0 := by
  by_contra hv0
  have hℓ := eq_span_singleton_of_finrank_eq_one hwμ hv hv0
  apply hv0
  refine hBl v fun u => ?_
  have hu : u ∈ Module.End.eigenspace (w : Module.End K V) μ ⊔
      Module.End.eigenspace (w : Module.End K V) ν := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
  rw [hℓ] at ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  rw [map_add, map_smul, smul_eq_mul, h0, mul_zero, zero_add]
  exact apply_eq_zero_of_mem_eigenspace hK hwS hμ hμν hv hb

end Homology

section Conjugates

variable [FiniteDimensional K V] (hK : UnitaryFieldData 2 f K) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}

theorem map_eigenspace_eq_or_orthogonal (hV : finrank K V = 3) (hB : B.IsSymm)
    {H : Subgroup (LinearMap.GeneralLinearGroup K V)} (hHS : H ≤ sesqSpecialUnitaryGroup B)
    (hodd : Odd (Nat.card H)) (hsolv : Group.IsSolvable H)
    {w : LinearMap.GeneralLinearGroup K V} (hwH : w ∈ H) {ν μ : K} (hνμ : ν ≠ μ)
    (hμ : hK.norm μ = 1)
    (hwν : finrank K (Module.End.eigenspace (w : Module.End K V) ν) = 2)
    (hwμ : finrank K (Module.End.eigenspace (w : Module.End K V) μ) = 1)
    {g : LinearMap.GeneralLinearGroup K V} (hgH : g ∈ H) :
    (Module.End.eigenspace (w : Module.End K V) μ).map (g : V →ₗ[K] V) =
        Module.End.eigenspace (w : Module.End K V) μ ∨
      ∀ v ∈ Module.End.eigenspace (w : Module.End K V) μ,
        ∀ y ∈ (Module.End.eigenspace (w : Module.End K V) μ).map (g : V →ₗ[K] V), B v y = 0 := by
  classical
  have := hK.finite
  have : CharP K 2 := hK.charP
  have hwS : w ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B (hHS hwH)
  have hgS : g ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B (hHS hgH)
  set ℓ := Module.End.eigenspace (w : Module.End K V) μ with hℓdef
  set P := Module.End.eigenspace (w : Module.End K V) ν with hPdef
  by_cases hgl : ℓ.map (g : V →ₗ[K] V) = ℓ
  · exact Or.inl hgl
  right
  set w' := g * w * g⁻¹ with hw'def
  have hw'H : w' ∈ H := H.mul_mem (H.mul_mem hgH hwH) (H.inv_mem hgH)
  set ℓ' := ℓ.map (g : V →ₗ[K] V) with hℓ'def
  set P' := P.map (g : V →ₗ[K] V) with hP'def
  have hℓ' : Module.End.eigenspace (w' : Module.End K V) μ = ℓ' := eigenspace_conj g w μ
  have hP' : Module.End.eigenspace (w' : Module.End K V) ν = P' := eigenspace_conj g w ν
  have htop : ℓ ⊔ P = ⊤ := eigenspace_sup_eq_top hV hνμ hwν hwμ
  have htop' : ℓ' ⊔ P' = ⊤ := by rw [hℓ'def, hP'def, ← Submodule.map_sup, htop, map_top_eq]
  have hdimℓ' : finrank K ℓ' = 1 := by rw [hℓ'def, finrank_map_eq, hwμ]
  set U := ℓ ⊔ ℓ' with hUdef
  have hinf : ℓ ⊓ ℓ' = ⊥ := by
    have hle : finrank K (ℓ ⊓ ℓ' : Submodule K V) ≤ 1 := hwμ ▸ Submodule.finrank_mono inf_le_left
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · exact Submodule.finrank_eq_zero.1 h
    · exfalso
      have h1 : ℓ ⊓ ℓ' = ℓ := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h, hwμ])
      have h2 : ℓ ⊓ ℓ' = ℓ' := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h, hdimℓ'])
      exact hgl (h2.symm.trans h1)
  have hdimU : finrank K U = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq ℓ ℓ'
    rw [hinf, finrank_bot, hwμ, hdimℓ'] at h
    omega
  have hwU : ∀ u ∈ U, (w : V →ₗ[K] V) u ∈ U := fun u hu =>
    apply_mem_of_eigenspace_le htop le_sup_left hu
  have hw'U : ∀ u ∈ U, (w' : V →ₗ[K] V) u ∈ U := fun u hu =>
    apply_mem_of_eigenspace_le (w := w') (ν := ν) (by rw [hℓ', hP']; exact htop')
      (by rw [hℓ']; exact le_sup_right) hu
  let StabU : Subgroup (LinearMap.GeneralLinearGroup K V) :=
    { carrier := {x | U.map (x : V →ₗ[K] V) = U}
      mul_mem' := fun {x y} hx hy => by
        change U.map _ = U
        change U.map _ = U at hx hy
        rw [map_mul_eq, hy, hx]
      one_mem' := map_one_eq U
      inv_mem' := fun {x} hx => by
        change U.map _ = U at hx
        change U.map _ = U
        calc U.map ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
            = (U.map (x : V →ₗ[K] V)).map
                ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := by rw [hx]
          _ = U := map_inv_map x U }
  have hmapU : ∀ x : LinearMap.GeneralLinearGroup K V, (∀ u ∈ U, (x : V →ₗ[K] V) u ∈ U) →
      x ∈ StabU := fun x hx =>
    Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 hx) (finrank_map_eq x U)
  let J : Subgroup H := closure {⟨w, hwH⟩, ⟨w', hw'H⟩}
  have hJ : ∀ j : J, ((j : H) : LinearMap.GeneralLinearGroup K V) ∈ StabU := by
    have hle : J ≤ StabU.comap H.subtype := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · exact hmapU _ hwU
      · exact hmapU _ hw'U
    exact fun j => hle j.2
  have hJU : ∀ (j : J), ∀ u ∈ U,
      (((j : H) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u ∈ U := by
    intro j u hu
    have h := hJ j
    change U.map _ = U at h
    rw [← h]
    exact Submodule.mem_map_of_mem hu
  let ρ : J →* Module.End K U :=
    { toFun := fun j => (((j : H) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V).restrict
        (hJU j)
      map_one' := LinearMap.ext fun u => Subtype.ext rfl
      map_mul' := fun j k => LinearMap.ext fun u => Subtype.ext rfl }
  have : Finite H := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hJodd : Odd (Nat.card J) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card J)
  have hcomm := commute_of_odd_of_finrank_two hJodd inferInstance hdimU ρ
    ⟨⟨w, hwH⟩, subset_closure (Or.inl rfl)⟩ ⟨⟨w', hw'H⟩, subset_closure (Or.inr rfl)⟩
  have hcommV : ∀ u ∈ U, (w : V →ₗ[K] V) ((w' : V →ₗ[K] V) u) =
      (w' : V →ₗ[K] V) ((w : V →ₗ[K] V) u) := by
    intro u hu
    exact congrArg (fun F : Module.End K U => ((F ⟨u, hu⟩ : U) : V)) hcomm
  have hℓne : ℓ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hwμ
    exact zero_ne_one hwμ
  obtain ⟨v, hvℓ, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓne
  have hℓspan := eq_span_singleton_of_finrank_eq_one hwμ hvℓ hv0
  have hw'v : (w' : V →ₗ[K] V) v ∈ ℓ := by
    rw [hℓdef, Module.End.mem_eigenspace_iff, hcommV v (le_sup_left (a := ℓ) hvℓ),
      Module.End.mem_eigenspace_iff.1 hvℓ, map_smul]
  rw [hℓspan] at hw'v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw'v
  have hvtop : v ∈ ℓ' ⊔ P' := by rw [htop']; exact Submodule.mem_top
  obtain ⟨a', ha', b', hb', hvab⟩ := Submodule.mem_sup.1 hvtop
  have ha'e : (w' : V →ₗ[K] V) a' = μ • a' :=
    Module.End.mem_eigenspace_iff.1 (by rw [hℓ']; exact ha')
  have hb'e : (w' : V →ₗ[K] V) b' = ν • b' :=
    Module.End.mem_eigenspace_iff.1 (by rw [hP']; exact hb')
  have hinf' : ℓ' ⊓ P' = ⊥ := by
    rw [← hℓ', ← hP']
    exact eigenspace_inf_eigenspace _ hνμ.symm
  have hrel : (μ - c) • a' = (c - ν) • b' := by
    have h1 : (w' : V →ₗ[K] V) v = c • v := hc.symm
    rw [← hvab, map_add, ha'e, hb'e, smul_add] at h1
    linear_combination (norm := module) h1
  have hmem : (μ - c) • a' ∈ ℓ' ⊓ P' := ⟨ℓ'.smul_mem _ ha', hrel ▸ P'.smul_mem _ hb'⟩
  rw [hinf', Submodule.mem_bot] at hmem
  have hmem2 : (c - ν) • b' = 0 := hrel ▸ hmem
  have ha'0 : a' = 0 := by
    by_contra ha'0
    have hcμ : μ = c := sub_eq_zero.1 ((smul_eq_zero.1 hmem).resolve_right ha'0)
    have hb'0 : b' = 0 := (smul_eq_zero.1 hmem2).resolve_left
      (by rw [← hcμ]; exact sub_ne_zero.2 hνμ.symm)
    have hvℓ' : v ∈ ℓ' := by rw [← hvab, hb'0, add_zero]; exact ha'
    apply hgl
    refine (Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hwμ, hdimℓ'])).symm
    rw [hℓspan]
    exact (Submodule.span_singleton_le_iff_mem v ℓ').2 hvℓ'
  have hvP' : v ∈ P' := by rw [← hvab, ha'0, zero_add]; exact hb'
  intro v₁ hv₁ y hy
  rw [hℓspan] at hv₁
  obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.1 hv₁
  obtain ⟨p, hp, hpv⟩ := Submodule.mem_map.1 hvP'
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hy
  rw [map_smulₛₗ, LinearMap.smul_apply, ← hpv, (mem_sesqUnitaryGroup.1 hgS) p l,
    apply_eq_zero_swap hK hB (apply_eq_zero_of_mem_eigenspace hK hwS hμ hνμ.symm hl hp),
    smul_zero]

omit [FiniteDimensional K V] in
theorem eq_of_eigenspace_eq {x y : Module.End K V} {ν μ : K}
    (htop : Module.End.eigenspace x μ ⊔ Module.End.eigenspace x ν = ⊤)
    (hμ : Module.End.eigenspace x μ ≤ Module.End.eigenspace y μ)
    (hν : Module.End.eigenspace x ν ≤ Module.End.eigenspace y ν) : x = y := by
  ext u
  have hu : u ∈ Module.End.eigenspace x μ ⊔ Module.End.eigenspace x ν := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add, map_add, Module.End.mem_eigenspace_iff.1 ha, Module.End.mem_eigenspace_iff.1 hb,
    Module.End.mem_eigenspace_iff.1 (hμ ha), Module.End.mem_eigenspace_iff.1 (hν hb)]

include hK in
theorem commute_of_forall_map_eigenspace_eq (hV : finrank K V = 3) (hBl : B.SeparatingLeft)
    {H : Subgroup (LinearMap.GeneralLinearGroup K V)} (hHS : H ≤ sesqSpecialUnitaryGroup B)
    {w : LinearMap.GeneralLinearGroup K V} (hwH : w ∈ H) {ν μ : K} (hνμ : ν ≠ μ)
    (hμ : hK.norm μ = 1) (hwν : finrank K (Module.End.eigenspace (w : Module.End K V) ν) = 2)
    (hwμ : finrank K (Module.End.eigenspace (w : Module.End K V) μ) = 1)
    (hfix : ∀ g ∈ H, (Module.End.eigenspace (w : Module.End K V) μ).map (g : V →ₗ[K] V) =
      Module.End.eigenspace (w : Module.End K V) μ) :
    ∀ g ∈ H, g * w = w * g := by
  have hwS : w ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B (hHS hwH)
  set ℓ := Module.End.eigenspace (w : Module.End K V) μ with hℓdef
  set P := Module.End.eigenspace (w : Module.End K V) ν with hPdef
  have htop : ℓ ⊔ P = ⊤ := eigenspace_sup_eq_top hV hνμ hwν hwμ
  intro g hgH
  have hgS : g ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B (hHS hgH)
  have hPle : P.map (g : V →ₗ[K] V) ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    have hx : (g : V →ₗ[K] V) p ∈ ℓ ⊔ P := by rw [htop]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
    have hBa : B a ((g : V →ₗ[K] V) p) = 0 := by
      have ha' : a ∈ ℓ.map (g : V →ₗ[K] V) := by rw [hfix g hgH]; exact ha
      obtain ⟨a'', ha'', rfl⟩ := Submodule.mem_map.1 ha'
      rw [(mem_sesqUnitaryGroup.1 hgS) a'' p]
      exact apply_eq_zero_of_mem_eigenspace hK hwS hμ hνμ.symm ha'' hp
    rw [← hab, map_add, apply_eq_zero_of_mem_eigenspace hK hwS hμ hνμ.symm ha hb,
      add_zero] at hBa
    have ha0 := eq_zero_of_apply_self_eq_zero hK hBl hwS hμ hνμ.symm htop hwμ ha hBa
    rw [← hab, ha0, zero_add]
    exact hb
  have hPeq : P.map (g : V →ₗ[K] V) = P :=
    Submodule.eq_of_le_of_finrank_eq hPle (finrank_map_eq g P)
  have hconj : g * w * g⁻¹ = w := by
    apply Units.ext
    symm
    refine eq_of_eigenspace_eq (ν := ν) (μ := μ) htop ?_ ?_
    · rw [eigenspace_conj, hfix g hgH]
    · rw [eigenspace_conj, hPeq]
  calc g * w = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [hconj]

omit [FiniteDimensional K V] in
include hK in
theorem linearIndependent_of_orthogonal {ι : Type*} [Fintype ι] {v : ι → V}
    (horth : ∀ i j, i ≠ j → B (v i) (v j) = 0) (hiso : ∀ i, B (v i) (v i) ≠ 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (B (v i)) hc
  rw [map_sum, map_zero, Finset.sum_eq_single i] at h
  · rw [map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_right (hiso i)
  · intro j _ hji
    rw [map_smul, horth i j (Ne.symm hji), smul_zero]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

omit [FiniteDimensional K V] in
include hK in
theorem exists_apply_smul_smul_eq_one (hB : B.IsSymm) {v : V} (hv : B v v ≠ 0) :
    ∃ c : K, B (c • v) (c • v) = 1 := by
  have hd : hK.bar (B v v) = B v v := hB.eq v v
  have hd' : (B v v)⁻¹ ∈ hK.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hd]
  obtain ⟨c, hc⟩ := hK.normHom_surjective ⟨(B v v)⁻¹, hd'⟩
  refine ⟨c, ?_⟩
  rw [apply_smul_smul hK, show hK.norm c = (B v v)⁻¹ from congrArg Subtype.val hc,
    inv_mul_cancel₀ hv]

include hK in
theorem false_of_four_orthogonal (hV : finrank K V = 3) (hB : B.IsSymm) {x₁ x₂ x₃ x₄ : V}
    (h12 : B x₁ x₂ = 0) (h13 : B x₁ x₃ = 0) (h14 : B x₁ x₄ = 0) (h23 : B x₂ x₃ = 0)
    (h24 : B x₂ x₄ = 0) (h34 : B x₃ x₄ = 0) (h1 : B x₁ x₁ ≠ 0) (h2 : B x₂ x₂ ≠ 0)
    (h3 : B x₃ x₃ ≠ 0) (h4 : B x₄ x₄ ≠ 0) : False := by
  have h21 := apply_eq_zero_swap hK hB h12
  have h31 := apply_eq_zero_swap hK hB h13
  have h41 := apply_eq_zero_swap hK hB h14
  have h32 := apply_eq_zero_swap hK hB h23
  have h42 := apply_eq_zero_swap hK hB h24
  have h43 := apply_eq_zero_swap hK hB h34
  have hli := linearIndependent_of_orthogonal hK (B := B) (v := ![x₁, x₂, x₃, x₄])
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
    (fun i => by fin_cases i <;> simp_all)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hV] at this
  omega

end Conjugates

theorem odd_solvable_unitary_homology_forces_orthogonal_monomial_action
    (hK : UnitaryFieldData 2 f K) [FiniteDimensional K V] (hV : finrank K V = 3)
    {B : V →ₛₗ[hK.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {H : Subgroup (LinearMap.GeneralLinearGroup K V)} (hHS : H ≤ sesqSpecialUnitaryGroup B)
    (hodd : Odd (Nat.card H)) (hsolv : Group.IsSolvable H)
    {w : LinearMap.GeneralLinearGroup K V} (hwH : w ∈ H) (hwZ : ∃ g ∈ H, g * w ≠ w * g)
    {ν μ : K} (hνμ : ν ≠ μ) (hμ : hK.norm μ = 1)
    (hwν : finrank K (Module.End.eigenspace (w : Module.End K V) ν) = 2)
    (hwμ : finrank K (Module.End.eigenspace (w : Module.End K V) μ) = 1) :
    (∃ e : Basis (Fin 3) K V, (∀ i j, B (e i) (e j) = if i = j then 1 else 0) ∧
      (∀ g ∈ H, glMatrix e g ∈ monomialX (normOne K (2 ^ f))) ∧
      (∃ g ∈ H, ∃ d ∈ torus3 (normOne K (2 ^ f)), glMatrix e g = d * cycGL) ∧
      K ∙ e 2 = Module.End.eigenspace (w : Module.End K V) μ) ∧
    ∀ t ∈ sesqSpecialUnitaryGroup B, orderOf t = 2 →
      t ∈ normalizer (H : Set (LinearMap.GeneralLinearGroup K V)) → t * w = w * t →
      ∃ e : Basis (Fin 3) K V, (∀ i j, B (e i) (e j) = if i = j then 1 else 0) ∧
        (∀ g ∈ H, glMatrix e g ∈ monomialX (normOne K (2 ^ f))) ∧
        (∃ g ∈ H, ∃ d ∈ torus3 (normOne K (2 ^ f)), glMatrix e g = d * cycGL) ∧
        K ∙ e 2 = Module.End.eigenspace (w : Module.End K V) μ ∧ glMatrix e t = s01GL := by
  classical
  have := hK.finite
  have : CharP K 2 := hK.charP
  have hwS : w ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B (hHS hwH)
  set ℓ := Module.End.eigenspace (w : Module.End K V) μ with hℓdef
  set P := Module.End.eigenspace (w : Module.End K V) ν with hPdef
  have htop : ℓ ⊔ P = ⊤ := eigenspace_sup_eq_top hV hνμ hwν hwμ
  have hFinH : Finite H := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hoddo : ∀ h ∈ H, Odd (orderOf h) := fun h hh => by
    have := Odd.of_dvd_nat hodd (orderOf_dvd_natCard (⟨h, hh⟩ : H))
    rwa [Subgroup.orderOf_mk] at this
  have hiso : ∀ h ∈ H, ∀ x y, B ((h : V →ₗ[K] V) x) ((h : V →ₗ[K] V) y) = B x y :=
    fun h hh => mem_sesqUnitaryGroup.1 (sesqSpecialUnitaryGroup_le B (hHS hh))
  have hℓne : ℓ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hwμ
    exact zero_ne_one hwμ
  obtain ⟨v₀, hv₀ℓ, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓne
  have hBv₀ : B v₀ v₀ ≠ 0 := fun h =>
    hv₀0 (eq_zero_of_apply_self_eq_zero hK hBl hwS hμ hνμ.symm htop hwμ hv₀ℓ h)
  obtain ⟨c₀, hc₀⟩ := exists_apply_smul_smul_eq_one hK hB hBv₀
  set u₀ := c₀ • v₀ with hu₀def
  have hu₀ℓ : u₀ ∈ ℓ := ℓ.smul_mem _ hv₀ℓ
  have horth : ∀ k₁ ∈ H, ∀ k₂ ∈ H, ℓ.map (k₁ : V →ₗ[K] V) ≠ ℓ.map (k₂ : V →ₗ[K] V) →
      ∀ x ∈ ℓ, ∀ y ∈ ℓ, B ((k₁ : V →ₗ[K] V) x) ((k₂ : V →ₗ[K] V) y) = 0 := by
    intro k₁ hk₁ k₂ hk₂ hne x hx y hy
    have hk : k₁⁻¹ * k₂ ∈ H := H.mul_mem (H.inv_mem hk₁) hk₂
    rcases map_eigenspace_eq_or_orthogonal hK hV hB hHS hodd hsolv hwH hνμ hμ hwν hwμ hk with
      h | h <;> rw [← hℓdef] at h
    · exfalso
      apply hne
      calc ℓ.map (k₁ : V →ₗ[K] V) =
          (ℓ.map ((k₁⁻¹ * k₂ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)).map
            (k₁ : V →ₗ[K] V) := by rw [h]
        _ = ℓ.map (k₂ : V →ₗ[K] V) := by rw [← map_mul_eq, mul_inv_cancel_left]
    · have hy' : ((k₁⁻¹ * k₂ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y ∈
          ℓ.map ((k₁⁻¹ * k₂ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) :=
        Submodule.mem_map_of_mem hy
      have h' := h x hx _ hy'
      rw [← hiso k₁ hk₁, Units.val_mul, Module.End.mul_apply, apply_inv_apply] at h'
      exact h'
  obtain ⟨g, hgH, hgℓ⟩ : ∃ g ∈ H, ℓ.map (g : V →ₗ[K] V) ≠ ℓ := by
    by_contra! h
    obtain ⟨g', hg', hg'w⟩ := hwZ
    exact hg'w (commute_of_forall_map_eigenspace_eq hK hV hBl hHS hwH hνμ hμ hwν hwμ
      (by rw [← hℓdef]; exact h) g' hg')
  have hgg : g * g ∈ H := H.mul_mem hgH hgH
  set ℓ0 := ℓ.map (g : V →ₗ[K] V) with hℓ0def
  set ℓ1 := ℓ.map ((g * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) with hℓ1def
  have hℓ1g : ℓ1 = ℓ0.map (g : V →ₗ[K] V) := map_mul_eq g g ℓ
  have h02 : ℓ0 ≠ ℓ := hgℓ
  have h12 : ℓ1 ≠ ℓ := fun h => hgℓ (map_eq_of_map_sq_eq g (hoddo g hgH) (by rw [sq]; exact h))
  have h10 : ℓ1 ≠ ℓ0 := fun h => hgℓ (map_injective g (by rw [← hℓ1g]; exact h))
  have hunit : ∀ k ∈ H, B ((k : V →ₗ[K] V) u₀) ((k : V →ₗ[K] V) u₀) = 1 := fun k hk => by
    rw [hiso k hk, hc₀]
  have hone : (1 : V →ₗ[K] V) u₀ = u₀ := rfl
  have hthree : ∀ h ∈ H, ℓ.map (h : V →ₗ[K] V) = ℓ0 ∨ ℓ.map (h : V →ₗ[K] V) = ℓ1 ∨
      ℓ.map (h : V →ₗ[K] V) = ℓ := by
    intro h hh
    by_contra hne
    push Not at hne
    obtain ⟨hn0, hn1, hn2⟩ := hne
    have hl : ℓ.map ((1 : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ℓ := map_one_eq ℓ
    refine false_of_four_orthogonal hK hV hB
      (horth h hh g hgH hn0 _ hu₀ℓ _ hu₀ℓ) (horth h hh (g * g) hgg hn1 _ hu₀ℓ _ hu₀ℓ)
      (horth h hh 1 H.one_mem (by rw [hl]; exact hn2) _ hu₀ℓ _ hu₀ℓ)
      (horth g hgH (g * g) hgg h10.symm _ hu₀ℓ _ hu₀ℓ)
      (horth g hgH 1 H.one_mem (by rw [hl]; exact h02) _ hu₀ℓ _ hu₀ℓ)
      (horth (g * g) hgg 1 H.one_mem (by rw [hl]; exact h12) _ hu₀ℓ _ hu₀ℓ)
      (by rw [hunit h hh]; exact one_ne_zero) (by rw [hunit g hgH]; exact one_ne_zero)
      (by rw [hunit _ hgg]; exact one_ne_zero) (by rw [hunit 1 H.one_mem]; exact one_ne_zero)
  have hgℓ1 : ℓ1.map (g : V →ₗ[K] V) = ℓ := by
    have hggg : g * (g * g) ∈ H := H.mul_mem hgH hgg
    have e : ℓ.map ((g * (g * g) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
        ℓ1.map (g : V →ₗ[K] V) := map_mul_eq g (g * g) ℓ
    rcases hthree _ hggg with h | h | h <;> rw [e] at h
    · exact absurd (map_injective g (h.trans hℓ0def)) h12
    · exact absurd (map_injective g (h.trans hℓ1g)) h10
    · exact h
  have hfix3 : ∀ h ∈ H, ℓ.map (h : V →ₗ[K] V) = ℓ →
      ℓ0.map (h : V →ₗ[K] V) = ℓ0 ∧ ℓ1.map (h : V →ₗ[K] V) = ℓ1 := by
    intro h hh hhℓ
    have e0 : ℓ0.map (h : V →ₗ[K] V) =
        ℓ.map ((h * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := (map_mul_eq h g ℓ).symm
    have e1 : ℓ1.map (h : V →ₗ[K] V) =
        ℓ.map ((h * (g * g) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) :=
      (map_mul_eq h (g * g) ℓ).symm
    have hn2 : ℓ0.map (h : V →ₗ[K] V) ≠ ℓ := fun h' =>
      h02 (map_injective h (h'.trans hhℓ.symm))
    have hn2' : ℓ1.map (h : V →ₗ[K] V) ≠ ℓ := fun h' =>
      h12 (map_injective h (h'.trans hhℓ.symm))
    have h0 : ℓ0.map (h : V →ₗ[K] V) = ℓ0 := by
      rcases hthree _ (H.mul_mem hh hgH) with h' | h' | h' <;> rw [← e0] at h'
      · exact h'
      · exfalso
        have h1 : ℓ1.map (h : V →ₗ[K] V) = ℓ0 := by
          rcases hthree _ (H.mul_mem hh hgg) with h'' | h'' | h'' <;> rw [← e1] at h''
          · exact h''
          · exact absurd (map_injective h (h''.trans h'.symm)) h10
          · exact absurd h'' hn2'
        have hsq : ℓ0.map ((h ^ 2 : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ℓ0 := by
          rw [sq, map_mul_eq, h', h1]
        exact h10 (h'.symm.trans (map_eq_of_map_sq_eq h (hoddo h hh) hsq))
      · exact absurd h' hn2
    refine ⟨h0, ?_⟩
    rcases hthree _ (H.mul_mem hh hgg) with h' | h' | h' <;> rw [← e1] at h'
    · exact absurd (map_injective h (h'.trans h0.symm)) h10
    · exact h'
    · exact absurd h' hn2'
  let Lf : Fin 3 → Submodule K V := ![ℓ0, ℓ1, ℓ]
  have hLdim : ∀ i, finrank K (Lf i) = 1 := by
    intro i
    fin_cases i
    · change finrank K ℓ0 = 1
      rw [hℓ0def, finrank_map_eq, hwμ]
    · change finrank K ℓ1 = 1
      rw [hℓ1def, finrank_map_eq, hwμ]
    · exact hwμ
  have hgL : ∀ i, (Lf i).map (g : V →ₗ[K] V) = Lf (finRotate 3 i) := by
    intro i
    fin_cases i
    · exact hℓ1g.symm
    · exact hgℓ1
    · rfl
  have hfixL : ∀ h ∈ H, ℓ.map (h : V →ₗ[K] V) = ℓ → ∀ i, (Lf i).map (h : V →ₗ[K] V) = Lf i := by
    intro h hh hhℓ i
    obtain ⟨h0, h1⟩ := hfix3 h hh hhℓ
    fin_cases i
    · exact h0
    · exact h1
    · exact hhℓ
  have hmono : ∀ e : Basis (Fin 3) K V, (∀ i j, B (e i) (e j) = if i = j then 1 else 0) →
      (∀ i, e i ∈ Lf i) → (∀ h ∈ H, glMatrix e h ∈ monomialX (normOne K (2 ^ f))) ∧
        ∃ d ∈ torus3 (normOne K (2 ^ f)), glMatrix e g = d * cycGL := by
    intro e he heL
    have he0 : ∀ i, e i ≠ 0 := fun i h => by
      have := he i i
      rw [h, map_zero, ite_eq_left rfl] at this
      exact zero_ne_one this
    have hspan : ∀ i, Lf i = K ∙ e i := fun i =>
      eq_span_singleton_of_finrank_eq_one (hLdim i) (heL i) (he0 i)
    have hdiag : ∀ h ∈ H, ℓ.map (h : V →ₗ[K] V) = ℓ →
        glMatrix e h ∈ torus3 (normOne K (2 ^ f)) := by
      intro h hh hhℓ
      have hc : ∀ i, ∃ c : K, (h : V →ₗ[K] V) (e i) = c • e i := by
        intro i
        have hm : (h : V →ₗ[K] V) (e i) ∈ Lf i := by
          rw [← hfixL h hh hhℓ i]
          exact Submodule.mem_map_of_mem (heL i)
        rw [hspan i] at hm
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
        exact ⟨c, hc.symm⟩
      choose c hc using hc
      exact glMatrix_mem_torus3 hK e he (hHS hh) c hc
    have hcyc : ∃ d ∈ torus3 (normOne K (2 ^ f)), glMatrix e g = d * cycGL := by
      have hc : ∀ i, ∃ c : K, (g : V →ₗ[K] V) (e i) = c • e (finRotate 3 i) := by
        intro i
        have hm : (g : V →ₗ[K] V) (e i) ∈ Lf (finRotate 3 i) := by
          rw [← hgL i]
          exact Submodule.mem_map_of_mem (heL i)
        rw [hspan] at hm
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
        exact ⟨c, hc.symm⟩
      choose c hc using hc
      exact exists_glMatrix_eq_mul_cycGL hK e he (hHS hgH) c hc
    obtain ⟨d, hd, hgd⟩ := hcyc
    have hgX : glMatrix e g ∈ monomialX (normOne K (2 ^ f)) := by
      rw [hgd]
      exact mul_mem (mem_sup_left hd) (mem_sup_right (mem_zpowers _))
    refine ⟨fun h hh => ?_, d, hd, hgd⟩
    rcases hthree h hh with h' | h' | h'
    · have hfix' : ℓ.map ((g⁻¹ * h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ℓ := by
        rw [map_mul_eq, h', hℓ0def, map_inv_map]
      have hm := hdiag _ (H.mul_mem (H.inv_mem hgH) hh) hfix'
      rw [show h = g * (g⁻¹ * h) by group, map_mul]
      exact mul_mem hgX (mem_sup_left hm)
    · have hfix' :
          ℓ.map (((g * g)⁻¹ * h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ℓ := by
        rw [map_mul_eq, h', hℓ1def, map_inv_map]
      have hm := hdiag _ (H.mul_mem (H.inv_mem hgg) hh) hfix'
      rw [show h = (g * g) * ((g * g)⁻¹ * h) by group, map_mul, map_mul]
      exact mul_mem (mul_mem hgX hgX) (mem_sup_left hm)
    · exact mem_sup_left (hdiag h hh h')
  have hl1 : ℓ.map ((1 : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ℓ := map_one_eq ℓ
  have hu₀0 : u₀ ≠ 0 := fun h => by simp [h] at hc₀
  let ev : Fin 3 → V :=
    ![(g : V →ₗ[K] V) u₀, ((g * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u₀, u₀]
  have hev : ∀ i j, B (ev i) (ev j) = if i = j then 1 else 0 := by
    have h01 := horth g hgH (g * g) hgg h10.symm _ hu₀ℓ _ hu₀ℓ
    have h02' := horth g hgH 1 H.one_mem (by rw [hl1]; exact h02) _ hu₀ℓ _ hu₀ℓ
    have h12' := horth (g * g) hgg 1 H.one_mem (by rw [hl1]; exact h12) _ hu₀ℓ _ hu₀ℓ
    have h10' := apply_eq_zero_swap hK hB h01
    have h20' := apply_eq_zero_swap hK hB h02'
    have h21' := apply_eq_zero_swap hK hB h12'
    have hg1 := hunit g hgH
    have hg2 := hunit _ hgg
    simp only [Units.val_one, Module.End.one_apply, Units.val_mul, Module.End.mul_apply]
      at h01 h02' h12' h10' h20' h21' hg2
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ev, h01, h02', h12', h10', h20', h21', hg1, hg2, hc₀]
  have hli : LinearIndependent K ev := linearIndependent_of_orthogonal hK (B := B)
    (fun i j hij => by rw [hev, ite_eq_right hij])
    (fun i => by rw [hev, ite_eq_left rfl]; exact one_ne_zero)
  let e := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have he : ∀ i, e i = ev i := fun i => by
    simp only [e, coe_basisOfLinearIndependentOfCardEqFinrank]
  have heo : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := fun i j => by rw [he, he, hev]
  have heL : ∀ i, e i ∈ Lf i := by
    intro i
    rw [he]
    fin_cases i
    · exact Submodule.mem_map_of_mem hu₀ℓ
    · exact Submodule.mem_map_of_mem hu₀ℓ
    · exact hu₀ℓ
  have he0 : ∀ i, e i ≠ 0 := fun i h => by
    have := heo i i
    rw [h, map_zero, ite_eq_left rfl] at this
    exact zero_ne_one this
  have hspan : ∀ i, Lf i = K ∙ e i := fun i =>
    eq_span_singleton_of_finrank_eq_one (hLdim i) (heL i) (he0 i)
  obtain ⟨hmono1, d, hd, hgd⟩ := hmono e heo heL
  refine ⟨⟨e, heo, hmono1, ⟨g, hgH, d, hd, hgd⟩, (hspan 2).symm⟩, ?_⟩
  intro t htS ht2 htN htw
  have htiso := mem_sesqUnitaryGroup.1 (sesqSpecialUnitaryGroup_le B htS)
  have htsq : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have htt : ∀ x, (t : V →ₗ[K] V) ((t : V →ₗ[K] V) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, htsq, Units.val_one, Module.End.one_apply]
  have hscal1 : ∀ x : V, x ≠ 0 → ∀ c : K, (t : V →ₗ[K] V) x = c • x → c = 1 := by
    intro x hx c hc
    have h := htt x
    rw [hc, map_smul, hc, smul_smul] at h
    have hc2 : c * c = 1 := by
      have h' : (c * c - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hx)
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : (c - 1) ^ 2 = 0 := by linear_combination hc2 - (c - 1) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h3)
  have htℓ : ℓ.map (t : V →ₗ[K] V) = ℓ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_map_eq t ℓ)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    rw [hℓdef, Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← Units.val_mul, ← htw, Units.val_mul, Module.End.mul_apply, hv,
      map_smul]
  have htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H := fun h hh => (mem_normalizer_iff.1 htN h).1 hh
  have htmap : ∀ h ∈ H, (ℓ.map (h : V →ₗ[K] V)).map (t : V →ₗ[K] V) =
      ℓ.map ((t * h * t⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := by
    intro h hh
    calc (ℓ.map (h : V →ₗ[K] V)).map (t : V →ₗ[K] V)
        = ℓ.map ((t * h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) :=
          (map_mul_eq t h ℓ).symm
      _ = ℓ.map ((t * h * t⁻¹ * t : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := by
          rw [inv_mul_cancel_right]
      _ = (ℓ.map (t : V →ₗ[K] V)).map
            ((t * h * t⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) :=
          map_mul_eq _ _ ℓ
      _ = _ := by rw [htℓ]
  have ht0 : ℓ0.map (t : V →ₗ[K] V) = ℓ1 := by
    rcases hthree _ (htH g hgH) with h | h | h <;> rw [← htmap g hgH] at h
    · exfalso
      have h1 : ℓ1.map (t : V →ₗ[K] V) = ℓ1 := by
        rcases hthree _ (htH (g * g) hgg) with h' | h' | h' <;> rw [← htmap (g * g) hgg] at h'
        · exact absurd (map_injective t (h'.trans h.symm)) h10
        · exact h'
        · exact absurd (map_injective t (h'.trans htℓ.symm)) h12
      have hfixall : ∀ i, (Lf i).map (t : V →ₗ[K] V) = Lf i := by
        intro i
        fin_cases i
        · exact h
        · exact h1
        · exact htℓ
      have ht1 : t = 1 := by
        apply Units.ext
        refine e.ext fun i => ?_
        have hm : (t : V →ₗ[K] V) (e i) ∈ Lf i := by
          rw [← hfixall i]
          exact Submodule.mem_map_of_mem (heL i)
        rw [hspan i] at hm
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
        rw [Units.val_one, Module.End.one_apply, ← hc, hscal1 (e i) (he0 i) c hc.symm, one_smul]
      rw [ht1, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    · exact h
    · exact absurd (map_injective t (h.trans htℓ.symm)) h02
  have ht0' : (t : V →ₗ[K] V) (e 0) ∈ Lf 1 := by
    change (t : V →ₗ[K] V) (e 0) ∈ ℓ1
    rw [← ht0]
    exact Submodule.mem_map_of_mem (heL 0)
  rw [hspan 1] at ht0'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ht0'
  have ht2' : (t : V →ₗ[K] V) (e 2) ∈ Lf 2 := by
    change (t : V →ₗ[K] V) (e 2) ∈ ℓ
    rw [← htℓ]
    exact Submodule.mem_map_of_mem (heL 2)
  rw [hspan 2] at ht2'
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.1 ht2'
  have hte2 : (t : V →ₗ[K] V) (e 2) = e 2 := by
    rw [← hc₂, hscal1 (e 2) (he0 2) c₂ hc₂.symm, one_smul]
  let ev' : Fin 3 → V := ![e 0, (t : V →ₗ[K] V) (e 0), e 2]
  have hev' : ∀ i j, B (ev' i) (ev' j) = if i = j then 1 else 0 := by
    have h00 := heo 0 0
    have h22 := heo 2 2
    have h02'' := heo 0 2
    have h20'' := heo 2 0
    have htt0 : B ((t : V →ₗ[K] V) (e 0)) ((t : V →ₗ[K] V) (e 0)) = 1 := by
      rw [htiso, h00, ite_eq_left rfl]
    have h01 : B (e 0) ((t : V →ₗ[K] V) (e 0)) = 0 := by
      rw [← hc, map_smul, heo 0 1, smul_eq_mul]
      simp
    have h21 : B (e 2) ((t : V →ₗ[K] V) (e 0)) = 0 := by
      rw [← hc, map_smul, heo 2 1, smul_eq_mul]
      simp
    have h10 := apply_eq_zero_swap hK hB h01
    have h12 := apply_eq_zero_swap hK hB h21
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ev', h00, h22, h02'', h20'', htt0, h01, h21, h10, h12]
  have hli' : LinearIndependent K ev' := linearIndependent_of_orthogonal hK (B := B)
    (fun i j hij => by rw [hev', ite_eq_right hij])
    (fun i => by rw [hev', ite_eq_left rfl]; exact one_ne_zero)
  let e' := basisOfLinearIndependentOfCardEqFinrank hli' (by rw [Fintype.card_fin, hV])
  have he' : ∀ i, e' i = ev' i := fun i => by
    simp only [e', coe_basisOfLinearIndependentOfCardEqFinrank]
  have heo' : ∀ i j, B (e' i) (e' j) = if i = j then 1 else 0 := fun i j => by
    rw [he', he', hev']
  have heL' : ∀ i, e' i ∈ Lf i := by
    intro i
    rw [he']
    fin_cases i
    · exact heL 0
    · change (t : V →ₗ[K] V) (e 0) ∈ ℓ1
      rw [← ht0]
      exact Submodule.mem_map_of_mem (heL 0)
    · exact heL 2
  obtain ⟨hmono2, d', hd', hgd'⟩ := hmono e' heo' heL'
  have he'0 : e' 2 ≠ 0 := by rw [he']; exact he0 2
  refine ⟨e', heo', hmono2, ⟨g, hgH, d', hd', hgd'⟩,
    (eq_span_singleton_of_finrank_eq_one hwμ (heL' 2) he'0).symm, ?_⟩
  have hte0 : (t : V →ₗ[K] V) (e' 0) = e' 1 := by rw [he', he']; rfl
  have hte1 : (t : V →ₗ[K] V) (e' 1) = e' 0 := by rw [he', he']; exact htt (e 0)
  have hte2' : (t : V →ₗ[K] V) (e' 2) = e' 2 := by rw [he']; exact hte2
  apply Units.ext
  rw [coe_glMatrix, coe_s01GL]
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases j
  · change (e'.repr ((t : V →ₗ[K] V) (e' 0))) i = s01Mat i 0
    rw [hte0, e'.repr_self]
    fin_cases i <;> simp [s01Mat, CharTwo.neg_eq]
  · change (e'.repr ((t : V →ₗ[K] V) (e' 1))) i = s01Mat i 1
    rw [hte1, e'.repr_self]
    fin_cases i <;> simp [s01Mat, CharTwo.neg_eq]
  · change (e'.repr ((t : V →ₗ[K] V) (e' 2))) i = s01Mat i 2
    rw [hte2', e'.repr_self]
    fin_cases i <;> simp [s01Mat, CharTwo.neg_eq]

end CFSG.OddSolvableUnitary
