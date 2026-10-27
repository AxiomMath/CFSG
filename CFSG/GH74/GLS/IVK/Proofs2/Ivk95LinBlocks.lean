module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinSL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup
open scoped MatrixGroups Matrix

section Blocks

variable {k : Type} [Field k] {m : ℕ}

theorem ivk95l_block_fst {a b : ℕ} (hb : 1 ≤ b) {g : SL(m, k)}
    (Θ : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) ≃*
      GL (Fin a) k × GL (Fin b) k)
    (hΘ : ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))),
      Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
        (Matrix.GeneralLinearGroup.scalar (Fin a) c, Matrix.GeneralLinearGroup.scalar (Fin b) c))
    (hperf : Group.IsPerfect SL(a, k)) (hm : 0 < m) :
    ∃ ξ : SL(a, k) →* SL(m, k),
      (∀ x, Matrix.SpecialLinearGroup.toGL (ξ x) =
        ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1) : Subgroup.centralizer
          ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k)) ∧
      (∀ x, ξ x * g = g * ξ x) ∧
      (∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ x * n⁻¹ = ξ x') ∧
      (∀ x, ξ x ∈ Subgroup.center SL(m, k) → x = 1) := by
  let ψ : SL(a, k) →* GL (Fin m) k :=
    (Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))).subtype.comp
      (Θ.symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp Matrix.SpecialLinearGroup.toGL))
  have hψ : ∀ x, ψ x = ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1) : Subgroup.centralizer
      ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) := fun x => rfl
  have hdet : ∀ x, (ψ x : Matrix (Fin m) (Fin m) k).det = 1 := by
    intro x
    have h1 := ivk95l_hom_one_of_perfect hperf
      ((Matrix.GeneralLinearGroup.det : GL (Fin m) k →* kˣ).comp ψ)
    have h2 := congrArg (fun f : SL(a, k) →* kˣ => ((f x : kˣ) : k)) h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
  let ξ : SL(a, k) →* SL(m, k) :=
    { toFun := fun x => ⟨(ψ x : Matrix (Fin m) (Fin m) k), hdet x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((ψ (x * y) : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
          (ψ x : Matrix (Fin m) (Fin m) k) * (ψ y : Matrix (Fin m) (Fin m) k)
        rw [map_mul, Units.val_mul]) }
  have hξ : ∀ x, Matrix.SpecialLinearGroup.toGL (ξ x) = ψ x := fun x => Units.ext rfl
  have hcent : ∀ x, ψ x * Matrix.SpecialLinearGroup.toGL g = Matrix.SpecialLinearGroup.toGL g * ψ x :=
    fun x => Subgroup.mem_centralizer_singleton_iff.1
      ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1)).2)
  refine ⟨ξ, fun x => by rw [hξ, hψ], fun x => ?_, fun n hn x => ?_, fun x hx => ?_⟩
  · apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hξ]
    exact hcent x
  · have hnc : Matrix.SpecialLinearGroup.toGL n ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hn]
    obtain ⟨p, hp⟩ : ∃ p : GL (Fin a) k × GL (Fin b) k, Θ ⟨Matrix.SpecialLinearGroup.toGL n, hnc⟩ = p :=
      ⟨_, rfl⟩
    obtain ⟨y₁, y₂⟩ := p
    have hdx : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL x) = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact x.2)
    have hdetx : ((y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹ : GL (Fin a) k) :
        Matrix (Fin a) (Fin a) k).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y₁), mul_assoc,
          mul_inv_cancel, mul_one, hdx]
      have h2 := Matrix.GeneralLinearGroup.val_det_apply
        (y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹)
      rw [h1, Units.val_one] at h2
      exact h2.symm
    let x' : SL(a, k) := ⟨((y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹ : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k), hdetx⟩
    have hx'GL : Matrix.SpecialLinearGroup.toGL x' = y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹ :=
      Units.ext rfl
    have hnc' : (⟨Matrix.SpecialLinearGroup.toGL n, hnc⟩ : Subgroup.centralizer
        ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) = Θ.symm (y₁, y₂) := by
      rw [← hp, MulEquiv.symm_apply_apply]
    have hnGL : Matrix.SpecialLinearGroup.toGL n = ((Θ.symm (y₁, y₂) : Subgroup.centralizer
        ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) :=
      congrArg Subtype.val hnc'
    refine ⟨x', ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, hξ, hξ, hψ, hψ, hx'GL, hnGL]
    calc ((Θ.symm (y₁, y₂) : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
          GL (Fin m) k) *
        ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1) : Subgroup.centralizer
          ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) *
        ((Θ.symm (y₁, y₂) : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
          GL (Fin m) k)⁻¹
        = ((Θ.symm (y₁, y₂) * Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1) * (Θ.symm (y₁, y₂))⁻¹ :
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
            GL (Fin m) k) := rfl
      _ = ((Θ.symm ((y₁, y₂) * (Matrix.SpecialLinearGroup.toGL x, 1) * (y₁, y₂)⁻¹) :
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
            GL (Fin m) k) := by rw [map_mul, map_mul, map_inv]
      _ = ((Θ.symm (y₁ * Matrix.SpecialLinearGroup.toGL x * y₁⁻¹, 1) :
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
            GL (Fin m) k) := by
          congr 2
          simp
  · obtain ⟨c, hc⟩ := ivk95l_center_scalar hm hx
    have hcc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Matrix.GeneralLinearGroup.scalar_commute c _)
    have h1 : Θ.symm (Matrix.SpecialLinearGroup.toGL x, 1) = ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hcc⟩ :=
      Subtype.ext (by
        exact ((hψ x).symm.trans (hξ x).symm).trans hc)
    have h2 : (Matrix.SpecialLinearGroup.toGL x, 1) =
        (Matrix.GeneralLinearGroup.scalar (Fin a) c, Matrix.GeneralLinearGroup.scalar (Fin b) c) := by
      rw [← hΘ c hcc, ← h1, MulEquiv.apply_symm_apply]
    have h3 : Matrix.SpecialLinearGroup.toGL x = Matrix.GeneralLinearGroup.scalar (Fin a) c :=
      congrArg Prod.fst h2
    have h4 : (1 : GL (Fin b) k) = Matrix.GeneralLinearGroup.scalar (Fin b) c := congrArg Prod.snd h2
    have hc1 : c = 1 := ivk95l_scalar_eq_one hb h4.symm
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [h3, hc1, map_one, map_one]

theorem ivk95l_block_pair {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {g : SL(m, k)}
    (Θ : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) ≃*
      GL (Fin a) k × GL (Fin b) k)
    (hΘ : ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))),
      Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
        (Matrix.GeneralLinearGroup.scalar (Fin a) c, Matrix.GeneralLinearGroup.scalar (Fin b) c))
    (hpa : Group.IsPerfect SL(a, k)) (hpb : Group.IsPerfect SL(b, k)) (hm : 0 < m) :
    ∃ (ξ₁ : SL(a, k) →* SL(m, k)) (ξ₂ : SL(b, k) →* SL(m, k)),
      ((∀ x, ξ₁ x * g = g * ξ₁ x) ∧
        (∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ₁ x * n⁻¹ = ξ₁ x') ∧
        (∀ x, ξ₁ x ∈ Subgroup.center SL(m, k) → x = 1)) ∧
      ((∀ y, ξ₂ y * g = g * ξ₂ y) ∧
        (∀ n : SL(m, k), n * g = g * n → ∀ y, ∃ y', n * ξ₂ y * n⁻¹ = ξ₂ y') ∧
        (∀ y, ξ₂ y ∈ Subgroup.center SL(m, k) → y = 1)) ∧
      (∀ x y, ξ₁ x * ξ₂ y = ξ₂ y * ξ₁ x) ∧
      (∀ (c : kˣ) (u : SL(a, k)) (v : SL(b, k)), Matrix.SpecialLinearGroup.toGL u =
          Matrix.GeneralLinearGroup.scalar (Fin a) c → Matrix.SpecialLinearGroup.toGL v =
          Matrix.GeneralLinearGroup.scalar (Fin b) c → ξ₁ u * ξ₂ v ∈ Subgroup.center SL(m, k)) ∧
      (∀ x y, ξ₁ x * ξ₂ y ∈ Subgroup.center SL(m, k) →
        ∃ c : kˣ, Matrix.SpecialLinearGroup.toGL x = Matrix.GeneralLinearGroup.scalar (Fin a) c) := by
  obtain ⟨ξ₁, h1a, h1b, h1c, h1d⟩ := ivk95l_block_fst hb Θ hΘ hpa hm
  let Θ' : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) ≃*
      GL (Fin b) k × GL (Fin a) k := Θ.trans MulEquiv.prodComm
  have hΘ' : ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))),
      Θ' ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
        (Matrix.GeneralLinearGroup.scalar (Fin b) c, Matrix.GeneralLinearGroup.scalar (Fin a) c) := by
    intro c hc
    show Prod.swap (Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩) = _
    rw [hΘ c hc]
    rfl
  obtain ⟨ξ₂, h2a, h2b, h2c, h2d⟩ := ivk95l_block_fst ha Θ' hΘ' hpb hm
  have hξ₂ : ∀ y, Matrix.SpecialLinearGroup.toGL (ξ₂ y) =
      ((Θ.symm (1, Matrix.SpecialLinearGroup.toGL y) : Subgroup.centralizer
        ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) := by
    intro y
    rw [h2a]
    rfl
  have hprod : ∀ x y, Matrix.SpecialLinearGroup.toGL (ξ₁ x * ξ₂ y) =
      ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, Matrix.SpecialLinearGroup.toGL y) :
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
        GL (Fin m) k) := by
    intro x y
    rw [map_mul, h1a, hξ₂, ← Subgroup.coe_mul, ← map_mul]
    simp
  refine ⟨ξ₁, ξ₂, ⟨h1b, h1c, h1d⟩, ⟨h2b, h2c, h2d⟩, fun x y => ?_, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.toGL_injective
    have h1 := hprod x y
    have h2 : Matrix.SpecialLinearGroup.toGL (ξ₂ y * ξ₁ x) =
        ((Θ.symm (Matrix.SpecialLinearGroup.toGL x, Matrix.SpecialLinearGroup.toGL y) :
          Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
          GL (Fin m) k) := by
      rw [map_mul, h1a, hξ₂, ← Subgroup.coe_mul, ← map_mul]
      simp
    rw [h1, h2]
  · intro c u v hu hv
    have hcc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Matrix.GeneralLinearGroup.scalar_commute c _)
    refine ivk95l_mem_center_of_scalar (c := c) ?_
    rw [hprod, hu, hv, ← hΘ c hcc, MulEquiv.symm_apply_apply]
  · intro x y hxy
    obtain ⟨c, hc⟩ := ivk95l_center_scalar hm hxy
    have hcc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Matrix.GeneralLinearGroup.scalar_commute c _)
    refine ⟨c, ?_⟩
    have h3 : Θ.symm (Matrix.SpecialLinearGroup.toGL x, Matrix.SpecialLinearGroup.toGL y) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hcc⟩ :=
      Subtype.ext ((hprod x y).symm.trans hc)
    have h4 : (Matrix.SpecialLinearGroup.toGL x, Matrix.SpecialLinearGroup.toGL y) =
        (Matrix.GeneralLinearGroup.scalar (Fin a) c, Matrix.GeneralLinearGroup.scalar (Fin b) c) := by
      rw [← hΘ c hcc, ← h3, MulEquiv.apply_symm_apply]
    exact congrArg Prod.fst h4

theorem ivk95l_block_quad {E : Type} [Field E] [Algebra k E] {d : ℕ} {g : SL(m, k)}
    (Θ : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) ≃* GL (Fin d) E)
    (hΘ : ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))),
      Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
        Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (algebraMap k E).toMonoidHom c))
    (hperf : Group.IsPerfect SL(d, E)) (hm : 0 < m) :
    ∃ ξ : SL(d, E) →* SL(m, k),
      (∀ x, ξ x * g = g * ξ x) ∧
      (∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ x * n⁻¹ = ξ x') ∧
      (∀ x, ξ x ∈ Subgroup.center SL(m, k) → x ∈ Subgroup.center SL(d, E)) ∧
      (∀ (c : kˣ) (x : SL(d, E)), Matrix.SpecialLinearGroup.toGL x =
          Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (algebraMap k E).toMonoidHom c) →
          ξ x ∈ Subgroup.center SL(m, k)) := by
  let ψ : SL(d, E) →* GL (Fin m) k :=
    (Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))).subtype.comp
      (Θ.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL)
  have hψ : ∀ x, ψ x = ((Θ.symm (Matrix.SpecialLinearGroup.toGL x) : Subgroup.centralizer
      ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) := fun x => rfl
  have hdet : ∀ x, (ψ x : Matrix (Fin m) (Fin m) k).det = 1 := by
    intro x
    have h1 := ivk95l_hom_one_of_perfect hperf
      ((Matrix.GeneralLinearGroup.det : GL (Fin m) k →* kˣ).comp ψ)
    have h2 := congrArg (fun f : SL(d, E) →* kˣ => ((f x : kˣ) : k)) h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
  let ξ : SL(d, E) →* SL(m, k) :=
    { toFun := fun x => ⟨(ψ x : Matrix (Fin m) (Fin m) k), hdet x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((ψ (x * y) : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
          (ψ x : Matrix (Fin m) (Fin m) k) * (ψ y : Matrix (Fin m) (Fin m) k)
        rw [map_mul, Units.val_mul]) }
  have hξ : ∀ x, Matrix.SpecialLinearGroup.toGL (ξ x) = ψ x := fun x => Units.ext rfl
  have hcent : ∀ x, ψ x * Matrix.SpecialLinearGroup.toGL g = Matrix.SpecialLinearGroup.toGL g * ψ x :=
    fun x => Subgroup.mem_centralizer_singleton_iff.1
      ((Θ.symm (Matrix.SpecialLinearGroup.toGL x)).2)
  refine ⟨ξ, fun x => ?_, fun n hn x => ?_, fun x hx => ?_, fun c x hx => ?_⟩
  · apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hξ]
    exact hcent x
  · have hnc : Matrix.SpecialLinearGroup.toGL n ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hn]
    obtain ⟨y, hy⟩ : ∃ y : GL (Fin d) E, Θ ⟨Matrix.SpecialLinearGroup.toGL n, hnc⟩ = y := ⟨_, rfl⟩
    have hdx : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL x) = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact x.2)
    have hdetx : ((y * Matrix.SpecialLinearGroup.toGL x * y⁻¹ : GL (Fin d) E) :
        Matrix (Fin d) (Fin d) E).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (y * Matrix.SpecialLinearGroup.toGL x * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_assoc,
          mul_inv_cancel, mul_one, hdx]
      have h2 := Matrix.GeneralLinearGroup.val_det_apply (y * Matrix.SpecialLinearGroup.toGL x * y⁻¹)
      rw [h1, Units.val_one] at h2
      exact h2.symm
    let x' : SL(d, E) := ⟨((y * Matrix.SpecialLinearGroup.toGL x * y⁻¹ : GL (Fin d) E) :
      Matrix (Fin d) (Fin d) E), hdetx⟩
    have hx'GL : Matrix.SpecialLinearGroup.toGL x' = y * Matrix.SpecialLinearGroup.toGL x * y⁻¹ :=
      Units.ext rfl
    have hnc' : (⟨Matrix.SpecialLinearGroup.toGL n, hnc⟩ : Subgroup.centralizer
        ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) = Θ.symm y := by
      rw [← hy, MulEquiv.symm_apply_apply]
    have hnGL : Matrix.SpecialLinearGroup.toGL n = ((Θ.symm y : Subgroup.centralizer
        ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) :=
      congrArg Subtype.val hnc'
    refine ⟨x', ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, hξ, hξ, hψ, hψ, hx'GL, hnGL]
    calc ((Θ.symm y : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
          GL (Fin m) k) *
        ((Θ.symm (Matrix.SpecialLinearGroup.toGL x) : Subgroup.centralizer
          ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) : GL (Fin m) k) *
        ((Θ.symm y : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
          GL (Fin m) k)⁻¹
        = ((Θ.symm y * Θ.symm (Matrix.SpecialLinearGroup.toGL x) * (Θ.symm y)⁻¹ :
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
            GL (Fin m) k) := rfl
      _ = ((Θ.symm (y * Matrix.SpecialLinearGroup.toGL x * y⁻¹) :
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :
            GL (Fin m) k) := by rw [map_mul, map_mul, map_inv]
  · obtain ⟨c, hc⟩ := ivk95l_center_scalar hm hx
    have hcc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Matrix.GeneralLinearGroup.scalar_commute c _)
    have h1 : Θ.symm (Matrix.SpecialLinearGroup.toGL x) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hcc⟩ :=
      Subtype.ext (((hψ x).symm.trans (hξ x).symm).trans hc)
    have h2 : Matrix.SpecialLinearGroup.toGL x =
        Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (algebraMap k E).toMonoidHom c) := by
      rw [← hΘ c hcc, ← h1, MulEquiv.apply_symm_apply]
    exact ivk95l_mem_center_of_scalar h2
  · refine ivk95l_mem_center_of_scalar (c := c) ?_
    have hcc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
        Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Matrix.GeneralLinearGroup.scalar_commute c _)
    rw [hξ, hψ, hx, ← hΘ c hcc, MulEquiv.symm_apply_apply]

end Blocks

end CFSG.GH74.GLS.IVK.Proofs2
