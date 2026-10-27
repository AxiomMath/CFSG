module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareModel
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Proj

variable (Q : QuadraticForm K V)

abbrev orthogonalOmega : Subgroup (V ≃ₗ[K] V) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

@[expose] def omegaScalars : Subgroup (orthogonalOmega Q) where
  carrier := {g | ∃ c : K, ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id}
  one_mem' := ⟨1, by ext; simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c * c', LinearMap.ext fun v => ?_⟩
    have h1 := LinearMap.congr_fun hc (((b : V ≃ₗ[K] V) : V →ₗ[K] V) v)
    have h2 := LinearMap.congr_fun hc' v
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
    change (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = (c * c') • v
    rw [h1, h2, smul_smul]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    refine ⟨c⁻¹, LinearMap.ext fun v => ?_⟩
    have hav : ∀ w, (a : V ≃ₗ[K] V) w = c • w := fun w => LinearMap.congr_fun hc w
    have hinv : ∀ w, (a : V ≃ₗ[K] V) (((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) w) = w :=
      fun w => by
        change ((a * a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) w = w
        rw [mul_inv_cancel]
        rfl
    change ((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v = c⁻¹ • v
    by_cases hc0 : c = 0
    · have hz : ∀ w : V, w = 0 := fun w => by rw [← hinv w, hav, hc0, zero_smul]
      rw [hz (((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v), hz v, smul_zero]
    · apply (a : V ≃ₗ[K] V).injective
      rw [hinv, hav, smul_smul, mul_inv_cancel₀ hc0, one_smul]

theorem mem_omegaScalars {g : orthogonalOmega Q} :
    g ∈ omegaScalars Q ↔ ∃ c : K, ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id :=
  Iff.rfl

instance omegaScalars_normal : (omegaScalars Q).Normal :=
  ⟨fun n ⟨c, hc⟩ g => ⟨c, LinearMap.ext fun v => by
    have h1 := LinearMap.congr_fun hc (((g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v)
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h1
    change (g : V ≃ₗ[K] V) ((n : V ≃ₗ[K] V) (((g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v)) = c • v
    rw [h1, map_smul]
    change c • ((g * g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v = c • v
    rw [mul_inv_cancel]
    rfl⟩⟩

abbrev OrthogonalProj : Type _ :=
  orthogonalOmega Q ⧸ omegaScalars Q

@[expose] def orthogonalProj : orthogonalOmega Q →* OrthogonalProj Q :=
  QuotientGroup.mk' (omegaScalars Q)

end Proj

section Pairs

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}

@[expose] def NotScalar (g : V ≃ₗ[K] V) : Prop :=
  ∀ c : K, (g : V →ₗ[K] V) ≠ c • LinearMap.id

theorem exists_four_of_omega_pair_le {C : Subgroup (V ≃ₗ[K] V)} {u v : V ≃ₗ[K] V}
    (hu : u ∈ orthogonalOmega Q) (hv : v ∈ orthogonalOmega Q) (huA : u ∈ C) (hvA : v ∈ C)
    (huu : u * u = 1) (hvv : v * v = 1) (huv : u * v = v * u) (hun : NotScalar u)
    (hvn : NotScalar v) (huvn : NotScalar (u * v)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let u' : orthogonalOmega Q := ⟨u, hu⟩
  let v' : orthogonalOmega Q := ⟨v, hv⟩
  have hπ : ∀ g : orthogonalOmega Q, orthogonalProj Q g = 1 ↔ g ∈ omegaScalars Q :=
    fun g => QuotientGroup.eq_one_iff g
  have hsq : ∀ (w : V ≃ₗ[K] V) (hw : w ∈ orthogonalOmega Q), w * w = 1 →
      orthogonalProj Q ⟨w, hw⟩ * orthogonalProj Q ⟨w, hw⟩ = 1 := fun w hw h => by
    rw [← map_mul, hπ]
    exact ⟨1, by rw [one_smul]; exact congrArg (fun g : V ≃ₗ[K] V => (g : V →ₗ[K] V)) h⟩
  have hpne1 : ∀ (w : V ≃ₗ[K] V) (hw : w ∈ orthogonalOmega Q), NotScalar w →
      orthogonalProj Q ⟨w, hw⟩ ≠ 1 := fun w hw hn h => by
    obtain ⟨c, hc⟩ := (hπ _).1 h
    exact hn c hc
  have hpxy : orthogonalProj Q u' * orthogonalProj Q v' =
      orthogonalProj Q v' * orthogonalProj Q u' := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext huv)
  have hpne : orthogonalProj Q u' ≠ orthogonalProj Q v' := fun h => by
    have h1 : orthogonalProj Q (u' * v') = 1 := by rw [map_mul, ← h, hsq u hu huu]
    exact hpne1 (u * v) (mul_mem hu hv) huvn h1
  obtain ⟨W, -, hWle, hW, hWcard⟩ := FourGroup.exists_kleinFour (hsq u hu huu) (hsq v hv hvv)
    hpxy (hpne1 u hu hun) (hpne1 v hv hvn) hpne
  exact ⟨W, hWle _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 huA))
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hvA)), hW, hWcard⟩

theorem exists_four_of_omega_pair {u v : V ≃ₗ[K] V} (hu : u ∈ orthogonalOmega Q)
    (hv : v ∈ orthogonalOmega Q) (huA : u ∈ Subgroup.centralizer {A})
    (hvA : v ∈ Subgroup.centralizer {A}) (huu : u * u = 1) (hvv : v * v = 1)
    (huv : u * v = v * u) (hun : NotScalar u) (hvn : NotScalar v) (huvn : NotScalar (u * v)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 :=
  exists_four_of_omega_pair_le hu hv huA hvA huu hvv huv hun hvn huvn

theorem mul_mem_omega [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {x y : V ≃ₗ[K] V}
    (hx : x ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hy : y ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q) (hxΩ : x ∉ orthogonalOmega Q)
    (hyΩ : y ∉ orthogonalOmega Q) : x * y ∈ orthogonalOmega Q := by
  obtain ⟨-, -, -, hidx⟩ := odd_orthogonal_abelianization_order_bound hK hQ
  set H := (orthogonalOmega Q).subgroupOf (TauCeti.QuadraticMap.specialOrthogonalGroup Q)
  have hidx' : H.index ≤ 2 := hidx
  have hxH : (⟨x, hx⟩ : TauCeti.QuadraticMap.specialOrthogonalGroup Q) ∉ H := hxΩ
  have hyH : (⟨y, hy⟩ : TauCeti.QuadraticMap.specialOrthogonalGroup Q) ∉ H := hyΩ
  have hpos : H.index ≠ 0 := by
    intro h0
    rw [h0] at hidx'
    have : H.index = 0 := h0
    exact absurd this (Subgroup.index_ne_zero_of_finite (hH := by
      have : Finite (V ≃ₗ[K] V) := by
        have : Finite (Module.End K V) := Module.finite_of_finite K
        exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : Module.End K V))
          fun _ _ h => LinearEquiv.ext (LinearMap.congr_fun h)
      infer_instance))
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · exact absurd (by rw [Subgroup.index_eq_one.1 h1]; trivial) hxH
  · have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).2
      (iff_of_false hxH hyH)
    exact this

theorem exists_four_of_triple_le [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {C : Subgroup (V ≃ₗ[K] V)} {t₁ t₂ t₃ : V ≃ₗ[K] V}
    (hS₁ : t₁ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₂ : t₂ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₃ : t₃ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hA₁ : t₁ ∈ C) (hA₂ : t₂ ∈ C) (hA₃ : t₃ ∈ C) (h₁ : t₁ * t₁ = 1) (h₂ : t₂ * t₂ = 1)
    (h₃ : t₃ * t₃ = 1) (h₁₂ : t₁ * t₂ = t₂ * t₁) (h₁₃ : t₁ * t₃ = t₃ * t₁)
    (h₂₃ : t₂ * t₃ = t₃ * t₂) (hn₁ : NotScalar t₁) (hn₂ : NotScalar t₂) (hn₃ : NotScalar t₃)
    (hn₁₂ : NotScalar (t₁ * t₂)) (hn₁₃ : NotScalar (t₁ * t₃)) (hn₂₃ : NotScalar (t₂ * t₃))
    (hn₁₂₃ : NotScalar (t₁ * t₂ * t₃)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have c12 : Commute t₁ t₂ := h₁₂
  have c13 : Commute t₁ t₃ := h₁₃
  have c23 : Commute t₂ t₃ := h₂₃
  have i12 : t₁ * t₂ * (t₁ * t₂) = 1 := by
    rw [show t₁ * t₂ * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ by group, ← h₁₂,
      show t₁ * (t₁ * t₂) * t₂ = t₁ * t₁ * (t₂ * t₂) by group, h₁, h₂, one_mul]
  have i13 : t₁ * t₃ * (t₁ * t₃) = 1 := by
    rw [show t₁ * t₃ * (t₁ * t₃) = t₁ * (t₃ * t₁) * t₃ by group, ← h₁₃,
      show t₁ * (t₁ * t₃) * t₃ = t₁ * t₁ * (t₃ * t₃) by group, h₁, h₃, one_mul]
  have i23 : t₂ * t₃ * (t₂ * t₃) = 1 := by
    rw [show t₂ * t₃ * (t₂ * t₃) = t₂ * (t₃ * t₂) * t₃ by group, ← h₂₃,
      show t₂ * (t₂ * t₃) * t₃ = t₂ * t₂ * (t₃ * t₃) by group, h₂, h₃, one_mul]
  have hc : ∀ {a b : V ≃ₗ[K] V}, a ∈ C → b ∈ C → a * b ∈ C := fun ha hb => mul_mem ha hb
  by_cases g₁ : t₁ ∈ orthogonalOmega Q <;> by_cases g₂ : t₂ ∈ orthogonalOmega Q <;>
    by_cases g₃ : t₃ ∈ orthogonalOmega Q
  · exact exists_four_of_omega_pair_le g₁ g₂ hA₁ hA₂ h₁ h₂ h₁₂ hn₁ hn₂ hn₁₂
  · exact exists_four_of_omega_pair_le g₁ g₂ hA₁ hA₂ h₁ h₂ h₁₂ hn₁ hn₂ hn₁₂
  · exact exists_four_of_omega_pair_le g₁ g₃ hA₁ hA₃ h₁ h₃ h₁₃ hn₁ hn₃ hn₁₃
  · refine exists_four_of_omega_pair_le g₁ (mul_mem_omega hK hQ hS₂ hS₃ g₂ g₃) hA₁ (hc hA₂ hA₃) h₁
      i23 (c12.mul_right c13).eq hn₁ hn₂₃ ?_
    rw [← mul_assoc]
    exact hn₁₂₃
  · exact exists_four_of_omega_pair_le g₂ g₃ hA₂ hA₃ h₂ h₃ h₂₃ hn₂ hn₃ hn₂₃
  · refine exists_four_of_omega_pair_le g₂ (mul_mem_omega hK hQ hS₁ hS₃ g₁ g₃) hA₂ (hc hA₁ hA₃) h₂
      i13 (c12.symm.mul_right c23).eq hn₂ hn₁₃ ?_
    rw [← mul_assoc, ← h₁₂]
    exact hn₁₂₃
  · refine exists_four_of_omega_pair_le g₃ (mul_mem_omega hK hQ hS₁ hS₂ g₁ g₂) hA₃ (hc hA₁ hA₂) h₃
      i12 (c13.symm.mul_right c23.symm).eq hn₃ hn₁₂ ?_
    rw [(c13.symm.mul_right c23.symm).eq]
    exact hn₁₂₃
  · have hm12 := mul_mem_omega hK hQ hS₁ hS₂ g₁ g₂
    have hm13 := mul_mem_omega hK hQ hS₁ hS₃ g₁ g₃
    refine exists_four_of_omega_pair_le hm12 hm13 (hc hA₁ hA₂) (hc hA₁ hA₃) i12 i13
      (((Commute.refl t₁).mul_right c13).mul_left (c12.symm.mul_right c23)).eq hn₁₂ hn₁₃ ?_
    have : t₁ * t₂ * (t₁ * t₃) = t₂ * t₃ := by
      rw [show t₁ * t₂ * (t₁ * t₃) = t₁ * (t₂ * t₁) * t₃ by group, ← h₁₂,
        show t₁ * (t₁ * t₂) * t₃ = t₁ * t₁ * (t₂ * t₃) by group, h₁, one_mul]
    rw [this]
    exact hn₂₃

theorem exists_four_of_triple [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {t₁ t₂ t₃ : V ≃ₗ[K] V}
    (hS₁ : t₁ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₂ : t₂ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₃ : t₃ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hA₁ : t₁ ∈ Subgroup.centralizer {A}) (hA₂ : t₂ ∈ Subgroup.centralizer {A})
    (hA₃ : t₃ ∈ Subgroup.centralizer {A}) (h₁ : t₁ * t₁ = 1) (h₂ : t₂ * t₂ = 1)
    (h₃ : t₃ * t₃ = 1) (h₁₂ : t₁ * t₂ = t₂ * t₁) (h₁₃ : t₁ * t₃ = t₃ * t₁)
    (h₂₃ : t₂ * t₃ = t₃ * t₂) (hn₁ : NotScalar t₁) (hn₂ : NotScalar t₂) (hn₃ : NotScalar t₃)
    (hn₁₂ : NotScalar (t₁ * t₂)) (hn₁₃ : NotScalar (t₁ * t₃)) (hn₂₃ : NotScalar (t₂ * t₃))
    (hn₁₂₃ : NotScalar (t₁ * t₂ * t₃)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 :=
  exists_four_of_triple_le hK hQ hS₁ hS₂ hS₃ hA₁ hA₂ hA₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hn₁ hn₂ hn₃
    hn₁₂ hn₁₃ hn₂₃ hn₁₂₃

end Pairs

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def signEquiv (c : Basis ι K V) (S : Finset ι) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin c c (signDiag S)) (Matrix.toLin c c (signDiag S))
    (by rw [← Matrix.toLin_mul, signDiag_mul_self, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, signDiag_mul_self, Matrix.toLin_one])

theorem coe_signEquiv (c : Basis ι K V) (S : Finset ι) :
    ((signEquiv c S : V ≃ₗ[K] V) : V →ₗ[K] V) = Matrix.toLin c c (signDiag S) :=
  rfl

theorem signEquiv_mul (c : Basis ι K V) (S T : Finset ι) :
    signEquiv c S * signEquiv c T = signEquiv c (symmDiff S T) := by
  refine LinearEquiv.toLinearMap_injective ?_
  change Matrix.toLin c c (signDiag S) ∘ₗ Matrix.toLin c c (signDiag T) =
    Matrix.toLin c c (signDiag (symmDiff S T))
  rw [← Matrix.toLin_mul, signDiag_mul_signDiag]

theorem signEquiv_mul_self (c : Basis ι K V) (S : Finset ι) :
    signEquiv c S * signEquiv c S = 1 := by
  rw [signEquiv_mul, symmDiff_self]
  refine LinearEquiv.toLinearMap_injective ?_
  change Matrix.toLin c c (signDiag ⊥) = LinearMap.id
  rw [show (⊥ : Finset ι) = ∅ from rfl]
  rw [show signDiag (K := K) (∅ : Finset ι) = 1 by
    rw [signDiag]
    simp [diagonal_one], Matrix.toLin_one]

theorem signEquiv_comm (c : Basis ι K V) (S T : Finset ι) :
    signEquiv c S * signEquiv c T = signEquiv c T * signEquiv c S := by
  rw [signEquiv_mul, signEquiv_mul, symmDiff_comm]

theorem det_signEquiv (c : Basis ι K V) (S : Finset ι) :
    (LinearEquiv.det (signEquiv c S) : K) = (-1) ^ S.card := by
  rw [LinearEquiv.coe_det, coe_signEquiv, LinearMap.det_toLin, det_signDiag]

theorem notScalar_signEquiv (h2 : (2 : K) ≠ 0) (c : Basis ι K V) {S : Finset ι} {i j : ι}
    (hi : i ∈ S) (hj : j ∉ S) : NotScalar (signEquiv c S) := fun a h =>
  signDiag_ne_smul h2 hi hj a (toLin_eq_smul_id c (by rw [← coe_signEquiv, h]))

theorem signEquiv_preserves (B : LinearMap.BilinForm K V) (c : Basis ι K V) {S : Finset ι}
    (hS : ∀ i j, B (c i) (c j) ≠ 0 → (i ∈ S ↔ j ∈ S)) (v w : V) :
    B (signEquiv c S v) (signEquiv c S w) = B v w :=
  toLin_preserves B c (Matrix.of fun i j => B (c i) (c j)) (fun _ _ => rfl) (fun _ _ => rfl)
    (signDiag_conj fun i j h => hS i j h) v w

theorem signEquiv_mem_centralizer (c : Basis ι K V) {A : V ≃ₗ[K] V} {S : Finset ι}
    (hS : ∀ i j, LinearMap.toMatrix c c (A : V →ₗ[K] V) i j ≠ 0 → (i ∈ S ↔ j ∈ S)) :
    signEquiv c S ∈ Subgroup.centralizer {A} := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (LinearEquiv.toLinearMap_injective ?_)
  change Matrix.toLin c c (signDiag S) ∘ₗ (A : V →ₗ[K] V) =
    (A : V →ₗ[K] V) ∘ₗ Matrix.toLin c c (signDiag S)
  exact toLin_commute c (signDiag_mul_comm hS)

end Sign

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
