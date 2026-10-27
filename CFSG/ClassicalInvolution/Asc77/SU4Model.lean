module

public import CFSG.ClassicalInvolution.Asc77.SU4Bridge
public import CFSG.ClassicalInvolution.Asc77.SU4Lift
public import CFSG.ClassicalInvolution.Asc77.SU4Trace
public import CFSG.ClassicalInvolution.Asc77.SU4Torus
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.ClassicalInvolution.Asc77.SU4Hyp
public import CFSG.ClassicalInvolution.Asc77.SU4Struct

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

section Aux

theorem phi_sq_eq {K : Type} [Field K] (σ φ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hfix : ∀ c, σ c = c → φ c = c) (y : K) : φ (φ y) = y := by
  have ht : φ (y + σ y) = y + σ y := hfix _ (by rw [map_add, hσσ, add_comm])
  have hn : φ (σ y * y) = σ y * y := hfix _ (by rw [map_mul, hσσ, mul_comm])
  have root : ∀ z : K, z ^ 2 - (y + σ y) * z + σ y * y = 0 → φ z = y ∨ φ z = σ y := by
    intro z hz
    have h1 : φ z ^ 2 - (y + σ y) * φ z + σ y * y = 0 := by
      have := congrArg φ hz
      rw [map_add, map_sub, map_pow, hn, map_mul, ht, map_zero] at this
      exact this
    have h2 : (φ z - y) * (φ z - σ y) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases root y (by ring) with h | h
  · rw [h, h]
  · rcases root (σ y) (by ring) with h' | h'
    · rw [h, h']
    · have hs : σ y = y := φ.injective (by rw [h', h])
      rw [h, h', hs]

end Aux

section Matrices

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem conjTr_mapMatrix (σ φ : K ≃+* K) (hσφ : ∀ x, σ (φ x) = φ (σ x))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    conjTr σ (φ.mapMatrix A) = φ.mapMatrix (conjTr σ A) := by
  ext i j
  simp [conjTr, hσφ]

theorem alpha_sq_matrix (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hφφ : ∀ y, φ (φ y) = y)
    (hmat : ∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) *
        φ.mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (x : Su K p f 4) :
    suMat (α (α x)) =
      ((g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (g : Matrix (Fin 4) (Fin 4) K)) * suMat x *
        (φ.mapMatrix ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  have hφm : ∀ M : Matrix (Fin 4) (Fin 4) K, φ.mapMatrix (φ.mapMatrix M) = M := fun M => by
    ext i j
    simp [hφφ]
  have h1 : suMat (α (α x)) = (g : Matrix (Fin 4) (Fin 4) K) *
      φ.mapMatrix (suMat (α x)) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    hmat (α x)
  have h2 : suMat (α x) = (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
      ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := hmat x
  rw [h1, h2]
  simp only [map_mul, hφm, Matrix.mul_assoc]

end Matrices

section Core

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem core_fixed_short (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) {F : Type} [Field F] [Finite F] (ε : F ≃+* fixedSubfield K p f)
    (u : Fˣ) (hu : u ^ 2 = -1) {X : Type} [Group X] (ψ : Su K p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) (hnorm : ψ.range.Normal) (ρ : X ≃* X)
    (hρ : ∀ x, ρ (ρ (ρ (ρ x))) = x) (θ : SL(2, F) →* X)
    (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (hθρ : ∀ s, ρ (θ s) = θ (diagConj2 u⁻¹ 1 s)) :
    ∃ (Q : GL (Fin 4) K) (hQ : conjTr (unitaryInvolution K p f) (Q : Matrix (Fin 4) (Fin 4) K) *
        (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4),
      (∀ r : Fin 4, r = 0 ∨ r = 1 → (Q : Matrix (Fin 4) (Fin 4) K) r 0 = 0 ∧
        (Q : Matrix (Fin 4) (Fin 4) K) r 3 = 0) ∧
      ∀ (y : Su K p f 4) (M : Matrix (Fin 4) (Fin 4) K), M * levi4 = levi4 * M →
        suMat y = (Q : Matrix (Fin 4) (Fin 4) K) * M *
          ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) → ρ (ρ (ψ y)) = ψ y := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set R : Subgroup (Su K p f 4) := rootSU2 K p f hn with hR
  have hRlong : IsLongRootSU2 K p f hn R (rootInvSU K p f hn) := isLongRootSU2_standard hn
  have hker1 : ∀ z ∈ R, z ∈ ψ.ker → z = 1 :=
    Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hK hp2 hq (by norm_num : 3 ≤ 4) hRlong hker
  set i₀ : Su K p f 4 := rootInvSU K p f hn with hi₀
  have hi₀R : i₀ ∈ R := rootInvSU_mem_rootSU2 hn
  have hi₀ord : orderOf i₀ = 2 := (isClassicalSL2_rootSU2 hK hp2 hn).orderOf_eq_two
  have hi₀nc : i₀ ∉ Subgroup.center (Su K p f 4) := by
    intro hc
    have := Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hK hp2 hq (by norm_num : 3 ≤ 4) hRlong
      (θ := QuotientGroup.mk' (Subgroup.center (Su K p f 4))) (by rw [QuotientGroup.ker_mk'])
      i₀ hi₀R (by rw [QuotientGroup.ker_mk']; exact hc)
    rw [this, orderOf_one] at hi₀ord
    omega
  have hρi₀ : ρ (ψ i₀) ∈ ψ.range := by
    have hψi₀ : ψ i₀ ∈ θ.range := by rw [hθ]; exact ⟨i₀, hi₀R, rfl⟩
    obtain ⟨s, hs⟩ := hψi₀
    rw [← hs, hθρ]
    have : θ (diagConj2 u⁻¹ 1 s) ∈ θ.range := ⟨_, rfl⟩
    rw [hθ] at this
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  have hstab := stab_of_noncentral hK hq ψ hnorm ρ hi₀nc hρi₀
  obtain ⟨α, g, φ, hα, hmat, hiso⟩ := exists_lift_of_stab hK hp2 hq ψ hker ρ hρ hstab
  obtain ⟨θ', hθ'inj, hθ'range, hθ'ψ, hequiv, hfix⟩ :=
    exists_chart_lift hK hp2 hq ε ψ hker θ hθ ρ u⁻¹ hθρ α g φ hα hmat
  have hσφ : ∀ x, σ (φ x) = φ (σ x) := fun x => by
    rw [hσ, unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have hφφ : ∀ y, φ (φ y) = y :=
    phi_sq_eq σ φ hσσ (fun c hc => hfix c ((mem_fixedSubfield (F := K) (p := p) (f := f)).2 hc))
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set H : Matrix (Fin 4) (Fin 4) K := G * φ.mapMatrix G with hH
  set Hi : Matrix (Fin 4) (Fin 4) K := φ.mapMatrix Gi * Gi with hHi
  have hHHi : H * Hi = 1 := by
    rw [hH, hHi]
    calc G * φ.mapMatrix G * (φ.mapMatrix Gi * Gi) = G * φ.mapMatrix (G * Gi) * Gi := by
          simp only [map_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGGi, map_one, Matrix.mul_one, hGGi]
  have hHiH : Hi * H = 1 := by
    rw [hH, hHi]
    calc φ.mapMatrix Gi * Gi * (G * φ.mapMatrix G)
        = φ.mapMatrix Gi * (Gi * G) * φ.mapMatrix G := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGiG, Matrix.mul_one, ← map_mul, hGiG, map_one]
  have hα2 : ∀ x : Su K p f 4, suMat (α (α x)) = H * suMat x * Hi := fun x =>
    alpha_sq_matrix α g φ hφφ hmat x
  have hperf : Group.IsPerfect (Su K p f 4) :=
    ⟨(CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_su hK hq (k := 4) (by norm_num)).1⟩
  have hα4 : ∀ x, α (α (α (α x))) = x := by
    have := hom_eq_of_central_ker_perfect (G := Su K p f 4) (θ := ψ) hker
      (α.comp (α.comp (α.comp α))) (MonoidHom.id _) (fun x => by
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
        rw [hα, hα, hα, hα, hρ])
    exact fun x => DFunLike.congr_fun this x
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hHsq : ∃ s : K, H * H = s • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) (H * H) fun y hy => ?_
    have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
    have h4 := hα4 ⟨y, hy'⟩
    have h5 : suMat (α (α (α (α ⟨y, hy'⟩)))) =
        (H * H) * (y : Matrix (Fin 4) (Fin 4) K) * (Hi * Hi) := by
      rw [hα2 (α (α ⟨y, hy'⟩)), hα2 ⟨y, hy'⟩]
      simp only [Matrix.mul_assoc]
      rfl
    rw [h4] at h5
    have h6 : (Hi * Hi) * (H * H) = 1 := by
      calc Hi * Hi * (H * H) = Hi * (Hi * H) * H := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hHiH, Matrix.mul_one, hHiH]
    calc H * H * (y : Matrix (Fin 4) (Fin 4) K)
        = (H * H * (y : Matrix (Fin 4) (Fin 4) K) * (Hi * Hi)) * (H * H) := by
          rw [Matrix.mul_assoc (H * H * (y : Matrix (Fin 4) (Fin 4) K)), h6, Matrix.mul_one]
      _ = (y : Matrix (Fin 4) (Fin 4) K) * (H * H) := by rw [← h5]; rfl
  have hGiso : conjTr σ G * G = 1 := hiso
  have hHiso : conjTr σ H * H = 1 := by
    rw [hH, conjTr_mul, conjTr_mapMatrix σ φ hσφ]
    calc φ.mapMatrix (conjTr σ G) * conjTr σ G * (G * φ.mapMatrix G)
        = φ.mapMatrix (conjTr σ G) * (conjTr σ G * G) * φ.mapMatrix G := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGiso, Matrix.mul_one, ← map_mul, hGiso, map_one]
  have hdetG : G.det ^ (p ^ f + 1) = 1 := by
    have h1 := congrArg Matrix.det hGiso
    have e : (conjTr σ G).det = σ G.det := by
      show ((G.map σ)ᵀ).det = σ G.det
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (σ : K →+* K) G).symm
    rw [Matrix.det_mul, e, Matrix.det_one] at h1
    exact norm_pow_eq_one h1
  have hdetH : H.det ^ ((p ^ f + 1) / 2) = 1 := by
    have h1 : H.det = G.det * φ G.det := by
      rw [hH, Matrix.det_mul]
      congr 1
      exact (RingHom.map_det (φ : K →+* K) G).symm
    rw [h1]
    refine mul_map_pow_half (φ : K →+* K) ?_
    have : 2 * ((p ^ f + 1) / 2) = p ^ f + 1 := by omega
    rw [this]
    exact hdetG
  have hu0 : (u : F) * (u : F) = -1 := units_sq_eq_neg_one hu
  have hF2 : (2 : F) ≠ 0 := by
    intro h
    apply h2
    have h1 : (2 : fixedSubfield K p f) = 0 := by
      have := congrArg ε h
      rwa [map_ofNat, map_zero] at this
    have h3 : (2 : K) = ((2 : fixedSubfield K p f) : K) :=
      (map_ofNat (fixedSubfield K p f).subtype 2).symm
    rw [h3, h1]
    rfl
  set r : Su K p f 4 := θ' (torusW u) with hr
  have hrR : r ∈ R := by
    have : r ∈ θ'.range := ⟨torusW u, rfl⟩
    rw [hθ'range] at this
    exact this
  have hα2R : ∀ s : SL(2, F), α (α (θ' s)) = r * θ' s * r⁻¹ := by
    intro s
    rw [hequiv, hequiv, diagConj2_sq hu, map_mul, map_mul, map_inv]
  have hrr : r * r = i₀ := by
    have h1 : r * r = θ' (-1) := by rw [hr, ← map_mul, torusW_mul_self hu]
    have hz : θ' (-1) ∈ R := by
      have : θ' (-1) ∈ θ'.range := ⟨-1, rfl⟩
      rw [hθ'range] at this
      exact this
    have hneg : ((-1 : SL(2, F)) * (-1)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hz2 : θ' (-1) * θ' (-1) = 1 := by rw [← map_mul, hneg, map_one]
    have hne : θ' (-1) ≠ 1 := by
      intro h
      have h' : (-1 : SL(2, F)) = 1 := hθ'inj (by rw [h, map_one])
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h'
      simp at this
      exact hF2 (by linear_combination -this)
    have hord : orderOf (θ' (-1)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hne
    rw [h1]
    exact hRlong.eq_of_orderOf_eq_two hK hp2 hz hord
  obtain ⟨r₁, hr₁⟩ := hrR
  have hr2 : suMat r₁ * suMat r₁ = -1 := by
    have h1 : r₁ * r₁ = negOneSU K p f :=
      blockEmb_injective (by omega) (by rw [map_mul, hr₁, hrr]; rfl)
    rw [← suMat_mul, h1, suMat_negOneSU]
  have hcomm : ∀ A : Su K p f 2, H * blockMat 4 0 (suMat A) =
      blockMat 4 0 (suMat r₁ * suMat A * suMat r₁⁻¹) * H := by
    intro A
    obtain ⟨s, hs⟩ : ∃ s, θ' s = blockEmb K p f 4 2 0 (by omega) A := by
      have : blockEmb K p f 4 2 0 (by omega) A ∈ rootSU2 K p f hn := ⟨A, rfl⟩
      rw [← hθ'range] at this
      exact this
    have h1 := hα2R s
    rw [hs] at h1
    have h2 := congrArg suMat h1
    rw [hα2, suMat_mul, suMat_mul] at h2
    have h3 : H * suMat (blockEmb K p f 4 2 0 (by omega) A) =
        (suMat r * suMat (blockEmb K p f 4 2 0 (by omega) A) * suMat r⁻¹) * H := by
      calc H * suMat (blockEmb K p f 4 2 0 (by omega) A)
          = H * suMat (blockEmb K p f 4 2 0 (by omega) A) * (Hi * H) := by
            rw [hHiH, Matrix.mul_one]
        _ = (H * suMat (blockEmb K p f 4 2 0 (by omega) A) * Hi) * H := by
            simp only [Matrix.mul_assoc]
        _ = (suMat r * suMat (blockEmb K p f 4 2 0 (by omega) A) * suMat r⁻¹) * H := by
            rw [h2]
    have e1 : suMat r = blockMat 4 0 (suMat r₁) := by rw [← hr₁]; rfl
    have e2 : suMat r⁻¹ = blockMat 4 0 (suMat r₁⁻¹) := by rw [← hr₁, ← map_inv]; rfl
    have e3 : suMat (blockEmb K p f 4 2 0 (by omega) A) = blockMat 4 0 (suMat A) := rfl
    rw [e1, e2, e3] at h3
    rw [h3, blockMat_mul (by omega), blockMat_mul (by omega)]
  obtain ⟨ι, hι, hσι⟩ : ∃ ι : K, ι * ι = -1 ∧ σ ι = ι := by
    refine ⟨((ε (u : F) : fixedSubfield K p f) : K), ?_, ?_⟩
    · have : (ε (u : F)) * (ε (u : F)) = -1 := by rw [← map_mul, hu0, map_neg, map_one]
      have h' := congrArg Subtype.val this
      simpa using h'
    · exact (mem_fixedSubfield (F := K) (p := p) (f := f)).1 (ε (u : F)).2
  obtain ⟨a, H₁, H₂, hHform, ha, hiso₁, hsq₁, hn₁, hn₁', hiso₂, hsq₂, hn₂, hn₂'⟩ :=
    block_data hK hp2 hq hq4 hι hσι r₁ hr2 hcomm hHiso hHsq hdetH
  obtain ⟨Q, hQ, hsupp, heig⟩ :=
    exists_witt_eigenbasis σ hσσ h2 ha hiso₁ hsq₁ hn₁ hn₁' hiso₂ hsq₂ hn₂ hn₂'
  refine ⟨Q, hQ, hsupp, ?_⟩
  intro y M hM hy
  set Qm : Matrix (Fin 4) (Fin 4) K := (Q : Matrix (Fin 4) (Fin 4) K) with hQm
  set Qi : Matrix (Fin 4) (Fin 4) K := ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hQi
  have hQQi : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hD : Matrix.diagonal ![a, a, -a, -a] = a • (levi4 : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levi4]
  have hHeq : H = blockMat 4 0 H₁ * blockMat 4 2 H₂ := hHform
  have hHQ : H * Qm = Qm * (a • levi4) := by
    rw [hHeq, ← hD]
    exact heig
  have hQiH : Qi * H = (a • levi4) * Qi := by
    calc Qi * H = Qi * H * (Qm * Qi) := by rw [hQQi, Matrix.mul_one]
      _ = Qi * (H * Qm) * Qi := by simp only [Matrix.mul_assoc]
      _ = Qi * (Qm * (a • levi4)) * Qi := by rw [hHQ]
      _ = (a • levi4) * Qi := by simp only [← Matrix.mul_assoc, hQiQ, Matrix.one_mul]
  have hcm : (a • (levi4 : Matrix (Fin 4) (Fin 4) K)) * M = M * (a • levi4) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM]
  have hcommy : H * suMat y = suMat y * H := by
    have hy' : suMat y = Qm * M * Qi := hy
    rw [hy']
    calc H * (Qm * M * Qi) = (H * Qm) * M * Qi := by simp only [Matrix.mul_assoc]
      _ = Qm * ((a • levi4) * M) * Qi := by rw [hHQ]; simp only [Matrix.mul_assoc]
      _ = Qm * (M * (a • levi4)) * Qi := by rw [hcm]
      _ = Qm * M * ((a • levi4) * Qi) := by simp only [Matrix.mul_assoc]
      _ = Qm * M * (Qi * H) := by rw [hQiH]
      _ = Qm * M * Qi * H := by simp only [Matrix.mul_assoc]
  have hα2y : α (α y) = y := by
    apply suMat_injective
    rw [hα2 y, hcommy, Matrix.mul_assoc, hHHi, Matrix.mul_one]
  calc ρ (ρ (ψ y)) = ψ (α (α y)) := by rw [hα, hα]
    _ = ψ y := by rw [hα2y]

end Core

section Outer

variable {p f : ℕ} [Fact p.Prime]

theorem exists_fixed_shortPair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1)
    {b c : GaloisField p f} [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    {X : Type} [Group X] (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4))
    (hnorm : ψ.range.Normal) (ρ : X ≃* X) (hρ : ∀ x, ρ (ρ (ρ (ρ x))) = x)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (θ : SL(2, GaloisField p f) →* X) (hθ : θ.range = R.map ψ) (u : (GaloisField p f)ˣ)
    (hu : u ^ 2 = -1) (hθρ : ∀ s, ρ (θ s) = θ (diagConj2 u⁻¹ 1 s)) :
    ∃ (S : Subgroup (Su (GaloisField p (2 * f)) p f 4)) (W : Subgroup X),
      TwistedB2BlockPair hirr W (R.map ψ) (S.map ψ) ∧ R ⊔ S = ⊤ ∧
        ∀ y ∈ S, ρ (ρ (ψ y)) = ψ y := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK := card_galoisField_two_mul_eq (p := p) hq
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp hR
  set ψ₁ : Su (GaloisField p (2 * f)) p f 4 →* X := ψ.comp (MulAut.conj g₁).toMonoidHom with hψ₁
  have hψ₁range : ψ₁.range = ψ.range := by
    rw [hψ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective,
      Subgroup.map_top]
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro y hy
    have h1 : (MulAut.conj g₁).toMonoidHom y ∈ ψ.ker := hy
    have h2 := hker h1
    exact (MulEquivClass.apply_mem_center_iff (MulAut.conj g₁)).1 h2
  have hθ₁ : θ.range = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
    rw [hθ, hg₁, Subgroup.map_map]
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hcardk : Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) = p ^ f :=
    card_fixedSubfield hK
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield (GaloisField p (2 * f)) p f) := by
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield (GaloisField p (2 * f)) p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hcardk])⟩
  have hcore := core_fixed_short hK hp2 hq hq4 ε u hu ψ₁ hψ₁ker (hψ₁range ▸ hnorm) ρ hρ θ hθ₁ hθρ
  obtain ⟨Q, hQ, hsupp, hfix⟩ := hcore
  obtain ⟨Φ, hΦlevi, hΦlb⟩ := exists_phiSU_bridge hp2 hf hirr
  set e' : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4 := Φ.trans (conjEquiv Q hQ) with he'
  have hlb : (spinMinusModel hirr).lb.range.map e'.toMonoidHom =
      rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) := hΦlb Q hQ hsupp
  have hR₀ : rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) ∈
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4) :=
    ⟨_, isLongRootSU2_standard (by norm_num : 2 ≤ 4)⟩
  obtain ⟨hpair, hsup⟩ := twistedPair_of_equiv hp2 hq hg6 e' hR₀ hlb ψ₁ hψ₁ker
  set S₀ : Subgroup (Su (GaloisField p (2 * f)) p f 4) :=
    (spinMinusModel hirr).sb.range.map e'.toMonoidHom with hS₀
  refine ⟨S₀.map (MulAut.conj g₁).toMonoidHom, (ψ₁.comp e'.toMonoidHom).range, ?_, ?_, ?_⟩
  · have h1 : R.map ψ = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
      rw [hg₁, Subgroup.map_map]
    have h2 : (S₀.map (MulAut.conj g₁).toMonoidHom).map ψ = S₀.map ψ₁ := by
      rw [Subgroup.map_map]
    rw [h1, h2]
    exact hpair
  · rw [hg₁, ← Subgroup.map_sup, hsup, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective
  · rintro _ ⟨y₀, hy₀, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hy₀
    have hψy : ψ ((MulAut.conj g₁).toMonoidHom (e'.toMonoidHom x₀)) =
        ψ₁ (e'.toMonoidHom x₀) := rfl
    rw [hψy]
    refine hfix (e'.toMonoidHom x₀)
      (((Φ x₀ : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4) :
        GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f)))
      (hΦlevi x₀ hx₀) ?_
    show (((conjEquiv Q hQ (Φ x₀) : Su (GaloisField p (2 * f)) p f 4) :
      GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) = _
    rw [coe_conjEquiv, Units.val_mul, Units.val_mul]

end Outer

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
