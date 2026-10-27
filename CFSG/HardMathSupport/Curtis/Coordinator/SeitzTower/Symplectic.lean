module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.RankThree.PartTwo.Sec8.Item812ProofOut

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Out

variable {r : ℕ} {K : Type} [Field K]

theorem multiplier_gspFieldMap_symp [NeZero r] (σ : K ≃+* K) (A : gsp r K) :
    multiplier r K (gspFieldMap σ A) = Units.map (σ : K →* K) (multiplier r K A) := by
  apply multiplier_eq
  change (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ).transpose *
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
    σ (multiplier r K A : K) • formJ r K
  have h1 : (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).transpose *
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).map σ =
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ).transpose *
        formJ r K *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ := by
    rw [map_mul_ringEquiv, map_mul_ringEquiv, Matrix.transpose_map, formJ_map]
  rw [← h1, multiplier_spec]
  ext i j
  have h := congrFun (congrFun (formJ_map (r := r) (K := K) σ) i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h ⊢
  rw [h]

theorem isSquare_ratio_units [Finite K] (σ : K ≃+* K) (x : Kˣ) :
    ∃ c : Kˣ, Units.map (σ : K →* K) x * x⁻¹ = c * c := by
  classical
  have := Fintype.ofFinite K
  have hx : (x : K) ≠ 0 := x.ne_zero
  have hσx : σ (x : K) ≠ 0 := fun h => hx (σ.injective (by rw [h, map_zero]))
  have ha : σ (x : K) * (x : K)⁻¹ ≠ 0 := mul_ne_zero hσx (inv_ne_zero hx)
  have hsq : IsSquare (σ (x : K) * (x : K)⁻¹) := by
    by_cases h2 : ringChar K = 2
    · exact FiniteField.isSquare_of_char_two h2 _
    · set q := Fintype.card K with hq
      have hqodd : Odd q := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two h2)
      have hq2 : 2 * (q / 2) = q - 1 := by
        obtain ⟨m, hm⟩ := hqodd
        omega
      have hs2 : ((x : K) ^ (q / 2)) * ((x : K) ^ (q / 2)) = 1 := by
        rw [← pow_add, ← two_mul, hq2]
        exact FiniteField.pow_card_sub_one_eq_one _ hx
      have hsσ : σ ((x : K) ^ (q / 2)) = (x : K) ^ (q / 2) := by
        rcases mul_self_eq_one_iff.mp hs2 with h | h
        · rw [h, map_one]
        · rw [h, map_neg, map_one]
      rw [FiniteField.isSquare_iff h2 ha, mul_pow, inv_pow, ← map_pow, hsσ]
      exact mul_inv_cancel₀ (pow_ne_zero _ hx)
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by rw [hc]; simp)
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa using hc

theorem outerComm_statedProj_sp_of_forall [NeZero r] [Finite K]
    (hform : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ) :
    OuterComm (StatedProj (StatedSp r K)) := by
  intro α β
  obtain ⟨A, σ, rfl⟩ := hform α
  obtain ⟨B, τ, rfl⟩ := hform β
  have hcomm : fieldAut r K σ * fieldAut r K τ = fieldAut r K τ * fieldAut r K σ := by
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  set M : gsp r K := A * gspFieldMap σ B * (gspFieldMap τ A)⁻¹ * B⁻¹ with hMdef
  have h1 : conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ) *
      (conjAut r K A * fieldAut r K σ)⁻¹ * (conjAut r K B * fieldAut r K τ)⁻¹ =
      conjAut r K M := by
    have e1 : fieldAut r K σ * fieldAut r K τ * (fieldAut r K σ)⁻¹ = fieldAut r K τ := by
      rw [hcomm]; group
    have e2 := fieldAut_mul_conjAut_mul_inv σ B
    have e3 := fieldAut_mul_conjAut_mul_inv τ A
    calc conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ) *
          (conjAut r K A * fieldAut r K σ)⁻¹ * (conjAut r K B * fieldAut r K τ)⁻¹
        = conjAut r K A * (fieldAut r K σ * conjAut r K B * (fieldAut r K σ)⁻¹) *
            (fieldAut r K σ * fieldAut r K τ * (fieldAut r K σ)⁻¹) * (conjAut r K A)⁻¹ *
            (fieldAut r K τ)⁻¹ * (conjAut r K B)⁻¹ := by group
      _ = conjAut r K A * conjAut r K (gspFieldMap σ B) * fieldAut r K τ * (conjAut r K A)⁻¹ *
            (fieldAut r K τ)⁻¹ * (conjAut r K B)⁻¹ := by rw [e1, e2]
      _ = conjAut r K A * conjAut r K (gspFieldMap σ B) *
            (fieldAut r K τ * conjAut r K A * (fieldAut r K τ)⁻¹)⁻¹ * (conjAut r K B)⁻¹ := by
          group
      _ = conjAut r K M := by rw [e3, hMdef]; simp only [map_mul, map_inv]
  rw [h1]
  obtain ⟨c₁, hc₁⟩ := isSquare_ratio_units σ (multiplier r K B)
  obtain ⟨c₂, hc₂⟩ := isSquare_ratio_units τ (multiplier r K A)
  have hmM : multiplier r K M = (c₁ * c₂⁻¹) * (c₁ * c₂⁻¹) := by
    have hcg : ∀ a b sb ta : Kˣ, a * sb * ta⁻¹ * b⁻¹ = (sb * b⁻¹) * (ta * a⁻¹)⁻¹ := by
      intro a b sb ta
      simp only [mul_inv_rev, inv_inv, mul_comm, mul_left_comm, mul_assoc]
    have hcg2 : c₁ * c₁ * (c₂ * c₂)⁻¹ = (c₁ * c₂⁻¹) * (c₁ * c₂⁻¹) := by
      simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    rw [hMdef]
    simp only [map_mul, map_inv, multiplier_gspFieldMap_symp]
    rw [hcg, hc₁, hc₂]
    exact hcg2
  exact conjAut_mem_inner_of_isSquare ⟨((c₁ * c₂⁻¹ : Kˣ) : K), by rw [hmM, Units.val_mul]⟩

end Out

theorem outerComm_statedProj_sp_two (K : Type) [Field K] [Finite K] :
    OuterComm (StatedProj (StatedSp 2 K)) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := h2 ▸ ringChar.charP K
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    intro γ α
    exact CFSG.RankThree.PartTwo.Sec8.isInnerAut_commutator_statedSp_two n.pos
      (by rw [Nat.card_eq_fintype_card]; exact hn) γ α
  · exact outerComm_statedProj_sp_of_forall
      (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard h2
        le_rfl)

theorem outerComm_statedProj_sp {r : ℕ} (hr : 3 ≤ r) (K : Type) [Field K] [Finite K] :
    OuterComm (StatedProj (StatedSp r K)) :=
  haveI : NeZero r := ⟨by omega⟩
  outerComm_statedProj_sp_of_forall (automorphism_generation hr).2

theorem p1OffCharAlmostSimpleNonNormalAt_C {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.C r q, hv⟩ := by
  have hr : 3 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      (outerComm_statedProj_sp hr _))

theorem p1OffCharAlmostSimpleNonNormalAt_B_two {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.B 2 q, hv⟩ := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (outerComm_statedProj_sp_two _))

theorem p1OffCharAlmostSimpleNonNormalAt_B_even {r : ℕ} {q : TauCeti.PrimePower} (hr : 3 ≤ r)
    (hq : q.p = 2) (hv : (TauCeti.LieTypeIndex.B r q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.B r q, hv⟩ := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B r q, hv⟩
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq hr)
      (outerComm_statedProj_sp hr _))

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
