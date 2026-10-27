module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCNOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_mem_blockSpecialLinear_mul_pointRadElem [CharP K 2] {c : Fin n}
    {B : SpecialLinearGroup (Fin n) K}
    (hB : ∀ i, (B : Matrix (Fin n) (Fin n) K) i c = (1 : Matrix (Fin n) (Fin n) K) i c) :
    ∃ A ∈ blockSpecialLinear (K := K) ({c}ᶜ : Finset (Fin n)), ∃ r : Fin n → K,
      B = A * pointRadElem c r := by
  classical
  set r : Fin n → K := fun j => (B : Matrix (Fin n) (Fin n) K) c j with hr
  have hsq : pointRadElem c r * pointRadElem c r = 1 := by
    rw [pointRadElem_mul, show r + r = 0 from by
      ext k
      simp only [Pi.add_apply, Pi.zero_apply]
      rw [← two_mul, CharTwo.two_eq_zero, zero_mul], pointRadElem_zero]
  refine ⟨B * pointRadElem c r, ?_, r, ?_⟩
  · have hBc : (B : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1 = Pi.single c 1 := by
      rw [mulVec_single_one, col_eq_single_of_forall_apply_eq_one_apply hB]
    have hcoe : ((B * pointRadElem c r : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) + vecMulVec (Pi.single c 1) (Function.update r c 0) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_pointRadElem, pointRadMat, Matrix.mul_add,
        Matrix.mul_one, mul_vecMulVec, hBc]
    rw [mem_blockSpecialLinear]
    intro i j hij
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hij
    rw [hcoe, Matrix.add_apply, vecMulVec_apply]
    rcases hij with rfl | rfl
    · rw [Pi.single_eq_same, one_mul]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, add_zero, hB j]
      · rw [Function.update_of_ne hj, hr, ← two_mul, CharTwo.two_eq_zero, zero_mul,
          one_apply_ne (Ne.symm hj)]
    · rw [Function.update_self, mul_zero, add_zero, hB i]
  · rw [mul_assoc, hsq, mul_one]

theorem mem_sup_blockSL_of_mem_normalizer_pointRadical [CharP K 2] (hK : Nat.card K = 2)
    (hn : 2 ≤ n) {c : Fin n} {p : projectiveSL n K}
    (hp : p ∈ normalizer (pointRadical (K := K) c : Set (projectiveSL n K))) :
    p ∈ pointRadical (K := K) c ⊔ blockSL (K := K) ({c}ᶜ : Finset (Fin n)) := by
  classical
  obtain ⟨B, rfl⟩ := proj_surjective n K p
  obtain ⟨j, hjc⟩ : ∃ j : Fin n, j ≠ c := by
    have hcard : 0 < (({c}ᶜ : Finset (Fin n))).card := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hcard
    exact ⟨j, by simpa using hj⟩
  set g := pointRadElem c (Pi.single j (1 : K)) with hg
  have h1 := (mem_normalizer_iff.1 hp _).1 (proj_pointRadElem_single_mem (K := K) hjc)
  obtain ⟨r', -, hr'⟩ := mem_pointRadical_iff_exists_pointRadElem.1 h1
  rw [← hg, ← map_inv (proj n K), ← map_mul, ← map_mul] at hr'
  have h2 := proj_injective_of_natCard_eq_two hK hr'
  have h3 : (B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) =
      (pointRadMat c r') * B := by
    have h4 : pointRadElem c r' * B = B * g := by rw [h2]; group
    have h5 := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) h4
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_pointRadElem] at h5
    exact h5.symm
  rw [hg, coe_pointRadElem, pointRadMat_single hjc, pointRadMat] at h3
  have hcol : ∀ i : Fin n, i ≠ c → (B : Matrix (Fin n) (Fin n) K) i c = 0 := by
    intro i hic
    have h6 := congrFun₂ (vecMulVec_eq_of_commute_one_add h3) i j
    simp only [vecMulVec_apply, mulVec_single_one, col_apply, Pi.single_eq_same, mul_one,
      Pi.single_apply, hic, ↓reduceIte, zero_mul] at h6
    exact h6
  have hcc : (B : Matrix (Fin n) (Fin n) K) c c = 1 := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c c) with h0 | h1
    · exfalso
      have hdet : (B : Matrix (Fin n) (Fin n) K).det = 0 :=
        det_eq_zero_of_column_eq_zero c fun i => by
          by_cases hi : i = c
          · rw [hi, h0]
          · exact hcol i hi
      rw [B.2] at hdet
      exact one_ne_zero hdet
    · exact h1
  have hB : ∀ i, (B : Matrix (Fin n) (Fin n) K) i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
    intro i
    by_cases hi : i = c
    · rw [hi, hcc, one_apply_eq]
    · rw [hcol i hi, one_apply_ne hi]
  obtain ⟨A, hA, r, rfl⟩ := exists_mem_blockSpecialLinear_mul_pointRadElem hB
  rw [map_mul]
  exact mul_mem (mem_sup_right (proj_mem_blockSL hA))
    (mem_sup_left (proj_pointRadElem_mem_pointRadical c r))

theorem not_forall_conj_dualAut_mem [CharP K 2] (hK : Nat.card K = 2) (hn : 3 ≤ n) (c : Fin n)
    (p : projectiveSL n K) :
    ¬ ∀ v ∈ pointRadical (K := K) c, p * dualAut n K v * p⁻¹ ∈ pointRadical (K := K) c := by
  classical
  intro h
  obtain ⟨B, rfl⟩ := proj_surjective n K p
  have hzero : ∀ j : Fin n, j ≠ c → ∀ i : Fin n, i ≠ c →
      (B : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro j hjc i hic
    set g := pointRadElem c (Pi.single j (1 : K)) with hg
    have hg2 : g⁻¹ = g := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [hg, pointRadElem_mul, show (Pi.single j (1 : K) : Fin n → K) + Pi.single j (1 : K) = 0
        from by
        ext k
        simp only [Pi.add_apply, Pi.zero_apply]
        rw [← two_mul, CharTwo.two_eq_zero, zero_mul], pointRadElem_zero]
    have h1 := h _ (proj_pointRadElem_single_mem (K := K) hjc)
    rw [← hg, dualAut_proj, hg2] at h1
    obtain ⟨r', -, hr'⟩ := mem_pointRadical_iff_exists_pointRadElem.1 h1
    rw [← map_inv (proj n K), ← map_mul, ← map_mul] at hr'
    have h2 := proj_injective_of_natCard_eq_two hK hr'
    have h3 : (B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ =
        (pointRadMat c r') * B := by
      have h4 : pointRadElem c r' * B = B * g.transpose := by rw [h2]; group
      have h5 := congrArg
        (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) h4
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_pointRadElem,
        Matrix.SpecialLinearGroup.coe_transpose] at h5
      exact h5.symm
    rw [hg, coe_pointRadElem, pointRadMat_single hjc, transpose_add, transpose_one,
      transpose_vecMulVec, pointRadMat] at h3
    have h6 := congrFun₂ (vecMulVec_eq_of_commute_one_add h3) i c
    simp only [vecMulVec_apply, mulVec_single_one, col_apply, Pi.single_eq_same, mul_one,
      Pi.single_apply, hic, ↓reduceIte, zero_mul] at h6
    exact h6
  obtain ⟨j₁, j₂, hj₁, hj₂, h12⟩ := exists_two_ne_of_three_le hn c
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = 0 := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c j₁) with
      h0 | h1
    · refine det_eq_zero_of_column_eq_zero j₁ fun i => ?_
      by_cases hi : i = c
      · rw [hi, h0]
      · exact hzero j₁ hj₁ i hi
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c j₂) with
      h0' | h1'
    · refine det_eq_zero_of_column_eq_zero j₂ fun i => ?_
      by_cases hi : i = c
      · rw [hi, h0']
      · exact hzero j₂ hj₂ i hi
    refine det_zero_of_column_eq h12 fun i => ?_
    by_cases hi : i = c
    · rw [hi, h1, h1']
    · rw [hzero j₁ hj₁ i hi, hzero j₂ hj₂ i hi]
  rw [B.2] at hdet
  exact one_ne_zero hdet

end Model

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem modelToG_sup_eq_sup {n : ℕ} {K : Type} [Field K] (e : L ≃* projectiveSL n K)
    (A B : Subgroup (projectiveSL n K)) : modelToG e (A ⊔ B) = modelToG e A ⊔ modelToG e B := by
  rw [modelToG, modelToG, modelToG, Subgroup.map_sup, Subgroup.map_sup]

omit [Finite G] in
theorem mem_of_symm_mem_modelToG {n : ℕ} {K : Type} [Field K] (e : L ≃* projectiveSL n K)
    {A : Subgroup (projectiveSL n K)} {x : projectiveSL n K}
    (hx : ((e.symm x : L) : G) ∈ modelToG e A) : x ∈ A := by
  obtain ⟨y, hy, hyx⟩ := (mem_modelToG e).1 hx
  rwa [e.symm.injective (Subtype.ext hyx)] at hy

theorem normalizer_pointRadical_inf_le (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin n) :
    normalizer (modelToG e (pointRadical (K := K) c) : Set G) ⊓ centralizer ({t} : Set G) ≤
      modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ⊔ zpowers t := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  rintro g ⟨hgV, hgt⟩
  have hgL : g ∈ normalizer (L : Set G) := hCN hgt
  set α : MulAut (projectiveSL n K) := e.symm.trans ((conjAutOfMemNormalizer hgL).trans e)
    with hα
  have hαapp : ∀ x : projectiveSL n K, ((e.symm (α x) : L) : G) = g * (e.symm x : G) * g⁻¹ := by
    intro x
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      coe_conjAutOfMemNormalizer_apply]
  have hαV : ∀ v ∈ pointRadical (K := K) c, α v ∈ pointRadical (K := K) c := by
    intro v hv
    refine mem_of_symm_mem_modelToG e ?_
    rw [hαapp]
    exact (mem_normalizer_iff.1 hgV _).1 (symm_mem_modelToG e hv)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn).2 α
  rw [SeitzQ2.fieldAut_eq_one_of_card_eq_two hK σ, mul_one] at hαeq
  obtain ⟨p, hp⟩ := SeitzQ2.conjAut_mem_inner_of_card_eq_two hK A
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one, ← hp] at hαeq
    set l : L := e.symm p with hl
    have hgl : ∀ y : L, g * (y : G) * g⁻¹ = (l : G) * y * (l : G)⁻¹ := by
      intro y
      have h1 := hαapp (e y)
      rw [hαeq, MulAut.conj_apply, MulEquiv.symm_apply_apply] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    have hlt : (l : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l l.2)
    have hlg : (l : G)⁻¹ * g ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun y hy => ?_, mul_mem (inv_mem hlt) hgt⟩
      have h1 := hgl ⟨y, hy⟩
      calc y * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * g := by group
        _ = (l : G)⁻¹ * (g * y * g⁻¹) * g := by rw [← h1]
        _ = (l : G)⁻¹ * g * y := by group
    rw [hKt] at hlg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hlg
    have hgeq : g = (l : G) * t ^ k := by rw [hk]; group
    have hpN : p ∈ normalizer (pointRadical (K := K) c : Set (projectiveSL n K)) := by
      rw [mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        have h1 := hαV v hv
        rwa [hαeq, MulAut.conj_apply] at h1
      · intro hv
        have hinj : Set.InjOn (fun x => p * x * p⁻¹) (pointRadical (K := K) c : Set _) :=
          fun x _ y _ hxy => by simpa using hxy
        have hmaps : Set.MapsTo (fun x => p * x * p⁻¹) (pointRadical (K := K) c : Set _)
            (pointRadical (K := K) c : Set _) := fun x hx => by
          have h1 := hαV x hx
          rwa [hαeq, MulAut.conj_apply] at h1
        have hfin : (pointRadical (K := K) c : Set (projectiveSL n K)).Finite := Set.toFinite _
        obtain ⟨x, hx, hxv⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hv
        have hxv' : x = v := by simpa using hxv
        rw [← hxv']
        exact hx
    have hpS := mem_sup_blockSL_of_mem_normalizer_pointRadical hK (by omega) hpN
    have hlS : (l : G) ∈ modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) := by
      rw [← modelToG_sup_eq_sup]
      exact symm_mem_modelToG e hpS
    rw [hgeq]
    exact mul_mem (mem_sup_left hlS) (mem_sup_right (zpow_mem (mem_zpowers t) k))
  · rw [pow_one, ← hp] at hαeq
    refine absurd (fun v hv => ?_) (not_forall_conj_dualAut_mem hK hn c p)
    have h1 := hαV v hv
    rw [hαeq] at h1
    simpa only [MulAut.mul_apply, MulAut.conj_apply] using h1

theorem lFiveNormalizerPointRadicalInput : LFiveNormalizerPointRadicalInput :=
  fun _ _ _ _ hset _ _ _ hK e _ ht hKt c =>
    normalizer_pointRadical_inf_le hset (by norm_num) hK e ht hKt c

end Seitz

end CFSG.SeitzReduction.LinearPilot
