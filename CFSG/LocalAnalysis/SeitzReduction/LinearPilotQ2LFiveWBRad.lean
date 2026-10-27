module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBRadCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2Centralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

namespace InvPlacement

variable (P : InvPlacement n 1)

theorem eq_pointRadElem_of_mem_radical_of_freeRowCol_snd_eq_zero
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.radical K) (h : (P.freeRowCol B).2 = 0) :
    B = pointRadElem (P.u 0) ((B : Matrix (Fin n) (Fin n) K) (P.u 0)) := by
  apply Subtype.ext
  ext i j
  rw [coe_pointRadElem, pointRadMat_apply]
  by_cases hi : i = P.u 0
  · subst hi
    by_cases hj : j = P.u 0
    · subst hj
      rw [hB _ _ le_rfl, ite_eq_right (fun h => h.2 rfl), add_zero]
    · rw [ite_eq_left ⟨rfl, hj⟩, one_apply_ne (Ne.symm hj), zero_add]
  · rw [ite_eq_right (fun h => hi h.1), add_zero]
    by_cases hle : P.level j ≤ P.level i
    · exact hB i j hle
    · have hi0 : P.level i ≠ 0 := fun h => hi (P.level_eq_zero_iff_eq_u_zero.1 h)
      have hi2 := P.level_le_two i
      have hj2 := P.level_le_two j
      have hi1 : P.level i = 1 := by omega
      have hjw : j = P.w 0 := P.level_eq_two_iff_eq_w_zero.1 (by omega)
      subst hjw
      have hiw : i ≠ P.w 0 := fun h => by rw [h, P.level_w] at hi1; omega
      rw [one_apply_ne hiw]
      exact congrFun h ⟨i, P.mem_free.2 hi1⟩

theorem transpose_eq_pointRadElem_of_mem_radical_of_freeRowCol_fst_eq_zero
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.radical K) (h : (P.freeRowCol B).1 = 0) :
    Matrix.SpecialLinearGroup.transpose B =
      pointRadElem (P.w 0) (fun i => (B : Matrix (Fin n) (Fin n) K) i (P.w 0)) := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, transpose_apply, coe_pointRadElem,
    pointRadMat_apply]
  by_cases hi : i = P.w 0
  · subst hi
    by_cases hj : j = P.w 0
    · subst hj
      rw [hB _ _ le_rfl, ite_eq_right (fun h => h.2 rfl), add_zero]
    · rw [ite_eq_left ⟨rfl, hj⟩, one_apply_ne (Ne.symm hj), zero_add]
  · rw [ite_eq_right (fun h => hi h.1), add_zero]
    by_cases hle : P.level i ≤ P.level j
    · rw [hB j i hle, one_apply, one_apply]
      by_cases hij : i = j
      · rw [ite_eq_left hij.symm, ite_eq_left hij]
      · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
    · have hi2' : P.level i ≠ 2 := fun h => hi (P.level_eq_two_iff_eq_w_zero.1 h)
      have hi2 := P.level_le_two i
      have hi1 : P.level i = 1 := by omega
      have hju : j = P.u 0 := P.level_eq_zero_iff_eq_u_zero.1 (by omega)
      subst hju
      have hiu : i ≠ P.u 0 := fun h => by rw [h, P.level_u] at hi1; omega
      rw [one_apply_ne hiu]
      exact congrFun h ⟨i, P.mem_free.2 hi1⟩

private theorem transpose_inv_eq_inv_transpose_SL (B : SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.transpose B⁻¹ = (Matrix.SpecialLinearGroup.transpose B)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one]

theorem le_pointRadical_or_map_dualAut_le [CharP K 2] (hK : Nat.card K = 2)
    (hJ : 3 ≤ P.free.card) {T : Subgroup (LinearFlag.projectiveSL n K)} (hT : T ≤ P.radicalP K)
    (hN : blockSL (K := K) P.free ≤ normalizer (T : Set (LinearFlag.projectiveSL n K)))
    (hcard : Nat.card T < 2 ^ P.free.card * 2 ^ P.free.card) :
    T ≤ pointRadical (P.u 0) ∨
      T.map (LinearFlag.dualAut n K).toMonoidHom ≤ pointRadical (P.w 0) := by
  have hinj := proj_injective_of_natCard_eq_two (n := n) hK
  set R' := T.comap (LinearFlag.proj n K) with hR'def
  have hTR : R'.map (LinearFlag.proj n K) = T :=
    map_comap_eq_self_of_surjective (LinearFlag.proj_surjective n K) T
  have hR : R' ≤ P.radical K := by
    intro B hB
    obtain ⟨B₀, hB₀, hB₀B⟩ := hT hB
    rw [← hinj hB₀B]
    exact hB₀
  have hN' : ∀ (i j : Fin n) (hij : i ≠ j), i ∈ P.free → j ∈ P.free → ∀ B ∈ R',
      Matrix.SpecialLinearGroup.transvection hij (1 : K) * B *
        (Matrix.SpecialLinearGroup.transvection hij (1 : K))⁻¹ ∈ R' := by
    intro i j hij hi hj B hB
    have hmem := mem_normalizer_iff.1 (hN (proj_transvection_mem_blockSL hij hi hj (1 : K)))
    show LinearFlag.proj n K _ ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (hmem _).1 hB
  have hcard' : Nat.card R' < 2 ^ P.free.card * 2 ^ P.free.card := by
    rwa [← hTR, card_map_of_injective hinj] at hcard
  rcases P.freeRowCol_snd_eq_zero_or_fst_eq_zero hK hJ hR hN' hcard' with h | h
  · left
    intro x hx
    obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective n K x
    have hB : B ∈ R' := hx
    rw [P.eq_pointRadElem_of_mem_radical_of_freeRowCol_snd_eq_zero (hR hB) (h B hB)]
    exact proj_pointRadElem_mem_pointRadical _ _
  · right
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective n K x
    have hB : B ∈ R' := hx
    show LinearFlag.dualAut n K (LinearFlag.proj n K B) ∈ _
    rw [LinearFlag.dualAut_proj, transpose_inv_eq_inv_transpose_SL,
      P.transpose_eq_pointRadElem_of_mem_radical_of_freeRowCol_fst_eq_zero (hR hB) (h B hB),
      map_inv]
    exact inv_mem (proj_pointRadElem_mem_pointRadical _ _)

end InvPlacement

private theorem centralizer_conj_singleton_eq_map {X : Type*} [Group X] (c y : X) :
    centralizer ({c * y * c⁻¹} : Set X) =
      (centralizer ({y} : Set X)).map (MulAut.conj c).toMonoidHom := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulAut.conj_symm_apply]
  constructor
  · intro h
    calc c⁻¹ * x * c * y = c⁻¹ * (x * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * x) * c := by rw [h]
      _ = y * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * y * c⁻¹) = c * ((c⁻¹ * x * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * x := by group

theorem exists_conj_map_eq_pointRadical_or_dualAut [CharP K 2] (hK : Nat.card K = 2)
    (hn : 5 ≤ n) {z : LinearFlag.projectiveSL n K} (hz : IsInvolutionClass 1 z)
    {R : Subgroup (LinearFlag.projectiveSL n K)} (hRz : R ≤ centralizer {z})
    (hRn : centralizer {z} ≤ normalizer (R : Set (LinearFlag.projectiveSL n K)))
    (hRc : Nat.card R = 2 ^ (n - 1)) :
    ∃ (c : LinearFlag.projectiveSL n K) (d : Fin n),
      R.map (MulAut.conj c).toMonoidHom = pointRadical d ∨
        (R.map (MulAut.conj c).toMonoidHom).map (LinearFlag.dualAut n K).toMonoidHom =
          pointRadical d := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨-, P, c, hc, hJ, -, hC, -, -, hO2⟩ := centralizer_transvection_perfect_two hK hn hz
  set T := R.map (MulAut.conj c).toMonoidHom with hTdef
  have hTc : Nat.card T = 2 ^ (n - 1) := by
    rw [hTdef, card_map_of_injective (MulAut.conj c).injective, hRc]
  have hCz : centralizer {P.elt K} = (centralizer {z}).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    exact centralizer_conj_singleton_eq_map c z
  have hTC : T ≤ centralizer {P.elt K} := by
    rw [hCz]
    exact map_mono hRz
  have hTN : centralizer {P.elt K} ≤ normalizer (T : Set (LinearFlag.projectiveSL n K)) := by
    rw [hCz, hTdef, ← map_equiv_normalizer_eq]
    exact map_mono hRn
  have hTQ : T ≤ P.radicalP K := hO2 T (IsPGroup.of_card hTc) hTC hTN
  have hTB : blockSL (K := K) P.free ≤ normalizer (T : Set (LinearFlag.projectiveSL n K)) := by
    refine le_trans ?_ hTN
    rw [hC]
    exact le_sup_right
  have hlt : Nat.card T < 2 ^ P.free.card * 2 ^ P.free.card := by
    rw [hTc, hJ, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hV : ∀ d : Fin n, Nat.card (pointRadical (K := K) d) = 2 ^ (n - 1) := fun d => by
    rw [pointRadical, card_pointRadOn hK d (by simp), Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
  rcases P.le_pointRadical_or_map_dualAut_le hK (by omega) hTQ hTB hlt with h | h
  · exact ⟨c, P.u 0, Or.inl (eq_of_le_of_card_ge h (by rw [hV, hTc]))⟩
  · refine ⟨c, P.w 0, Or.inr (eq_of_le_of_card_ge h ?_)⟩
    rw [hV, card_map_of_injective (f := (LinearFlag.dualAut n K).toMonoidHom)
      (LinearFlag.dualAut n K).injective, hTc]

theorem exists_mulAut_map_eq_pointRadical [CharP K 2] (hK : Nat.card K = 2)
    {z : LinearFlag.projectiveSL 5 K} (hz : IsInvolutionClass 1 z)
    {R : Subgroup (LinearFlag.projectiveSL 5 K)}
    (hRz : R ≤ Subgroup.centralizer {z})
    (hRn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (R : Set (LinearFlag.projectiveSL 5 K)))
    (hRc : Nat.card R = 2 ^ 4) :
    ∃ (α : MulAut (LinearFlag.projectiveSL 5 K)) (d : Fin 5),
      R.map α.toMonoidHom = pointRadical d := by
  obtain ⟨c, d, h | h⟩ := exists_conj_map_eq_pointRadical_or_dualAut hK le_rfl hz hRz hRn hRc
  · exact ⟨MulAut.conj c, d, h⟩
  · exact ⟨LinearFlag.dualAut 5 K * MulAut.conj c, d, by rw [← h, Subgroup.map_map]; rfl⟩

end CFSG.SeitzReduction.LinearPilot
