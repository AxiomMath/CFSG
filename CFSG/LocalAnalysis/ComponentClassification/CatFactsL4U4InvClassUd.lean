module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUc

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassU

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def blkSU : unitarySU p f K 3 →* Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) K where
  toFun g := fromBlocks ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 1
  map_one' := by simp [fromBlocks_one]
  map_mul' g g' := by simp [fromBlocks_multiply]

theorem blkSU_apply (g : unitarySU p f K 3) :
    blkSU g = fromBlocks ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 1 := rfl

theorem blkSU_isometry (g : unitarySU p f K 3) :
    ((blkSU g).map h.bar)ᵀ * 1 * blkSU g = 1 := by
  have hg := ((mem_unitarySU_iff h).mp g.2).2
  rw [blkSU_apply, Matrix.mul_one, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  simp [hg, fromBlocks_one]

include h in
theorem det_blkSU (g : unitarySU p f K 3) : (blkSU g).det = 1 := by
  rw [blkSU_apply, det_fromBlocks_zero₂₁, ((mem_unitarySU_iff h).mp g.2).1, det_one, mul_one]

theorem diag_mul_bar {a : K} (ha : h.norm a = 1) : a * h.bar a = 1 := ha

@[expose] noncomputable def diagSU (a b c : K) (ha : h.norm a = 1) (hb : h.norm b = 1)
    (hc : h.norm c = 1) (habc : a * b * c = 1) : unitarySU p f K 3 :=
  ⟨⟨diagonal ![a, b, c], diagonal ![h.bar a, h.bar b, h.bar c], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [diag_mul_bar h ha, diag_mul_bar h hb, diag_mul_bar h hc], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm (h.bar _), diag_mul_bar h ha, diag_mul_bar h hb,
      diag_mul_bar h hc]⟩,
    (mem_unitarySU_iff h).mpr ⟨by
      change (diagonal ![a, b, c]).det = 1
      rw [det_diagonal, Fin.prod_univ_three]
      simpa using habc, by
      change ((diagonal ![a, b, c]).map h.bar)ᵀ * diagonal ![a, b, c] = 1
      rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm (h.bar _), diag_mul_bar h ha, diag_mul_bar h hb,
        diag_mul_bar h hc]⟩⟩

theorem coe_diagSU (a b c : K) (ha : h.norm a = 1) (hb : h.norm b = 1) (hc : h.norm c = 1)
    (habc : a * b * c = 1) :
    (((diagSU h a b c ha hb hc habc : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![a, b, c] := rfl

theorem blkSU_diagSU (a b c : K) (ha : h.norm a = 1) (hb : h.norm b = 1) (hc : h.norm c = 1)
    (habc : a * b * c = 1) :
    blkSU (diagSU h a b c ha hb hc habc) = diagonal (Sum.elim ![a, b, c] fun _ => 1) := by
  rw [blkSU_apply, coe_diagSU, ← fromBlocks_diagonal, diagonal_one]

omit h in
theorem blkSU_injective : Function.Injective (blkSU (p := p) (f := f) (K := K)) := by
  intro g g' hgg
  apply Subtype.ext
  apply Units.ext
  have := congrArg Matrix.toBlocks₁₁ hgg
  rwa [blkSU_apply, blkSU_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁] at this

theorem unorm_neg (a : K) : h.norm (-a) = h.norm a := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_neg, neg_mul_neg]

theorem unorm_neg_one : h.norm (-1 : K) = 1 := by
  rw [unorm_neg, UnitaryFieldData.norm, map_one, one_mul]

theorem unorm_one : h.norm (1 : K) = 1 := by
  rw [UnitaryFieldData.norm, map_one, one_mul]

theorem exists_sqrt_neg_one_norm_one (hq : p ^ f % 4 = 3) :
    ∃ i : K, i * i = -1 ∧ h.norm i = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have hsq : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, h.card,
      show p ^ (2 * f) = (p ^ f) ^ 2 by rw [← pow_mul, mul_comm], Nat.pow_mod, hq]
    norm_num
  obtain ⟨i, hi⟩ := hsq
  refine ⟨i, hi.symm, ?_⟩
  rw [h.norm_eq_pow]
  obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m := ⟨(p ^ f + 1) / 4, by omega⟩
  rw [hm, pow_mul, show i ^ 4 = (i * i) * (i * i) by ring, ← hi]
  norm_num

@[expose] noncomputable def wD1 : unitarySU p f K 3 :=
  diagSU h (-1) 1 (-1) (unorm_neg_one h) (unorm_one h) (unorm_neg_one h) (by ring)

@[expose] noncomputable def xD1 {i : K} (hi : i * i = -1) (hiN : h.norm i = 1) :
    unitarySU p f K 3 :=
  diagSU h i (-i) 1 hiN (by rw [unorm_neg]; exact hiN) (unorm_one h) (by linear_combination -hi)

theorem blkSU_wD1 : blkSU (wD1 h) = diagonal (Sum.elim ![-1, 1, -1] fun _ => 1) :=
  blkSU_diagSU h _ _ _ _ _ _ _

theorem blkSU_xD1 {i : K} (hi : i * i = -1) (hiN : h.norm i = 1) :
    blkSU (xD1 h hi hiN) = diagonal (Sum.elim ![i, -i, 1] fun _ => 1) :=
  blkSU_diagSU h _ _ _ _ _ _ _

theorem exists_D1Hom {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {d : K}
    {v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => d) (fun _ => -d) i • v i) :
    ∃ ψ : unitarySU p f K 3 →* hypSU h 2 0,
      (∀ x, hypProj h 2 0 (ψ x) = 1 ↔ ∃ c : K, blkSU x = c • 1) ∧
      ∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
          ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  have hG : (Matrix.of fun i j => hypForm h 2 0 (v i) (v j)) = 1 := by
    ext i j
    rw [Matrix.of_apply, hv, one_apply]
  obtain ⟨ψ, hψs, hψA⟩ := exists_frameHom h (by simp) hG (Matrix.one_mul 1) blkSU
    (blkSU_isometry h) (det_blkSU h)
  exact ⟨ψ, fun x => (hypProj_eq_one_iff h (ψ x)).trans (exists_congr fun c => hψs x c),
    hψA hA hAv fun x => diagonal_elim_comm _ _ _ _⟩

section D1

variable {P : Type*} [Group P] {ρ : unitarySU p f K 3 →* P}
  (hρ : ∀ x, ρ x = 1 ↔ ∃ c : K, blkSU x = c • 1)

include hρ

theorem D1_involution (hp : p ≠ 2) : orderOf (ρ (wD1 h)) = 2 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  refine orderOf_eq_two_of hρ ⟨1, ?_⟩ ?_
  · rw [map_pow, blkSU_wD1, diagonal_pow, one_smul, ← diagonal_one]
    congr 1
    funext k
    rcases k with k | k
    · fin_cases k <;> simp
    · simp
  · rintro ⟨c, hc⟩
    rw [blkSU_wD1] at hc
    have h0 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
    have h1 := congrFun (congrFun hc (Sum.inl 1)) (Sum.inl 1)
    simp at h0 h1
    exact h2 (by linear_combination h1 - h0)

theorem D1_z4z2 (hp : p ≠ 2) {i : K} (hi : i * i = -1) (hiN : h.norm i = 1) :
    orderOf (ρ (xD1 h hi hiN)) = 4 ∧ orderOf (ρ (wD1 h)) = 2 ∧
      Commute (ρ (xD1 h hi hiN)) (ρ (wD1 h)) ∧ ρ (wD1 h) ≠ ρ (xD1 h hi hiN) ^ 2 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  have hi2 : i ^ 2 = -1 := by rw [pow_two, hi]
  have hx2 : blkSU (xD1 h hi hiN ^ 2) = diagonal (Sum.elim ![-1, -1, 1] fun _ => 1) := by
    rw [map_pow, blkSU_xD1, diagonal_pow]
    congr 1
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [hi2]
    · simp
  refine ⟨orderOf_eq_four_of hρ ?_ ?_, D1_involution h hρ hp, ?_, ?_⟩
  · apply blkSU_injective
    rw [map_pow, blkSU_xD1, diagonal_pow, map_one, ← diagonal_one]
    congr 1
    funext k
    rcases k with k | k
    · have hi4 : i ^ 4 = 1 := by rw [show i ^ 4 = (i ^ 2) ^ 2 by ring, hi2]; norm_num
      have hmi4 : (-i) ^ 4 = 1 := by rw [show (-i) ^ 4 = (i ^ 2) ^ 2 by ring, hi2]; norm_num
      fin_cases k <;> simp [hi4, hmi4]
    · simp
  · rintro ⟨c, hc⟩
    rw [hx2] at hc
    have h0 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
    have h2' := congrFun (congrFun hc (Sum.inl 2)) (Sum.inl 2)
    simp at h0 h2'
    exact h2 (by linear_combination h2' - h0)
  · rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    apply blkSU_injective
    rw [map_mul, map_mul, blkSU_xD1, blkSU_wD1, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  · intro he
    rw [← map_pow] at he
    obtain ⟨c, hc⟩ := eq_smul_of_eq hρ he
    rw [hx2, blkSU_wD1] at hc
    have h0 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
    have h1 := congrFun (congrFun hc (Sum.inl 1)) (Sum.inl 1)
    simp at h0 h1
    exact h2 (by linear_combination h0 + h1)

end D1

theorem exists_pairFrameHom {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {l : K}
    {e g : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i = l • e i)
    (hAg : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i = (-l) • g i)
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    ∃ ψ : SpecialLinearGroup (Fin 2) K →* hypSU h 2 0,
      (∀ x (c : K),
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = c • 1 ↔
          pairHom h x = c • 1) ∧
      ∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
          ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (e j) (g i), heg]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hG : (Matrix.of fun i j => hypForm h 2 0 (Sum.elim e g i) (Sum.elim e g j)) =
      (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    ext (i | i) (j | j) <;> simp [hee, hgg, heg, hge, one_apply]
  have hGG : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks 0 1 1 0 = 1 := by
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  obtain ⟨ψ, hψs, hψA⟩ := exists_frameHom h (by simp) hG hGG (pairHom h)
    (pairHom_isometry h) (det_pairHom h)
  refine ⟨ψ, hψs, hψA hA (d := Sum.elim (fun _ => l) (fun _ => -l)) ?_ fun x => ?_⟩
  · rintro (i | i)
    · exact hAe i
    · exact hAg i
  · rw [pairHom_apply]
    exact diagonal_elim_comm _ _ _ _

theorem pairHom_sq_quatI : pairHom h (slQuatI K ^ 2) = (-1 : K) • 1 := by
  rw [pairHom_apply, coe_slQuatI_sq]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, one_apply]

theorem pair_involution {P : Type*} [Group P] {ρ : SpecialLinearGroup (Fin 2) K →* P}
    (hρ : ∀ x, ρ x = 1 ↔ ∃ c : K, pairHom h x = c • 1) :
    orderOf (ρ (slQuatI K)) = 2 :=
  orderOf_eq_two_of hρ ⟨-1, pairHom_sq_quatI h⟩ fun ⟨c, hc⟩ =>
    pairHom_slQuatI_ne_smul_one h c hc

end InvClassU

end CFSG.ComponentClassification.CatFactsL4U4
