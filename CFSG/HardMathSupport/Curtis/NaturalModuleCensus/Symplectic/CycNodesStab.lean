module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer mem_flagStabilizer)

variable {r : ℕ} {K : Type} [Field K]

theorem pairMat_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) K) (v : ι → K) (x : ι) :
    (pairMat a b g *ᵥ v) x =
      if x = a then g 0 0 * v a + g 0 1 * v b
      else if x = b then g 1 0 * v a + g 1 1 * v b else v x := by
  by_cases hxa : x = a
  · subst hxa
    rw [mulVec, dotProduct, Fintype.sum_eq_add x b hab (fun y hy => by
      simp [pairMat_apply_fst, hy.1, hy.2])]
    simp [pairMat_apply_fst, hab.symm]
  by_cases hxb : x = b
  · subst hxb
    rw [mulVec, dotProduct, Fintype.sum_eq_add a x hab (fun y hy => by
      simp [pairMat_apply_snd hab, hy.1, hy.2])]
    simp [pairMat_apply_snd hab, hxa]
  · simp [mulVec, dotProduct, pairMat_apply_of_ne hxa hxb, hxa, hxb, one_apply,
      Finset.sum_ite_eq]

theorem rho_mulVec_mem_isoFlag {m : ℕ} {i j : Fin r} (hij : i ≠ j)
    (h : (i : ℕ) < m ↔ (j : ℕ) < m) (g : SpecialLinearGroup (Fin 2) K)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ isoFlag r K m) :
    ((rho i j hij g : StatedSp r K) : GL (Fin r ⊕ Fin r) K).1 *ᵥ v ∈ isoFlag r K m := by
  obtain ⟨hv1, hv2⟩ := mem_isoFlag.mp hv
  rw [coe_rho', mem_isoFlag, fromBlocks_mulVec]
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · have h0 : (v ∘ Sum.inr) = 0 := funext hv1
    simp [h0]
  · have h0 : (v ∘ Sum.inr) = 0 := funext hv1
    simp only [h0, mulVec_zero, add_zero, Sum.elim_inl]
    rw [pairMat_mulVec hij]
    have hi : m ≤ (i : ℕ) → v (Sum.inl i) = 0 := hv2 i
    have hj : m ≤ (j : ℕ) → v (Sum.inl j) = 0 := hv2 j
    split_ifs with hki hkj
    · subst hki
      have : m ≤ (k : ℕ) := hk
      have hj' := hj (by have := mt h.mpr (show ¬ (k : ℕ) < m by omega); omega)
      simp only [Function.comp]; rw [hi this, hj']; simp
    · subst hkj
      have : m ≤ (k : ℕ) := hk
      have hi' := hi (by have := mt h.mp (show ¬ (k : ℕ) < m by omega); omega)
      simp only [Function.comp]; rw [hi', hj this]; simp
    · simp only [Function.comp]; exact hv2 k hk

theorem lam_mulVec_mem_isoFlag {m : ℕ} {i : Fin r} (hi : m ≤ (i : ℕ))
    (g : SpecialLinearGroup (Fin 2) K) {v : Fin r ⊕ Fin r → K} (hv : v ∈ isoFlag r K m) :
    ((lam i g : StatedSp r K) : GL (Fin r ⊕ Fin r) K).1 *ᵥ v ∈ isoFlag r K m := by
  obtain ⟨hv1, hv2⟩ := mem_isoFlag.mp hv
  have hvi : v (Sum.inl i) = 0 := hv2 i hi
  rw [coe_lam, mem_isoFlag]
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [pairMat_mulVec Sum.inl_ne_inr]
    simp [hvi, hv1]
  · rw [pairMat_mulVec Sum.inl_ne_inr]
    by_cases hki : k = i
    · subst hki; simp [hvi, hv1]
    · simp [hki, hv2 k hk]

theorem rho_mem_stabilizer {m : ℕ} (hm : m ≤ r) {i j : Fin r} (hij : i ≠ j)
    (h : (i : ℕ) < m ↔ (j : ℕ) < m) (g : SpecialLinearGroup (Fin 2) K) :
    rho i j hij g ∈ stabilizer r K (flag r K m) := by
  refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) fun v hv => ?_
  · rw [mem_flag_of_le hm] at hv ⊢
    exact rho_mulVec_mem_isoFlag hij h g hv
  · rw [← map_inv]
    rw [mem_flag_of_le hm] at hv ⊢
    exact rho_mulVec_mem_isoFlag hij h _ hv

theorem lam_mem_stabilizer {m : ℕ} (hm : m ≤ r) {i : Fin r} (hi : m ≤ (i : ℕ))
    (g : SpecialLinearGroup (Fin 2) K) : lam i g ∈ stabilizer r K (flag r K m) := by
  refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) fun v hv => ?_
  · rw [mem_flag_of_le hm] at hv ⊢
    exact lam_mulVec_mem_isoFlag hi g hv
  · rw [← map_inv]
    rw [mem_flag_of_le hm] at hv ⊢
    exact lam_mulVec_mem_isoFlag hi _ hv

theorem range_rho_le_flagStabilizer {I : Set ℕ} (hI : ∀ m ∈ I, m ≤ r) {i j : Fin r}
    (hij : i ≠ j) (h : ∀ m ∈ I, (i : ℕ) < m ↔ (j : ℕ) < m) :
    (rho i j hij : SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤ flagStabilizer r K I := by
  rintro _ ⟨g, rfl⟩
  exact mem_flagStabilizer.mpr fun m hm => rho_mem_stabilizer (hI m hm) hij (h m hm) g

theorem range_lam_le_flagStabilizer {I : Set ℕ} (hI : ∀ m ∈ I, m ≤ r) {i : Fin r}
    (h : ∀ m ∈ I, m ≤ (i : ℕ)) :
    (lam i : SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤ flagStabilizer r K I := by
  rintro _ ⟨g, rfl⟩
  exact mem_flagStabilizer.mpr fun m hm => lam_mem_stabilizer (hI m hm) (h m hm) g

theorem rho_sl2Diag {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    rho i j hij (sl2Diag a) = torusHom (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) := by
  apply statedSp_ext
  have hT : ∀ x y : K, (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![x, 0; 0, y] := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [coe_rho', coe_torusHom, ← map_inv, coe_sl2Diag, coe_sl2Diag, hT, pairMat_diag hij,
    pairMat_diag hij, fromBlocks_diagonal]
  congr 1
  funext x
  rcases x with x | x <;>
  · by_cases hxi : x = i
    · subst hxi; simp [hij]
    · by_cases hxj : x = j
      · subst hxj; simp [hxi, Pi.mulSingle_apply]
      · simp [hxi, hxj, Pi.mulSingle_apply]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
