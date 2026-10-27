module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {K : Type*} [Field K]

theorem exists_eq_map_conj_flagStabilizer [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ}
    (hn : 1 ≤ n) (T : Sylow p (projectiveSL n K)) (J : Subgroup (projectiveSL n K))
    (hJ : Subgroup.normalizer ((T : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) ≤ J) :
    ∃ (g : projectiveSL n K) (I : Set ℕ), (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧
      Subgroup.normalizer ((T : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) =
        (projUpperTriangular n K).map (MulAut.conj g).toMonoidHom ∧
      J = ((flagStabilizer n K I).map (proj n K)).map (MulAut.conj g).toMonoidHom := by
  have hmem : Subgroup.normalizer ((T : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) ∈
      sylowNormalizers (projectiveSL n K) p := ⟨T, rfl⟩
  rw [sylowNormalizers_eq p hn] at hmem
  obtain ⟨g, hg⟩ := hmem
  set J' := J.map (MulAut.conj g⁻¹).toMonoidHom with hJ'
  have hJJ' : J = J'.map (MulAut.conj g).toMonoidHom := by
    rw [hJ', Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id J]
    congr 1
    ext y
    simp
  have hBJ' : projUpperTriangular n K ≤ J' := by
    intro y hy
    refine ⟨MulAut.conj g y, hJ ?_, by simp [mul_assoc]⟩
    rw [hg]
    exact ⟨y, hy, rfl⟩
  set A := J'.comap (proj n K) with hA
  have hBA : upperTriangular n K ≤ A := by
    rw [hA, ← Subgroup.map_le_iff_le_comap]
    exact hBJ'
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  refine ⟨g, borelOvergroupCuts A, fun i ⟨hi, hin, _⟩ => ⟨hi, hin⟩, hg, ?_⟩
  rw [hJJ', ← hAI, hA, Subgroup.map_comap_eq_self_of_surjective (proj_surjective n K)]

theorem flagStabilizer_one_two : flagStabilizer 3 K {1, 2} = upperTriangular 3 K := by
  refine le_antisymm (fun g hg => ?_) (upperTriangular_le_flagStabilizer _)
  have h1 := mem_stabilizer.mp (mem_flagStabilizer.mp hg 1 (by simp))
  have h2 := mem_stabilizer.mp (mem_flagStabilizer.mp hg 2 (by simp))
  have hc0 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 ∈ flagSpace 3 K 1 :=
    h1 ▸ ⟨_, single_zero_mem_flagSpace_one, rfl⟩
  have hc1 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 1 1 ∈ flagSpace 3 K 2 :=
    h2 ▸ ⟨_, mem_flagSpace_two_iff.mpr (by simp), rfl⟩
  rw [mem_flagSpace] at hc0
  rw [mem_flagSpace_two_iff] at hc1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  · simpa [Matrix.mulVec_single_one] using hc0 1 le_rfl
  · simpa [Matrix.mulVec_single_one] using hc0 2 (by simp)
  · simpa [Matrix.mulVec_single_one] using hc1

theorem eq_map_conj_projStabilizer_of_sylow [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (T : Sylow p (projectiveSL 3 K)) (J : Subgroup (projectiveSL 3 K))
    (hJ : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) ≤ J)
    (hne : J ≠ Subgroup.normalizer ((T : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)))
    (htop : J ≠ ⊤) :
    ∃ (g : projectiveSL 3 K) (d : ℕ), (d = 1 ∨ d = 2) ∧
      J = (projStabilizer (flagSpace 3 K d)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, I, hI, hT, rfl⟩ := exists_eq_map_conj_flagStabilizer p (by norm_num) T J hJ
  have hsub : I ⊆ {1, 2} := fun i hi => by
    obtain ⟨h1, h3⟩ := hI i hi
    interval_cases i <;> simp
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · refine absurd ?_ hne
    rw [hT, show I = {1, 2} from le_antisymm hsub (by
      rintro i (rfl | rfl)
      exacts [h1, h2]), flagStabilizer_one_two]
    rfl
  · refine ⟨g, 1, Or.inl rfl, ?_⟩
    rw [show I = {1} from le_antisymm (fun i hi => by
      rcases hsub hi with rfl | rfl
      · rfl
      · exact absurd hi h2) (by rintro i rfl; exact h1), flagStabilizer_singleton]
    rfl
  · refine ⟨g, 2, Or.inr rfl, ?_⟩
    rw [show I = {2} from le_antisymm (fun i hi => by
      rcases hsub hi with rfl | rfl
      · exact absurd hi h1
      · rfl) (by rintro i rfl; exact h2), flagStabilizer_singleton]
    rfl
  · refine absurd ?_ htop
    rw [show I = ∅ from Set.eq_empty_of_forall_notMem fun i hi => by
      rcases hsub hi with rfl | rfl
      exacts [h1 hi, h2 hi], flagStabilizer_empty,
      Subgroup.map_top_of_surjective _ (proj_surjective 3 K),
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

theorem apply_zero_eq_zero_of_mem_stabilizer_one {n : ℕ} [NeZero n]
    {h : SpecialLinearGroup (Fin n) K} (hh : h ∈ stabilizer (flagSpace n K 1)) {k : Fin n}
    (hk : k ≠ 0) : (h : Matrix (Fin n) (Fin n) K) k 0 = 0 := by
  have hc : (h : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single 0 1 ∈ flagSpace n K 1 :=
    (mem_stabilizer.mp hh) ▸ ⟨_, single_zero_mem_flagSpace_one, rfl⟩
  have := mem_flagSpace.mp hc k (Nat.one_le_iff_ne_zero.mpr fun h0 => hk (Fin.ext h0))
  simpa [Matrix.mulVec_single_one] using this

theorem mulVec_single_zero_of_mem_stabilizer_one {n : ℕ} [NeZero n]
    {h : SpecialLinearGroup (Fin n) K} (hh : h ∈ stabilizer (flagSpace n K 1)) :
    (h : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single 0 1 =
      (h : Matrix (Fin n) (Fin n) K) 0 0 • Pi.single 0 1 := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk, apply_zero_eq_zero_of_mem_stabilizer_one hh hk]

def pointEntry (n : ℕ) [NeZero n] (K : Type*) [Field K] :
    stabilizer (flagSpace n K 1) →* K where
  toFun g := ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      rw [apply_zero_eq_zero_of_mem_stabilizer_one h.2 hk, mul_zero]) (by simp)]

theorem map_commutatorElement_eq_one {G M : Type*} [Group G] [CommMonoid M] (f : G →* M)
    (a b : G) : f ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, mul_assoc (f a * f b),
    mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, one_mul]

theorem commutator_le_map_ker {G M : Type*} [Group G] [CommMonoid M] {H : Subgroup G}
    (f : H →* M) : ⁅H, H⁆ ≤ f.ker.map H.subtype := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, map_commutatorElement_eq_one f _ _, rfl⟩

theorem mulVec_single_zero_of_mem_commutator {n : ℕ} [NeZero n]
    {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ ⁅stabilizer (flagSpace n K 1), stabilizer (flagSpace n K 1)⁆) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨g', hg', rfl⟩ := commutator_le_map_ker (pointEntry n K) hg
  have h1 : ((g' : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0 = 1 := hg'
  change ((g' : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single 0 1 = _
  rw [mulVec_single_zero_of_mem_stabilizer_one g'.2, h1, one_smul]

theorem mulVec_single_zero_of_perfect {n : ℕ} [NeZero n]
    {V : Subgroup (SpecialLinearGroup (Fin n) K)} (hV : V ≤ stabilizer (flagSpace n K 1))
    (hVp : ⁅V, V⁆ = V) {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ V) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  mulVec_single_zero_of_mem_commutator (Subgroup.commutator_mono hV hV (hVp.symm ▸ hg))

theorem apply_two_eq_zero_of_mem_stabilizer_two {h : SpecialLinearGroup (Fin 3) K}
    (hh : h ∈ stabilizer (flagSpace 3 K 2)) {k : Fin 3} (hk : k ≠ 2) :
    (h : Matrix (Fin 3) (Fin 3) K) 2 k = 0 := by
  have hc : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single k 1 ∈ flagSpace 3 K 2 :=
    (mem_stabilizer.mp hh) ▸ ⟨_, mem_flagSpace_two_iff.mpr (by simp [Ne.symm hk]), rfl⟩
  simpa [Matrix.mulVec_single_one] using mem_flagSpace_two_iff.mp hc

def lineEntry (K : Type*) [Field K] : stabilizer (flagSpace 3 K 2) →* K where
  toFun g := ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single 2 (fun k _ hk => by
      rw [apply_two_eq_zero_of_mem_stabilizer_two g.2 hk, zero_mul]) (by simp)]

theorem mulVec_sub_mem_of_apply_two {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ stabilizer (flagSpace 3 K 2)) (h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1)
    (v : Fin 3 → K) : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ flagSpace 3 K 2 := by
  rw [mem_flagSpace_two_iff, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    apply_two_eq_zero_of_mem_stabilizer_two hg (by decide : (0 : Fin 3) ≠ 2),
    apply_two_eq_zero_of_mem_stabilizer_two hg (by decide : (1 : Fin 3) ≠ 2), h22]
  ring

theorem mulVec_sub_mem_of_mem_commutator {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ ⁅stabilizer (flagSpace 3 K 2), stabilizer (flagSpace 3 K 2)⁆) (v : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ flagSpace 3 K 2 := by
  obtain ⟨g', hg', rfl⟩ := commutator_le_map_ker (lineEntry K) hg
  exact mulVec_sub_mem_of_apply_two g'.2 hg' v

theorem mulVec_sub_mem_of_perfect {V : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hV : V ≤ stabilizer (flagSpace 3 K 2)) (hVp : ⁅V, V⁆ = V)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ V) (v : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ flagSpace 3 K 2 :=
  mulVec_sub_mem_of_mem_commutator (Subgroup.commutator_mono hV hV (hVp.symm ▸ hg)) v

end CFSG.AGLEmbedding.LinearThreeKit
