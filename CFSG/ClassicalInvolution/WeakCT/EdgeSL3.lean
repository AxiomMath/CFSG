module

public import CFSG.ClassicalInvolution.WeakCT.A2Signs

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

@[expose] def epsPos {r : ℕ} (F : Type) [Field F]
    (C : (Fin r → ℤ) → (Fin r → ℤ) → ℕ × ℕ → ℤ) (i j : Fin r) : F :=
  Nz F C i j (1, 0) (0, 1)

@[expose] def epsNeg {r : ℕ} (F : Type) [Field F]
    (C : (Fin r → ℤ) → (Fin r → ℤ) → ℕ × ℕ → ℤ) (i j : Fin r) : F :=
  -Nz F C i j (-1, 0) (0, -1)

theorem Nz_mul_self (hdiv : D.divisible = ∅) (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1)
    (hij : i ≠ j)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    {z w : ℤ × ℤ} (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ∈ zEdge)
    (hdiff : w - z ∉ zEdge) : Nz F C i j z w * Nz F C i j z w = 1 := by
  have hsub : pairRoots D i j ⊆ pair i j '' zEdge :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  have hr := pair_mem_roots_zEdge hcij hcji
  have h := hC (pair i j z) (hr z hz) (pair i j w) (hr w hw) (by rw [← map_add]; exact hr _ hzw)
    (fun h => hdiff (mem_of_pair_mem hij hsub (by rwa [← map_sub] at h)))
  unfold Nz
  rcases Int.natAbs_eq_iff.1 h with h | h <;> rw [h] <;> simp

theorem epsPos_mul_self (hdiv : D.divisible = ∅) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) (hij : i ≠ j)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1) : epsPos F C i j * epsPos F C i j = 1 :=
  Nz_mul_self hdiv hcij hcji hij hC (by decide) (by decide) (by decide) (by decide)

theorem epsNeg_mul_self (hdiv : D.divisible = ∅) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) (hij : i ≠ j)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1) : epsNeg F C i j * epsNeg F C i j = 1 := by
  have h := Nz_mul_self (F := F) (C := C) hdiv hcij hcji hij hC (z := (-1, 0)) (w := (0, -1))
    (by decide) (by decide) (by decide) (by decide)
  unfold epsNeg
  rw [neg_mul_neg]
  exact h

theorem exists_sl3_signed [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    (hdiv : D.divisible = ∅) (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) F →* K, ∀ c, ρ (tv 0 1 c) = x (sroot i) c ∧
      ρ (tv 1 0 c) = x (-sroot i) c ∧ ρ (tv 1 2 c) = x (sroot j) c ∧
      ρ (tv 2 1 c) = x (-sroot j) c ∧ ρ (tv 0 2 c) = x (sroot i + sroot j) (epsPos F C i j * c) ∧
      ρ (tv 2 0 c) = x (-(sroot i + sroot j)) (epsNeg F C i j * c) := by
  have hr := pair_mem_roots_zEdge hcij hcji
  have hadd : ∀ z ∈ zEdge, ∀ s t, x (pair i j z) (s + t) = x (pair i j z) s * x (pair i j z) t :=
    fun z hz => (hE.param _ (hr z hz)).2.1
  have hrel := fun z w u (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w = u) (hu : u ∈ zEdge) s t =>
    rel_A2 hdiv hcij hcji hE hij hz hw hzw hu s t
  have hcomm := fun z w (hz : z ∈ zEdge) (hw : w ∈ zEdge) (hzw : z + w ≠ 0)
      (hu : z + w ∉ zEdge) s t => commute_A2 hdiv hcij hcji hE hij hz hw hzw hu s t
  have hA := sign_A hdiv hcij hcji hE hij
  have hB := sign_B hdiv hcij hcji hE hij
  have hC' := sign_C hdiv hcij hcji hE hij
  have hD := sign_D hdiv hcij hcji hE hij
  have hεp : Nz F C i j (1, 0) (0, 1) * Nz F C i j (1, 0) (0, 1) = 1 :=
    Nz_mul_self hdiv hcij hcji hij hC (by decide) (by decide) (by decide) (by decide)
  have hM : Nz F C i j (-1, 0) (0, -1) * Nz F C i j (-1, 0) (0, -1) = 1 :=
    Nz_mul_self hdiv hcij hcji hij hC (by decide) (by decide) (by decide) (by decide)
  have hεm : epsNeg F C i j = -Nz F C i j (-1, 0) (0, -1) := rfl
  have hεp' : epsPos F C i j = Nz F C i j (1, 0) (0, 1) := rfl
  let a : F → K := fun s => x (pair i j (1, 0)) s
  let b : F → K := fun s => x (pair i j (0, 1)) s
  let c : F → K := fun s => x (pair i j (1, 1)) (epsPos F C i j * s)
  let a' : F → K := fun s => x (pair i j (-1, 0)) s
  let b' : F → K := fun s => x (pair i j (0, -1)) s
  let c' : F → K := fun s => x (pair i j (-1, -1)) (epsNeg F C i j * s)
  have ha : ∀ s t, a (s + t) = a s * a t := hadd (1, 0) (by decide)
  have hb : ∀ s t, b (s + t) = b s * b t := hadd (0, 1) (by decide)
  have hc : ∀ s t, c (s + t) = c s * c t := fun s t => by
    show x (pair i j (1, 1)) (epsPos F C i j * (s + t)) = _
    rw [mul_add]
    exact hadd (1, 1) (by decide) _ _
  have ha' : ∀ s t, a' (s + t) = a' s * a' t := hadd (-1, 0) (by decide)
  have hb' : ∀ s t, b' (s + t) = b' s * b' t := hadd (0, -1) (by decide)
  have hc' : ∀ s t, c' (s + t) = c' s * c' t := fun s t => by
    show x (pair i j (-1, -1)) (epsNeg F C i j * (s + t)) = _
    rw [mul_add]
    exact hadd (-1, -1) (by decide) _ _
  obtain ⟨ρ, hρ⟩ := ARS.FrameSL3.exists_hom_of_steinberg (ARS.FrameSL3.fam_add ha hb hc ha' hb' hc')
    (fam_comm_signed ha hb hc ha' hb' hc'
      (fun s t => hcomm (1, 0) (1, 1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (1, 0) (0, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, 1) (1, 1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, 1) (-1, 0) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (-1, 0) (-1, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => hcomm (0, -1) (-1, -1) (by decide) (by decide) (by decide) (by decide) _ _)
      (fun s t => by
        show ⁅x (pair i j (1, 0)) s, x (pair i j (0, 1)) t⁆ =
          x (pair i j (1, 1)) (epsPos F C i j * (s * t))
        rw [hrel (1, 0) (0, 1) (1, 1) (by decide) (by decide) (by decide) (by decide)]
        congr 1
        rw [hεp']
        ring)
      (fun s t => by
        show ⁅x (pair i j (-1, 0)) s, x (pair i j (1, 1)) (epsPos F C i j * t)⁆ =
          x (pair i j (0, 1)) (s * t)
        rw [hrel (-1, 0) (1, 1) (0, 1) (by decide) (by decide) (by decide) (by decide), hA]
        congr 1
        rw [hεp']
        linear_combination (s * t) * hεp)
      (fun s t => by
        show ⁅x (pair i j (1, 0)) s, x (pair i j (-1, -1)) (epsNeg F C i j * t)⁆ =
          x (pair i j (0, -1)) (-(s * t))
        rw [hrel (1, 0) (-1, -1) (0, -1) (by decide) (by decide) (by decide) (by decide), hB]
        congr 1
        rw [hεm]
        linear_combination (-(s * t)) * hM)
      (fun s t => by
        show ⁅x (pair i j (-1, 0)) s, x (pair i j (0, -1)) t⁆ =
          x (pair i j (-1, -1)) (epsNeg F C i j * (-(s * t)))
        rw [hrel (-1, 0) (0, -1) (-1, -1) (by decide) (by decide) (by decide) (by decide)]
        congr 1
        rw [hεm]
        ring)
      (fun s t => by
        show ⁅x (pair i j (0, -1)) s, x (pair i j (1, 1)) (epsPos F C i j * t)⁆ =
          x (pair i j (1, 0)) (-(s * t))
        rw [hrel (0, -1) (1, 1) (1, 0) (by decide) (by decide) (by decide) (by decide), hD]
        congr 1
        rw [hεp']
        linear_combination (-(s * t)) * hεp)
      (fun s t => by
        show ⁅x (pair i j (0, 1)) s, x (pair i j (-1, -1)) (epsNeg F C i j * t)⁆ =
          x (pair i j (-1, 0)) (s * t)
        rw [hrel (0, 1) (-1, -1) (-1, 0) (by decide) (by decide) (by decide) (by decide), hC']
        congr 1
        rw [hεm]
        linear_combination (s * t) * hM))
  refine ⟨ρ, fun c => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tv_of_ne (by decide), hρ, ← pair_one_zero i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_zero i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_neg_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_one_one i j]
    rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_neg_one i j]
    rfl

theorem commute_nonadj (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hij : i ≠ j) (hcij : D.cartan i j = 0) (hcji : D.cartan j i = 0) (s t : F) :
    Commute (x (sroot i) s) (x (sroot j) t) ∧ Commute (x (sroot i) s) (x (-sroot j) t) ∧
      Commute (x (-sroot i) s) (x (sroot j) t) ∧ Commute (x (-sroot i) s) (x (-sroot j) t) := by
  have hsub : pairRoots D i j ⊆ pair i j '' zNon :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  have hcomm : ∀ z w, z ∈ zNon → w ∈ zNon → z + w ≠ 0 → z + w ∉ zNon →
      Commute (x (pair i j z) s) (x (pair i j w) t) := fun z w hz hw hzw hs =>
    commutatorElement_eq_one_iff_commute.1
      ((commutator_pair' hE hij hsub pair_mem_roots_zNon zNon_expPairs hz hw hzw s t).2 hs)
  rw [← pair_neg_one_zero i j, ← pair_zero_neg_one i j, ← pair_one_zero i j, ← pair_zero_one i j]
  exact ⟨hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide)⟩

end CFSG.ClassicalInvolution.WeakCT
