module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Fixer
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.TwoHomCube
public import CFSG.LieType.SeitzGeneration.HeisTorusU85

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem isCoordBlockOn_comm {n : ℕ} {a b : Fin n} {g : Matrix (Fin n) (Fin n) F}
    (hg : IsCoordBlockOn a b g) : IsCoordBlockOn b a g := by
  intro i j hij
  apply hg
  rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

@[expose] def permπ : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

theorem permP_eq_permMatrix : (permP : Matrix (Fin 3) (Fin 3) F) =
    Equiv.Perm.permMatrix F permπ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (h : UnitaryFieldData ℓ f F)

theorem modelHyperGen_one (hq2 : 2 < ℓ ^ f) (h3 : 3 ∣ ℓ ^ f + 1) (hq8 : ℓ ^ f ≠ 8)
    {σ : F ≃+* F} {ω : Fˣ} {D X : unitaryIsom3 h} (hh : HeisHypU h σ 1 ω D X)
    (hω : IsPrimitiveRoot (ω : F) 3) : ModelHyperGen 3 (heisCubeU h σ D X) := by
  have := h.finite
  rw [modelHyperGen_iff_closure]
  apply closure_eq_top_of_le_liftU
  set M := liftU h (hyperFixU h σ D X) with hMdef
  have hq0 := five_le_q0 h hh.ord h3 hq2 hq8
  have hq : 125 ≤ ℓ ^ f := by
    rw [U3NF.pow_eq_cube h hh.ord]
    exact le_trans (by norm_num) (Nat.pow_le_pow_left hq0 3)
  have h3F := three_ne_zero' h h3
  have hω3 : (ω : F) ^ 3 = 1 := hω.pow_eq_one
  have hω2 : (ω : F) ^ 2 + ω + 1 = 0 := by
    have hne : (ω : F) - 1 ≠ 0 := sub_ne_zero.2 (hω.ne_one (by norm_num))
    have : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left hne
  have hbω : h.bar (ω : F) = (ω : F) ^ 2 := by
    have hn : h.bar (ω : F) * ω = 1 := by
      rw [norm_eq_pow h]
      obtain ⟨k, hk⟩ := h3
      rw [hk, pow_mul, hω3, one_pow]
    have hω0 : (ω : F) ≠ 0 := hω.ne_zero (by norm_num)
    apply mul_right_cancel₀ hω0
    rw [hn, ← pow_succ, hω3]
  obtain ⟨s, hσs, hs, hs2, hs3⟩ := exists_fixed_norm_one h hh.ord hq0
  have hs0 := norm_one_ne_zero hs
  have hs12 := one_add_two_mul_ne_zero h h3F hs
  obtain ⟨x, κ, hκ0, hxM, hxmat⟩ := exists_fixer_mem hh h3 hω2 hbω hσs hs
  obtain ⟨-, h10, h20, h11, h21⟩ := xfix_apply hω2 h3F hs0 hs12
  have hx10 : ∀ i : Fin 2, ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i.succ 0 = 0 := by
    intro i
    rw [hxmat]
    fin_cases i
    · change κ * xfix (ω : F) s 1 0 = 0
      rw [h10, mul_zero]
    · change κ * xfix (ω : F) s 2 0 = 0
      rw [h20, mul_zero]
  have hxU := (mem_unitarySU_iff h).1 x.2
  have hx01 := ug85_row_zero h hxU.2 hx10
  obtain ⟨A, hAx, hAsub⟩ := ug85_exists_emb hx01 hx10 hxU.1
  set X₂ : Subgroup (GL (Fin 2) F) := M.comap (ug85_emb 2) with hX₂
  have hAX₂ : A ∈ X₂ := by
    rw [hX₂, Subgroup.mem_comap, hAx]
    exact hxM
  have hAU : ug83_adj h (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 :=
    ug85_adj_of_emb_mem_su h (by rw [hAx]; exact x.2)
  set e₀ : Fin 2 → F := Pi.single 0 1 with he₀
  have he₀n : ∑ i, h.bar (e₀ i) * e₀ i = 1 := by simp [he₀, Pi.single_apply]
  set u : Fin 2 → F := (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e₀ with hu
  have hu0 : u 0 = κ * (-(ω : F) * (1 + s + s ^ 2) / (1 + 2 * s)) := by
    rw [hu, he₀, mulVec_single_one, ← h11]
    change (A : Matrix (Fin 2) (Fin 2) F) 0 0 = _
    rw [hAsub, submatrix_apply, hxmat]
    rfl
  have hu1 : u 1 = κ * ((s ^ 2 - 1) / (1 + 2 * s)) := by
    rw [hu, he₀, mulVec_single_one, ← h21]
    change (A : Matrix (Fin 2) (Fin 2) F) 1 0 = _
    rw [hAsub, submatrix_apply, hxmat]
    rfl
  have hs2' : 1 + s + s ^ 2 ≠ 0 := by
    intro e
    apply hs3
    linear_combination (s - 1) * e
  have hu0ne : u 0 ≠ 0 := by
    rw [hu0]
    refine mul_ne_zero hκ0 (div_ne_zero (mul_ne_zero (neg_ne_zero.2 ?_) hs2') hs12)
    exact hω.ne_zero (by norm_num)
  have hu1ne : u 1 ≠ 0 := by
    rw [hu1]
    exact mul_ne_zero hκ0 (div_ne_zero (sub_ne_zero.2 hs2) hs12)
  obtain ⟨z, hz, hzo⟩ := exists_gen_cube h h3
  have hz0 := norm_one_ne_zero hz
  obtain ⟨T, hTM, hTmat⟩ := exists_diag_cube_mem hh hz
  obtain ⟨g₁, hg₁⟩ := ug83_exists_unit_hom h he₀n (pow_ne_zero 3 hz0)
  have hg₁X₂ : g₁ ∈ X₂ := by
    rw [hX₂, Subgroup.mem_comap]
    have e : ug85_emb 2 g₁ = (T : GL (Fin 3) F) := by
      apply Units.ext
      rw [ug85_emb_val, hg₁, hTmat, he₀, ug83_hom_single]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ug85_blk, Matrix.det_fin_two, Function.update, diagonal_apply]
    rw [e]
    exact hTM
  have hg₂ : ∃ g ∈ X₂, (g : Matrix (Fin 2) (Fin 2) F) = unitaryHomology h u (z ^ 3) := by
    refine ⟨A * g₁ * A⁻¹, mul_mem (mul_mem hAX₂ hg₁X₂) (inv_mem hAX₂), ?_⟩
    have hinv : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ug83_adj h (A : Matrix (Fin 2) (Fin 2) F) :=
      Units.inv_eq_of_mul_eq_one_left hAU
    rw [Units.val_mul, Units.val_mul, hinv, hg₁, ug83_conj_hom h _ hAU he₀n]
  have hw : h.bar (e₀ 0) * e₀ 0 + h.bar (e₀ 1) * e₀ 1 ≠ 0 := by
    simp [he₀, Pi.single_apply]
  have hun : h.bar (u 0) * u 0 + h.bar (u 1) * u 1 ≠ 0 := by
    have := ug83_norm_mulVec h (A : Matrix (Fin 2) (Fin 2) F) hAU e₀
    rw [Fin.sum_univ_two] at this
    rw [hu, this, he₀n]
    exact one_ne_zero
  have hwu : h.bar (e₀ 0) * u 0 + h.bar (e₀ 1) * u 1 ≠ 0 := by
    simpa [he₀, Pi.single_apply] using hu0ne
  have hind : e₀ 0 * u 1 - e₀ 1 * u 0 ≠ 0 := by
    simpa [he₀, Pi.single_apply] using hu1ne
  have hN : (ℓ ^ f + 1) / 3 ∣ ℓ ^ f + 1 := Nat.div_dvd_of_dvd h3
  have hN3 : ℓ ^ f + 1 ≤ 3 * ((ℓ ^ f + 1) / 3) := by rw [Nat.mul_div_cancel' h3]
  have hSU2 := su2_le_of_two_homologies_of_order h (by omega) hN hN3 X₂ hw hun hwu hind hzo hzo
    ⟨g₁, hg₁X₂, hg₁⟩ hg₂
  have hblk12 : ∀ y ∈ unitarySU ℓ f F 3,
      IsCoordBlockOn (1 : Fin 3) 2 (y : Matrix (Fin 3) (Fin 3) F) → y ∈ M := by
    intro y hy hyb
    have hyb' : IsCoordBlockOn (0 : Fin 2).succ (1 : Fin 2).succ
        (y : Matrix (Fin 3) (Fin 3) F) := hyb
    obtain ⟨h00, h01, h10', hsub⟩ := ug85_block_succ hyb'
    have hyU := (mem_unitarySU_iff h).1 hy
    obtain ⟨A', hAy, hAsub'⟩ := ug85_exists_emb h01 h10' hyU.1
    have hyblk : (y : Matrix (Fin 3) (Fin 3) F) =
        ug85_blk 1 (A' : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAsub', ← h00]
      exact ug85_eq_blk h01 h10'
    have hAS : A' ∈ unitarySU ℓ f F 2 := by
      rw [mem_unitarySU_iff h]
      have hd := hyU.1
      have hu' : ug83_adj h (y : Matrix (Fin 3) (Fin 3) F) *
          (y : Matrix (Fin 3) (Fin 3) F) = 1 := hyU.2
      rw [hyblk, ug85_blk_det, one_mul] at hd
      rw [hyblk, ug85_adj_blk, ug85_blk_mul, ← ug85_blk_one] at hu'
      exact ⟨hd, (ug85_blk_inj hu').2⟩
    have hAX := hSU2 hAS
    rw [hX₂, Subgroup.mem_comap, hAy] at hAX
    exact hAX
  have hP : ∃ c : F, ∃ g ∈ M, (g : Matrix (Fin 3) (Fin 3) F) =
      c • Equiv.Perm.permMatrix F permπ := by
    refine ⟨1, X, mem_liftU_X hh, ?_⟩
    rw [one_smul, ← permP_eq_permMatrix, hh.hX, monomGL_one_val]
  have hMS : M ≤ unitarySU ℓ f F 3 := liftU_le _
  have hblk01 := ug85_good_perm (unitarySU ℓ f F 3) M hMS permπ hP hblk12
  have hblk20 := ug85_good_perm (unitarySU ℓ f F 3) M hMS permπ hP hblk01
  have h01 : ∀ y ∈ unitarySU ℓ f F 3,
      IsCoordBlockOn (0 : Fin 3) 1 (y : Matrix (Fin 3) (Fin 3) F) → y ∈ M := hblk01
  have h20' : ∀ y ∈ unitarySU ℓ f F 3,
      IsCoordBlockOn (2 : Fin 3) 0 (y : Matrix (Fin 3) (Fin 3) F) → y ∈ M := hblk20
  refine unitarySU_le_of_blocks h (by omega) (by norm_num) M ?_
  intro a b hab g hg hgb
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact h01 g hg hgb
  · exact h20' g hg (isCoordBlockOn_comm hgb)
  · exact h01 g hg (isCoordBlockOn_comm hgb)
  · exact absurd rfl hab
  · exact hblk12 g hg hgb
  · exact h20' g hg hgb
  · exact hblk12 g hg (isCoordBlockOn_comm hgb)
  · exact absurd rfl hab

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
