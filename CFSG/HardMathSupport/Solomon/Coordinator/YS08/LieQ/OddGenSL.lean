module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGen
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open scoped Matrix

section SLGen

variable {n : ℕ} {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime] [CharP F q]

@[expose] def slUrad (W : Submodule F (Fin n → F)) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | (∀ v, (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W) ∧
    ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F) *ᵥ w = w}
  one_mem' := ⟨fun v => by simp, fun w _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    have hmul : ((g * h : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) :=
      Matrix.SpecialLinearGroup.coe_mul g h
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have : ((g * h : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v - v =
          ((g : Matrix (Fin n) (Fin n) F) *ᵥ ((h : Matrix (Fin n) (Fin n) F) *ᵥ v) -
            (h : Matrix (Fin n) (Fin n) F) *ᵥ v) +
          ((h : Matrix (Fin n) (Fin n) F) *ᵥ v - v) := by
        rw [hmul, ← mulVec_mulVec]
        abel
      rw [this]
      exact add_mem (hg1 _) (hh1 v)
    · rw [hmul, ← mulVec_mulVec, hh2 w hw, hg2 w hw]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hgi : (g : Matrix (Fin n) (Fin n) F) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hig : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (g : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h1 := hg1 (((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v)
      have h2 : (g : Matrix (Fin n) (Fin n) F) *ᵥ
          (((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) = v := by
        rw [mulVec_mulVec, hgi, one_mulVec]
      rw [h2] at h1
      have := neg_mem h1
      simpa using this
    · have := hg2 w hw
      have h3 : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
          ((g : Matrix (Fin n) (Fin n) F) *ᵥ w) = w := by
        rw [mulVec_mulVec, hig, one_mulVec]
      rw [this] at h3
      exact h3

theorem slUrad_isPGroup (W : Submodule F (Fin n → F)) : IsPGroup q (slUrad W) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨hg1, hg2⟩ := g.2
  set g' : SpecialLinearGroup (Fin n) F := (g : SpecialLinearGroup (Fin n) F) with hg'
  set M : Matrix (Fin n) (Fin n) F := (g' : Matrix (Fin n) (Fin n) F) with hM
  set N : Matrix (Fin n) (Fin n) F := M - 1 with hN
  have hNN : N * N = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [← mulVec_mulVec, zero_mulVec]
    have h1 : N *ᵥ v ∈ W := by
      rw [hN, sub_mulVec, one_mulVec]
      exact hg1 v
    have h2 := hg2 _ h1
    rw [hN, sub_mulVec, one_mulVec, h2, sub_self]
  have hpow : ∀ k : ℕ, M ^ k = 1 + (k : F) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hMN : M = 1 + N := by rw [hN]; abel
      rw [pow_succ, ih, hMN]
      have : ((1 : Matrix (Fin n) (Fin n) F) + (k : F) • N) * (1 + N) =
          1 + N + (k : F) • N + (k : F) • (N * N) := by
        rw [add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_add, mul_one, smul_add]
        abel
      rw [this, hNN, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
      abel
  have hq1 : (g : slUrad W) ^ q = 1 := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h := congrFun (congrFun (hpow q) i) j
    have hc : ((q : ℕ) : F) = 0 := CharP.cast_eq_zero F q
    rw [hc, zero_smul, add_zero] at h
    have hcoe : (((g : slUrad W) ^ q : slUrad W) : SpecialLinearGroup (Fin n) F) = g' ^ q := rfl
    show ((((g : slUrad W) ^ q : slUrad W) : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
    rw [hcoe, Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact h
  have hdvd : orderOf (g : slUrad W) ∣ q := orderOf_dvd_of_pow_eq_one hq1
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hdvd with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

theorem mulVec_mem_of_mem_stabilizer {W : Submodule F (Fin n → F)}
    {g : SpecialLinearGroup (Fin n) F} (hg : g ∈ LinearFlag.stabilizer W) {w : Fin n → F}
    (hw : w ∈ W) : (g : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  have hmem : (g : Matrix (Fin n) (Fin n) F) *ᵥ w ∈
      W.map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)) := ⟨w, hw, rfl⟩
  rw [LinearFlag.mem_stabilizer.1 hg] at hmem
  exact hmem

theorem conj_mem_slUrad {W : Submodule F (Fin n → F)} {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ LinearFlag.stabilizer W) {u : SpecialLinearGroup (Fin n) F} (hu : u ∈ slUrad W) :
    g * u * g⁻¹ ∈ slUrad W := by
  obtain ⟨hu1, hu2⟩ := hu
  have hgi : g⁻¹ ∈ LinearFlag.stabilizer W := inv_mem hg
  have hgg : (g : Matrix (Fin n) (Fin n) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcoe : ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * (u : Matrix (Fin n) (Fin n) F) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have hv : v = (g : Matrix (Fin n) (Fin n) F) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) := by
      rw [mulVec_mulVec, hgg, one_mulVec]
    have h1 : ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v - v =
        (g : Matrix (Fin n) (Fin n) F) *ᵥ ((u : Matrix (Fin n) (Fin n) F) *ᵥ
          (((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) -
          ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) := by
      rw [mulVec_sub, hcoe, ← mulVec_mulVec, ← mulVec_mulVec]
      congr 1
    rw [h1]
    exact mulVec_mem_of_mem_stabilizer hg (hu1 _)
  · have hBw := mulVec_mem_of_mem_stabilizer hgi hw
    have h2 := hu2 _ hBw
    rw [hcoe, ← mulVec_mulVec, ← mulVec_mulVec, h2, mulVec_mulVec, hgg, one_mulVec]

theorem stabilizer_le_normalizer_slUrad {W : Submodule F (Fin n → F)} :
    LinearFlag.stabilizer W ≤
      Subgroup.normalizer (slUrad W : Set (SpecialLinearGroup (Fin n) F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_slUrad hg
  · intro h2
    have := conj_mem_slUrad (inv_mem hg) h2
    simpa [mul_assoc] using this

theorem transvection_mem_slUrad {d : ℕ} {i j : Fin n} (hij : i ≠ j) (hid : (i : ℕ) < d)
    (hdj : d ≤ (j : ℕ)) (b : F) :
    Matrix.SpecialLinearGroup.transvection hij b ∈ slUrad (LinearFlag.flagSpace n F d) := by
  have hc : ((Matrix.SpecialLinearGroup.transvection hij b : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j b := rfl
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [hc, add_mulVec, one_mulVec, Matrix.single_mulVec_eq, add_sub_cancel_left]
    refine Submodule.smul_mem _ _ ?_
    rw [LinearFlag.mem_flagSpace]
    intro k hk
    have : k ≠ i := fun h => by subst h; omega
    simp [Pi.single_apply, this]
  · rw [hc, add_mulVec, one_mulVec, Matrix.single_mulVec_eq]
    have hwj : w j = 0 := (LinearFlag.mem_flagSpace.1 hw) j hdj
    rw [hwj, mul_zero, zero_smul, add_zero]

theorem transvection_notMem_scalars {i j : Fin n} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) ∉ LinearFlag.scalars n F := by
  rintro ⟨c, -, hc⟩
  have h1 := congrFun (congrFun hc i) j
  rw [Matrix.SpecialLinearGroup.transvection_coe] at h1
  simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, hij] at h1

theorem map_slUrad_ne_bot {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    (slUrad (LinearFlag.flagSpace n F d)).map (LinearFlag.proj n F) ≠ ⊥ := by
  intro hbot
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hmem := transvection_mem_slUrad (F := F) (d := d) hij (by simp; omega) (by simp; omega) 1
  rw [Subgroup.eq_bot_iff_forall] at hbot
  have := hbot _ ⟨_, hmem, rfl⟩
  exact transvection_notMem_scalars hij (LinearFlag.proj_eq_one_iff.1 this)

theorem flagSpace_bot_lt_lt_top {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    ⊥ < LinearFlag.flagSpace n F d ∧ LinearFlag.flagSpace n F d < ⊤ := by
  have hfin := LinearFlag.finrank_flagSpace (n := n) (K := F) (i := d) hdn.le
  refine ⟨bot_lt_iff_ne_bot.mpr fun h => ?_, lt_top_iff_ne_top.mpr fun h => ?_⟩
  · rw [h, finrank_bot] at hfin
    omega
  · rw [h, finrank_top, Module.finrank_fin_fun] at hfin
    omega

theorem twoParabolics_projectiveSL (hn : 3 ≤ n) :
    TwoParabolics q (LinearFlag.projectiveSL n F) := by
  have hn1 : 1 ≤ n := by omega
  have hB : LinearFlag.projUpperTriangular n F ∈
      sylowNormalizers (LinearFlag.projectiveSL n F) q := by
    rw [LinearFlag.sylowNormalizers_eq q hn1]
    refine ⟨1, ?_⟩
    have : (MulAut.conj (1 : LinearFlag.projectiveSL n F) :
        LinearFlag.projectiveSL n F →* LinearFlag.projectiveSL n F) = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  obtain ⟨U₀, hU₀⟩ := hB
  have hUB : (U₀ : Subgroup (LinearFlag.projectiveSL n F)) ≤ LinearFlag.projUpperTriangular n F :=
    hU₀ ▸ Subgroup.le_normalizer
  have hP₁ : IsCoatom (LinearFlag.projStabilizer (LinearFlag.flagSpace n F 1)) :=
    LinearFlag.isCoatom_projStabilizer_flagSpace le_rfl (by omega)
  have hP₂ : IsCoatom (LinearFlag.projStabilizer (LinearFlag.flagSpace n F 2)) :=
    LinearFlag.isCoatom_projStabilizer_flagSpace (by norm_num) (by omega)
  have hne : ¬ LinearFlag.projStabilizer (LinearFlag.flagSpace n F 2) ≤
      LinearFlag.projStabilizer (LinearFlag.flagSpace n F 1) := by
    intro hle
    rcases hP₂.le_iff.mp hle with h | h
    · exact hP₁.1 h
    · have hinj := (LinearFlag.maximal_parabolics (K := F) q hn1).2.1
        (flagSpace_bot_lt_lt_top (F := F) (le_refl 1) (by omega))
        (flagSpace_bot_lt_lt_top (F := F) (by norm_num : 1 ≤ 2) (by omega)) h
      have h1 := LinearFlag.finrank_flagSpace (n := n) (K := F) (i := 1) (by omega)
      have h2 := LinearFlag.finrank_flagSpace (n := n) (K := F) (i := 2) (by omega)
      rw [hinj] at h1
      omega
  have hQ : ∀ d, 1 ≤ d → d < n →
      ((slUrad (LinearFlag.flagSpace n F d)).map (LinearFlag.proj n F) ≠ ⊥ ∧
      IsPGroup q ((slUrad (LinearFlag.flagSpace n F d)).map (LinearFlag.proj n F)) ∧
      LinearFlag.projStabilizer (LinearFlag.flagSpace n F d) ≤
        Subgroup.normalizer
          (((slUrad (LinearFlag.flagSpace n F d)).map (LinearFlag.proj n F) :
            Subgroup (LinearFlag.projectiveSL n F)) : Set (LinearFlag.projectiveSL n F))) := by
    intro d hd hdn
    refine ⟨map_slUrad_ne_bot hd hdn, (slUrad_isPGroup _).map _, ?_⟩
    exact (Subgroup.map_mono stabilizer_le_normalizer_slUrad).trans
      (Subgroup.le_normalizer_map (LinearFlag.proj n F))
  obtain ⟨hQ1, hQ1p, hQ1n⟩ := hQ 1 le_rfl (by omega)
  obtain ⟨hQ2, hQ2p, hQ2n⟩ := hQ 2 (by norm_num) (by omega)
  exact ⟨U₀, _, _, _, _, hP₁, hne,
    hUB.trans (LinearFlag.projUpperTriangular_le_projStabilizer 1),
    hUB.trans (LinearFlag.projUpperTriangular_le_projStabilizer 2),
    hQ1, hQ1p, hQ1n, hQ2, hQ2p, hQ2n⟩

theorem twoParabolics_PSL (hn : 3 ≤ n) : TwoParabolics q (StatedProj (StatedSL n F)) :=
  (twoParabolics_projectiveSL (q := q) (F := F) hn).of_mulEquiv
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n F)

end SLGen

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
