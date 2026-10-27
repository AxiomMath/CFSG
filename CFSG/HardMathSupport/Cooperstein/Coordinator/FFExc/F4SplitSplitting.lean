module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitGroup

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule Matrix

variable (hV : e6Data.Valid) (K : Type*) [Field K] [CharP K 2]

@[expose] def v0 : Fin e6Data.d →₀ K := Finsupp.equivFunOnFinite.symm (s3K K)

@[expose] def fT : (Fin e6Data.d →₀ K) →ₗ[K] K := Finsupp.linearCombination K (s3K K)

@[expose] def commSub : Submodule K (Fin e6Data.d →₀ K) :=
  ⨆ g ∈ F4in27 hV K, LinearMap.range (hV.endo K g - 1)

variable {K}

theorem coe_v0 : ⇑(v0 K) = s3K K := rfl

theorem fT_apply (x : Fin e6Data.d →₀ K) : fT K x = s3K K ⬝ᵥ ⇑x := by
  rw [fT, Finsupp.linearCombination_apply, Finsupp.sum_fintype x (fun i a => a • s3K K i) (fun i => zero_smul K _)]
  simp only [dotProduct, smul_eq_mul, mul_comm]

theorem coe_endo (g : hV.minGroup K) (x : Fin e6Data.d →₀ K) :
    ⇑(hV.endo K g x) = rho hV g *ᵥ ⇑x := by
  have := LinearMap.toMatrix_mulVec_repr Finsupp.basisSingleOne Finsupp.basisSingleOne
    (hV.endo K g) x
  simpa [rho, Finsupp.basisSingleOne_repr] using this.symm

theorem endo_v0 {g : hV.minGroup K} (hg : g ∈ F4in27 hV K) : hV.endo K g (v0 K) = v0 K := by
  ext i
  rw [coe_endo, coe_v0, (inv_of_mem_F4in27 hV hg).1]

theorem fT_endo {g : hV.minGroup K} (hg : g ∈ F4in27 hV K) (x : Fin e6Data.d →₀ K) :
    fT K (hV.endo K g x) = fT K x := by
  rw [fT_apply, fT_apply, coe_endo, dotProduct_mulVec, (inv_of_mem_F4in27 hV hg).2]

theorem s3Z_dotProduct_self : s3Z ⬝ᵥ s3Z = 1 := by decide

theorem fT_v0 : fT K (v0 K) = 1 := by
  rw [fT_apply, coe_v0, s3K, ← RingHom.map_dotProduct, s3Z_dotProduct_self, map_one]

abbrev i12 : Ix := ⟨12, by decide⟩

abbrev i13 : Ix := ⟨13, by decide⟩

abbrev i14 : Ix := ⟨14, by decide⟩

theorem s3K_apply (j : Ix) :
    s3K K j = if j.val = 12 ∨ j.val = 13 ∨ j.val = 14 then 1 else 0 := by
  unfold s3K s3Z
  by_cases h : j.val = 12 ∨ j.val = 13 ∨ j.val = 14 <;> simp [h]

theorem fT_eq (x : Fin e6Data.d →₀ K) : fT K x = x i12 + x i13 + x i14 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]; simp only [Finsupp.add_apply]; ring
  | single j c =>
    have h : fT K (Finsupp.single j c) = c * s3K K j := by
      simp [fT, Finsupp.linearCombination_single]
    rw [h, s3K_apply]
    simp only [Finsupp.single_apply, Fin.ext_iff]
    by_cases h12 : j.val = 12
    · simp [h12]
    · by_cases h13 : j.val = 13
      · simp [h13]
      · by_cases h14 : j.val = 14
        · simp [h14]
        · simp [h12, h13, h14]

theorem commSub_le_ker : commSub hV K ≤ LinearMap.ker (fT K) := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, fT_endo hV hg, Module.End.one_apply,
    sub_self]

theorem sub_mem_commSub {g : hV.minGroup K} (hg : g ∈ F4in27 hV K) (x : Fin e6Data.d →₀ K) :
    hV.endo K g x - x ∈ commSub hV K :=
  le_iSup₂ (f := fun g (_ : g ∈ F4in27 hV K) => LinearMap.range (hV.endo K g - 1)) g hg
    ⟨x, by simp⟩

theorem rho_gen_one (k : ℕ) (hk : k < 72) :
    rho hV (gen hV K (e6root k) 1) = (cast2 K).mapMatrix (Gm2 k) := by
  unfold gen Gm2
  by_cases hfix : graphRoot (e6root k) = e6root k
  · rw [ite_eq_left hfix, ite_eq_left hfix, rho_xm hV k hk, map_add, map_one, one_smul]
    rfl
  · rw [ite_eq_right hfix, ite_eq_right hfix, graphRoot_root k hk, rho_mul, rho_xm hV k hk,
      rho_xm hV _ (gamK_lt k hk), map_mul, map_add, map_add, map_one, one_smul, one_smul]
    rfl

theorem col_apply (k : ℕ) (hk : k < 72) (a i : Ix) :
    (hV.endo K (gen hV K (e6root k) 1) (Finsupp.single a (1 : K)) -
        Finsupp.single a (1 : K)) i = cast2 K ((Gm2 k - 1) i a) := by
  rw [Finsupp.sub_apply]
  have h := congrFun (coe_endo hV (gen hV K (e6root k) 1) (Finsupp.single a (1 : K))) i
  rw [Finsupp.single_eq_pi_single] at h
  rw [h, Matrix.mulVec_single_one, rho_gen_one hV k hk]
  simp only [Matrix.sub_apply, Matrix.one_apply, Finsupp.single_apply, map_sub]
  by_cases h : a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem isRoot_e6root {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (e6root k) :=
  RootCertificate.isRoot_root Tag.E6.rootCertificate_check k hk

theorem single_mem_commSub (b : Ix) (hb : ¬ (b.val = 12 ∨ b.val = 13 ∨ b.val = 14)) :
    Finsupp.single b (1 : K) ∈ commSub hV K := by
  obtain ⟨hk, -, a, -, hcol⟩ := wit_check b hb
  have h := sub_mem_commSub hV (gen_mem_F4in27 hV _ (isRoot_e6root hk) (1 : K))
    (Finsupp.single a (1 : K))
  convert h using 1
  ext i
  rw [col_apply hV _ hk, hcol, Finsupp.single_apply]
  by_cases hi : i = b
  · subst hi; simp
  · simp [hi, Ne.symm hi]

abbrev i10 : Ix := ⟨10, by decide⟩

abbrev i11 : Ix := ⟨11, by decide⟩

theorem single_i12_add_i13_mem_commSub :
    Finsupp.single i12 (1 : K) + Finsupp.single i13 (1 : K) ∈ commSub hV K := by
  obtain ⟨a, -, -, hcol⟩ := trip_check_0
  have h := sub_mem_commSub hV (gen_mem_F4in27 hV _ (isRoot_e6root (k := 0) (by decide)) (1 : K))
    (Finsupp.single a (1 : K))
  have h10 := single_mem_commSub hV (K := K) i10 (by decide)
  convert sub_mem h h10 using 1
  ext i
  rw [Finsupp.sub_apply, col_apply hV _ (by decide), hcol]
  simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]
  by_cases h10 : i.val = 10
  · simp [h10]
  · by_cases h12 : i.val = 12
    · simp [h12]
    · by_cases h13 : i.val = 13
      · simp [h13]
      · simp [h10, h12, h13, Ne.symm h10, Ne.symm h12, Ne.symm h13]

theorem single_i13_add_i14_mem_commSub :
    Finsupp.single i13 (1 : K) + Finsupp.single i14 (1 : K) ∈ commSub hV K := by
  obtain ⟨a, -, -, hcol⟩ := trip_check_2
  have h := sub_mem_commSub hV (gen_mem_F4in27 hV _ (isRoot_e6root (k := 2) (by decide)) (1 : K))
    (Finsupp.single a (1 : K))
  have h11 := single_mem_commSub hV (K := K) i11 (by decide)
  convert sub_mem h h11 using 1
  ext i
  rw [Finsupp.sub_apply, col_apply hV _ (by decide), hcol]
  simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]
  by_cases h11 : i.val = 11
  · simp [h11]
  · by_cases h13 : i.val = 13
    · simp [h13]
    · by_cases h14 : i.val = 14
      · simp [h14]
      · simp [h11, h13, h14, Ne.symm h11, Ne.symm h13, Ne.symm h14]

theorem ker_le_of_targets (W : Submodule K (Fin e6Data.d →₀ K))
    (h1 : ∀ b : Ix, ¬ (b.val = 12 ∨ b.val = 13 ∨ b.val = 14) → Finsupp.single b (1 : K) ∈ W)
    (h2 : Finsupp.single i12 (1 : K) + Finsupp.single i13 (1 : K) ∈ W)
    (h3 : Finsupp.single i13 (1 : K) + Finsupp.single i14 (1 : K) ∈ W) :
    LinearMap.ker (fT K) ≤ W := by
  intro x hx
  rw [LinearMap.mem_ker, fT_eq] at hx
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  set y : Fin e6Data.d →₀ K := x - x i12 • (Finsupp.single i12 1 + Finsupp.single i13 1) -
    x i14 • (Finsupp.single i13 1 + Finsupp.single i14 1) with hy
  have hy12 : y i12 = 0 := by simp [hy, Fin.ext_iff]
  have hy13 : y i13 = 0 := by
    simp only [hy, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff]
    simp
    linear_combination hx + (-(x i12 + x i14)) * h2'
  have hy14 : y i14 = 0 := by simp [hy, Fin.ext_iff]
  have hyM : y ∈ W := by
    rw [← Finsupp.sum_single y]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hj' : y j ≠ 0 := Finsupp.mem_support_iff.1 hj
    have hjS : ¬ (j.val = 12 ∨ j.val = 13 ∨ j.val = 14) := by
      rintro (h | h | h)
      · exact hj' (by rw [show j = i12 from Fin.ext h]; exact hy12)
      · exact hj' (by rw [show j = i13 from Fin.ext h]; exact hy13)
      · exact hj' (by rw [show j = i14 from Fin.ext h]; exact hy14)
    have := Submodule.smul_mem _ (y j) (h1 j hjS)
    simpa using this
  have hx' : x = y + x i12 • (Finsupp.single i12 1 + Finsupp.single i13 1) +
      x i14 • (Finsupp.single i13 1 + Finsupp.single i14 1) := by
    rw [hy]; abel
  rw [hx']
  exact add_mem (add_mem hyM (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)

theorem ker_le_commSub : LinearMap.ker (fT K) ≤ commSub hV K :=
  ker_le_of_targets _ (fun b hb => single_mem_commSub hV b hb) (single_i12_add_i13_mem_commSub hV)
    (single_i13_add_i14_mem_commSub hV)

theorem commSub_eq_ker : commSub hV K = LinearMap.ker (fT K) :=
  le_antisymm (commSub_le_ker hV) (ker_le_commSub hV)

theorem v0_ne_zero : v0 K ≠ 0 := fun h => by
  have := fT_v0 (K := K)
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem isCompl_v0_commSub : IsCompl (Submodule.span K {v0 K}) (commSub hV K) := by
  rw [commSub_eq_ker hV]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.mem_ker, map_smul, fT_v0, smul_eq_mul, mul_one] at hx'
    rw [hx', zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have h1 : x - fT K x • v0 K ∈ LinearMap.ker (fT K) := by
      rw [LinearMap.mem_ker, map_sub, map_smul, fT_v0, smul_eq_mul, mul_one, sub_self]
    have h2 : fT K x • v0 K ∈ Submodule.span K {v0 K} := Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have := Submodule.add_mem_sup h2 h1
    rwa [add_sub_cancel] at this

@[expose] def M26 (_hV : e6Data.Valid) (K : Type*) [Field K] [CharP K 2] :
    Submodule K (Fin e6Data.d →₀ K) := LinearMap.ker (fT K)

theorem M26_eq_ker : M26 hV K = LinearMap.ker (fT K) := rfl

theorem M26_eq_commSub : M26 hV K = commSub hV K := (commSub_eq_ker hV).symm

theorem isCompl_v0_M26 : IsCompl (Submodule.span K {v0 K}) (M26 hV K) := by
  rw [M26_eq_commSub]; exact isCompl_v0_commSub hV

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
