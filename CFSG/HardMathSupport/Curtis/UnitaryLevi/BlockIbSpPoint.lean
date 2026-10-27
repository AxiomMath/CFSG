module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpKill

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag isoFlag)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {r : ℕ}

theorem spSupported_fixes_image {K : Type} [Field K] [CharP K 2] {f p : ℕ} {y : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (HB : SpPrimaryBlocks 2 f p y a) {u e : Fin r ⊕ Fin r → K}
    (hue : spEnd y u - u = e) {g : StatedSp r K} (hg : g ∈ spSupported y {X - 1}) :
    spEnd g e = e := by
  classical
  rw [mem_spSupported] at hg
  obtain ⟨hcomm, hfix⟩ := hg
  have hcomm' : ∀ z, spEnd g (spEnd y z) = spEnd y (spEnd g z) := by
    intro z
    rw [spEnd_apply, spEnd_apply, spEnd_apply, spEnd_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← spMat_mul, ← spMat_mul, hcomm]
  have hF1 : ∀ z, z ∈ primaryComponent (spEnd y) (X - 1) ↔ spEnd y z = z := by
    intro z
    rw [HB.fixed_eq, LinearMap.mem_ker]
    change spEnd y z - z = 0 ↔ _
    rw [sub_eq_zero]
  have hdec : ∃ a ∈ primaryComponent (spEnd y) (X - 1), ∃ b, spEnd g b = b ∧ u = a + b := by
    have htop : u ∈ ⨆ h : primaryFactors (spEnd y), primaryComponent (spEnd y) (h : K[X]) := by
      rw [HB.isInternal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction _ (motive := fun z => ∃ a ∈ primaryComponent (spEnd y) (X - 1),
      ∃ b, spEnd g b = b ∧ z = a + b) htop ?_ ?_ ?_
    · intro h z hz
      by_cases hh : (h : K[X]) = X - 1
      · refine ⟨z, ?_, 0, by simp, by simp⟩
        rw [← hh]; exact hz
      · exact ⟨0, Submodule.zero_mem _, z, hfix h h.2 hh z hz, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, 0, by simp, by simp⟩
    · rintro z z' ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
      refine ⟨a + a', Submodule.add_mem _ ha ha', b + b', by rw [map_add, hb, hb'], by abel⟩
  obtain ⟨a, haF, b, hb, hu⟩ := hdec
  have hya : spEnd y a = a := (hF1 a).1 haF
  have hga : spEnd y (spEnd g a) = spEnd g a := by rw [← hcomm', hya]
  have hdiff : spEnd g u - u = spEnd g a - a := by
    rw [hu, map_add, hb]; abel
  have hY : spEnd y (spEnd g u - u) = spEnd g u - u := by
    rw [hdiff, map_sub, hga, hya]
  have h1 := hY
  rw [map_sub] at h1
  rw [← hue, map_sub, hcomm']
  rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
  rw [h1]
  abel

section YPoint

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam pairMat)

@[expose] def yC : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem yC_pow : yC ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two]
  show _ * _ * _ = (1 : Matrix _ _ _)
  decide +kernel

@[expose] noncomputable def yP (i : Fin r) : StatedSp r (ZMod 2) := lam i yC

theorem spMat_yP (i : Fin r) :
    spMat (yP i) = pairMat (Sum.inl i) (Sum.inr i) !![(0 : ZMod 2), 1; 1, 1] := rfl

theorem yP_pow (i : Fin r) : yP i ^ 3 = 1 := by
  rw [yP, ← map_pow, yC_pow, map_one]

theorem yP_mulVec_other (i : Fin r) {x : Fin r ⊕ Fin r} (hx1 : x ≠ Sum.inl i)
    (hx2 : x ≠ Sum.inr i) :
    spMat (yP i) *ᵥ (Pi.single x 1 : Fin r ⊕ Fin r → ZMod 2) = Pi.single x 1 := by
  rw [Matrix.mulVec_single_one]
  funext z
  rw [Matrix.col_apply, spMat_yP, SymplecticTorusWeyl.pairMat_apply_of_ne' hx1 hx2]
  simp [Matrix.one_apply, Pi.single_apply]

theorem yP_mulVec_f (i : Fin r) :
    spMat (yP i) *ᵥ (Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → ZMod 2) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  rw [Matrix.mulVec_single_one]
  funext z
  rw [Matrix.col_apply, spMat_yP]
  by_cases h1 : z = Sum.inl i
  · subst h1
    rw [SymplecticTorusWeyl.pairMat_apply_fst]
    simp
  by_cases h2 : z = Sum.inr i
  · subst h2
    rw [SymplecticTorusWeyl.pairMat_apply_snd Sum.inl_ne_inr]
    simp
  · rw [SymplecticTorusWeyl.pairMat_apply_of_ne h1 h2]
    simp [h1, h2]

theorem yP_ne_one (i : Fin r) : yP i ≠ 1 := by
  intro h
  have := congrArg (fun g : StatedSp r (ZMod 2) => (spMat g) (Sum.inl i) (Sum.inl i)) h
  rw [spMat_yP, SymplecticTorusWeyl.pairMat_apply_fst, spMat_one] at this
  simp at this

end YPoint

theorem finrank_fixed_yP (hr : 3 ≤ r)
    (HB : SpPrimaryBlocks 2 1 3 (yP (⟨0, by omega⟩ : Fin r)) (SymplecticFlag.proj r (ZMod 2) (yP ⟨0, by omega⟩))) :
    4 ≤ Module.finrank (ZMod 2) (primaryComponent (spEnd (yP (⟨0, by omega⟩ : Fin r))) (X - 1)) := by
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  set σ : Fin 4 → Fin r ⊕ Fin r :=
    ![Sum.inl ⟨1, by omega⟩, Sum.inl ⟨2, by omega⟩, Sum.inr ⟨1, by omega⟩, Sum.inr ⟨2, by omega⟩]
    with hσdef
  have hσ : Function.Injective σ := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hli : LinearIndependent (ZMod 2)
      (fun k : Fin 4 => (Pi.single (σ k) 1 : Fin r ⊕ Fin r → ZMod 2)) := by
    have := (Pi.basisFun (ZMod 2) (Fin r ⊕ Fin r)).linearIndependent.comp σ hσ
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  have hF1 : ∀ z, z ∈ primaryComponent (spEnd (yP i0)) (X - 1) ↔ spEnd (yP i0) z = z := by
    intro z
    rw [HB.fixed_eq, LinearMap.mem_ker]
    change spEnd (yP i0) z - z = 0 ↔ _
    rw [sub_eq_zero]
  have hle : Submodule.span (ZMod 2) (Set.range
      (fun k : Fin 4 => (Pi.single (σ k) 1 : Fin r ⊕ Fin r → ZMod 2))) ≤
      primaryComponent (spEnd (yP i0)) (X - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hF1]
    refine yP_mulVec_other i0 ?_ ?_ <;>
      fin_cases k <;> simp [hσdef, hi0]
  calc 4 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
      (fun k : Fin 4 => (Pi.single (σ k) 1 : Fin r ⊕ Fin r → ZMod 2)))) := by
        rw [finrank_span_eq_card hli]; simp
    _ ≤ _ := Submodule.finrank_mono hle

theorem false_of_cyc_point (hr : 3 ≤ r)
    (hcyc : CFSG.AGLEmbedding.CycPerfect 3 (flagStabilizer r (ZMod 2) {1})) : False := by
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  have HB := exists_blocks_sp_three (K := ZMod 2) (f := 1) le_rfl (by simp) (by omega)
    (yP_pow i0) (yP_ne_one i0)
  obtain ⟨V, hV, hVp, Q, hQV, hQ3, hQnc⟩ := perfectNoncycThreeIn_spFixed HB
    (finrank_fixed_yP hr HB)
  have hue : spEnd (yP i0) (Pi.single (Sum.inr i0) 1) - Pi.single (Sum.inr i0) 1 =
      (Pi.single (Sum.inl i0) 1 : Fin r ⊕ Fin r → ZMod 2) := by
    rw [spEnd_apply, yP_mulVec_f]
    abel
  have hfix : ∀ g ∈ V, spMat g *ᵥ (Pi.single (Sum.inl i0) 1 : Fin r ⊕ Fin r → ZMod 2) =
      Pi.single (Sum.inl i0) 1 := fun g hg =>
    spSupported_fixes_image HB hue (hV hg)
  have hVJ : V ≤ flagStabilizer r (ZMod 2) {1} := by
    intro g hg
    rw [SymplecticHigher.mem_flagStabilizer]
    intro i hi
    rw [Set.mem_singleton_iff.mp hi]
    have hmap : ∀ g' ∈ V, ∀ x ∈ flag r (ZMod 2) 1, spMat g' *ᵥ x ∈ flag r (ZMod 2) 1 := by
      intro g' hg' x hx
      rcases flag_one_cases (by omega) hx with h0 | h0
      · rw [h0]; simp
      · rw [h0, hfix g' hg']
        exact h0 ▸ hx
    exact SymplecticFlag.mem_stabilizer_of_mulVec_mem (hmap g hg) (hmap g⁻¹ (V.inv_mem hg))
  exact hQnc (hcyc V hVJ hVp Q hQV hQ3)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
