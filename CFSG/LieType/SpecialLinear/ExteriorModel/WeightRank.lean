module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Weights
public import CFSG.LieType.SpecialLinear.ExteriorModel.OrbitCount
public import CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionMovedBlocks
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WeylOrbitBounds

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix Module
open CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionMovedBlocks
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

@[expose] def bWeights (k : Type) [Field k] (ε : τ → Finset (Fin n)) : Set (τ → Fin n → ℤ) :=
  {μ | ∃ w ∈ bCyc (k := k) ε, w ∉ bRad ε ∧ ∀ s, w s ≠ 0 → bWt ε s = μ}

@[expose] def permWt (π : Equiv.Perm (Fin n)) (μ : τ → Fin n → ℤ) : τ → Fin n → ℤ :=
  fun r a => μ r (π.symm a)

omit [Fintype τ] [DecidableEq τ] in
theorem bWt_btop (ε : τ → Finset (Fin n)) :
    bWt ε (btop ε) = fun r => topWt (ε r) := by
  have hmain : bWt ε (fun p : τ × Fin n => initSeg (bdeg_le ε p)) =
      fun r => topWt (ε r) := by
    funext r a
    simp only [bWt, topWt]
    have h : (Finset.univ.filter fun j : Fin n =>
          a ∈ ((initSeg (bdeg_le ε (r, j)) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n))) = (ε r).filter fun j => a < j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_initSeg, bdeg]
      by_cases hj : j ∈ ε r <;> simp [hj]
    rw [h]
  exact hmain

theorem symm_eq_of_mul_self {π : Equiv.Perm (Fin n)} (hπ : π * π = 1) : π.symm = π := by
  have h : π⁻¹ = π := mul_eq_one_iff_inv_eq.mp hπ
  apply Equiv.ext
  intro a
  have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) h) a
  simpa using this

omit [Fintype τ] [DecidableEq τ] in
theorem permWt_permWt {π : Equiv.Perm (Fin n)} (hπ : π * π = 1) (μ : τ → Fin n → ℤ) :
    permWt π (permWt π μ) = μ := by
  have hsymm : π.symm = π := symm_eq_of_mul_self hπ
  have hmul : ∀ a, π (π a) = a := by
    intro a
    have h := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hπ) a
    simpa using h
  funext r a
  simp [permWt, hsymm, hmul]

theorem exists_of_bMat_permMatrix_mulVec_ne_zero [CharP k 2] (ε : τ → Finset (Fin n))
    (ρ : τ → Equiv.Perm (Fin n)) {w : BIdx ε → k} {s : BIdx ε}
    (h : (bMat ε (fun r => (ρ r).permMatrix k) *ᵥ w) s ≠ 0) :
    ∃ t, w t ≠ 0 ∧ bWt ε s = fun r a => bWt ε t r ((ρ r) a) := by
  classical
  have hMT : (bMat ε (fun r => (ρ r).permMatrix k))ᵀ =
      bMat ε (fun r => ((ρ r)⁻¹).permMatrix k) := by
    rw [← bMat_transpose]
    congr 1
    funext r
    exact Matrix.transpose_permMatrix (σ := ρ r)
  have hentry : ∀ t, bMat ε (fun r => (ρ r).permMatrix k) s t ≠ 0 →
      s = bPerm ε (fun r => (ρ r)⁻¹) t := by
    intro t ht
    have ht' : bMat ε (fun r => ((ρ r)⁻¹).permMatrix k) t s ≠ 0 := by
      rw [← hMT, Matrix.transpose_apply]
      exact ht
    have hcol := bMat_permMatrix_mulVec_single (k := k) ε ρ s
    have hst : bMat ε (fun r => ((ρ r)⁻¹).permMatrix k) t s =
        (bMat ε (fun r => ((ρ r)⁻¹).permMatrix k) *ᵥ Pi.single s (1 : k)) t := by
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hst, hcol] at ht'
    have hts : t = bPerm ε ρ s := by
      by_contra hne
      exact ht' (by simp [Ne.symm hne])
    have h1 : bPerm ε (fun r => (ρ r)⁻¹) (bPerm ε ρ s) = s := by
      rw [← bPerm_mul, show (fun r => (ρ r)⁻¹ * ρ r) = (fun _ => 1) from by funext r; simp,
        bPerm_one]
    rw [hts]
    exact h1.symm
  have hsum : (bMat ε (fun r => (ρ r).permMatrix k) *ᵥ w) s =
      ∑ t, bMat ε (fun r => (ρ r).permMatrix k) s t * w t :=
    Matrix.mulVec_apply_eq_sum _ _ _
  rw [hsum] at h
  have hex : ∃ t, bMat ε (fun r => (ρ r).permMatrix k) s t * w t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (Finset.sum_eq_zero fun t _ => hc t)
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, right_ne_zero_of_mul ht, ?_⟩
  rw [hentry t (left_ne_zero_of_mul ht), bWt_bPerm]
  rfl

theorem bWt_of_bMat_permMatrix_mulVec_ne_zero [CharP k 2] (ε : τ → Finset (Fin n))
    {π : Equiv.Perm (Fin n)} (hπ : π * π = 1) {w : BIdx ε → k} {ν : τ → Fin n → ℤ}
    (hw : ∀ s, w s ≠ 0 → bWt ε s = ν) {s : BIdx ε}
    (h : (bMat ε (fun _ => π.permMatrix k) *ᵥ w) s ≠ 0) : bWt ε s = permWt π ν := by
  have hsymm : π.symm = π := symm_eq_of_mul_self hπ
  obtain ⟨t, ht, hwt⟩ := exists_of_bMat_permMatrix_mulVec_ne_zero ε (fun _ => π) h
  rw [hwt, hw t ht]
  funext r a
  simp [permWt, hsymm]

theorem mem_bWeights_of_rearr [CharP k 2] (ε : τ → Finset (Fin n)) {x : BIdx ε → k}
    (hxC : x ∈ bCyc (k := k) ε) (hxR : x ∉ bRad ε) {ν : τ → Fin n → ℤ}
    (hν : ∀ s, x s ≠ 0 → bWt ε s = ν) {μ : τ → Fin n → ℤ}
    (hμ : ∀ r, μ r ∈ rearr (ν r)) : μ ∈ bWeights k ε := by
  classical
  choose σ hσ using fun r => mem_rearr.mp (hμ r)
  let y : BIdx ε → k := bMat ε (fun r => (σ r).permMatrix k) *ᵥ x
  have hyC : y ∈ bCyc (k := k) ε := by
    have h := bMat_mulVec_mem_bCyc (k := k) ε (fun r => permSL (k := k) (σ r)) hxC
    simpa [y, permSL] using h
  have hyR : y ∉ bRad ε := by
    have h := bMat_mulVec_notMem_bRad (k := k) ε (fun r => permSL (k := k) (σ r)) hxR
    simpa [y, permSL] using h
  have hy : ∀ s, y s ≠ 0 → bWt ε s = μ := by
    intro s hs
    obtain ⟨t, ht, hwt⟩ := exists_of_bMat_permMatrix_mulVec_ne_zero ε σ hs
    rw [hwt, hν t ht]
    funext r a
    have hσr : μ r = ν r ∘ σ r := hσ r
    rw [hσr]
    rfl
  exact ⟨y, hyC, hyR, hy⟩

theorem mem_bWeights_of_mem_piFinset [CharP k 2] (ε : τ → Finset (Fin n))
    {μ : τ → Fin n → ℤ}
    (hμ : μ ∈ Fintype.piFinset fun r => rearr (topWt (ε r))) : μ ∈ bWeights k ε := by
  have hν : ∀ s, bvec (k := k) ε s ≠ 0 → bWt ε s = fun r => topWt (ε r) := by
    intro s hs
    have hst : s = btop ε := by
      by_contra hne
      exact hs (by simp [bvec, hne])
    rw [hst, bWt_btop]
  exact mem_bWeights_of_rearr ε (bvec_mem_bCyc ε) (bvec_notMem_bRad ε) hν
    (fun r => Fintype.mem_piFinset.mp hμ r)

noncomputable def homCompCyc (ε : τ → Finset (Fin n)) (e : τ → Fin n → ℤ) :
    bCyc (k := k) ε →ₗ[k] bCyc (k := k) ε where
  toFun w := ⟨homComp (bWt ε) e (w : BIdx ε → k), homComp_bWt_mem_bCyc ε w.2 e⟩
  map_add' x y :=
    Subtype.ext (map_add (homCompLin (bWt ε) e) (x : BIdx ε → k) (y : BIdx ε → k))
  map_smul' a x :=
    Subtype.ext (map_smul (homCompLin (bWt ε) e) a (x : BIdx ε → k))

noncomputable def homCompModel (ε : τ → Finset (Fin n)) (e : τ → Fin n → ℤ) :
    BModel k ε →ₗ[k] BModel k ε :=
  Submodule.mapQ ((bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)
    ((bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)
    (homCompCyc (k := k) ε e)
    (fun w hw => homComp_bWt_mem_bRad ε (by simpa using hw) e)

theorem homCompModel_mk (ε : τ → Finset (Fin n)) (e : τ → Fin n → ℤ) (w : bCyc (k := k) ε) :
    homCompModel (k := k) ε e (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (homCompCyc (k := k) ε e w) :=
  Submodule.mapQ_apply _ _ _ _

theorem homCompCyc_eq_self (ε : τ → Finset (Fin n)) (e : τ → Fin n → ℤ) {w : bCyc (k := k) ε}
    (hw : ∀ s, (w : BIdx ε → k) s ≠ 0 → bWt ε s = e) : homCompCyc (k := k) ε e w = w :=
  Subtype.ext (homComp_eq_self_of_forall_apply_ne_zero hw)

theorem homCompCyc_eq_zero (ε : τ → Finset (Fin n)) (e : τ → Fin n → ℤ) {w : bCyc (k := k) ε}
    (hw : ∀ s, (w : BIdx ε → k) s ≠ 0 → bWt ε s ≠ e) : homCompCyc (k := k) ε e w = 0 :=
  Subtype.ext (homComp_eq_zero_of_forall_apply_ne_zero_ne hw)

open _root_.Classical in
theorem card_moved_le_two_mul_finrank [CharP k 2] (ε : τ → Finset (Fin n))
    (π : Equiv.Perm (Fin n)) (hπ : π * π = 1) (S : Finset (τ → Fin n → ℤ))
    (hS : ∀ μ ∈ S, μ ∈ bWeights k ε) (hSπ : ∀ μ ∈ S, permWt π μ ∈ S) :
    (S.filter fun μ => permWt π μ ≠ μ).card ≤
      2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL π) -
        (1 : BModel k ε →ₗ[k] BModel k ε))) := by
  classical
  have hchoice : ∀ μ : ↥(S : Set (τ → Fin n → ℤ)), ∃ w : BIdx ε → k,
      w ∈ bCyc (k := k) ε ∧ w ∉ bRad ε ∧ ∀ s, w s ≠ 0 → bWt ε s = μ.1 := by
    rintro ⟨μ, hμ⟩
    exact hS μ hμ
  choose x hxC hxR hxwt using hchoice
  let σ : ↥(S : Set (τ → Fin n → ℤ)) → ↥(S : Set (τ → Fin n → ℤ)) :=
    fun μ => ⟨permWt π μ.1, hSπ μ.1 μ.2⟩
  have hσ : ∀ μ, σ (σ μ) = μ := by
    intro μ
    exact Subtype.ext (permWt_permWt hπ μ.1)
  obtain ⟨M, hMm, hMdisj, hMcard⟩ := exists_half_moved σ hσ
  have hcard_moved : (S.filter fun μ => permWt π μ ≠ μ).card =
      (Finset.univ.filter fun i : ↥(S : Set (τ → Fin n → ℤ)) => σ i ≠ i).card := by
    rw [Finset.univ_eq_attach]
    refine Finset.card_bij
      (fun (μ : τ → Fin n → ℤ) (_ : μ ∈ S.filter fun μ => permWt π μ ≠ μ) =>
        (⟨μ, (Finset.mem_filter.mp ‹_›).1⟩ : ↥(S : Set (τ → Fin n → ℤ)))) ?_ ?_ ?_
    · intro μ hμ
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_attach _ _, ?_⟩
      intro hc
      exact (Finset.mem_filter.mp hμ).2 (congrArg Subtype.val hc)
    · intro μ₁ _ μ₂ _ h
      exact congrArg Subtype.val h
    · intro i hi
      rw [Finset.mem_filter] at hi
      refine ⟨i.1, ?_, Subtype.ext rfl⟩
      rw [Finset.mem_filter]
      exact ⟨i.2, fun hc => hi.2 (Subtype.ext hc)⟩
  set W : Matrix (BIdx ε) (BIdx ε) k := bMat ε (fun _ => π.permMatrix k) with hW
  have hWmem : ∀ μ : ↥(S : Set (τ → Fin n → ℤ)), W *ᵥ x μ ∈ bCyc (k := k) ε := by
    intro μ
    have h := bMat_mulVec_mem_bCyc (k := k) ε (fun _ => permSL (k := k) π) (hxC μ)
    simpa [W, permSL] using h
  have hpureW : ∀ (μ : ↥(S : Set (τ → Fin n → ℤ))) (s : BIdx ε),
      (W *ᵥ x μ) s ≠ 0 → bWt ε s = permWt π μ.1 := by
    intro μ s hs
    exact bWt_of_bMat_permMatrix_mulVec_ne_zero ε hπ (hxwt μ) hs
  set T : BModel k ε →ₗ[k] BModel k ε :=
    bRep ε (fun _ => permSL π) - (1 : BModel k ε →ₗ[k] BModel k ε) with hT
  have hT_apply : ∀ μ : ↥(S : Set (τ → Fin n → ℤ)),
      T (Submodule.Quotient.mk ⟨x μ, hxC μ⟩) =
        Submodule.Quotient.mk ⟨W *ᵥ x μ, hWmem μ⟩ - Submodule.Quotient.mk ⟨x μ, hxC μ⟩ := by
    intro μ
    have h1 : T (Submodule.Quotient.mk ⟨x μ, hxC μ⟩) =
        (bRep (k := k) ε (fun _ => permSL (k := k) π))
            (Submodule.Quotient.mk ⟨x μ, hxC μ⟩) -
          Submodule.Quotient.mk ⟨x μ, hxC μ⟩ := by
      rw [hT, LinearMap.sub_apply]
      rfl
    rw [h1, bRep_mk]
    rfl
  have hindep : LinearIndependent k (fun μ : ↥M =>
      T (Submodule.Quotient.mk ⟨x μ.1, hxC μ.1⟩)) := by
    rw [linearIndependent_iff']
    intro s c hsum μ₀ hμ₀
    let e : τ → Fin n → ℤ := μ₀.1.1
    have hsum' : (∑ i ∈ s, c i •
        homCompModel (k := k) ε e (T (Submodule.Quotient.mk ⟨x i.1, hxC i.1⟩))) = 0 := by
      have h1 := congrArg (homCompModel (k := k) ε e) hsum
      rw [map_sum, map_zero] at h1
      simpa only [map_smul] using h1
    have hx_self : homCompCyc (k := k) ε e ⟨x μ₀.1, hxC μ₀.1⟩ = ⟨x μ₀.1, hxC μ₀.1⟩ :=
      homCompCyc_eq_self ε e (hxwt μ₀.1)
    have hx_zero : ∀ i : ↥M, i ≠ μ₀ →
        homCompCyc (k := k) ε e ⟨x i.1, hxC i.1⟩ = 0 := by
      intro i hi
      refine homCompCyc_eq_zero ε e (fun s hs => ?_)
      rw [hxwt i.1 s hs]
      intro hc
      exact hi (Subtype.ext (Subtype.ext hc))
    have hW_zero : ∀ i : ↥M,
        homCompCyc (k := k) ε e ⟨W *ᵥ x i.1, hWmem i.1⟩ = 0 := by
      intro i
      refine homCompCyc_eq_zero ε e (fun s hs => ?_)
      rw [hpureW i.1 s hs]
      intro hc
      have hσ : σ i.1 = μ₀.1 := Subtype.ext hc
      exact hMdisj i.1 i.2 (hσ ▸ μ₀.2)
    have hcomp_eq : ∀ i : ↥M,
        homCompModel (k := k) ε e (T (Submodule.Quotient.mk ⟨x i.1, hxC i.1⟩)) =
          Submodule.Quotient.mk (homCompCyc (k := k) ε e ⟨W *ᵥ x i.1, hWmem i.1⟩) -
            Submodule.Quotient.mk (homCompCyc (k := k) ε e ⟨x i.1, hxC i.1⟩) := by
      intro i
      rw [hT_apply i.1, map_sub, homCompModel_mk, homCompModel_mk]
    have hself : homCompModel (k := k) ε e
        (T (Submodule.Quotient.mk ⟨x μ₀.1, hxC μ₀.1⟩)) =
        - Submodule.Quotient.mk ⟨x μ₀.1, hxC μ₀.1⟩ := by
      rw [hcomp_eq μ₀, hW_zero μ₀, hx_self]
      simp
    have hzero : ∀ i : ↥M, i ≠ μ₀ →
        homCompModel (k := k) ε e (T (Submodule.Quotient.mk ⟨x i.1, hxC i.1⟩)) = 0 := by
      intro i hi
      rw [hcomp_eq i, hW_zero i, hx_zero i hi]
      simp
    have hsingle : (∑ i ∈ s, c i •
        homCompModel (k := k) ε e (T (Submodule.Quotient.mk ⟨x i.1, hxC i.1⟩))) =
        c μ₀ • homCompModel (k := k) ε e
          (T (Submodule.Quotient.mk ⟨x μ₀.1, hxC μ₀.1⟩)) := by
      refine Finset.sum_eq_single μ₀ ?_ ?_
      · intro i _ hi
        rw [hzero i hi, smul_zero]
      · intro hnot
        exact absurd hμ₀ hnot
    rw [hsingle, hself] at hsum'
    have h2 : c μ₀ • (Submodule.Quotient.mk ⟨x μ₀.1, hxC μ₀.1⟩ : BModel k ε) = 0 := by
      simpa using hsum'
    rcases smul_eq_zero.mp h2 with hc | hc
    · exact hc
    · exact absurd ((mk_eq_zero_iff ε ⟨x μ₀.1, hxC μ₀.1⟩).mp hc) (hxR μ₀.1)
  have hMle : M.card ≤ finrank k (LinearMap.range T) := by
    have hli : LinearIndependent k (fun μ : ↥M =>
        (⟨T (Submodule.Quotient.mk ⟨x μ.1, hxC μ.1⟩),
          LinearMap.mem_range_self T (Submodule.Quotient.mk ⟨x μ.1, hxC μ.1⟩)⟩ :
            ↥(LinearMap.range T))) :=
      LinearIndependent.of_comp (LinearMap.range T).subtype hindep
    simpa using hli.fintype_card_le_finrank
  calc (S.filter fun μ => permWt π μ ≠ μ).card
      = (Finset.univ.filter fun i : ↥(S : Set (τ → Fin n → ℤ)) => σ i ≠ i).card := hcard_moved
    _ ≤ 2 * M.card := hMcard
    _ ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL π) -
          (1 : BModel k ε →ₗ[k] BModel k ε))) := by
        rw [← hT]
        exact Nat.mul_le_mul_left 2 hMle

theorem comp_swap_eq_iff {α : Type*} {a b : Fin n} (μ : Fin n → α) :
    μ ∘ Equiv.swap a b = μ ↔ μ a = μ b := by
  constructor
  · intro h
    have := congrFun h a
    rw [Function.comp_apply, Equiv.swap_apply_left] at this
    exact this.symm
  · intro h
    funext x
    rw [Function.comp_apply, Equiv.swap_apply_def]
    by_cases hx : x = a
    · rw [if_pos hx, hx]
      exact h.symm
    · by_cases hx' : x = b
      · rw [if_neg hx, if_pos hx', hx']
        exact h
      · rw [if_neg hx, if_neg hx']

theorem card_moved_top_le [CharP k 2] (ε : τ → Finset (Fin n)) (hn : 2 ≤ n)
    (π : Equiv.Perm (Fin n)) (hπ : π * π = 1)
    (h01 : π ⟨0, by omega⟩ = ⟨1, by omega⟩) :
    ((Fintype.piFinset fun r => rearr (topWt (ε r))).filter
        fun μ => ∃ r, μ r ∘ Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ μ r).card ≤
      2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
  classical
  set S : Finset (τ → Fin n → ℤ) := Fintype.piFinset fun r => rearr (topWt (ε r)) with hSdef
  have hS : ∀ μ ∈ S, μ ∈ bWeights k ε := fun μ hμ => mem_bWeights_of_mem_piFinset ε hμ
  have hSπ : ∀ μ ∈ S, permWt π μ ∈ S := by
    intro μ hμ
    rw [hSdef, Fintype.mem_piFinset] at hμ ⊢
    intro r
    exact comp_mem_rearr (hμ r) π.symm
  have hsub : (S.filter fun μ =>
      ∃ r, μ r ∘ Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ μ r) ⊆
      (S.filter fun μ => permWt π μ ≠ μ) := by
    intro μ hμ
    rw [Finset.mem_filter] at hμ ⊢
    refine ⟨hμ.1, ?_⟩
    intro hfix
    obtain ⟨r, hr⟩ := hμ.2
    apply hr
    have h01ne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [comp_swap_eq_iff (μ r)]
    have hsymm : π.symm = π := symm_eq_of_mul_self hπ
    have hπμ : ∀ a, μ r (π a) = μ r a := by
      intro a
      have := congrFun (congrFun hfix r) a
      simpa [permWt, hsymm] using this
    have h1 : μ r ⟨1, by omega⟩ = μ r ⟨0, by omega⟩ := by
      rw [← h01]
      exact hπμ ⟨0, by omega⟩
    exact h1.symm
  exact Finset.card_le_card hsub |>.trans
    (card_moved_le_two_mul_finrank (k := k) ε π hπ S hS hSπ)

theorem image_topWt_one_two (hn : 3 ≤ n) :
    (Finset.univ.image (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)))) =
      ({0, 1, 2} : Finset ℤ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [topWt_pair_eq (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ a (by simp)]
    split_ifs <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨2, by omega⟩, (topWt_pair_eq_zero (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩
        ⟨2, by omega⟩ (by simp)).mpr (by simp)⟩
    · exact ⟨⟨1, by omega⟩, (topWt_pair_eq_one (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩
        ⟨1, by omega⟩ (by simp)).mpr (by simp)⟩
    · exact ⟨⟨0, by omega⟩, (topWt_pair_eq_two (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩
        ⟨0, by omega⟩ (by simp)).mpr (by simp)⟩

theorem card_fibre_topWt_one_two_zero (hn : 3 ≤ n) :
    (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 0).card = n - 2 := by
  have hf : (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 0) =
      Finset.Ici (⟨2, by omega⟩ : Fin n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    exact topWt_pair_eq_zero (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ a (by simp)
  rw [hf, Fin.card_Ici]

theorem card_fibre_topWt_one_two_one (hn : 3 ≤ n) :
    (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 1).card = 1 := by
  have hf : (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 1) =
      Finset.Ico (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    exact topWt_pair_eq_one (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ a (by simp)
  rw [hf, Fin.card_Ico]
  simp

theorem card_fibre_topWt_one_two_two (hn : 3 ≤ n) :
    (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 2).card = 1 := by
  have hf : (Finset.univ.filter fun a : Fin n =>
      topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) a = 2) =
      Finset.Iio (⟨1, by omega⟩ : Fin n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact topWt_pair_eq_two (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ a (by simp)
  rw [hf, Fin.card_Iio]

theorem factorial_eq_mul_pred_mul (hn : 3 ≤ n) :
    n.factorial = n * (n - 1) * (n - 2).factorial := by
  have h1 : n.factorial = n * (n - 1).factorial := by
    have hkey : n - 1 + 1 = n := by omega
    have := Nat.factorial_succ (n - 1)
    rwa [hkey] at this
  have h2 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    have hkey : n - 2 + 1 = n - 1 := by omega
    have := Nat.factorial_succ (n - 2)
    rwa [hkey] at this
  rw [h1, h2, mul_assoc]

theorem card_rearr_topWt_one_two (hn : 3 ≤ n) :
    (rearr (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)))).card = n * (n - 1) := by
  have hmain := card_rearr_mul_prod_factorial
    (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)))
  rw [image_topWt_one_two hn] at hmain
  rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
    Finset.prod_singleton] at hmain
  have h0 := card_fibre_topWt_one_two_zero (n := n) (by omega)
  have h1 := card_fibre_topWt_one_two_one (n := n) hn
  have h2 := card_fibre_topWt_one_two_two (n := n) hn
  rw [h0, h1, h2] at hmain
  simp only [Nat.factorial_one, mul_one] at hmain
  conv at hmain => rhs; rw [factorial_eq_mul_pred_mul (n := n) (by omega)]
  exact Nat.mul_right_cancel (Nat.factorial_pos _) hmain

theorem card_moved_rearr_topWt_one_two (hn : 4 ≤ n) :
    ((rearr (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)))).filter fun μ =>
      μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card = 4 * n - 6 := by
  have hmain := card_moved_rearr_mul
    (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n))) (by omega)
  rw [image_topWt_one_two (by omega)] at hmain
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_singleton] at hmain
  have h0 := card_fibre_topWt_one_two_zero (n := n) (by omega)
  have h1 := card_fibre_topWt_one_two_one (n := n) (by omega)
  have h2 := card_fibre_topWt_one_two_two (n := n) (by omega)
  simp only [h0, h1, h2] at hmain
  rw [card_rearr_topWt_one_two (by omega)] at hmain
  have hsq : n ^ 2 - ((n - 2) ^ 2 + (1 ^ 2 + 1 ^ 2)) = 4 * n - 6 := by
    have hsq' : n ^ 2 - ((n - 2) ^ 2 + 2) = 4 * n - 6 := by
      have h2' : 2 ≤ n := by omega
      have hle : (n - 2) ^ 2 + 2 ≤ n ^ 2 := by nlinarith [Nat.sub_add_cancel h2']
      have h4 : 6 ≤ 4 * n := by omega
      zify [hle, h4, h2']
      ring
    simpa using hsq'
  rw [hsq] at hmain
  rw [mul_comm (n * (n - 1))] at hmain
  exact Nat.mul_right_cancel (Nat.mul_pos (by omega) (by omega)) hmain

theorem card_moved_rearr_topWt_three (hn : 5 ≤ n) :
    ((rearr (topWt ({⟨3, by omega⟩} : Finset (Fin n)))).filter fun μ =>
      μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card = (n - 2) * (n - 3) := by
  rw [card_moved_rearr_topWt_singleton (by omega) (⟨3, by omega⟩ : Fin n) (by norm_num)]
  have hj : ((⟨3, by omega⟩ : Fin n) : ℕ) - 1 = 2 := by simp
  rw [hj, two_mul_choose_two]
  have hk : n - 2 - 1 = n - 3 := by omega
  rw [hk]

theorem image_topWt_three (hn : 4 ≤ n) :
    (Finset.univ.image (topWt ({⟨3, by omega⟩} : Finset (Fin n)))) = ({0, 1} : Finset ℤ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [topWt_singleton]
    split_ifs <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨3, by omega⟩, by rw [topWt_singleton]; simp⟩
    · exact ⟨⟨0, by omega⟩, by rw [topWt_singleton]; simp⟩

theorem image_topWt_last (hn : 5 ≤ n) :
    (Finset.univ.image (fun a : Fin n => topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1)) =
      ({1, 2} : Finset ℤ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [topWt_singleton]
    split_ifs <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨n - 1, by omega⟩, by rw [topWt_singleton]; simp; omega⟩
    · exact ⟨⟨0, by omega⟩, by rw [topWt_singleton]; simp; omega⟩

theorem card_moved_rearr_topWt_last (hn : 5 ≤ n) :
    ((rearr (fun a : Fin n => topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1)).filter fun μ =>
      μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card = (n - 2) * (n - 3) := by
  rw [card_moved_rearr_comp_injective (f := topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)))
    (e := fun x : ℤ => x + 1) (fun x y h => by linarith) (by omega)]
  rw [card_moved_rearr_topWt_singleton (by omega) (⟨n - 3, by omega⟩ : Fin n)
    (by simp only; omega)]
  have hj : ((⟨n - 3, by omega⟩ : Fin n) : ℕ) - 1 = n - 4 := by
    simp
    omega
  rw [hj]
  have hchoose : (n - 2).choose (n - 4) = (n - 2).choose 2 := by
    rw [show n - 4 = (n - 2) - 2 by omega]
    exact Nat.choose_symm (by omega)
  rw [hchoose, two_mul_choose_two]
  have hk : n - 2 - 1 = n - 3 := by omega
  rw [hk]

theorem rearr_zero_eq : rearr (0 : Fin n → ℤ) = {0} := by
  ext μ
  simp only [Finset.mem_singleton, mem_rearr]
  constructor
  · rintro ⟨σ, rfl⟩
    ext a
    rfl
  · rintro rfl
    exact ⟨1, by ext a; rfl⟩

theorem filter_zero_orbit_eq (π : Equiv.Perm (Fin n)) :
    (({0} : Finset (Fin n → ℤ)).filter fun ν => ν ∘ π = ν) = {0} := by
  ext ν
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    subst h
    exact ⟨rfl, by funext a; rfl⟩

theorem card_filter_piFinset_moved_of_singleton {O : τ → Finset (Fin n → ℤ)} {r₀ : τ}
    (hO : ∀ r, r ≠ r₀ → O r = {0}) (π : Equiv.Perm (Fin n)) :
    ((Fintype.piFinset O).filter fun μ => ∃ r, μ r ∘ π ≠ μ r).card =
      ((O r₀).filter fun ν => ν ∘ π ≠ ν).card := by
  classical
  have hprod : ∏ r, (O r).card = (O r₀).card :=
    Finset.prod_eq_single r₀ (fun r _ hr => by rw [hO r hr]; simp)
      (fun h => absurd (Finset.mem_univ r₀) h)
  have hfixed : ∏ r, ((O r).filter fun ν => ν ∘ π = ν).card =
      ((O r₀).filter fun ν => ν ∘ π = ν).card :=
    Finset.prod_eq_single r₀ (fun r _ hr => by rw [hO r hr, filter_zero_orbit_eq]; simp)
      (fun h => absurd (Finset.mem_univ r₀) h)
  have hmain := card_piFinset_moved O π
  rw [hprod, hfixed] at hmain
  have hsplit := Finset.card_filter_add_card_filter_not (s := O r₀)
    (p := fun ν => ν ∘ π ≠ ν)
  have hfixeq : (O r₀).filter (fun ν => ¬ν ∘ π ≠ ν) = (O r₀).filter fun ν => ν ∘ π = ν := by
    apply Finset.filter_congr
    intro ν _
    exact not_not
  rw [hfixeq] at hsplit
  omega

theorem topWt_empty : topWt (∅ : Finset (Fin n)) = 0 := by
  funext a
  simp [topWt]

theorem exists_extra_one_two [CharP k 2] (hn : 4 ≤ n) (ε : τ → Finset (Fin n)) {r₀ : τ}
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨2, by omega⟩}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    ∃ (x : BIdx ε → k) (ν : τ → Fin n → ℤ), x ∈ bCyc (k := k) ε ∧ x ∉ bRad ε ∧
      (∀ s, x s ≠ 0 → bWt ε s = ν) ∧
      (∀ r, r ≠ r₀ → ν r = 0) ∧ ν r₀ = topWt ({⟨3, by omega⟩} : Finset (Fin n)) := by
  classical
  have h1 : (⟨1, by omega⟩ : Fin n) ∈ ε r₀ := by rw [hε]; simp
  have h2 : (⟨2, by omega⟩ : Fin n) ∈ ε r₀ := by rw [hε]; simp
  refine ⟨bDer ε (r₀, ⟨2, by omega⟩, ⟨1, by omega⟩) *ᵥ
      (bDer ε (r₀, ⟨1, by omega⟩, ⟨0, by omega⟩) *ᵥ bvec ε),
    fun r a => if r = r₀ then topWt ({⟨3, by omega⟩} : Finset (Fin n)) a else 0,
    bDer_bDer_bvec_mem_bCyc ε r₀ (by omega) h1 h2,
    bDer_bDer_bvec_notMem_bRad ε r₀ (by omega) h1 h2, ?_, ?_, ?_⟩
  · intro s hs
    rw [bWt_of_bDer_bDer_bvec_ne_zero ε r₀ (by omega) h1 h2 hs, bWt_btop]
    funext r a
    change topWt (ε r) a + (Pi.single r₀ (Pi.single (⟨2, by omega⟩ : Fin n) (1 : ℤ) -
      Pi.single (⟨0, by omega⟩ : Fin n) 1) : τ → Fin n → ℤ) r a =
      if r = r₀ then topWt ({⟨3, by omega⟩} : Finset (Fin n)) a else 0
    by_cases hr : r = r₀
    · subst hr
      rw [hε]
      simp only [Pi.single_eq_same]
      have hsingle : (Pi.single (⟨2, by omega⟩ : Fin n) (1 : ℤ) -
          Pi.single (⟨0, by omega⟩ : Fin n) 1 : Fin n → ℤ) a =
          (if a = (⟨2, by omega⟩ : Fin n) then 1 else 0) -
            (if a = (⟨0, by omega⟩ : Fin n) then 1 else 0) := by
        simp [Pi.single_apply]
      rw [hsingle, topWt_pair_eq (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ a (by simp),
        topWt_singleton]
      by_cases ha0 : a < (⟨1, by omega⟩ : Fin n)
      · have hza : a = ⟨0, by omega⟩ := by
          apply Fin.ext
          have : (a : ℕ) < 1 := ha0
          simp
          omega
        simp [hza]
      · by_cases ha1 : a < (⟨2, by omega⟩ : Fin n)
        · have hza : a = ⟨1, by omega⟩ := by
            apply Fin.ext
            have hlt : (a : ℕ) < 2 := ha1
            have hge : ¬ (a : ℕ) < 1 := ha0
            simp
            omega
          simp [hza]
        · by_cases ha2 : a < (⟨3, by omega⟩ : Fin n)
          · have hza : a = ⟨2, by omega⟩ := by
              apply Fin.ext
              have hlt : (a : ℕ) < 3 := ha2
              have hge : ¬ (a : ℕ) < 2 := ha1
              simp
              omega
            simp [hza]
          · have hne2 : a ≠ (⟨2, by omega⟩ : Fin n) := by
              intro h
              apply ha2
              rw [h]
              simp
            have hne0 : a ≠ (⟨0, by omega⟩ : Fin n) := by
              intro h
              apply ha0
              rw [h]
              simp
            simp [ha0, ha1, ha2, hne2, hne0]
    · rw [hε' r hr, topWt_empty, Pi.single_eq_of_ne hr, if_neg hr]
      simp
  · intro r hr
    funext a
    simp [hr]
  · funext a
    simp

theorem exists_extra_last_two [CharP k 2] (hn : 5 ≤ n) (ε : τ → Finset (Fin n)) {r₀ : τ}
    (hε : ε r₀ = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    ∃ (x : BIdx ε → k) (ν : τ → Fin n → ℤ), x ∈ bCyc (k := k) ε ∧ x ∉ bRad ε ∧
      (∀ s, x s ≠ 0 → bWt ε s = ν) ∧
      (∀ r, r ≠ r₀ → ν r = 0) ∧
      ν r₀ = (fun a : Fin n => topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1) := by
  classical
  have h1 : (⟨n - 2, by omega⟩ : Fin n) ∈ ε r₀ := by rw [hε]; simp
  have h2 : (⟨n - 1, by omega⟩ : Fin n) ∈ ε r₀ := by rw [hε]; simp
  refine ⟨bDer ε (r₀, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) *ᵥ
      (bDer ε (r₀, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) *ᵥ bvec ε),
    fun r a => if r = r₀ then topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1 else 0,
    bDer_bDer_bvec_mem_bCyc_last ε r₀ (by omega) h1 h2,
    bDer_bDer_bvec_notMem_bRad_last ε r₀ (by omega) h1 h2, ?_, ?_, ?_⟩
  · intro s hs
    rw [bWt_of_bDer_bDer_bvec_ne_zero_last ε r₀ (by omega) h1 h2 hs, bWt_btop]
    funext r a
    change topWt (ε r) a + (Pi.single r₀ (Pi.single (⟨n - 1, by omega⟩ : Fin n) (1 : ℤ) -
      Pi.single (⟨n - 3, by omega⟩ : Fin n) 1) : τ → Fin n → ℤ) r a =
      if r = r₀ then topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1 else 0
    by_cases hr : r = r₀
    · subst hr
      rw [hε]
      simp only [Pi.single_eq_same]
      have hsingle : (Pi.single (⟨n - 1, by omega⟩ : Fin n) (1 : ℤ) -
          Pi.single (⟨n - 3, by omega⟩ : Fin n) 1 : Fin n → ℤ) a =
          (if a = (⟨n - 1, by omega⟩ : Fin n) then 1 else 0) -
            (if a = (⟨n - 3, by omega⟩ : Fin n) then 1 else 0) := by
        simp [Pi.single_apply]
      have hlt : (⟨n - 2, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
        simp only [Fin.lt_def]
        omega
      rw [hsingle, topWt_pair_eq (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a hlt,
        topWt_singleton]
      simp only [Fin.lt_def, Fin.ext_iff]
      split_ifs <;> omega
    · rw [hε' r hr, topWt_empty, Pi.single_eq_of_ne hr, if_neg hr]
      simp
  · intro r hr
    funext a
    simp [hr]
  · funext a
    simp

theorem four_mul_sub_six_add (hn : 4 ≤ n) :
    4 * n - 6 + (n - 2) * (n - 3) = n * (n - 1) := by
  have h1 : 2 ≤ n := by omega
  have h2 : 3 ≤ n := by omega
  have h6 : 6 ≤ 4 * n := by omega
  have hle : (n - 2) * (n - 3) ≤ n * (n - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hcast : ((4 * n - 6 + (n - 2) * (n - 3) : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by
    zify [h1, h2, h6]
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  exact_mod_cast hcast

theorem mul_le_two_mul_finrank_of_one_two [CharP k 2] (hn : 5 ≤ n) (ε : τ → Finset (Fin n))
    (r₀ : τ) (hε : ε r₀ = {⟨1, by omega⟩, ⟨2, by omega⟩})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (π : Equiv.Perm (Fin n)) (hπ : π * π = 1)
    (h01 : π ⟨0, by omega⟩ = ⟨1, by omega⟩) :
    n * (n - 1) ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  obtain ⟨x, ν, hxC, hxR, hxwt, hν0, hνr⟩ :=
    exists_extra_one_two (n := n) (k := k) (by omega) ε hε hε'
  let O₁ : τ → Finset (Fin n → ℤ) := fun r => rearr (topWt (ε r))
  let O₂ : τ → Finset (Fin n → ℤ) := fun r => rearr (ν r)
  have hO₁ : ∀ r, r ≠ r₀ → O₁ r = rearr (0 : Fin n → ℤ) := by
    intro r hr
    simp [O₁, hε' r hr, topWt_empty]
  have hO₂ : ∀ r, r ≠ r₀ → O₂ r = rearr (0 : Fin n → ℤ) := by
    intro r hr
    simp [O₂, hν0 r hr]
  have hS₁ : ∀ μ ∈ Fintype.piFinset O₁, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_mem_piFinset ε hμ
  have hS₂ : ∀ μ ∈ Fintype.piFinset O₂, μ ∈ bWeights k ε := by
    intro μ hμ
    exact mem_bWeights_of_rearr ε hxC hxR (ν := ν) hxwt
      (fun r => Fintype.mem_piFinset.mp hμ r)
  have hS : ∀ μ ∈ Fintype.piFinset O₁ ∪ Fintype.piFinset O₂, μ ∈ bWeights k ε := by
    intro μ hμ
    rw [Finset.mem_union] at hμ
    rcases hμ with hμ | hμ
    · exact hS₁ μ hμ
    · exact hS₂ μ hμ
  have hSπ : ∀ μ ∈ Fintype.piFinset O₁ ∪ Fintype.piFinset O₂, permWt π μ ∈
      Fintype.piFinset O₁ ∪ Fintype.piFinset O₂ := by
    intro μ hμ
    rw [Finset.mem_union] at hμ ⊢
    rcases hμ with hμ | hμ
    · left
      rw [Fintype.mem_piFinset] at hμ ⊢
      intro r
      exact comp_mem_rearr (hμ r) π.symm
    · right
      rw [Fintype.mem_piFinset] at hμ ⊢
      intro r
      exact comp_mem_rearr (hμ r) π.symm
  have hdisj : Disjoint (Fintype.piFinset O₁) (Fintype.piFinset O₂) := by
    rw [Finset.disjoint_left]
    intro μ hμ1 hμ2
    rw [Fintype.mem_piFinset] at hμ1 hμ2
    have h1 : μ r₀ ∈ rearr (topWt ({i1, i2} : Finset (Fin n))) := by
      simpa [O₁, hε, i1, i2] using hμ1 r₀
    have h2 : μ r₀ ∈ rearr (topWt ({i3} : Finset (Fin n))) := by
      simpa [O₂, hνr, i3] using hμ2 r₀
    obtain ⟨σ, hσ⟩ := mem_rearr.mp h1
    obtain ⟨τ', hτ⟩ := mem_rearr.mp h2
    have himg1 : Finset.univ.image (μ r₀) = ({0, 1, 2} : Finset ℤ) := by
      rw [hσ, image_comp_perm]
      exact image_topWt_one_two (by omega)
    have himg2 : Finset.univ.image (μ r₀) = ({0, 1} : Finset ℤ) := by
      rw [hτ, image_comp_perm]
      exact image_topWt_three (by omega)
    rw [himg1] at himg2
    exact (by decide : ({0, 1, 2} : Finset ℤ) ≠ {0, 1}) himg2
  have hcount₁ : ((Fintype.piFinset O₁).filter fun μ =>
      ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card = 4 * n - 6 := by
    refine (card_filter_piFinset_moved_of_singleton (O := O₁) (r₀ := r₀)
      (fun r hr => by rw [hO₁ r hr, rearr_zero_eq]) (Equiv.swap i0 i1)).trans ?_
    have hOr : O₁ r₀ = rearr (topWt ({i1, i2} : Finset (Fin n))) := by
      simp [O₁, hε, i1, i2]
    rw [hOr]
    have hfilt : ((rearr (topWt ({i1, i2} : Finset (Fin n)))).filter
        fun ν => ν ∘ Equiv.swap i0 i1 ≠ ν) =
        ((rearr (topWt ({i1, i2} : Finset (Fin n)))).filter fun ν => ν i0 ≠ ν i1) := by
      apply Finset.filter_congr
      intro ν _
      exact not_congr (comp_swap_eq_iff ν)
    rw [hfilt]
    simpa [i0, i1, i2] using card_moved_rearr_topWt_one_two (n := n) (by omega)
  have hcount₂ : ((Fintype.piFinset O₂).filter fun μ =>
      ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card = (n - 2) * (n - 3) := by
    refine (card_filter_piFinset_moved_of_singleton (O := O₂) (r₀ := r₀)
      (fun r hr => by rw [hO₂ r hr, rearr_zero_eq]) (Equiv.swap i0 i1)).trans ?_
    have hOr : O₂ r₀ = rearr (topWt ({i3} : Finset (Fin n))) := by
      simp [O₂, hνr, i3]
    rw [hOr]
    have hfilt : ((rearr (topWt ({i3} : Finset (Fin n)))).filter
        fun ν => ν ∘ Equiv.swap i0 i1 ≠ ν) =
        ((rearr (topWt ({i3} : Finset (Fin n)))).filter fun ν => ν i0 ≠ ν i1) := by
      apply Finset.filter_congr
      intro ν _
      exact not_congr (comp_swap_eq_iff ν)
    rw [hfilt]
    simpa [i0, i1, i3] using card_moved_rearr_topWt_three (n := n) hn
  have hsum : 4 * n - 6 + (n - 2) * (n - 3) = n * (n - 1) :=
    four_mul_sub_six_add (by omega)
  have hcount : n * (n - 1) ≤
      ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card := by
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [hcount₁, hcount₂, ← hsum]
    · exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hmono : ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card ≤
      ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => permWt π μ ≠ μ).card := by
    apply Finset.card_le_card
    intro μ hμ
    rw [Finset.mem_filter] at hμ ⊢
    refine ⟨hμ.1, ?_⟩
    intro hfix
    obtain ⟨r, hr⟩ := hμ.2
    apply hr
    have hsymm : π.symm = π := symm_eq_of_mul_self hπ
    have hπμ : ∀ a, μ r (π a) = μ r a := by
      intro a
      have := congrFun (congrFun hfix r) a
      simpa [permWt, hsymm] using this
    rw [comp_swap_eq_iff (μ r)]
    have h01' : π i0 = i1 := h01
    have h1 : μ r i1 = μ r i0 := by
      rw [← h01']
      exact hπμ i0
    exact h1.symm
  exact hcount.trans (hmono.trans
    (card_moved_le_two_mul_finrank (k := k) ε π hπ _ hS hSπ))

theorem image_topWt_last_pair (hn : 5 ≤ n) :
    (Finset.univ.image (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)))) =
      ({0, 1, 2} : Finset ℤ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  have hlt : (⟨n - 2, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
    simp only [Fin.lt_def]
    omega
  constructor
  · rintro ⟨a, rfl⟩
    rw [topWt_pair_eq (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a hlt]
    split_ifs <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨n - 1, by omega⟩, (topWt_pair_eq_zero (⟨n - 2, by omega⟩ : Fin n)
        ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ hlt).mpr (by simp)⟩
    · exact ⟨⟨n - 2, by omega⟩, (topWt_pair_eq_one (⟨n - 2, by omega⟩ : Fin n)
        ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ hlt).mpr ⟨le_rfl, hlt⟩⟩
    · exact ⟨⟨0, by omega⟩, (topWt_pair_eq_two (⟨n - 2, by omega⟩ : Fin n)
        ⟨n - 1, by omega⟩ ⟨0, by omega⟩ hlt).mpr (by simp; omega)⟩

theorem card_fibre_topWt_last_pair (hn : 5 ≤ n) :
    (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 0).card = 1 ∧
      (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 1).card = 1 ∧
      (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 2).card = n - 2 := by
  have hlt : (⟨n - 2, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
    simp only [Fin.lt_def]
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hf : (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 0) =
        Finset.Ici (⟨n - 1, by omega⟩ : Fin n) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      exact topWt_pair_eq_zero (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a hlt
    rw [hf, Fin.card_Ici]
    simp only
    omega
  · have hf : (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 1) =
        Finset.Ico (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
      exact topWt_pair_eq_one (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a hlt
    rw [hf, Fin.card_Ico]
    simp only
    omega
  · have hf : (Finset.univ.filter fun a : Fin n =>
        topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) a = 2) =
        Finset.Iio (⟨n - 2, by omega⟩ : Fin n) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      exact topWt_pair_eq_two (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ a hlt
    rw [hf, Fin.card_Iio]

theorem card_rearr_topWt_last_pair (hn : 5 ≤ n) :
    (rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)))).card =
      n * (n - 1) := by
  have hmain := card_rearr_mul_prod_factorial
    (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)))
  rw [image_topWt_last_pair hn] at hmain
  rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
    Finset.prod_singleton] at hmain
  obtain ⟨h0, h1, h2⟩ := card_fibre_topWt_last_pair hn
  rw [h0, h1, h2] at hmain
  simp only [Nat.factorial_one, one_mul] at hmain
  conv at hmain => rhs; rw [factorial_eq_mul_pred_mul (n := n) (by omega)]
  exact Nat.mul_right_cancel (Nat.factorial_pos _) hmain

theorem card_moved_rearr_topWt_last_pair (hn : 5 ≤ n) :
    ((rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)))).filter fun μ =>
      μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card = 4 * n - 6 := by
  have hmain := card_moved_rearr_mul
    (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n))) (by omega)
  rw [image_topWt_last_pair hn] at hmain
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_singleton] at hmain
  obtain ⟨h0, h1, h2⟩ := card_fibre_topWt_last_pair hn
  simp only [h0, h1, h2] at hmain
  rw [card_rearr_topWt_last_pair hn] at hmain
  have hsq : n ^ 2 - (1 ^ 2 + (1 ^ 2 + (n - 2) ^ 2)) = 4 * n - 6 := by
    have hsq' : n ^ 2 - ((n - 2) ^ 2 + 2) = 4 * n - 6 := by
      have h2' : 2 ≤ n := by omega
      have hle : (n - 2) ^ 2 + 2 ≤ n ^ 2 := by nlinarith [Nat.sub_add_cancel h2']
      have h4 : 6 ≤ 4 * n := by omega
      zify [hle, h4, h2']
      ring
    have e1 : 1 ^ 2 + (1 ^ 2 + (n - 2) ^ 2) = (n - 2) ^ 2 + 2 := by ring
    rw [e1]
    exact hsq'
  rw [hsq] at hmain
  rw [mul_comm (n * (n - 1))] at hmain
  exact Nat.mul_right_cancel (Nat.mul_pos (by omega) (by omega)) hmain

theorem mul_le_two_mul_finrank_of_last_two [CharP k 2] (hn : 5 ≤ n) (ε : τ → Finset (Fin n))
    (r₀ : τ) (hε : ε r₀ = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (π : Equiv.Perm (Fin n)) (hπ : π * π = 1)
    (h01 : π ⟨0, by omega⟩ = ⟨1, by omega⟩) :
    n * (n - 1) ≤ 2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let ilast : Fin n := ⟨n - 3, by omega⟩
  obtain ⟨x, ν, hxC, hxR, hxwt, hν0, hνr⟩ :=
    exists_extra_last_two (n := n) (k := k) hn ε hε hε'
  let O₁ : τ → Finset (Fin n → ℤ) := fun r => rearr (topWt (ε r))
  let O₂ : τ → Finset (Fin n → ℤ) := fun r => rearr (ν r)
  have hO₁ : ∀ r, r ≠ r₀ → O₁ r = rearr (0 : Fin n → ℤ) := by
    intro r hr
    simp [O₁, hε' r hr, topWt_empty]
  have hO₂ : ∀ r, r ≠ r₀ → O₂ r = rearr (0 : Fin n → ℤ) := by
    intro r hr
    simp [O₂, hν0 r hr]
  have hS₁ : ∀ μ ∈ Fintype.piFinset O₁, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_mem_piFinset ε hμ
  have hS₂ : ∀ μ ∈ Fintype.piFinset O₂, μ ∈ bWeights k ε := by
    intro μ hμ
    exact mem_bWeights_of_rearr ε hxC hxR (ν := ν) hxwt
      (fun r => Fintype.mem_piFinset.mp hμ r)
  have hS : ∀ μ ∈ Fintype.piFinset O₁ ∪ Fintype.piFinset O₂, μ ∈ bWeights k ε := by
    intro μ hμ
    rw [Finset.mem_union] at hμ
    rcases hμ with hμ | hμ
    · exact hS₁ μ hμ
    · exact hS₂ μ hμ
  have hSπ : ∀ μ ∈ Fintype.piFinset O₁ ∪ Fintype.piFinset O₂, permWt π μ ∈
      Fintype.piFinset O₁ ∪ Fintype.piFinset O₂ := by
    intro μ hμ
    rw [Finset.mem_union] at hμ ⊢
    rcases hμ with hμ | hμ
    · left
      rw [Fintype.mem_piFinset] at hμ ⊢
      intro r
      exact comp_mem_rearr (hμ r) π.symm
    · right
      rw [Fintype.mem_piFinset] at hμ ⊢
      intro r
      exact comp_mem_rearr (hμ r) π.symm
  have hdisj : Disjoint (Fintype.piFinset O₁) (Fintype.piFinset O₂) := by
    rw [Finset.disjoint_left]
    intro μ hμ1 hμ2
    rw [Fintype.mem_piFinset] at hμ1 hμ2
    have h1 : μ r₀ ∈ rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} :
        Finset (Fin n))) := by
      simpa [O₁, hε] using hμ1 r₀
    have h2 : μ r₀ ∈ rearr (fun a : Fin n =>
        topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1) := by
      simpa [O₂, hνr] using hμ2 r₀
    obtain ⟨σ, hσ⟩ := mem_rearr.mp h1
    obtain ⟨τ', hτ⟩ := mem_rearr.mp h2
    have himg1 : Finset.univ.image (μ r₀) = ({0, 1, 2} : Finset ℤ) := by
      rw [hσ, image_comp_perm]
      exact image_topWt_last_pair hn
    have himg2 : Finset.univ.image (μ r₀) = ({1, 2} : Finset ℤ) := by
      rw [hτ, image_comp_perm]
      exact image_topWt_last hn
    rw [himg1] at himg2
    exact (by decide : ({0, 1, 2} : Finset ℤ) ≠ {1, 2}) himg2
  have hcount₁ : ((Fintype.piFinset O₁).filter fun μ =>
      ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card = 4 * n - 6 := by
    refine (card_filter_piFinset_moved_of_singleton (O := O₁) (r₀ := r₀)
      (fun r hr => by rw [hO₁ r hr, rearr_zero_eq]) (Equiv.swap i0 i1)).trans ?_
    have hOr : O₁ r₀ = rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} :
        Finset (Fin n))) := by
      simp [O₁, hε]
    rw [hOr]
    have hfilt : ((rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} :
        Finset (Fin n)))).filter fun ν => ν ∘ Equiv.swap i0 i1 ≠ ν) =
        ((rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} :
          Finset (Fin n)))).filter fun ν => ν i0 ≠ ν i1) := by
      apply Finset.filter_congr
      intro ν _
      exact not_congr (comp_swap_eq_iff ν)
    rw [hfilt]
    simpa [i0, i1] using card_moved_rearr_topWt_last_pair (n := n) hn
  have hcount₂ : ((Fintype.piFinset O₂).filter fun μ =>
      ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card = (n - 2) * (n - 3) := by
    refine (card_filter_piFinset_moved_of_singleton (O := O₂) (r₀ := r₀)
      (fun r hr => by rw [hO₂ r hr, rearr_zero_eq]) (Equiv.swap i0 i1)).trans ?_
    have hOr : O₂ r₀ = rearr (fun a : Fin n =>
        topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1) := by
      simp [O₂, hνr]
    rw [hOr]
    have hfilt : ((rearr (fun a : Fin n =>
        topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1)).filter
        fun ν => ν ∘ Equiv.swap i0 i1 ≠ ν) =
        ((rearr (fun a : Fin n =>
          topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1)).filter
          fun ν => ν i0 ≠ ν i1) := by
      apply Finset.filter_congr
      intro ν _
      exact not_congr (comp_swap_eq_iff ν)
    rw [hfilt]
    simpa [i0, i1] using card_moved_rearr_topWt_last (n := n) hn
  have hsum : 4 * n - 6 + (n - 2) * (n - 3) = n * (n - 1) :=
    four_mul_sub_six_add (by omega)
  have hcount : n * (n - 1) ≤
      ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card := by
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [hcount₁, hcount₂, ← hsum]
    · exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hmono : ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => ∃ r, μ r ∘ Equiv.swap i0 i1 ≠ μ r).card ≤
      ((Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).filter
        fun μ => permWt π μ ≠ μ).card := by
    apply Finset.card_le_card
    intro μ hμ
    rw [Finset.mem_filter] at hμ ⊢
    refine ⟨hμ.1, ?_⟩
    intro hfix
    obtain ⟨r, hr⟩ := hμ.2
    apply hr
    have hsymm : π.symm = π := symm_eq_of_mul_self hπ
    have hπμ : ∀ a, μ r (π a) = μ r a := by
      intro a
      have := congrFun (congrFun hfix r) a
      simpa [permWt, hsymm] using this
    rw [comp_swap_eq_iff (μ r)]
    have h01' : π i0 = i1 := h01
    have h1 : μ r i1 = μ r i0 := by
      rw [← h01']
      exact hπμ i0
    exact h1.symm
  exact hcount.trans (hmono.trans
    (card_moved_le_two_mul_finrank (k := k) ε π hπ _ hS hSπ))

end CFSG.LieType.SpecialLinear.ExteriorModel
