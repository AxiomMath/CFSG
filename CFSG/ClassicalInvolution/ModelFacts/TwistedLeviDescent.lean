module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Stability

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem exists_diagramMap_conj_pinnedX_unit {γ : Fin t.tag.rank → ℤ} (hγ : IsRoot t.tag γ) :
    ∃ μ : kˣ, ∀ c : k, diagramMap t k * pinnedX t.tag k γ c * (diagramMap t k)⁻¹ =
      pinnedX t.tag k (permLattice t.perm γ) (μ * c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := k) t hγ
  exact ⟨Units.mkOfMulEqOne ε ε hε, h⟩

theorem map_frobTwistGL_rootSpan_diagram (e : ℕ) {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α) :
    (rootSpan t.tag k S).map (frobTwistGL t.tag k p e (diagramMap t k)) =
      rootSpan t.tag k (permLattice t.perm '' S) :=
  map_frobTwistGL_rootSpan_of_conj p e (θ := permLattice t.perm)
    (fun _ hγ => exists_diagramMap_conj_pinnedX_unit t hγ) hS

theorem frobTwistGL_mem_torus_sup_rootSpan_diagram [IsAlgClosed k] (e : ℕ)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α)
    (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S) {g : ModGL t.tag k}
    (hg : g ∈ torusGroup t.tag k ⊔ rootSpan t.tag k S) :
    frobTwistGL t.tag k p e (diagramMap t k) g ∈ torusGroup t.tag k ⊔ rootSpan t.tag k S := by
  have hle : (torusGroup t.tag k ⊔ rootSpan t.tag k S).map
      (frobTwistGL t.tag k p e (diagramMap t k)) ≤ torusGroup t.tag k ⊔ rootSpan t.tag k S := by
    rw [Subgroup.map_sup, map_frobTwistGL_torusGroup p e (diagramMap_mem_normalizer t),
      map_frobTwistGL_rootSpan_diagram p t e hS]
    refine sup_le_sup_left (rootSpan_mono ?_) _
    rintro _ ⟨α, hα, rfl⟩
    exact hSρ α hα
  exact hle (Subgroup.mem_map_of_mem _ hg)

omit [PerfectRing k p] in
theorem exists_frobTwistGL_diagram_pinnedX_unit (e : ℕ) {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL t.tag k p e (diagramMap t k) (pinnedX t.tag k γ c) =
      pinnedX t.tag k (permLattice t.perm γ) ((μ : k) * iterateFrobenius k p e c) :=
  exists_frobTwistGL_pinnedX_of_conj p e (θ := permLattice t.perm)
    (fun _ hγ' => exists_diagramMap_conj_pinnedX_unit t hγ') hγ

theorem frobTwistGL_mem_parabolicLevi_diagram [IsAlgClosed k] (e : ℕ)
    {J : Set (Fin t.tag.rank)} (hJ : ∀ j ∈ J, t.perm j ∈ J) {g : ModGL t.tag k}
    (hg : g ∈ parabolicLevi t.tag k J) :
    frobTwistGL t.tag k p e (diagramMap t k) g ∈ parabolicLevi t.tag k J := by
  have hle : parabolicLevi t.tag k J ≤
      (parabolicLevi t.tag k J).comap (frobTwistGL t.tag k p e (diagramMap t k)) := by
    refine sup_le (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_comap]
      have h1 : frobTwistGL t.tag k p e (diagramMap t k) g ∈ torusGroup t.tag k := by
        rw [← map_frobTwistGL_torusGroup p e (diagramMap_mem_normalizer t)]
        exact Subgroup.mem_map_of_mem _ hg
      exact torusGroup_le_parabolicLevi J h1
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, ← pinnedX_single]
        obtain ⟨μ, hμ⟩ := exists_frobTwistGL_diagram_pinnedX_unit p t (k := k) e
          (isRoot_single t.tag j)
        rw [hμ, permLattice_single, pinnedX_single]
        exact xUnit_mem_parabolicLevi (hJ j hj) _
      · rw [SetLike.mem_coe, Subgroup.mem_comap, ← pinnedX_neg_single]
        obtain ⟨μ, hμ⟩ := exists_frobTwistGL_diagram_pinnedX_unit p t (k := k) e
          (isRoot_neg_single t.tag j)
        rw [hμ, permLattice_neg, permLattice_single, pinnedX_neg_single]
        exact yUnit_mem_parabolicLevi (hJ j hj) _
  exact hle hg

end Stability

section Descent

variable {τ : Tag} {k : Type} [Field k]

theorem rootDiagUnit_thetaDiag_comm_levi' (θ : Fin τ.rank → ℤ) (c : kˣ) {J : Set (Fin τ.rank)}
    (hθJ : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) {g : ModGL τ k}
    (hg : g ∈ parabolicLevi τ k J) :
    rootDiagUnit τ (thetaDiag θ c) * g = g * rootDiagUnit τ (thetaDiag θ c) := by
  have hle : parabolicLevi τ k J ≤ Subgroup.centralizer {rootDiagUnit τ (thetaDiag θ c)} := by
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation τ k (thetaDiag θ c)
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
    · rintro _ ⟨j, hj, c', rfl | rfl⟩
      · have h1 : thetaDiag θ c j = 1 := by simp [thetaDiag, hθJ j hj]
        have h2 := hx j c'
        rw [h1, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
      · have h1 : thetaDiag θ c j = 1 := by simp [thetaDiag, hθJ j hj]
        have h2 := hy j c'
        rw [h1, inv_one, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

end Descent

section Main

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_twisted_levi_fixed_conj {e : ℕ} (he : 1 ≤ e) {J : Set (Fin t.tag.rank)}
    (hJρ : ∀ j ∈ J, t.perm j ∈ J) {θ δ : Fin t.tag.rank → ℤ}
    (hρ : ∀ x y : Fin t.tag.rank → ℤ,
      iform (permLattice t.perm x) (permLattice t.perm y) = iform x y)
    (hθρ : permLattice t.perm θ = θ) (hδρ : permLattice t.perm δ = δ) {c : kˣ}
    (hker : ∀ σ ∈ rootCharKernel (thetaDiag δ (-1) * thetaDiag θ c),
      IsRoot t.tag σ ∧ iform θ σ = 0 ∧ rootChar (thetaDiag δ (-1 : kˣ)) σ = 1)
    (hJroots : ∀ σ, IsRoot t.tag σ → iform θ σ = 0 → σ ∈ parabolicRoots t.tag J)
    (hθJ : ∀ j ∈ J, iform θ (Pi.single j 1) = 0)
    (hstab : ∀ w ∈ rootCharStabilizer (thetaDiag δ (-1 : kˣ) * thetaDiag θ c),
      w ∈ kernelReflectionGroup (thetaDiag δ (-1 : kˣ) * thetaDiag θ c))
    (hsign : ∀ i, thetaDiag δ (-1 : kˣ) i = 1 ∨ thetaDiag δ (-1 : kˣ) i = -1)
    {y v : ModGL t.tag k} (hv : v ∈ parabolicLevi t.tag k J)
    (hFy : frobTwistGL t.tag k p e (diagramMap t k) y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit t.tag (thetaDiag δ (-1 : kˣ))) :
    ∃ h ∈ parabolicLevi t.tag k J, frobTwistGL t.tag k p e (diagramMap t k) h = h ∧
      h * y * h⁻¹ = rootDiagUnit t.tag (thetaDiag δ (-1 : kˣ)) := by
  classical
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set a' := thetaDiag δ (-1 : kˣ) * thetaDiag θ c with ha'
  set d := rootDiagUnit t.tag (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit t.tag (thetaDiag θ c) with hdb
  have hFd : F d = d := by
    rw [hF, hd, frobTwistGL_diagramMap_rootDiagUnit_of_sign p t e hsign]
    congr 1
    funext i
    simp only [thetaDiag]
    congr 1
    have h1 := hρ δ (Pi.single (t.perm.symm i) 1)
    rw [hδρ, permLattice_single, Equiv.apply_symm_apply] at h1
    exact h1.symm
  have hχ : kernelRoots (rootCharHom a') = rootCharKernel a' := kernelRoots_rootCharHom a'
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots (rootCharHom a')) with hM
  have hker' : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot t.tag σ ∧ iform θ σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := fun σ hσ => hker σ (hχ ▸ hσ)
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun s hs => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ hs).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker' σ hσ).1, (hker' σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi t.tag k J := by
    refine sup_le (torusGroup_le_parabolicLevi J) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact hJroots σ (hker' σ hσ).1 (hker' σ hσ).2.1
  have hρσ : ∀ σ ∈ kernelRoots (rootCharHom a'), permLattice t.perm σ ∈
      kernelRoots (rootCharHom a') := by
    intro σ hσ
    rw [hχ] at hσ ⊢
    refine ⟨IsRoot.permLattice (TwistTag.cartan_perm t) hσ.1, ?_⟩
    have h1 := hσ.2
    rw [ha', rootChar_mul, rootChar_thetaDiag, rootChar_thetaDiag] at h1 ⊢
    have e1 : iform δ (permLattice t.perm σ) = iform δ σ := by
      have := hρ δ σ
      rwa [hδρ] at this
    have e2 : iform θ (permLattice t.perm σ) = iform θ σ := by
      have := hρ θ σ
      rwa [hθρ] at this
    rw [e1, e2]
    exact h1
  have hMS : ∀ g ∈ M, F g ∈ M := fun g hg =>
    frobTwistGL_mem_torus_sup_rootSpan_diagram p t e (fun σ hσ => (hker' σ hσ).1) hρσ hg
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * F m := by
    intro u hu
    have hM' := isConnectedAlgebraicSubgroup_torus_sup_rootSpan (k := k) (rootCharHom a')
    obtain ⟨hsm, -, -⟩ := hM'.smooth
    exact exists_eq_inv_mul_frobTwistGL p he (diagramMap t k) hM' hsm hMS hu
  have hFvJ : F v ∈ parabolicLevi t.tag k J := frobTwistGL_mem_parabolicLevi_diagram p t e hJρ hv
  have hu : F v * v⁻¹ ∈ M := by
    set u := F v * v⁻¹ with hudef
    have huJ : u ∈ parabolicLevi t.tag k J := mul_mem hFvJ (inv_mem hv)
    have hF' : F v * y * (F v)⁻¹ = d := by
      have := congrArg F hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy]; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = F v * (v⁻¹ * d * v) * (F v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF']
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi' θ c hθJ huJ
    have hmem : u ∈ toralCentralizer t.tag k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup J huJ), ?_⟩
      have hmul : rootDiagUnit t.tag a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a' hstab hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj F hvy hMd hlang hu
  exact ⟨m * v, mul_mem (hMJ hm) hv, hFix, hconj⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
