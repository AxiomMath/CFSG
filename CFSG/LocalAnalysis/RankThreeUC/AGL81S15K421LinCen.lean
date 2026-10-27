module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421CenProof

open Matrix

theorem matrix_add_self {m n : Type} (Q : Matrix m n (ZMod 2)) : Q + Q = 0 := by
  ext i j
  have h : ∀ z : ZMod 2, z + z = 0 := by decide
  exact h (Q i j)

theorem fromBlocks_diag_mul {l m : Type} [Fintype l] [Fintype m] {α : Type} [Semiring α]
    (A A' : Matrix l l α) (D D' : Matrix m m α) :
    fromBlocks A 0 0 D * fromBlocks A' 0 0 D' = fromBlocks (A * A') 0 0 (D * D') := by
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

section Psi

variable {K : Type} [Field K] (ψ : K →+* Matrix (Fin 2) (Fin 2) (ZMod 2))
variable {β : Type} [Fintype β] [DecidableEq β]

@[expose] def psiB : Matrix β β K →+* Matrix (β × Fin 2) (β × Fin 2) (ZMod 2) :=
  (Matrix.compRingEquiv β (Fin 2) (ZMod 2)).toRingHom.comp ψ.mapMatrix

theorem psiB_injective : Function.Injective (psiB ψ : Matrix β β K →+* _) := by
  intro A B h
  have h1 : ψ.mapMatrix A = ψ.mapMatrix B :=
    (Matrix.compRingEquiv β (Fin 2) (ZMod 2)).injective h
  exact Matrix.map_injective ψ.injective h1

end Psi

section Main

variable {K : Type} [Field K] (ψ : K →+* Matrix (Fin 2) (Fin 2) (ZMod 2))
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

@[expose] def gmat (ω : K) : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2) :=
  fromBlocks 1 0 0 (psiB ψ (Matrix.scalar β ω))

@[expose] def gGL (ω : K) (hω3 : ω * (ω * ω) = 1) : GL (ι ⊕ (β × Fin 2)) (ZMod 2) :=
  ⟨gmat ψ ω, fromBlocks 1 0 0 (psiB ψ (Matrix.scalar β (ω * ω))),
    by
      have h : psiB ψ (Matrix.scalar β ω) * psiB ψ (Matrix.scalar β (ω * ω)) = 1 := by
        rw [← map_mul, ← map_mul, hω3, map_one, map_one]
      rw [gmat, fromBlocks_diag_mul, one_mul, h, fromBlocks_one],
    by
      have h : psiB ψ (Matrix.scalar β (ω * ω)) * psiB ψ (Matrix.scalar β ω) = 1 := by
        rw [← map_mul, ← map_mul, mul_assoc, hω3, map_one, map_one]
      rw [gmat, fromBlocks_diag_mul, one_mul, h, fromBlocks_one]⟩

@[expose] def PhiFun (A : GL ι (ZMod 2)) (B : GL β K) : GL (ι ⊕ (β × Fin 2)) (ZMod 2) :=
  ⟨fromBlocks (A : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (B : Matrix β β K)),
    fromBlocks ((A⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) 0 0
      (psiB ψ ((B⁻¹ : GL β K) : Matrix β β K)),
    by
      have h1 : (A : Matrix ι ι (ZMod 2)) * ((A⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = 1 :=
        A.mul_inv
      have h2 : psiB ψ (B : Matrix β β K) * psiB ψ ((B⁻¹ : GL β K) : Matrix β β K) = 1 := by
        rw [← map_mul, B.mul_inv, map_one]
      rw [fromBlocks_diag_mul, h1, h2, fromBlocks_one],
    by
      have h1 : ((A⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) * (A : Matrix ι ι (ZMod 2)) = 1 :=
        A.inv_mul
      have h2 : psiB ψ ((B⁻¹ : GL β K) : Matrix β β K) * psiB ψ (B : Matrix β β K) = 1 := by
        rw [← map_mul, B.inv_mul, map_one]
      rw [fromBlocks_diag_mul, h1, h2, fromBlocks_one]⟩

@[expose] def Phi : GL ι (ZMod 2) × GL β K →* GL (ι ⊕ (β × Fin 2)) (ZMod 2) where
  toFun p := PhiFun ψ p.1 p.2
  map_one' := Units.ext (by
    show fromBlocks (1 : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (1 : Matrix β β K)) = 1
    rw [map_one, fromBlocks_one])
  map_mul' p q := Units.ext (by
    show fromBlocks ((p.1 * q.1 : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) 0 0
        (psiB ψ ((p.2 * q.2 : GL β K) : Matrix β β K)) =
      fromBlocks (p.1 : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (p.2 : Matrix β β K)) *
        fromBlocks (q.1 : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (q.2 : Matrix β β K))
    rw [fromBlocks_diag_mul, Units.val_mul, Units.val_mul, map_mul])

theorem Phi_injective : Function.Injective (Phi ψ : GL ι (ZMod 2) × GL β K →* _) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ h
  have h1 := congrArg Units.val h
  have h2 : fromBlocks (A : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (B : Matrix β β K)) =
      fromBlocks (A' : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (B' : Matrix β β K)) := h1
  obtain ⟨hA, -, -, hB⟩ := fromBlocks_inj.1 h2
  have hB' : (B : Matrix β β K) = B' := psiB_injective ψ hB
  have hA' : A = A' := Units.ext hA
  have hB'' : B = B' := Units.ext hB'
  rw [hA', hB'']

variable {ψ}

theorem blocks_of_comm {ω : K} (hω : ω * ω = ω + 1)
    (hψ : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2), M * ψ ω = ψ ω * M → ∃ k, ψ k = M)
    {M : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)}
    (hM : gmat ψ ω * M = M * gmat ψ ω) :
    ∃ (P : Matrix ι ι (ZMod 2)) (B : Matrix β β K), M = fromBlocks P 0 0 (psiB ψ B) := by
  rw [← fromBlocks_toBlocks M] at hM
  rw [gmat, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero,
    zero_add] at hM
  obtain ⟨-, hQ, hR, hS⟩ := fromBlocks_inj.1 hM
  set Ω : Matrix (β × Fin 2) (β × Fin 2) (ZMod 2) := psiB ψ (Matrix.scalar β ω) with hΩdef
  have hΩ2 : Ω * Ω = Ω + 1 := by
    rw [hΩdef, ← map_mul, ← map_mul, hω, map_add, map_add, map_one, map_one]
  have hQ0 : M.toBlocks₁₂ = 0 := by
    have h1 : M.toBlocks₁₂ * (Ω * Ω) = M.toBlocks₁₂ := by
      rw [← Matrix.mul_assoc, ← hQ, ← hQ]
    have h2 : M.toBlocks₁₂ * (Ω * Ω) = M.toBlocks₁₂ + M.toBlocks₁₂ := by
      rw [hΩ2, Matrix.mul_add, Matrix.mul_one, ← hQ]
    calc M.toBlocks₁₂ = M.toBlocks₁₂ * (Ω * Ω) := h1.symm
      _ = M.toBlocks₁₂ + M.toBlocks₁₂ := h2
      _ = 0 := matrix_add_self _
  have hR0 : M.toBlocks₂₁ = 0 := by
    have h1 : (Ω * Ω) * M.toBlocks₂₁ = M.toBlocks₂₁ := by
      rw [Matrix.mul_assoc, hR, hR]
    have h2 : (Ω * Ω) * M.toBlocks₂₁ = M.toBlocks₂₁ + M.toBlocks₂₁ := by
      rw [hΩ2, Matrix.add_mul, Matrix.one_mul, hR]
    calc M.toBlocks₂₁ = (Ω * Ω) * M.toBlocks₂₁ := h1.symm
      _ = M.toBlocks₂₁ + M.toBlocks₂₁ := h2
      _ = 0 := matrix_add_self _
  let e := Matrix.compRingEquiv β (Fin 2) (ZMod 2)
  have hΩe : Ω = e (ψ.mapMatrix (Matrix.scalar β ω)) := rfl
  have hscal : ψ.mapMatrix (Matrix.scalar β ω) = Matrix.diagonal (fun _ : β => ψ ω) := by
    refine Matrix.ext fun b b' => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    split_ifs
    · rfl
    · exact map_zero ψ
  have hT : Matrix.diagonal (fun _ : β => ψ ω) * e.symm M.toBlocks₂₂ =
      e.symm M.toBlocks₂₂ * Matrix.diagonal (fun _ : β => ψ ω) := by
    rw [← hscal]
    have h3 := congrArg e.symm hS
    rw [map_mul, map_mul, hΩe, RingEquiv.symm_apply_apply] at h3
    exact h3
  have hcomm : ∀ b b' : β, e.symm M.toBlocks₂₂ b b' * ψ ω = ψ ω * e.symm M.toBlocks₂₂ b b' := by
    intro b b'
    have h4 := congrFun (congrFun hT b) b'
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h4
    exact h4.symm
  choose k hk using fun b b' => hψ _ (hcomm b b')
  refine ⟨M.toBlocks₁₁, k, ?_⟩
  have hSk : M.toBlocks₂₂ = psiB ψ k := by
    have h5 : ψ.mapMatrix k = e.symm M.toBlocks₂₂ := by
      refine Matrix.ext fun b b' => ?_
      exact hk b b'
    show M.toBlocks₂₂ = e (ψ.mapMatrix k)
    rw [h5, RingEquiv.apply_symm_apply]
  calc M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
        (fromBlocks_toBlocks M).symm
    _ = fromBlocks M.toBlocks₁₁ 0 0 (psiB ψ k) := by rw [hQ0, hR0, hSk]

theorem range_Phi {ω : K} (hω : ω * ω = ω + 1) (hω3 : ω * (ω * ω) = 1)
    (hψ : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2), M * ψ ω = ψ ω * M → ∃ k, ψ k = M) :
    (Phi ψ : GL ι (ZMod 2) × GL β K →* GL (ι ⊕ (β × Fin 2)) (ZMod 2)).range =
      Subgroup.centralizer ({gGL ψ ω hω3} : Set (GL (ι ⊕ (β × Fin 2)) (ZMod 2))) := by
  ext h
  constructor
  · rintro ⟨⟨A, B⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Units.ext
    show gmat ψ ω * fromBlocks (A : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (B : Matrix β β K)) =
      fromBlocks (A : Matrix ι ι (ZMod 2)) 0 0 (psiB ψ (B : Matrix β β K)) * gmat ψ ω
    have hc : psiB ψ (Matrix.scalar β ω) * psiB ψ (B : Matrix β β K) =
        psiB ψ (B : Matrix β β K) * psiB ψ (Matrix.scalar β ω) := by
      rw [← map_mul, ← map_mul, (Matrix.scalar_commute ω (fun r => Commute.all ω r) _).eq]
    rw [gmat, fromBlocks_diag_mul, fromBlocks_diag_mul, one_mul, mul_one, hc]
  · intro hh
    rw [Subgroup.mem_centralizer_iff] at hh
    have hc1 : gGL ψ ω hω3 * h = h * gGL ψ ω hω3 := hh _ (Set.mem_singleton _)
    have hc2 : gGL ψ ω hω3 * h⁻¹ = h⁻¹ * gGL ψ ω hω3 := by
      have h1 : h⁻¹ * (gGL ψ ω hω3 * h) * h⁻¹ = h⁻¹ * (h * gGL ψ ω hω3) * h⁻¹ := by rw [hc1]
      simpa [mul_assoc] using h1.symm
    have hc1' : gmat ψ ω * (h : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) =
        (h : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) * gmat ψ ω :=
      congrArg Units.val hc1
    have hc2' : gmat ψ ω *
        ((h⁻¹ : GL (ι ⊕ (β × Fin 2)) (ZMod 2)) :
          Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) =
        ((h⁻¹ : GL (ι ⊕ (β × Fin 2)) (ZMod 2)) :
          Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) * gmat ψ ω :=
      congrArg Units.val hc2
    obtain ⟨P, B, hPB⟩ := blocks_of_comm hω hψ hc1'
    obtain ⟨P', B', hPB'⟩ := blocks_of_comm hω hψ hc2'
    have hmul : (h : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) *
        ((h⁻¹ : GL (ι ⊕ (β × Fin 2)) (ZMod 2)) :
          Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) = 1 := h.mul_inv
    have hmul' : ((h⁻¹ : GL (ι ⊕ (β × Fin 2)) (ZMod 2)) :
          Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) *
        (h : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) = 1 := h.inv_mul
    rw [hPB, hPB', fromBlocks_diag_mul, ← fromBlocks_one] at hmul
    rw [hPB, hPB', fromBlocks_diag_mul, ← fromBlocks_one] at hmul'
    obtain ⟨hPP, -, -, hSS⟩ := fromBlocks_inj.1 hmul
    obtain ⟨hPP', -, -, hSS'⟩ := fromBlocks_inj.1 hmul'
    have hBB : B * B' = 1 := by
      apply psiB_injective ψ
      rw [map_mul, hSS, map_one]
    have hBB' : B' * B = 1 := by
      apply psiB_injective ψ
      rw [map_mul, hSS', map_one]
    refine ⟨(⟨P, P', hPP, hPP'⟩, ⟨B, B', hBB, hBB'⟩), Units.ext ?_⟩
    exact hPB.symm

end Main

end K421CenProof

end CFSG.LocalAnalysis.RankThreeUC.S15
