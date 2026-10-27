module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuWitt

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU4Su

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_four)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

section Roots

variable {F : Type*} [Field F] {n : ℕ}

theorem single_comm_diag (d : Fin n → F) (i j : Fin n) (c : F) (h : d i = d j) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.diagonal d * Matrix.single i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [h, mul_comm]
  · simp [hab]

theorem rootMatrix_comm_diag (σ : F ≃+* F) (d : Fin n → F) (i j : Fin n) (c : F)
    (h : d i = d j) (h' : d (Fin.rev j) = d (Fin.rev i)) :
    rootMatrix σ i j c * Matrix.diagonal d = Matrix.diagonal d * rootMatrix σ i j c := by
  rw [rootMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_comm_diag d i j c h,
    single_comm_diag d (Fin.rev j) (Fin.rev i) (σ c) h']

theorem longRootMatrix_comm_diag (d : Fin n → F) (i : Fin n) (c : F)
    (h : d i = d (Fin.rev i)) :
    longRootMatrix i c * Matrix.diagonal d = Matrix.diagonal d * longRootMatrix i c := by
  rw [longRootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_comm_diag d i (Fin.rev i) c h]

end Roots

section ModelRoots

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem rootHom_mem_centralizer (hσσ : ∀ c, σ (σ c) = c) (y : SU σ 4) (d : Fin 4 → F)
    (hd : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d) {i j : Fin 4}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (h : d i = d j)
    (h' : d (Fin.rev j) = d (Fin.rev i)) (c : Multiplicative F) :
    rootHom σ hσσ hij hi hj c ∈ Subgroup.centralizer ({y} : Set (SU σ 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_rootHom, hd]
  exact rootMatrix_comm_diag σ d i j c.toAdd h h'

theorem longRootHom_mem_centralizer (y : SU σ 4) (d : Fin 4 → F)
    (hd : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d) {i : Fin 4}
    (hi : i ≠ Fin.rev i) (h : d i = d (Fin.rev i)) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ Subgroup.centralizer ({y} : Set (SU σ 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_longRootHom, hd]
  exact longRootMatrix_comm_diag d i c.toAdd h

theorem su4_root_gen (hσ : IsUnitaryInvolution σ) {ι : F} (xm um : SU σ 4)
    (hx : ((xm : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, 1, 1, -1])
    (hu : ((um : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ι, ι, -ι, -ι]) :
    Subgroup.centralizer ({xm} : Set (SU σ 4)) ⊔ Subgroup.centralizer ({um} : Set (SU σ 4)) ⊔
      Subgroup.centralizer ({xm * um} : Set (SU σ 4)) = ⊤ := by
  have hxu : (((xm * um : SU σ 4) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![-ι, ι, -ι, ι] := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hx, hu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  set R := Subgroup.centralizer ({xm} : Set (SU σ 4)) ⊔ Subgroup.centralizer ({um} : Set (SU σ 4)) ⊔
    Subgroup.centralizer ({xm * um} : Set (SU σ 4)) with hR
  have hmx : ∀ g, g ∈ Subgroup.centralizer ({xm} : Set (SU σ 4)) → g ∈ R := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hg)
  have hmu : ∀ g, g ∈ Subgroup.centralizer ({um} : Set (SU σ 4)) → g ∈ R := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right hg)
  have hmxu : ∀ g, g ∈ Subgroup.centralizer ({xm * um} : Set (SU σ 4)) → g ∈ R := fun g hg =>
    Subgroup.mem_sup_right hg
  refine eq_top_of_rootElements_le hσ.invol hσ.exists_traceZero hσ.trace_surj
    (fun x hx => hσ.exists_norm hx) (by norm_num) R ?_ ?_ ?_
  · intro i j hij hi hj hjr c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hmu _ (rootHom_mem_centralizer hσ.invol um _ hu hij hi hj (by simp) (by simp) c)
    · exact hmxu _ (rootHom_mem_centralizer hσ.invol (xm * um) _ hxu hij hi hj (by simp)
        (by simp) c)
    · exact absurd rfl hjr
    · exact hmu _ (rootHom_mem_centralizer hσ.invol um _ hu hij hi hj (by simp) (by simp) c)
    · exact absurd rfl hij
    · exact absurd rfl hjr
    · exact hmxu _ (rootHom_mem_centralizer hσ.invol (xm * um) _ hxu hij hi hj (by simp)
        (by simp) c)
    · exact hmxu _ (rootHom_mem_centralizer hσ.invol (xm * um) _ hxu hij hi hj (by simp)
        (by simp) c)
    · exact absurd rfl hjr
    · exact absurd rfl hij
    · exact hmu _ (rootHom_mem_centralizer hσ.invol um _ hu hij hi hj (by simp) (by simp) c)
    · exact absurd rfl hjr
    · exact hmxu _ (rootHom_mem_centralizer hσ.invol (xm * um) _ hxu hij hi hj (by simp)
        (by simp) c)
    · exact hmu _ (rootHom_mem_centralizer hσ.invol um _ hu hij hi hj (by simp) (by simp) c)
    · exact absurd rfl hij
  · intro i hi c
    exact hmx _ (longRootHom_mem_centralizer xm _ hx hi (by fin_cases i <;> simp) c)
  · intro i k hi hik hk
    exfalso
    have := congrArg Fin.val hk
    simp [Fin.val_rev] at this
    omega

end ModelRoots

theorem su4_caseB (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = ι) (B B' : Su K p f 2) (hB : suMat B * suMat B = -1)
    (hB' : suMat B' * suMat B' = -1) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (B, B')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (B, B')} : Set (Su K p f 4)) = ⊤ := by
  set σ := unitaryInvolution K p f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨fp, fm, hfp, hfm, h1, h2', h3⟩ := exists_witt_pair h2 hι hσι B hB
  obtain ⟨gp, gm, hgp, hgm, k1, k2, k3⟩ := exists_witt_pair h2 hι hσι B' hB'
  have hgram := wittW_gram fp fm gp gm hσ h1 h2' h3 k1 k2 k3
  have hdetW := wittW_det_ne_zero fp fm gp gm hgram
  let Wg : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (wittW fp fm gp gm) hdetW
  have hWg : (Wg : Matrix (Fin 4) (Fin 4) K) = wittW fp fm gp gm := rfl
  let φ : SU σ 4 ≃* Su K p f 4 := conjEquiv Wg (by rw [hWg]; exact hgram)
  have hxW := xU_mul_wittW (K := K) (p := p) (f := f) fp fm gp gm
  have huW := phiU_mul_wittW B B' fp fm gp gm hfp hfm hgp hgm
  have hWinv : ((Wg⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Wg : Matrix (Fin 4) (Fin 4) K)
      = 1 := Units.inv_mul Wg
  have hdiagconj : ∀ (y : Su K p f 4) (D : Matrix (Fin 4) (Fin 4) K),
      suMat y * wittW fp fm gp gm = wittW fp fm gp gm * D →
      ((φ.symm y : SU σ 4) : GL (Fin 4) K).val = D := by
    intro y D hyD
    show ((Wg⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * suMat y * (Wg : Matrix _ _ K) = D
    rw [Matrix.mul_assoc, hWg, hyD, ← Matrix.mul_assoc, ← hWg, hWinv, Matrix.one_mul]
  have hxm := hdiagconj _ _ hxW
  have hum := hdiagconj _ _ huW
  have key := su4_root_gen hσ (φ.symm (xU K p f)) (φ.symm (phiU K p f (B, B'))) hxm hum
  refine sup_centralizer_of_equiv φ.symm _ _ _ ?_
  rw [map_mul]
  exact key

end CFSG.GH74.Generic.BProg.B2.GenLocU4Su
