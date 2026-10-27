module

public import CFSG.LieType.SeitzGeneration.OuterLinearCore
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

section Plane

variable {n : ℕ} {K : Type} [Field K]

theorem fieldAut_conjAut_apply (σ : K ≃+* K) (A : GL (Fin n) K) (y : projectiveSL n K) :
    fieldAut n K σ (conjAut n K A y) =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) (fieldAut n K σ y) := by
  have h := (standard_automorphism_transport (K := K) (n := n)).2.2.1 σ A
  have h2 := congrArg (fun φ : MulAut (projectiveSL n K) => φ (fieldAut n K σ y)) h
  simp only [MulAut.mul_apply, MulAut.inv_apply] at h2
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

theorem slSub_le_comap_planeClosure {k : Subfield K} (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    {E : Subgroup (MulAut (projectiveSL n K))} (hσE : fieldAut n K σ ∈ E)
    (hσout : ∀ x, fieldAut n K σ ≠ MulAut.conj x) {g : projectiveSL n K}
    (hgE : MulAut.conj g ∈ E) {Ĝ : GL (Fin n) K} (hĜ : conjAut n K Ĝ = MulAut.conj g)
    (M : GL (Fin n) K) (hgM : (Ĝ : Matrix (Fin n) (Fin n) K) *
      (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    slSub n k ≤ (planeClosure E).comap (proj n K) ∧
      ∀ B ∈ slSub n k, slConjugation n K M B ∈ (planeClosure E).comap (proj n K) := by
  set α : MulAut (projectiveSL n K) := MulAut.conj g * fieldAut n K σ with hα
  have hαE : α ∈ E := E.mul_mem hgE hσE
  have hf1 : fieldAut n K σ ≠ 1 := fun h => hσout 1 (by rw [h, map_one])
  have hα1 : α ≠ 1 := by
    intro h
    apply hσout g⁻¹
    have h1 : fieldAut n K σ = (MulAut.conj g)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, map_inv]
  have hfixB : ∀ B ∈ slSub n k, fieldAut n K σ (proj n K B) = proj n K B := by
    intro B hB
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, (hk _).mp ((mem_slSub.mp hB) i j)]
  have hGM : Ĝ * GeneralLinearGroup.map (σ : K →+* K) M = M := Units.ext (by simpa using hgM)
  refine ⟨fun B hB => mem_planeClosure_of_fixed hσE hf1 (hfixB B hB), fun B hB => ?_⟩
  show proj n K (slConjugation n K M B) ∈ planeClosure E
  refine mem_planeClosure_of_fixed hαE hα1 ?_
  rw [← conjAut_proj]
  calc α (conjAut n K M (proj n K B))
      = MulAut.conj g (fieldAut n K σ (conjAut n K M (proj n K B))) := rfl
    _ = conjAut n K Ĝ (conjAut n K (GeneralLinearGroup.map (σ : K →+* K) M)
          (proj n K B)) := by rw [fieldAut_conjAut_apply, hfixB B hB, hĜ]
    _ = conjAut n K (Ĝ * GeneralLinearGroup.map (σ : K →+* K) M) (proj n K B) := by
        rw [map_mul]; rfl
    _ = conjAut n K M (proj n K B) := by rw [hGM]

theorem planeGen_of_comap_eq_top {E : Subgroup (MulAut (projectiveSL n K))}
    (h : (planeClosure E).comap (proj n K) = ⊤) : PlaneGen E := by
  rw [PlaneGen, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := proj_surjective n K x
  have hy : y ∈ (planeClosure E).comap (proj n K) := h ▸ Subgroup.mem_top y
  exact hy

theorem planeGen_of_eigenvector [Finite K] {k : Subfield K} {ℓ e : ℕ} (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK' : Nat.card K = ℓ ^ e) (hσ : orderOf σ = p) (hK : Nat.card K = Nat.card k ^ p)
    (hpK : (p : K) ≠ 0) (hn : 3 ≤ n) {E : Subgroup (MulAut (projectiveSL n K))}
    (hσE : fieldAut n K σ ∈ E) (hσout : ∀ x, fieldAut n K σ ≠ MulAut.conj x)
    {g : projectiveSL n K} (hgE : MulAut.conj g ∈ E) {Ĝ : GL (Fin n) K}
    (hĜ : conjAut n K Ĝ = MulAut.conj g) (hĜσ : (Ĝ : Matrix (Fin n) (Fin n) K).map σ = Ĝ)
    (hĜp : (Ĝ : Matrix (Fin n) (Fin n) K) ^ p = 1) (hĜ1 : (Ĝ : Matrix (Fin n) (Fin n) K) ≠ 1)
    {w : Fin n → K} (hwk : ∀ i, w i ∈ k) (hw0 : w ≠ 0)
    (hĜw : (Ĝ : Matrix (Fin n) (Fin n) K) *ᵥ w = w) : PlaneGen E := by
  obtain ⟨M, hgM, hMw⟩ := exists_fixed_matrix_rational_column σ hk hp hℓ he hK' hσ
    (Ĝ : Matrix (Fin n) (Fin n) K) hĜσ hĜp hwk hw0 hĜw ⟨0, by omega⟩
  obtain ⟨hkH, hMH⟩ := slSub_le_comap_planeClosure σ hk hσE hσout hgE hĜ M hgM
  exact planeGen_of_comap_eq_top
    (eq_top_of_fixed_matrix σ hk hp hK hpK hn hkH (Ĝ : Matrix (Fin n) (Fin n) K) hĜp hĜ1 M hgM
      hMw hMH)

end Plane

section Pair

variable {n : ℕ} {K : Type} [Field K]

@[expose] def SubfieldPairSLLt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (p : ℕ), p.Prime →
    Nat.card K = Nat.card k ^ p → ∀ n : ℕ, 3 ≤ n → n < p → ∀ A : GL (Fin n) K,
      (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k →
        Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
          ((slSub n k).map (slConjugation n K A).toMonoidHom :
            Set (SpecialLinearGroup (Fin n) K))) = ⊤

theorem planeGen_of_pair [Finite K] (hpair : SubfieldPairSLLt) {k : Subfield K} {ℓ e : ℕ}
    (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (he : 1 ≤ e) (hK' : Nat.card K = ℓ ^ e) (hσ : orderOf σ = p)
    (hK : Nat.card K = Nat.card k ^ p) (hn : 3 ≤ n) (hnp : n < p)
    {E : Subgroup (MulAut (projectiveSL n K))} (hσE : fieldAut n K σ ∈ E)
    (hσout : ∀ x, fieldAut n K σ ≠ MulAut.conj x) {g : projectiveSL n K}
    (hgE : MulAut.conj g ∈ E) {Ĝ : GL (Fin n) K} (hĜ : conjAut n K Ĝ = MulAut.conj g)
    (hĜσ : (Ĝ : Matrix (Fin n) (Fin n) K).map σ = Ĝ)
    (hĜp : (Ĝ : Matrix (Fin n) (Fin n) K) ^ p = 1)
    (hĜns : ∀ c : K, (Ĝ : Matrix (Fin n) (Fin n) K) ≠ c • 1) : PlaneGen E := by
  obtain ⟨M₀, hdet, hM₀⟩ := exists_fixed_matrix hp hℓ he hK' σ hσ (Ĝ : Matrix (Fin n) (Fin n) K)
    hĜσ hĜp
  let M : GL (Fin n) K := Matrix.nonsingInvUnit M₀ hdet
  have hgM : (Ĝ : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M := hM₀
  obtain ⟨hkH, hMH⟩ := slSub_le_comap_planeClosure σ hk hσE hσout hgE hĜ M hgM
  have hne := slConjugation_map_ne σ hk hp.pos (Ĝ : Matrix (Fin n) (Fin n) K) hĜp hĜns M hgM
  have hclos := hpair K k p hp hK n hn hnp M hne
  refine planeGen_of_comap_eq_top (eq_top_iff.mpr ?_)
  rw [← hclos, Subgroup.closure_le]
  rintro x (hx | ⟨B, hB, rfl⟩)
  · exact hkH hx
  · exact hMH B hB

end Pair

end CFSG.LieType.SeitzGeneration
