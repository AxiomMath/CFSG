module

public import CFSG.LieType.SeitzGeneration.HyperIrrGen
public import CFSG.LieType.SeitzGeneration.HyperIrrNoncentral
public import CFSG.LieType.SeitzGeneration.HyperIrrNormal
public import CFSG.LieType.SeitzGeneration.HyperLeaf

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open

variable {F : Type*} [Field F]

theorem conjUnit_conjUnit_inv_self {m : ℕ} (P : GL (Fin m) F) (g : SpecialLinearGroup (Fin m) F) :
    conjUnit P (conjUnit P⁻¹ g) = g := by
  apply Subtype.ext
  rw [conjUnit_coe, conjUnit_coe, inv_inv]
  have h1 : (P : Matrix (Fin m) (Fin m) F) * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (P : Matrix (Fin m) (Fin m) F) * (((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        (g : Matrix (Fin m) (Fin m) F) * (P : Matrix (Fin m) (Fin m) F)) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
      = ((P : Matrix (Fin m) (Fin m) F) * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) *
        (g : Matrix (Fin m) (Fin m) F) *
        ((P : Matrix (Fin m) (Fin m) F) * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
        simp only [Matrix.mul_assoc]
    _ = g := by rw [h1, Matrix.one_mul, Matrix.mul_one]

theorem commute_conjUnit {m : ℕ} {M N : Matrix (Fin m) (Fin m) F} (P : GL (Fin m) F)
    (hMN : M * (P : Matrix (Fin m) (Fin m) F) = (P : Matrix (Fin m) (Fin m) F) * N)
    {g₀ : SpecialLinearGroup (Fin m) F}
    (hg : N * (g₀ : Matrix (Fin m) (Fin m) F) = (g₀ : Matrix (Fin m) (Fin m) F) * N) :
    M * ((conjUnit P g₀ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((conjUnit P g₀ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) * M := by
  have hPi : (P : Matrix (Fin m) (Fin m) F) *
      ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiP : ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      (P : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hNP : N * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * M := by
    calc N * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
        = ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          ((P : Matrix (Fin m) (Fin m) F) * N) *
          ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
          rw [← Matrix.mul_assoc, hiP, Matrix.one_mul]
      _ = ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          (M * (P : Matrix (Fin m) (Fin m) F)) *
          ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by rw [hMN]
      _ = ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * M *
          ((P : Matrix (Fin m) (Fin m) F) *
            ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
          simp only [Matrix.mul_assoc]
      _ = ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * M := by rw [hPi, Matrix.mul_one]
  rw [conjUnit_coe]
  calc M * ((P : Matrix (Fin m) (Fin m) F) * (g₀ : Matrix (Fin m) (Fin m) F) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
      = (M * (P : Matrix (Fin m) (Fin m) F)) * (g₀ : Matrix (Fin m) (Fin m) F) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin m) (Fin m) F) * (N * (g₀ : Matrix (Fin m) (Fin m) F)) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
        rw [hMN]; simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin m) (Fin m) F) * ((g₀ : Matrix (Fin m) (Fin m) F) * N) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by rw [hg]
    _ = (P : Matrix (Fin m) (Fin m) F) * (g₀ : Matrix (Fin m) (Fin m) F) *
        (N * ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin m) (Fin m) F) * (g₀ : Matrix (Fin m) (Fin m) F) *
        (((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * M) := by rw [hNP]
    _ = (P : Matrix (Fin m) (Fin m) F) * (g₀ : Matrix (Fin m) (Fin m) F) *
        ((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * M := by
        simp only [Matrix.mul_assoc]

theorem toPSL_commute_of_matrix {m : ℕ} {a g : SpecialLinearGroup (Fin m) F}
    (h : (a : Matrix (Fin m) (Fin m) F) * g = g * a) :
    (toPSL a : ProjectiveSpecialLinearGroup (Fin m) F) * toPSL g = toPSL g * toPSL a := by
  rw [← map_mul, ← map_mul]
  exact congrArg toPSL (Subtype.ext h)

theorem toPSL_conjUnit_mem {m p : ℕ} {E : Subgroup (ProjectiveSpecialLinearGroup (Fin m) F)}
    {a b : SpecialLinearGroup (Fin m) F} {Na Nb : Matrix (Fin m) (Fin m) F} (P : GL (Fin m) F)
    (haE : toPSL a ∈ E) (hbE : toPSL b ∈ E)
    (hrel : (Subgroup.closure ({toPSL a, toPSL b} :
      Set (ProjectiveSpecialLinearGroup (Fin m) F))).relIndex E = p)
    (hMa : (a : Matrix (Fin m) (Fin m) F) * (P : Matrix (Fin m) (Fin m) F) =
      (P : Matrix (Fin m) (Fin m) F) * Na)
    (hMb : (b : Matrix (Fin m) (Fin m) F) * (P : Matrix (Fin m) (Fin m) F) =
      (P : Matrix (Fin m) (Fin m) F) * Nb)
    {g₀ : SpecialLinearGroup (Fin m) F}
    (hga : Na * (g₀ : Matrix (Fin m) (Fin m) F) = (g₀ : Matrix (Fin m) (Fin m) F) * Na)
    (hgb : Nb * (g₀ : Matrix (Fin m) (Fin m) F) = (g₀ : Matrix (Fin m) (Fin m) F) * Nb) :
    toPSL (conjUnit P g₀) ∈ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin m) F | k ∈ (⊤ : Subgroup _) ∧
        ∃ F₀ : Subgroup (ProjectiveSpecialLinearGroup (Fin m) F), F₀ ≤ E ∧ F₀.relIndex E = p ∧
          ∀ f ∈ F₀, f * k = k * f} := by
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _,
    Subgroup.closure {toPSL a, toPSL b}, closure_pair_le haE hbE, hrel, ?_⟩
  intro f hf
  exact commute_of_mem_closure_pair (toPSL_commute_of_matrix (commute_conjUnit P hMa hga))
    (toPSL_commute_of_matrix (commute_conjUnit P hMb hgb)) hf

theorem hyperGen_top_of_irreducible_nonabelian [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {x y : SpecialLinearGroup (Fin n) F}
    (hx : toPSL x ∈ E) (hy : toPSL y ∈ E) (hxy : x * y ≠ y * x)
    (hirr : ∀ W : Submodule F (Fin n → F),
      (∀ z : SpecialLinearGroup (Fin n) F, toPSL z ∈ E →
        ∀ w ∈ W, (z : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤) :
    HyperGen p (⊤ : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)) E := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      apply hxy
      have : x = y := Subtype.ext (Matrix.ext fun i => i.elim0)
      rw [this]
    · exact h
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x', y', r, sx, sy, ζ, c, A, B, C, u₀, hx'E, hy'E, hrE, hgen, hxA, hyB, hrC, hk⟩ :=
    exists_kron_data hp hp2 hpF hn hcomm hE.2 hcard hx hy hxy hirr
  obtain rfl : n = p * p := hk.card_eq_sq
  obtain ⟨P, hAP, hBP, hCP⟩ := exists_kron_model hk
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hKp := compMat_pow_eq hp.pos hk.hC P hCP
  have hc1 : 1 + c ≠ 0 := by
    intro h0
    apply hk.notPow (-1)
    rw [hodd.neg_one_pow]
    linear_combination (-1 : F) * h0
  obtain ⟨a, D, D', U, N, haC, haK, hDD, hUN, haeq⟩ :=
    exists_noncentral_block hp3 hodd hk.prim hc1 hKp
  have hxP : (x' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sx • kr (shiftMat p F) 1) := by
    rw [hxA, Matrix.smul_mul, hAP, Matrix.mul_smul]
  have hyP : (y' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sy • kr (charMat p ζ⁻¹) 1) := by
    rw [hyB, Matrix.smul_mul, hBP, Matrix.mul_smul]
  have hrP : (r : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 (compMat p c) := by
    rw [hrC]; exact hCP
  have hrel := relIndex_three_pairs hp.pos hx'E hy'E hrE (hcomm _ hx'E _ hy'E)
    (hcomm _ hx'E _ hrE) (hcomm _ hy'E _ hrE) (hE.2 _ hx'E) (hE.2 _ hy'E) (hE.2 _ hrE) hgen hcard
  let K'' : Subgroup (SpecialLinearGroup (Fin (p * p)) F) :=
    ((Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin (p * p)) F |
      k ∈ (⊤ : Subgroup _) ∧ ∃ F₀ : Subgroup (ProjectiveSpecialLinearGroup (Fin (p * p)) F),
        F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f}).comap toPSL).comap (conjUnit P)
  have hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K'' := by
    intro u
    refine toPSL_conjUnit_mem P hx'E hy'E hrel.1 hxP hyP ?_ ?_
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_dHom, kr_mul, Matrix.mul_one,
        Matrix.one_mul]
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_dHom, kr_mul, Matrix.mul_one,
        Matrix.one_mul]
  have ht : ∀ (m : Fin p) (z : F) (hz : z ^ p = 1), tEl m z hz ∈ K'' := by
    intro m z hz
    have hdc : charMat p ζ⁻¹ * diagUpd m z = diagUpd m z * charMat p ζ⁻¹ := by
      simp only [charMat, diagUpd, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    refine toPSL_conjUnit_mem P hy'E hrE hrel.2.2 hyP hrP ?_ ?_
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_tEl, kr_mul, Matrix.mul_one, hdc]
    · simp only [coe_tEl, kr_mul, Matrix.mul_one, Matrix.one_mul]
  have hdetMf : (Mf (a : Matrix (Fin p) (Fin p) F)).det = 1 := by
    rw [haeq]; exact det_Mf_conj hpF hDD hUN
  have hKa : compMat p c * ((a : Matrix (Fin p) (Fin p) F) - 1) =
      ((a : Matrix (Fin p) (Fin p) F) - 1) * compMat p c := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, haK]
  have haB : (⟨Mf (a : Matrix (Fin p) (Fin p) F), hdetMf⟩ :
      SpecialLinearGroup (Fin (p * p)) F) ∈ K'' := by
    refine toPSL_conjUnit_mem P hx'E hrE hrel.2.1 hxP hrP ?_ ?_
    · show sx • kr (shiftMat p F) 1 * Mf (a : Matrix (Fin p) (Fin p) F) =
        Mf (a : Matrix (Fin p) (Fin p) F) * (sx • kr (shiftMat p F) 1)
      simp only [Matrix.smul_mul, Matrix.mul_smul, Mf, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, kr_mul, shiftMat_mul_projF hp.pos,
        projF_mul_shiftMat hp.pos, smul_add]
    · show kr 1 (compMat p c) * Mf (a : Matrix (Fin p) (Fin p) F) =
        Mf (a : Matrix (Fin p) (Fin p) F) * kr 1 (compMat p c)
      simp only [Mf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, kr_mul, hKa]
  have hblock : a ∈ blockSub hpF K'' := ⟨_, haB, rfl⟩
  have htop : K'' = ⊤ := eq_top_of_three_families hk.prim hp3 hpF hd ht haC hblock
  unfold HyperGen
  intro g _
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
  have h1 : conjUnit P⁻¹ g' ∈ K'' := htop ▸ Subgroup.mem_top _
  have h2 : toPSL (conjUnit P (conjUnit P⁻¹ g')) ∈ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin (p * p)) F |
      k ∈ (⊤ : Subgroup _) ∧ ∃ F₀ : Subgroup (ProjectiveSpecialLinearGroup (Fin (p * p)) F),
        F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := h1
  rwa [conjUnit_conjUnit_inv_self] at h2

end CFSG.LieType.SeitzGeneration
