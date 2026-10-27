module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealTriple
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealSingle

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.GLTheoremB

section Group

theorem u6r_cube_twist {G : Type*} [Group G] {x C s : G} (hs : ∀ y, s * y = y * s)
    (hC : C * x * C⁻¹ = s * x) : (x * C) ^ 3 = s ^ 3 * x ^ 3 * C ^ 3 := by
  have e1 : (x * C) ^ 3 = x * (C * x * C⁻¹) * (C * (C * x * C⁻¹) * C⁻¹) * C ^ 3 := by
    rw [pow_three, pow_three]
    group
  have e2 : C * (s * x) * C⁻¹ = s * (C * x * C⁻¹) := by
    have hCs : C * s = s * C := (hs C).symm
    calc C * (s * x) * C⁻¹ = (C * s) * x * C⁻¹ := by group
      _ = (s * C) * x * C⁻¹ := by rw [hCs]
      _ = s * (C * x * C⁻¹) := by group
  have hxs : x * s = s * x := (hs x).symm
  rw [e1, hC, e2, hC]
  have key : ∀ z, x * (s * z) = s * (x * z) := fun z => by rw [← mul_assoc, hxs, mul_assoc]
  simp only [mul_assoc, key, pow_three]

theorem u6r_map_mul {P : Type*} [Group P] (H : Subgroup P) (a b : MulAut P) :
    H.map (a * b).toMonoidHom = (H.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem u6r_map_one {P : Type*} [Group P] (H : Subgroup P) :
    H.map (1 : MulAut P).toMonoidHom = H := by
  ext x
  simp

theorem u6r_cube_one_of_conj {K : Type} [Field K] {g C : GL (Fin 6) K} {μ ζ : Kˣ}
    (hg3 : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ)
    (hζ : C * g * C⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g) : ζ ^ 3 = 1 := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 6) (ζ ^ 3) = 1 := by
    have e1 : (C * g * C⁻¹) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ := by
      rw [conj_pow, hg3, (commute_scalar μ C).eq, mul_inv_cancel_right]
    rw [hζ, (commute_scalar ζ g).symm.mul_pow, hg3, ← map_pow] at e1
    exact mul_right_cancel (e1.trans (one_mul _).symm)
  have h2 := congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K) 0 0) h1
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h2
  exact Units.ext (by simpa using h2)

end Group

section Core

variable {f : ℕ} {K : Type} [Field K]

theorem u6r_exists_twist (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : UnitaryFieldData 2 f K) {A : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    {ψ : MulAut (primeFormP h (idGram K 6))} {J : Subgroup (primeFormP h (idGram K 6))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K 6)) A ψ J q) (hq : 10 ≤ q)
    (hA : ∀ a ∈ A, ∃ B : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) B = a)
    (g : primeFormUnitary h (idGram K 6)) (hg : primeFormConjHom h (idGram K 6) g = ψ) {μ : Kˣ}
    (hg3 : (g : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ) :
    ∃ C : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) C ∈ A ∧
      primeFormConjHom h (idGram K 6) C ∉ Subgroup.zpowers ψ ∧
      ∃ ν : Kˣ, ν ^ (2 ^ f + 1) = 1 ∧
        (C : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) ν ∧
        ∃ ζ : Kˣ, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧
          (C : GL (Fin 6) K) * g * (C : GL (Fin 6) K)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  obtain ⟨η, hηA, hηψ⟩ := exists_mem_not_zpowers hψ3 c.card
  obtain ⟨C, rfl⟩ := hA η hηA
  have hη3 : primeFormConjHom h (idGram K 6) C ^ 3 = 1 := c.elemAbelian.2 _ hηA
  obtain ⟨ν, hν1, hC3⟩ := u6r_cube_scalar (by norm_num) C hη3
  have hcomm : primeFormConjHom h (idGram K 6) C * primeFormConjHom h (idGram K 6) g =
      primeFormConjHom h (idGram K 6) g * primeFormConjHom h (idGram K 6) C := by
    rw [hg]
    exact congrArg Subtype.val (c.elemAbelian.1.is_comm.comm ⟨_, hηA⟩ ⟨ψ, c.mem⟩)
  obtain ⟨ζ, hζ⟩ := u6r_comm_scalar (by norm_num) g C hcomm
  have hζ3 : ζ ^ 3 = 1 := u6r_cube_one_of_conj hg3 hζ
  refine ⟨C, hηA, hηψ, ν, hν1, hC3, ζ, ?_, hζ3, hζ⟩
  intro hζ1
  have hCg : (C : GL (Fin 6) K) * g = g * C := by
    have e : (C : GL (Fin 6) K) * g * (C : GL (Fin 6) K)⁻¹ = g := by
      rw [hζ, hζ1, map_one, one_mul]
    calc (C : GL (Fin 6) K) * g = (C : GL (Fin 6) K) * g * (C : GL (Fin 6) K)⁻¹ * C := by group
      _ = g * C := by rw [e]
  obtain ⟨⟨hst, -⟩, -⟩ := c.field _ hηA hηψ
  have hJ : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) g)) J := by
    rw [hg]
    exact c.comp
  exact c.u6r_not_inner hηA hηψ hst
    (u6r_inner_of_commute hO (by norm_num) g C hg3 hC3 hCg hJ hq c.typeL2 hst)

theorem u6r_cube_false (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : UnitaryFieldData 2 f K) (hf : Odd f) {A : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    {ψ : MulAut (primeFormP h (idGram K 6))} {J : Subgroup (primeFormP h (idGram K 6))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K 6)) A ψ J q) (hq : 10 ≤ q)
    (hA : ∀ a ∈ A, ∃ B : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) B = a)
    (g : primeFormUnitary h (idGram K 6)) (hg : primeFormConjHom h (idGram K 6) g = ψ) {μ : Kˣ}
    (hμ1 : μ ^ (2 ^ f + 1) = 1)
    (hg3 : (g : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ) {a : Kˣ}
    (ha : a ^ 3 = μ) : False := by
  have ha1 : a ^ (2 ^ f + 1) = 1 := u6r_pow_succ_eq_one_of_cube h hf (by rw [ha]; exact hμ1)
  obtain ⟨g', hg'coe, hg'c⟩ := u6r_rescale g ha1
  have hg'3 : (g' : GL (Fin 6) K) ^ 3 = 1 := by
    rw [hg'coe, (commute_scalar a⁻¹ (g : GL (Fin 6) K)).symm.mul_pow, hg3, ← map_pow, ← map_mul,
      inv_pow, ha, inv_mul_cancel, map_one]
  obtain ⟨C, hCA, hCψ, ν, -, hC3, ζ, hζ1, -, hζ⟩ := u6r_exists_twist hO h c hq hA g hg hg3
  have hζ' : (C : GL (Fin 6) K) * g' * (C : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g' := by
    rw [hg'coe]
    have hs : (C : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * C :=
      (commute_scalar a⁻¹ (C : GL (Fin 6) K)).eq
    calc (C : GL (Fin 6) K) * (Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * g) *
          (C : GL (Fin 6) K)⁻¹
        = ((C : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹) * g *
          (C : GL (Fin 6) K)⁻¹ := by simp only [mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * C) * g * (C : GL (Fin 6) K)⁻¹ := by
          rw [hs]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          ((C : GL (Fin 6) K) * g * (C : GL (Fin 6) K)⁻¹) := by simp only [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g) := by rw [hζ]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * g) := by
          rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm a⁻¹ ζ]
  have hg'ψ : primeFormConjHom h (idGram K 6) g' = ψ := hg'c.trans hg
  have hJ : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) g')) J := by
    rw [hg'ψ]
    exact c.comp
  have hf4 := u6r_four_le hf g' C hg'3 hζ1 hζ' hJ
  obtain ⟨H₁, H₂, H₃, hiff, h12, h13, h23, -, hm1, hm2, hm3⟩ := u6r_triple hf hf4 g' C hg'3 hζ1 hζ'
  obtain ⟨⟨hst, -⟩, -⟩ := c.field _ hCA hCψ
  have hJmap : J.map (primeFormConjHom h (idGram K 6) C).toMonoidHom = J := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hst j).2 hj
    · intro hy
      exact ⟨(primeFormConjHom h (idGram K 6) C).symm y, (hst _).1 (by simpa using hy), by simp⟩
  rcases (hiff J).1 hJ with rfl | rfl | rfl
  · exact h12 (hJmap.symm.trans hm1)
  · exact h23 (hJmap.symm.trans hm2)
  · exact h13 (hJmap.symm.trans hm3).symm

theorem u6r_noncube (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : UnitaryFieldData 2 f K) (hf : Odd f) {A : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    {ψ : MulAut (primeFormP h (idGram K 6))} {J : Subgroup (primeFormP h (idGram K 6))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K 6)) A ψ J q) (hq : 64 ≤ q)
    (hA : ∀ a ∈ A, ∃ B : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) B = a)
    (g : primeFormUnitary h (idGram K 6)) (hg : primeFormConjHom h (idGram K 6) g = ψ) {μ : Kˣ}
    (hμ1 : μ ^ (2 ^ f + 1) = 1)
    (hg3 : (g : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) μ)
    (hμ : ∀ a : Kˣ, a ^ 3 ≠ μ) :
    q = (2 ^ f) ^ 3 ∧ (∀ J' : Subgroup (primeFormP h (idGram K 6)),
        GLAPComponent 3 (Lemma510Ns.fixSub ψ) J' → J' = J) ∧
      ∃ η ∈ A, η ≠ 1 ∧ ∃ H₁ H₂ H₃ : Subgroup (primeFormP h (idGram K 6)),
        (∀ H : Subgroup (primeFormP h (idGram K 6)),
          GLAPComponent 3 (Lemma510Ns.fixSub η) H ↔ (H = H₁ ∨ H = H₂ ∨ H = H₃)) ∧
        H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
        (∀ H : Subgroup (primeFormP h (idGram K 6)), (H = H₁ ∨ H = H₂ ∨ H = H₃) →
          IsTypeL2 (2 ^ f) (barOf 3 H)) ∧
        ∀ H H' : Subgroup (primeFormP h (idGram K 6)), (H = H₁ ∨ H = H₂ ∨ H = H₃) →
          (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) → ∃ e ∈ A, H.map e.toMonoidHom = H' := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin g) :=
    t6psuh_primaryData_toLin' h g.2 Nat.prime_three (by norm_num) hg3
  have hJg : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) g)) J := by
    rw [hg]
    exact c.comp
  obtain ⟨i₀, hi₀, hT₀⟩ := u6r_single hf g hg3 hμ
  obtain ⟨i, hi⟩ := u6r_exists_block g H hJg
  rw [hi₀ i] at hi
  have hJeq := u6r_eq_block g H hJg i₀ hi hT₀
  have hTq : IsTypeL2 q ↥((t6psub_block g i₀).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))) :=
    isTypeL2_of_barX_eq (u6r_comp_sub g hJg) (u6r_block_le g i₀) (u6r_block_normal g i₀)
      (u6r_block_quasisimple g H i₀) hi c.typeL2
  have hqr : q = (2 ^ f) ^ 3 := by
    rcases CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds _ q ((2 ^ f) ^ 3) hTq hT₀ with
      h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · omega
    · omega
  have hlayer : ∀ J' : Subgroup (primeFormP h (idGram K 6)),
      GLAPComponent 3 (Lemma510Ns.fixSub ψ) J' → J' = J := by
    intro J' hJ'
    have hJ'g : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K 6) g)) J' := by
      rw [hg]
      exact hJ'
    obtain ⟨i', hi'⟩ := u6r_exists_block g H hJ'g
    rw [hi₀ i'] at hi'
    rw [hJeq]
    exact u6r_eq_block g H hJ'g i₀ hi' hT₀
  refine ⟨hqr, hlayer, ?_⟩
  have hf4 : 4 ≤ 2 ^ f := by
    by_contra hlt
    have h3 : (2 ^ f) ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  obtain ⟨C, hCA, hCψ, ν, hν1, hC3, ζ, hζ1, hζ3, hζ⟩ :=
    u6r_exists_twist hO h c (by omega) hA g hg hg3
  obtain ⟨j, -, a, ha⟩ := u6r_exists_mul_cube h hμ ν
  set B₀ : primeFormUnitary h (idGram K 6) := g ^ j * C with hB₀
  have hB₀coe : (B₀ : GL (Fin 6) K) = (g : GL (Fin 6) K) ^ j * C := by
    rw [hB₀, Subgroup.coe_mul, Subgroup.coe_pow]
  have hCgj : (C : GL (Fin 6) K) * (g : GL (Fin 6) K) ^ j * (C : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (ζ ^ j) * (g : GL (Fin 6) K) ^ j := by
    rw [← conj_pow, hζ, (commute_scalar ζ (g : GL (Fin 6) K)).symm.mul_pow, map_pow]
  have hB₀3 : (B₀ : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (ν * μ ^ j) := by
    rw [hB₀coe, u6r_cube_twist (fun y => (commute_scalar (ζ ^ j) y).eq.symm) hCgj]
    have e1 : (Matrix.GeneralLinearGroup.scalar (Fin 6) (ζ ^ j)) ^ 3 = 1 := by
      rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow, map_one]
    have e2 : ((g : GL (Fin 6) K) ^ j) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (μ ^ j) := by
      rw [← pow_mul, mul_comm, pow_mul, hg3, map_pow]
    rw [e1, e2, hC3, one_mul, ← map_mul, mul_comm]
  have ha1 : a ^ (2 ^ f + 1) = 1 := by
    refine u6r_pow_succ_eq_one_of_cube h hf ?_
    rw [ha, mul_pow, ← pow_mul, mul_comm j, pow_mul, hμ1, one_pow, mul_one, hν1]
  obtain ⟨B, hBcoe, hBc⟩ := u6r_rescale B₀ ha1
  have hB3 : (B : GL (Fin 6) K) ^ 3 = 1 := by
    rw [hBcoe, (commute_scalar a⁻¹ (B₀ : GL (Fin 6) K)).symm.mul_pow, hB₀3, ← map_pow, ← map_mul,
      inv_pow, ha, inv_mul_cancel, map_one]
  have hgC : (g : GL (Fin 6) K) * C * (g : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ * C := by
    have hCg : (C : GL (Fin 6) K) * g = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g * C := by
      calc (C : GL (Fin 6) K) * g = (C : GL (Fin 6) K) * g * (C : GL (Fin 6) K)⁻¹ * C := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g * C := by rw [hζ]
    calc (g : GL (Fin 6) K) * C * (g : GL (Fin 6) K)⁻¹
        = (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * g * C) * (g : GL (Fin 6) K)⁻¹ := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ)⁻¹ * ((C : GL (Fin 6) K) * g) *
          (g : GL (Fin 6) K)⁻¹ := by rw [hCg]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ * C := by rw [map_inv]; group
  have hgB : (g : GL (Fin 6) K) * B * (g : GL (Fin 6) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ * B := by
    rw [hBcoe, hB₀coe]
    have hga : (g : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * g := (commute_scalar a⁻¹ _).eq
    have hgj : (g : GL (Fin 6) K) * (g : GL (Fin 6) K) ^ j = (g : GL (Fin 6) K) ^ j * g :=
      (Commute.self_pow _ _).eq
    have hzj : (g : GL (Fin 6) K) ^ j * Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ * (g : GL (Fin 6) K) ^ j :=
      (commute_scalar ζ⁻¹ _).eq
    calc (g : GL (Fin 6) K) * (Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          ((g : GL (Fin 6) K) ^ j * C)) * (g : GL (Fin 6) K)⁻¹
        = ((g : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹) *
          ((g : GL (Fin 6) K) ^ j * C) * (g : GL (Fin 6) K)⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          (((g : GL (Fin 6) K) * (g : GL (Fin 6) K) ^ j) * C * (g : GL (Fin 6) K)⁻¹) := by
          rw [hga]; group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          ((g : GL (Fin 6) K) ^ j * ((g : GL (Fin 6) K) * C * (g : GL (Fin 6) K)⁻¹)) := by
          rw [hgj]; group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          (((g : GL (Fin 6) K) ^ j * Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹) * C) := by
          rw [hgC]; group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ * (g : GL (Fin 6) K) ^ j * C) := by
          rw [hzj]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) a⁻¹ * ((g : GL (Fin 6) K) ^ j * C)) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, mul_comm a⁻¹ ζ⁻¹, map_mul]
          group
  have hζ1' : ζ⁻¹ ≠ 1 := inv_ne_one.2 hζ1
  obtain ⟨H₁, H₂, H₃, hiff, h12, h13, h23, htype, hm1, hm2, hm3⟩ :=
    u6r_triple hf hf4 B g hB3 hζ1' hgB
  rw [hg] at hm1 hm2 hm3
  have hBA : primeFormConjHom h (idGram K 6) B ∈ A := by
    rw [hBc, hB₀, map_mul, map_pow, hg]
    exact A.mul_mem (A.pow_mem c.mem j) hCA
  have hB1 : primeFormConjHom h (idGram K 6) B ≠ 1 := by
    intro h1
    apply hCψ
    rw [hBc, hB₀, map_mul, map_pow, hg] at h1
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) j)
  have hψψ : ψ * ψ ∈ A := A.mul_mem c.mem c.mem
  have h1A : (1 : MulAut (primeFormP h (idGram K 6))) ∈ A := A.one_mem
  refine ⟨_, hBA, hB1, H₁, H₂, H₃, hiff, h12, h13, h23, htype, ?_⟩
  rintro H H' (rfl | rfl | rfl) (rfl | rfl | rfl)
  · exact ⟨1, h1A, u6r_map_one _⟩
  · exact ⟨ψ, c.mem, hm1⟩
  · exact ⟨ψ * ψ, hψψ, by rw [u6r_map_mul, hm1, hm2]⟩
  · exact ⟨ψ * ψ, hψψ, by rw [u6r_map_mul, hm2, hm3]⟩
  · exact ⟨1, h1A, u6r_map_one _⟩
  · exact ⟨ψ, c.mem, hm2⟩
  · exact ⟨ψ, c.mem, hm3⟩
  · exact ⟨ψ * ψ, hψψ, by rw [u6r_map_mul, hm3, hm1]⟩
  · exact ⟨1, h1A, u6r_map_one _⟩

theorem u6r_core (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : UnitaryFieldData 2 f K) (hf : Odd f) {A : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    {ψ : MulAut (primeFormP h (idGram K 6))} {J : Subgroup (primeFormP h (idGram K 6))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K 6)) A ψ J q) (hq : 64 ≤ q)
    (hA : ∀ a ∈ A, ∃ B : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) B = a) :
    q = (2 ^ f) ^ 3 ∧ (∀ J' : Subgroup (primeFormP h (idGram K 6)),
        GLAPComponent 3 (Lemma510Ns.fixSub ψ) J' → J' = J) ∧
      ∃ η ∈ A, η ≠ 1 ∧ ∃ H₁ H₂ H₃ : Subgroup (primeFormP h (idGram K 6)),
        (∀ H : Subgroup (primeFormP h (idGram K 6)),
          GLAPComponent 3 (Lemma510Ns.fixSub η) H ↔ (H = H₁ ∨ H = H₂ ∨ H = H₃)) ∧
        H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
        (∀ H : Subgroup (primeFormP h (idGram K 6)), (H = H₁ ∨ H = H₂ ∨ H = H₃) →
          IsTypeL2 (2 ^ f) (barOf 3 H)) ∧
        ∀ H H' : Subgroup (primeFormP h (idGram K 6)), (H = H₁ ∨ H = H₂ ∨ H = H₃) →
          (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) → ∃ e ∈ A, H.map e.toMonoidHom = H' := by
  obtain ⟨g, hg⟩ := hA ψ c.mem
  obtain ⟨μ, hμ1, hg3⟩ := u6r_cube_scalar (le_refl 3 |>.trans (by norm_num)) g
    (by rw [hg]; exact c.elemAbelian.2 ψ c.mem)
  by_cases hcube : ∃ a : Kˣ, a ^ 3 = μ
  · obtain ⟨a, ha⟩ := hcube
    exact (u6r_cube_false hO h hf c (by omega) hA g hg hμ1 hg3 ha).elim
  · push Not at hcube
    exact u6r_noncube hO h hf c hq hA g hg hμ1 hg3 hcube

end Core

end CFSG.HardMathSupport.Dickson.Sec6.I1431
