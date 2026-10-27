module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpLevi
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open scoped MatrixGroups

section Form

variable {F : Type} [Field F] {n : ℕ}

theorem formJ_mul_self : formJ n F * formJ n F = -1 := by
  rw [formJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem formJ_transpose : (formJ n F)ᵀ = -formJ n F := by
  rw [formJ, fromBlocks_transpose, fromBlocks_neg]
  simp

variable (F n) in
@[expose] noncomputable def omega : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) :=
  Matrix.toBilin' (formJ n F)

theorem omega_apply (u v : Fin n ⊕ Fin n → F) : omega F n u v = u ⬝ᵥ (formJ n F *ᵥ v) :=
  Matrix.toBilin'_apply' _ u v

theorem omega_skew (u v : Fin n ⊕ Fin n → F) : omega F n u v = -omega F n v u := by
  rw [omega_apply, omega_apply, dotProduct_mulVec, ← mulVec_transpose, formJ_transpose,
    neg_mulVec, neg_dotProduct, dotProduct_comm]

theorem omega_nondegenerate : (omega F n).Nondegenerate := by
  refine LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ fun h => ?_
  have h1 := congrArg Matrix.det (formJ_mul_self (F := F) (n := n))
  rw [det_mul, h, zero_mul, det_neg, det_one, mul_one] at h1
  exact neg_one_pow_ne_zero (R := F) _ h1.symm

theorem omega_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {μ : F}
    (hA : Aᵀ * formJ n F * A = μ • formJ n F) (u v : Fin n ⊕ Fin n → F) :
    omega F n (A *ᵥ u) (A *ᵥ v) = μ * omega F n u v := by
  rw [omega_apply, omega_apply]
  have e1 : ∀ w, (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := fun w => by
    rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  rw [e1, mulVec_mulVec, mulVec_mulVec, hA, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem transpose_formJ_of_apply (col : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → F))
    (c c' : Fin n ⊕ Fin n) :
    ((Matrix.of fun r c => col c r)ᵀ * formJ n F * Matrix.of fun r c => col c r) c c' =
      omega F n (col c) (col c') := by
  rw [omega_apply]
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem mul_of_apply (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (col : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → F)) (r c : Fin n ⊕ Fin n) :
    (A * Matrix.of fun r c => col c r) r c = (A *ᵥ col c) r := by
  simp only [Matrix.mul_apply, mulVec, dotProduct, Matrix.of_apply]

end Form

section Std

variable {F : Type} [Field F] {n : ℕ}

theorem exists_adapted_symplectic_basis (h2 : (2 : F) ≠ 0)
    {a : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} (ha2 : a * a = 1)
    (hωa : ∀ u v, omega F n (a u) (a v) = -omega F n u v) :
    ∃ e f : Fin n → (Fin n ⊕ Fin n → F), (∀ i, a (e i) = e i) ∧ (∀ j, a (f j) = -f j) ∧
      (∀ i i', omega F n (e i) (e i') = 0) ∧ (∀ j j', omega F n (f j) (f j') = 0) ∧
      (∀ i j, omega F n (e i) (f j) = if i = j then 1 else 0) := by
  classical
  have hc : IsCompl (plusSp a) (minusSp a) := isCompl_plusSp_minusSp h2 ha2
  have hPP : ∀ u ∈ plusSp a, ∀ u' ∈ plusSp a, omega F n u u' = 0 := by
    intro u hu u' hu'
    have h1 := hωa u u'
    rw [mem_plusSp.mp hu, mem_plusSp.mp hu'] at h1
    have : (2 : F) * omega F n u u' = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hMM : ∀ u ∈ minusSp a, ∀ u' ∈ minusSp a, omega F n u u' = 0 := by
    intro u hu u' hu'
    have h1 := hωa u u'
    rw [mem_minusSp.mp hu, mem_minusSp.mp hu'] at h1
    simp only [map_neg, LinearMap.neg_apply, neg_neg] at h1
    have : (2 : F) * omega F n u u' = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hdim : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hsum : Module.finrank F (plusSp a) + Module.finrank F (minusSp a) = 2 * n := by
    rw [← hdim]
    exact Submodule.finrank_add_eq_of_isCompl hc
  have hle : ∀ U : Submodule F (Fin n ⊕ Fin n → F), (∀ u ∈ U, ∀ u' ∈ U, omega F n u u' = 0) →
      Module.finrank F U ≤ n := by
    intro U hU
    have hUle : U ≤ (omega F n).orthogonal U := by
      intro u hu
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      exact hU x hx u hu
    have h1 := Submodule.finrank_mono hUle
    rw [LinearMap.BilinForm.finrank_orthogonal omega_nondegenerate, hdim] at h1
    have h3 := Submodule.finrank_le U
    omega
  have hPn : Module.finrank F (plusSp a) = n := by
    have := hle _ hPP
    have := hle _ hMM
    omega
  have hMn : Module.finrank F (minusSp a) = n := by omega
  let b : Module.Basis (Fin n) F (plusSp a) := Module.finBasisOfFinrankEq F _ hPn
  let Ψ : minusSp a →ₗ[F] (Fin n → F) :=
    LinearMap.pi fun i => (omega F n (b i : Fin n ⊕ Fin n → F)).comp (minusSp a).subtype
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : ∀ i, omega F n (b i : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) = 0 := fun i => by
      have := congrFun hw i
      simpa [Ψ] using this
    have hPw : ∀ u ∈ plusSp a, omega F n u (w : Fin n ⊕ Fin n → F) = 0 := by
      intro u hu
      have hfun : ((omega F n).flip (w : Fin n ⊕ Fin n → F)).comp (plusSp a).subtype = 0 :=
        b.ext fun i => by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
          exact hw' i
      have := LinearMap.congr_fun hfun ⟨u, hu⟩
      simpa using this
    have hall : ∀ x, omega F n x (w : Fin n ⊕ Fin n → F) = 0 := by
      intro x
      have hx : x ∈ plusSp a ⊔ minusSp a := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨p, hp, m, hm, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, LinearMap.add_apply, hPw p hp, hMM m hm _ w.2, add_zero]
    exact Subtype.ext (omega_nondegenerate.2 (w : Fin n ⊕ Fin n → F) fun x => hall x)
  have hΨsurj : Function.Surjective Ψ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hΨinj
    rw [hMn, Module.finrank_fin_fun]
  choose f hf using fun j : Fin n => hΨsurj (Pi.single j 1)
  refine ⟨fun i => (b i : Fin n ⊕ Fin n → F), fun j => ((f j : minusSp a) : Fin n ⊕ Fin n → F),
    fun i => mem_plusSp.mp (b i).2, fun j => mem_minusSp.mp (f j).2,
    fun i i' => hPP _ (b i).2 _ (b i').2, fun j j' => hMM _ (f j).2 _ (f j').2, fun i j => ?_⟩
  have := congrFun (hf j) i
  simp only [Ψ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Pi.single_apply] at this
  exact this

theorem exists_sp_standardizing (h2 : (2 : F) ≠ 0) {A : GL (Fin n ⊕ Fin n) F}
    (hA : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * formJ n F * A = (-1 : F) • formJ n F)
    (hA2 : A * A = 1) : ∃ g ∈ StatedSp n F, A * g = g * Levi.a₀GL F n := by
  classical
  have happ : ∀ v, glLin A v = (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v := fun v =>
    glLin_apply A v
  have ha2 : glLin A * glLin A = 1 := by rw [← map_mul, hA2, map_one]
  have hωa : ∀ u v, omega F n (glLin A u) (glLin A v) = -omega F n u v := fun u v => by
    rw [happ, happ, omega_mulVec hA, neg_one_mul]
  obtain ⟨e, f, he, hf, hee, hff, hef⟩ := exists_adapted_symplectic_basis h2 ha2 hωa
  let col : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → F) := Sum.elim e f
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.of fun r c => col c r
  have hGJ : Gᵀ * formJ n F * G = formJ n F := by
    ext c c'
    rw [transpose_formJ_of_apply col c c']
    rcases c with i | j <;> rcases c' with i' | j'
    · simp [col, hee, formJ]
    · simp [col, hef, formJ, Matrix.one_apply]
    · simp only [col, Sum.elim_inl, Sum.elim_inr]
      rw [omega_skew, hef]
      simp [formJ, Matrix.one_apply, eq_comm]
    · simp [col, hff, formJ]
  have hGinv' : (-(formJ n F * Gᵀ * formJ n F)) * G = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Gᵀ, hGJ,
      formJ_mul_self, neg_neg]
  have hGinv : G * (-(formJ n F * Gᵀ * formJ n F)) = 1 := mul_eq_one_comm.mp hGinv'
  let g : GL (Fin n ⊕ Fin n) F := ⟨G, -(formJ n F * Gᵀ * formJ n F), hGinv, hGinv'⟩
  refine ⟨g, SymplecticTorusWeyl.mem_statedSp_iff.mpr hGJ, Units.ext ?_⟩
  show (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * G = G * diagonal (Levi.dsign F n)
  ext r c
  rw [mul_diagonal, mul_of_apply]
  have hAc : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ col c =
      Levi.dsign F n c • col c := by
    rw [← happ]
    rcases c with i | j
    · simp [col, he, Levi.dsign]
    · simp [col, hf, Levi.dsign]
  rw [hAc, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem oddCoreIn_fixed_conjSp_of_sim_involution [Finite F] (hF : Nat.card F = 3) (hn : 1 ≤ n)
    (A : gsp n F)
    (hA : ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
      formJ n F * (A : GL (Fin n ⊕ Fin n) F) = (-1 : F) • formJ n F)
    (hA2 : (A : GL (Fin n ⊕ Fin n) F) * A = 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (StatedSp n F) (conjSp n F A))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  obtain ⟨g, hg, hAg⟩ := exists_sp_standardizing h2 hA hA2
  set G : gsp n F := ⟨g, statedSp_le_gsp hg⟩ with hGdef
  set A₀ : gsp n F := ⟨Levi.a₀GL F n, a₀_mem_gsp⟩ with hA₀
  have hAeq : A = G * A₀ * G⁻¹ := by
    refine Subtype.ext ?_
    show (A : GL (Fin n ⊕ Fin n) F) = g * Levi.a₀GL F n * g⁻¹
    rw [← hAg]
    group
  rw [hAeq, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact oddCoreIn_fixed_conj_eq_bot _ _ (oddCoreIn_fixed_conjSp_a₀ hF hn)

end Std

end CFSG.ClassicalInvolution.Q3.TL4.SpL
